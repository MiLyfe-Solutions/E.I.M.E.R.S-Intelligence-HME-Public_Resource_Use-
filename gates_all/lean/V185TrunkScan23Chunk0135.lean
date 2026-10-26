import V185TrunkScan23Chunk0134

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_799189 : List Nat := [1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 3]
def baseStart_799189 : Nat := 118140960795 + 799189 * 2 ^ 59
def prefixEnd_799189 : Nat := 4983230072969 + 3 ^ 40 * 799189 * 2
def baseEnd_799189 : Nat := 410368090786178903062103

theorem tailTrace_799189 : CollatzResearch.WordTrace tailWord_799189 prefixEnd_799189 410368090786178903062103 := by
  unfold tailWord_799189
  simp only [CollatzResearch.WordTrace]
  refine ⟨29148817501682218459736621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19432545001121478973157747 29148817501682218459736621)
  ·
    refine ⟨10930806563130831922401233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29148817501682218459736621 10930806563130831922401233)
    ·
      refine ⟨8198104922348123941800925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10930806563130831922401233 8198104922348123941800925)
      ·
        refine ⟨3074289345880546478175347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8198104922348123941800925 3074289345880546478175347)
        ·
          refine ⟨4611434018820819717263021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3074289345880546478175347 4611434018820819717263021)
          ·
            refine ⟨1729287757057807393973633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4611434018820819717263021 1729287757057807393973633)
            ·
              refine ⟨1296965817793355545480225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729287757057807393973633 1296965817793355545480225)
              ·
                refine ⟨972724363345016659110169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296965817793355545480225 972724363345016659110169)
                ·
                  refine ⟨729543272508762494332627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 972724363345016659110169 729543272508762494332627)
                  ·
                    refine ⟨1094314908763143741498941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 729543272508762494332627 1094314908763143741498941)
                    ·
                      refine ⟨410368090786178903062103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1094314908763143741498941 410368090786178903062103)
                      ·
                        rfl

theorem cell23_799189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_799189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799189 prefixEnd_799189 := by exact prefixLift 799189
  have htrace : WordTrace (prefixWord ++ tailWord_799189) baseStart_799189 baseEnd_799189 := by
    simpa [prefixWord, tailWord_799189, baseEnd_799189] using wordTrace_append hprefix tailTrace_799189
  have hstable : (prefixWord ++ tailWord_799189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799189).length < 2 ^ (prefixWord ++ tailWord_799189).sum := by decide
  have hdescent : baseEnd_799189 < baseStart_799189 := by decide
  rcases family_descends (prefixWord ++ tailWord_799189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799212 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_799212 : Nat := 118140960795 + 799212 * 2 ^ 59
def prefixEnd_799212 : Nat := 4983230072969 + 3 ^ 40 * 799212 * 2
def baseEnd_799212 : Nat := 410379900841232313074497

theorem tailTrace_799212 : CollatzResearch.WordTrace tailWord_799212 prefixEnd_799212 410379900841232313074497 := by
  unfold tailWord_799212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574828190299446693911945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19433104253732595591882593 14574828190299446693911945)
  ·
    refine ⟨10931121142724585020433959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14574828190299446693911945 10931121142724585020433959)
    ·
      refine ⟨16396681714086877530650939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10931121142724585020433959 16396681714086877530650939)
      ·
        refine ⟨24595022571130316295976409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16396681714086877530650939 24595022571130316295976409)
        ·
          refine ⟨18446266928347737221982307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24595022571130316295976409 18446266928347737221982307)
          ·
            refine ⟨27669400392521605832973461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18446266928347737221982307 27669400392521605832973461)
            ·
              refine ⟨1297003143399450273420631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27669400392521605832973461 1297003143399450273420631)
              ·
                refine ⟨1945504715099175410130947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297003143399450273420631 1945504715099175410130947)
                ·
                  refine ⟨2918257072648763115196421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945504715099175410130947 2918257072648763115196421)
                  ·
                    refine ⟨547173201121643084099329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918257072648763115196421 547173201121643084099329)
                    ·
                      refine ⟨410379900841232313074497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547173201121643084099329 410379900841232313074497)
                      ·
                        rfl

theorem cell23_799212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_799212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799212 prefixEnd_799212 := by exact prefixLift 799212
  have htrace : WordTrace (prefixWord ++ tailWord_799212) baseStart_799212 baseEnd_799212 := by
    simpa [prefixWord, tailWord_799212, baseEnd_799212] using wordTrace_append hprefix tailTrace_799212
  have hstable : (prefixWord ++ tailWord_799212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799212).length < 2 ^ (prefixWord ++ tailWord_799212).sum := by decide
  have hdescent : baseEnd_799212 < baseStart_799212 := by decide
  rcases family_descends (prefixWord ++ tailWord_799212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799228 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_799228 : Nat := 118140960795 + 799228 * 2 ^ 59
def prefixEnd_799228 : Nat := 4983230072969 + 3 ^ 40 * 799228 * 2
def baseEnd_799228 : Nat := 410388116531704250474423

theorem tailTrace_799228 : CollatzResearch.WordTrace tailWord_799228 prefixEnd_799228 410388116531704250474423 := by
  unfold tailWord_799228
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575119974270464060203169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19433493299027285413604225 14575119974270464060203169)
  ·
    refine ⟨10931339980702848045152377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14575119974270464060203169 10931339980702848045152377)
    ·
      refine ⟨8198504985527136033864283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10931339980702848045152377 8198504985527136033864283)
      ·
        refine ⟨12297757478290704050796425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8198504985527136033864283 12297757478290704050796425)
        ·
          refine ⟨9223318108718028038097319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12297757478290704050796425 9223318108718028038097319)
          ·
            refine ⟨13834977163077042057145979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9223318108718028038097319 13834977163077042057145979)
            ·
              refine ⟨20752465744615563085718969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13834977163077042057145979 20752465744615563085718969)
              ·
                refine ⟨15564349308461672314289227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20752465744615563085718969 15564349308461672314289227)
                ·
                  refine ⟨23346523962692508471433841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15564349308461672314289227 23346523962692508471433841)
                  ·
                    refine ⟨17509892972019381353575381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23346523962692508471433841 17509892972019381353575381)
                    ·
                      refine ⟨410388116531704250474423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17509892972019381353575381 410388116531704250474423)
                      ·
                        rfl

theorem cell23_799228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_799228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799228 prefixEnd_799228 := by exact prefixLift 799228
  have htrace : WordTrace (prefixWord ++ tailWord_799228) baseStart_799228 baseEnd_799228 := by
    simpa [prefixWord, tailWord_799228, baseEnd_799228] using wordTrace_append hprefix tailTrace_799228
  have hstable : (prefixWord ++ tailWord_799228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799228).length < 2 ^ (prefixWord ++ tailWord_799228).sum := by decide
  have hdescent : baseEnd_799228 < baseStart_799228 := by decide
  rcases family_descends (prefixWord ++ tailWord_799228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799246 : List Nat := [4, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_799246 : Nat := 118140960795 + 799246 * 2 ^ 59
def prefixEnd_799246 : Nat := 4983230072969 + 3 ^ 40 * 799246 * 2
def baseEnd_799246 : Nat := 410397359183485180049341

theorem tailTrace_799246 : CollatzResearch.WordTrace tailWord_799246 prefixEnd_799246 410397359183485180049341 := by
  unfold tailWord_799246
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643862057809464649320199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19433930974983811463041061 3643862057809464649320199)
  ·
    refine ⟨5465793086714196973980299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3643862057809464649320199 5465793086714196973980299)
    ·
      refine ⟨8198689630071295460970449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465793086714196973980299 8198689630071295460970449)
      ·
        refine ⟨6149017222553471595727837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8198689630071295460970449 6149017222553471595727837)
        ·
          refine ⟨2305881458457551848397939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6149017222553471595727837 2305881458457551848397939)
          ·
            refine ⟨3458822187686327772596909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305881458457551848397939 3458822187686327772596909)
            ·
              refine ⟨1297058320382372914723841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3458822187686327772596909 1297058320382372914723841)
              ·
                refine ⟨972793740286779686042881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297058320382372914723841 972793740286779686042881)
                ·
                  refine ⟨729595305215084764532161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 972793740286779686042881 729595305215084764532161)
                  ·
                    refine ⟨547196478911313573399121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729595305215084764532161 547196478911313573399121)
                    ·
                      refine ⟨410397359183485180049341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547196478911313573399121 410397359183485180049341)
                      ·
                        rfl

theorem cell23_799246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_799246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799246 prefixEnd_799246 := by exact prefixLift 799246
  have htrace : WordTrace (prefixWord ++ tailWord_799246) baseStart_799246 baseEnd_799246 := by
    simpa [prefixWord, tailWord_799246, baseEnd_799246] using wordTrace_append hprefix tailTrace_799246
  have hstable : (prefixWord ++ tailWord_799246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799246).length < 2 ^ (prefixWord ++ tailWord_799246).sum := by decide
  have hdescent : baseEnd_799246 < baseStart_799246 := by decide
  rcases family_descends (prefixWord ++ tailWord_799246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799252 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 7]
def baseStart_799252 : Nat := 118140960795 + 799252 * 2 ^ 59
def prefixEnd_799252 : Nat := 4983230072969 + 3 ^ 40 * 799252 * 2
def baseEnd_799252 : Nat := 45600048896379128508257

theorem tailTrace_799252 : CollatzResearch.WordTrace tailWord_799252 prefixEnd_799252 45600048896379128508257 := by
  unfold tailWord_799252
  simp only [CollatzResearch.WordTrace]
  refine ⟨14575557650226990109640005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19434076866969320146186673 14575557650226990109640005)
  ·
    refine ⟨2732917059417560645557501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14575557650226990109640005 2732917059417560645557501)
    ·
      refine ⟨1024843897281585242084063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2732917059417560645557501 1024843897281585242084063)
      ·
        refine ⟨1537265845922377863126095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024843897281585242084063 1537265845922377863126095)
        ·
          refine ⟨2305898768883566794689143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537265845922377863126095 2305898768883566794689143)
          ·
            refine ⟨3458848153325350192033715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2305898768883566794689143 3458848153325350192033715)
            ·
              refine ⟨5188272229988025288050573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3458848153325350192033715 5188272229988025288050573)
              ·
                refine ⟨1945602086245509483018965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188272229988025288050573 1945602086245509483018965)
                ·
                  refine ⟨45600048896379128508257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1945602086245509483018965 45600048896379128508257)
                  ·
                    rfl

theorem cell23_799252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_799252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799252 prefixEnd_799252 := by exact prefixLift 799252
  have htrace : WordTrace (prefixWord ++ tailWord_799252) baseStart_799252 baseEnd_799252 := by
    simpa [prefixWord, tailWord_799252, baseEnd_799252] using wordTrace_append hprefix tailTrace_799252
  have hstable : (prefixWord ++ tailWord_799252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799252).length < 2 ^ (prefixWord ++ tailWord_799252).sum := by decide
  have hdescent : baseEnd_799252 < baseStart_799252 := by decide
  rcases family_descends (prefixWord ++ tailWord_799252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799285 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_799285 : Nat := 118140960795 + 799285 * 2 ^ 59
def prefixEnd_799285 : Nat := 4983230072969 + 3 ^ 40 * 799285 * 2
def baseEnd_799285 : Nat := 410417384929010527461661

theorem tailTrace_799285 : CollatzResearch.WordTrace tailWord_799285 prefixEnd_799285 410417384929010527461661 := by
  unfold tailWord_799285
  simp only [CollatzResearch.WordTrace]
  refine ⟨29152318909334426855231309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19434879272889617903487539 29152318909334426855231309)
  ·
    refine ⟨10932119591000410070711741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29152318909334426855231309 10932119591000410070711741)
    ·
      refine ⟨4099544846625153776516903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10932119591000410070711741 4099544846625153776516903)
      ·
        refine ⟨6149317269937730664775355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4099544846625153776516903 6149317269937730664775355)
        ·
          refine ⟨9223975904906595997163033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149317269937730664775355 9223975904906595997163033)
          ·
            refine ⟨6917981928679946997872275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9223975904906595997163033 6917981928679946997872275)
            ·
              refine ⟨10376972893019920496808413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6917981928679946997872275 10376972893019920496808413)
              ·
                refine ⟨3891364834882470186303155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10376972893019920496808413 3891364834882470186303155)
                ·
                  refine ⟨5837047252323705279454733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3891364834882470186303155 5837047252323705279454733)
                  ·
                    refine ⟨2188892719621389479795525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5837047252323705279454733 2188892719621389479795525)
                    ·
                      refine ⟨410417384929010527461661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2188892719621389479795525 410417384929010527461661)
                      ·
                        rfl

theorem cell23_799285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_799285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799285 prefixEnd_799285 := by exact prefixLift 799285
  have htrace : WordTrace (prefixWord ++ tailWord_799285) baseStart_799285 baseEnd_799285 := by
    simpa [prefixWord, tailWord_799285, baseEnd_799285] using wordTrace_append hprefix tailTrace_799285
  have hstable : (prefixWord ++ tailWord_799285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799285).length < 2 ^ (prefixWord ++ tailWord_799285).sum := by decide
  have hdescent : baseEnd_799285 < baseStart_799285 := by decide
  rcases family_descends (prefixWord ++ tailWord_799285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799286 : List Nat := [5, 1, 2, 1, 2, 3, 1, 3, 5]
def baseStart_799286 : Nat := 118140960795 + 799286 * 2 ^ 59
def prefixEnd_799286 : Nat := 4983230072969 + 3 ^ 40 * 799286 * 2
def baseEnd_799286 : Nat := 45601988712185002616573

theorem tailTrace_799286 : CollatzResearch.WordTrace tailWord_799286 prefixEnd_799286 45601988712185002616573 := by
  unfold tailWord_799286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822022211395675251626107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19434903588220536017345141 1822022211395675251626107)
  ·
    refine ⟨2733033317093512877439161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822022211395675251626107 2733033317093512877439161)
    ·
      refine ⟨2049774987820134658079371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2733033317093512877439161 2049774987820134658079371)
      ·
        refine ⟨3074662481730201987119057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049774987820134658079371 3074662481730201987119057)
        ·
          refine ⟨2305996861297651490339293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3074662481730201987119057 2305996861297651490339293)
          ·
            refine ⟨864748822986619308877235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2305996861297651490339293 864748822986619308877235)
            ·
              refine ⟨1297123234479928963315853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864748822986619308877235 1297123234479928963315853)
              ·
                refine ⟨486421212929973361243445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297123234479928963315853 486421212929973361243445)
                ·
                  refine ⟨45601988712185002616573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486421212929973361243445 45601988712185002616573)
                  ·
                    rfl

theorem cell23_799286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_799286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799286 prefixEnd_799286 := by exact prefixLift 799286
  have htrace : WordTrace (prefixWord ++ tailWord_799286) baseStart_799286 baseEnd_799286 := by
    simpa [prefixWord, tailWord_799286, baseEnd_799286] using wordTrace_append hprefix tailTrace_799286
  have hstable : (prefixWord ++ tailWord_799286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799286).length < 2 ^ (prefixWord ++ tailWord_799286).sum := by decide
  have hdescent : baseEnd_799286 < baseStart_799286 := by decide
  rcases family_descends (prefixWord ++ tailWord_799286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799352 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_799352 : Nat := 118140960795 + 799352 * 2 ^ 59
def prefixEnd_799352 : Nat := 4983230072969 + 3 ^ 40 * 799352 * 2
def baseEnd_799352 : Nat := 410451788132861765323853

theorem tailTrace_799352 : CollatzResearch.WordTrace tailWord_799352 prefixEnd_799352 410451788132861765323853 := by
  unfold tailWord_799352
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577381300045848648960155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19436508400061131531946873 14577381300045848648960155)
  ·
    refine ⟨21866071950068772973440233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14577381300045848648960155 21866071950068772973440233)
    ·
      refine ⟨16399553962551579730080175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21866071950068772973440233 16399553962551579730080175)
      ·
        refine ⟨24599330943827369595120263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16399553962551579730080175 24599330943827369595120263)
        ·
          refine ⟨36898996415741054392680395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24599330943827369595120263 36898996415741054392680395)
          ·
            refine ⟨55348494623611581589020593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36898996415741054392680395 55348494623611581589020593)
            ·
              refine ⟨41511370967708686191765445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55348494623611581589020593 41511370967708686191765445)
              ·
                refine ⟨7783382056445378660956021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41511370967708686191765445 7783382056445378660956021)
                ·
                  refine ⟨729692067791754249464627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7783382056445378660956021 729692067791754249464627)
                  ·
                    refine ⟨1094538101687631374196941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 729692067791754249464627 1094538101687631374196941)
                    ·
                      refine ⟨410451788132861765323853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1094538101687631374196941 410451788132861765323853)
                      ·
                        rfl

theorem cell23_799352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_799352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799352 prefixEnd_799352 := by exact prefixLift 799352
  have htrace : WordTrace (prefixWord ++ tailWord_799352) baseStart_799352 baseEnd_799352 := by
    simpa [prefixWord, tailWord_799352, baseEnd_799352] using wordTrace_append hprefix tailTrace_799352
  have hstable : (prefixWord ++ tailWord_799352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799352).length < 2 ^ (prefixWord ++ tailWord_799352).sum := by decide
  have hdescent : baseEnd_799352 < baseStart_799352 := by decide
  rcases family_descends (prefixWord ++ tailWord_799352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799395 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_799395 : Nat := 118140960795 + 799395 * 2 ^ 59
def prefixEnd_799395 : Nat := 4983230072969 + 3 ^ 40 * 799395 * 2
def baseEnd_799395 : Nat := 410473867801005097086155

theorem tailTrace_799395 : CollatzResearch.WordTrace tailWord_799395 prefixEnd_799395 410473867801005097086155 := by
  unfold tailWord_799395
  simp only [CollatzResearch.WordTrace]
  refine ⟨29156330938935915641735639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19437553959290610427823759 29156330938935915641735639)
  ·
    refine ⟨43734496408403873462603459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29156330938935915641735639 43734496408403873462603459)
    ·
      refine ⟨65601744612605810193905189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43734496408403873462603459 65601744612605810193905189)
      ·
        refine ⟨12300327114863589411357223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65601744612605810193905189 12300327114863589411357223)
        ·
          refine ⟨18450490672295384117035835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12300327114863589411357223 18450490672295384117035835)
          ·
            refine ⟨27675736008443076175553753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18450490672295384117035835 27675736008443076175553753)
            ·
              refine ⟨20756802006332307131665315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27675736008443076175553753 20756802006332307131665315)
              ·
                refine ⟨31135203009498460697497973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20756802006332307131665315 31135203009498460697497973)
                ·
                  refine ⟨2918925282140480690390435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31135203009498460697497973 2918925282140480690390435)
                  ·
                    refine ⟨4378387923210721035585653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2918925282140480690390435 4378387923210721035585653)
                    ·
                      refine ⟨410473867801005097086155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4378387923210721035585653 410473867801005097086155)
                      ·
                        rfl

theorem cell23_799395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_799395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799395 prefixEnd_799395 := by exact prefixLift 799395
  have htrace : WordTrace (prefixWord ++ tailWord_799395) baseStart_799395 baseEnd_799395 := by
    simpa [prefixWord, tailWord_799395, baseEnd_799395] using wordTrace_append hprefix tailTrace_799395
  have hstable : (prefixWord ++ tailWord_799395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799395).length < 2 ^ (prefixWord ++ tailWord_799395).sum := by decide
  have hdescent : baseEnd_799395 < baseStart_799395 := by decide
  rcases family_descends (prefixWord ++ tailWord_799395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799406 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 1, 5]
def baseStart_799406 : Nat := 118140960795 + 799406 * 2 ^ 59
def prefixEnd_799406 : Nat := 4983230072969 + 3 ^ 40 * 799406 * 2
def baseEnd_799406 : Nat := 136826505362734851349535

theorem tailTrace_799406 : CollatzResearch.WordTrace tailWord_799406 prefixEnd_799406 136826505362734851349535 := by
  unfold tailWord_799406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644591517737008065048259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19437821427930709680257381 3644591517737008065048259)
  ·
    refine ⟨5466887276605512097572389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644591517737008065048259 5466887276605512097572389)
    ·
      refine ⟨1025041364363533518294823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5466887276605512097572389 1025041364363533518294823)
      ·
        refine ⟨1537562046545300277442235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025041364363533518294823 1537562046545300277442235)
        ·
          refine ⟨2306343069817950416163353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537562046545300277442235 2306343069817950416163353)
          ·
            refine ⟨1729757302363462812122515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2306343069817950416163353 1729757302363462812122515)
            ·
              refine ⟨2594635953545194218183773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729757302363462812122515 2594635953545194218183773)
              ·
                refine ⟨972988482579447831818915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594635953545194218183773 972988482579447831818915)
                ·
                  refine ⟨1459482723869171747728373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972988482579447831818915 1459482723869171747728373)
                  ·
                    refine ⟨136826505362734851349535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1459482723869171747728373 136826505362734851349535)
                    ·
                      rfl

theorem cell23_799406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_799406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799406 prefixEnd_799406 := by exact prefixLift 799406
  have htrace : WordTrace (prefixWord ++ tailWord_799406) baseStart_799406 baseEnd_799406 := by
    simpa [prefixWord, tailWord_799406, baseEnd_799406] using wordTrace_append hprefix tailTrace_799406
  have hstable : (prefixWord ++ tailWord_799406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799406).length < 2 ^ (prefixWord ++ tailWord_799406).sum := by decide
  have hdescent : baseEnd_799406 < baseStart_799406 := by decide
  rcases family_descends (prefixWord ++ tailWord_799406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799422 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_799422 : Nat := 118140960795 + 799422 * 2 ^ 59
def prefixEnd_799422 : Nat := 4983230072969 + 3 ^ 40 * 799422 * 2
def baseEnd_799422 : Nat := 410487731778676491448531

theorem tailTrace_799422 : CollatzResearch.WordTrace tailWord_799422 prefixEnd_799422 410487731778676491448531 := by
  unfold tailWord_799422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644664463729762406621065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19438210473225399501979013 3644664463729762406621065)
  ·
    refine ⟨2733498347797321804965799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3644664463729762406621065 2733498347797321804965799)
    ·
      refine ⟨4100247521695982707448699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2733498347797321804965799 4100247521695982707448699)
      ·
        refine ⟨6150371282543974061173049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100247521695982707448699 6150371282543974061173049)
        ·
          refine ⟨4612778461907980545879787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6150371282543974061173049 4612778461907980545879787)
          ·
            refine ⟨6919167692861970818819681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612778461907980545879787 6919167692861970818819681)
            ·
              refine ⟨5189375769646478114114761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919167692861970818819681 5189375769646478114114761)
              ·
                refine ⟨3892031827234858585586071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189375769646478114114761 3892031827234858585586071)
                ·
                  refine ⟨5838047740852287878379107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892031827234858585586071 5838047740852287878379107)
                  ·
                    refine ⟨8757071611278431817568661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5838047740852287878379107 8757071611278431817568661)
                    ·
                      refine ⟨410487731778676491448531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8757071611278431817568661 410487731778676491448531)
                      ·
                        rfl

theorem cell23_799422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_799422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799422 prefixEnd_799422 := by exact prefixLift 799422
  have htrace : WordTrace (prefixWord ++ tailWord_799422) baseStart_799422 baseEnd_799422 := by
    simpa [prefixWord, tailWord_799422, baseEnd_799422] using wordTrace_append hprefix tailTrace_799422
  have hstable : (prefixWord ++ tailWord_799422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799422).length < 2 ^ (prefixWord ++ tailWord_799422).sum := by decide
  have hdescent : baseEnd_799422 < baseStart_799422 := by decide
  rcases family_descends (prefixWord ++ tailWord_799422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799460 : List Nat := [2, 3, 1, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_799460 : Nat := 118140960795 + 799460 * 2 ^ 59
def prefixEnd_799460 : Nat := 4983230072969 + 3 ^ 40 * 799460 * 2
def baseEnd_799460 : Nat := 410507244043547342773357

theorem tailTrace_799460 : CollatzResearch.WordTrace tailWord_799460 prefixEnd_799460 410507244043547342773357 := by
  unfold tailWord_799460
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579350841850215871425917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19439134455800287828567889 14579350841850215871425917)
  ·
    refine ⟨5467256565693830951784719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14579350841850215871425917 5467256565693830951784719)
    ·
      refine ⟨8200884848540746427677079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467256565693830951784719 8200884848540746427677079)
      ·
        refine ⟨12301327272811119641515619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8200884848540746427677079 12301327272811119641515619)
        ·
          refine ⟨18451990909216679462273429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12301327272811119641515619 18451990909216679462273429)
          ·
            refine ⟨864937073869531849794067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18451990909216679462273429 864937073869531849794067)
            ·
              refine ⟨1297405610804297774691101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 864937073869531849794067 1297405610804297774691101)
              ·
                refine ⟨486527104051611665509163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1297405610804297774691101 486527104051611665509163)
                ·
                  refine ⟨729790656077417498263745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486527104051611665509163 729790656077417498263745)
                  ·
                    refine ⟨547342992058063123697809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 729790656077417498263745 547342992058063123697809)
                    ·
                      refine ⟨410507244043547342773357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547342992058063123697809 410507244043547342773357)
                      ·
                        rfl

theorem cell23_799460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_799460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799460 prefixEnd_799460 := by exact prefixLift 799460
  have htrace : WordTrace (prefixWord ++ tailWord_799460) baseStart_799460 baseEnd_799460 := by
    simpa [prefixWord, tailWord_799460, baseEnd_799460] using wordTrace_append hprefix tailTrace_799460
  have hstable : (prefixWord ++ tailWord_799460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799460).length < 2 ^ (prefixWord ++ tailWord_799460).sum := by decide
  have hdescent : baseEnd_799460 < baseStart_799460 := by decide
  rcases family_descends (prefixWord ++ tailWord_799460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799492 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_799492 : Nat := 118140960795 + 799492 * 2 ^ 59
def prefixEnd_799492 : Nat := 4983230072969 + 3 ^ 40 * 799492 * 2
def baseEnd_799492 : Nat := 136841225141497072524403

theorem tailTrace_799492 : CollatzResearch.WordTrace tailWord_799492 prefixEnd_799492 136841225141497072524403 := by
  unfold tailWord_799492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14579934409792250604008365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19439912546389667472011153 14579934409792250604008365)
  ·
    refine ⟨5467475403672093976503137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14579934409792250604008365 5467475403672093976503137)
    ·
      refine ⟨4100606552754070482377353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5467475403672093976503137 4100606552754070482377353)
      ·
        refine ⟨3075454914565552861783015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100606552754070482377353 3075454914565552861783015)
        ·
          refine ⟨4613182371848329292674523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075454914565552861783015 4613182371848329292674523)
          ·
            refine ⟨6919773557772493939011785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4613182371848329292674523 6919773557772493939011785)
            ·
              refine ⟨5189830168329370454258839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6919773557772493939011785 5189830168329370454258839)
              ·
                refine ⟨7784745252494055681388259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189830168329370454258839 7784745252494055681388259)
                ·
                  refine ⟨11677117878741083522082389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784745252494055681388259 11677117878741083522082389)
                  ·
                    refine ⟨136841225141497072524403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11677117878741083522082389 136841225141497072524403)
                    ·
                      rfl

theorem cell23_799492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_799492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799492 prefixEnd_799492 := by exact prefixLift 799492
  have htrace : WordTrace (prefixWord ++ tailWord_799492) baseStart_799492 baseEnd_799492 := by
    simpa [prefixWord, tailWord_799492, baseEnd_799492] using wordTrace_append hprefix tailTrace_799492
  have hstable : (prefixWord ++ tailWord_799492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799492).length < 2 ^ (prefixWord ++ tailWord_799492).sum := by decide
  have hdescent : baseEnd_799492 < baseStart_799492 := by decide
  rcases family_descends (prefixWord ++ tailWord_799492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799499 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 4, 2]
def baseStart_799499 : Nat := 118140960795 + 799499 * 2 ^ 59
def prefixEnd_799499 : Nat := 4983230072969 + 3 ^ 40 * 799499 * 2
def baseEnd_799499 : Nat := 410527269789072690185677

theorem tailTrace_799499 : CollatzResearch.WordTrace tailWord_799499 prefixEnd_799499 410527269789072690185677 := by
  unfold tailWord_799499
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160124130559141403521551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19440082753706094269014367 29160124130559141403521551)
  ·
    refine ⟨43740186195838712105282327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29160124130559141403521551 43740186195838712105282327)
    ·
      refine ⟨65610279293758068157923491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43740186195838712105282327 65610279293758068157923491)
      ·
        refine ⟨98415418940637102236885237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65610279293758068157923491 98415418940637102236885237)
        ·
          refine ⟨9226445525684728334707991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98415418940637102236885237 9226445525684728334707991)
          ·
            refine ⟨13839668288527092502061987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226445525684728334707991 13839668288527092502061987)
            ·
              refine ⟨20759502432790638753092981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839668288527092502061987 20759502432790638753092981)
              ·
                refine ⟨1946203353074122383102467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20759502432790638753092981 1946203353074122383102467)
                ·
                  refine ⟨2919305029611183574653701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946203353074122383102467 2919305029611183574653701)
                  ·
                    refine ⟨547369693052096920247569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919305029611183574653701 547369693052096920247569)
                    ·
                      refine ⟨410527269789072690185677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547369693052096920247569 410527269789072690185677)
                      ·
                        rfl

theorem cell23_799499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 4, 2].length) (baseStart_799499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799499 prefixEnd_799499 := by exact prefixLift 799499
  have htrace : WordTrace (prefixWord ++ tailWord_799499) baseStart_799499 baseEnd_799499 := by
    simpa [prefixWord, tailWord_799499, baseEnd_799499] using wordTrace_append hprefix tailTrace_799499
  have hstable : (prefixWord ++ tailWord_799499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799499).length < 2 ^ (prefixWord ++ tailWord_799499).sum := by decide
  have hdescent : baseEnd_799499 < baseStart_799499 := by decide
  rcases family_descends (prefixWord ++ tailWord_799499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799512 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_799512 : Nat := 118140960795 + 799512 * 2 ^ 59
def prefixEnd_799512 : Nat := 4983230072969 + 3 ^ 40 * 799512 * 2
def baseEnd_799512 : Nat := 410533945037581139323117

theorem tailTrace_799512 : CollatzResearch.WordTrace tailWord_799512 prefixEnd_799512 410533945037581139323117 := by
  unfold tailWord_799512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580299139756022311872395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19440398853008029749163193 14580299139756022311872395)
  ·
    refine ⟨21870448709634033467808593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14580299139756022311872395 21870448709634033467808593)
    ·
      refine ⟨16402836532225525100856445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21870448709634033467808593 16402836532225525100856445)
      ·
        refine ⟨6151063699584571912821167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16402836532225525100856445 6151063699584571912821167)
        ·
          refine ⟨9226595549376857869231751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151063699584571912821167 9226595549376857869231751)
          ·
            refine ⟨13839893324065286803847627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9226595549376857869231751 13839893324065286803847627)
            ·
              refine ⟨20759839986097930205771441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13839893324065286803847627 20759839986097930205771441)
              ·
                refine ⟨15569879989573447654328581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20759839986097930205771441 15569879989573447654328581)
                ·
                  refine ⟨2919352498045021435186609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15569879989573447654328581 2919352498045021435186609)
                  ·
                    refine ⟨2189514373533766076389957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2919352498045021435186609 2189514373533766076389957)
                    ·
                      refine ⟨410533945037581139323117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2189514373533766076389957 410533945037581139323117)
                      ·
                        rfl

theorem cell23_799512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_799512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799512 prefixEnd_799512 := by exact prefixLift 799512
  have htrace : WordTrace (prefixWord ++ tailWord_799512) baseStart_799512 baseEnd_799512 := by
    simpa [prefixWord, tailWord_799512, baseEnd_799512] using wordTrace_append hprefix tailTrace_799512
  have hstable : (prefixWord ++ tailWord_799512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799512).length < 2 ^ (prefixWord ++ tailWord_799512).sum := by decide
  have hdescent : baseEnd_799512 < baseStart_799512 := by decide
  rcases family_descends (prefixWord ++ tailWord_799512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799516 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_799516 : Nat := 118140960795 + 799516 * 2 ^ 59
def prefixEnd_799516 : Nat := 4983230072969 + 3 ^ 40 * 799516 * 2
def baseEnd_799516 : Nat := 410535998960199123673099

theorem tailTrace_799516 : CollatzResearch.WordTrace tailWord_799516 prefixEnd_799516 410535998960199123673099 := by
  unfold tailWord_799516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14580372085748776653445201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19440496114331702204593601 14580372085748776653445201)
  ·
    refine ⟨10935279064311582490083901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14580372085748776653445201 10935279064311582490083901)
    ·
      refine ⟨4100729649116843433781463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10935279064311582490083901 4100729649116843433781463)
      ·
        refine ⟨6151094473675265150672195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100729649116843433781463 6151094473675265150672195)
        ·
          refine ⟨9226641710512897726008293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151094473675265150672195 9226641710512897726008293)
          ·
            refine ⟨1729995320721168323626555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9226641710512897726008293 1729995320721168323626555)
            ·
              refine ⟨2594992981081752485439833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729995320721168323626555 2594992981081752485439833)
              ·
                refine ⟨1946244735811314364079875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594992981081752485439833 1946244735811314364079875)
                ·
                  refine ⟨2919367103716971546119813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946244735811314364079875 2919367103716971546119813)
                  ·
                    refine ⟨547381331946932164897465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919367103716971546119813 547381331946932164897465)
                    ·
                      refine ⟨410535998960199123673099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547381331946932164897465 410535998960199123673099)
                      ·
                        rfl

theorem cell23_799516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_799516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799516 prefixEnd_799516 := by exact prefixLift 799516
  have htrace : WordTrace (prefixWord ++ tailWord_799516) baseStart_799516 baseEnd_799516 := by
    simpa [prefixWord, tailWord_799516, baseEnd_799516] using wordTrace_append hprefix tailTrace_799516
  have hstable : (prefixWord ++ tailWord_799516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799516).length < 2 ^ (prefixWord ++ tailWord_799516).sum := by decide
  have hdescent : baseEnd_799516 < baseStart_799516 := by decide
  rcases family_descends (prefixWord ++ tailWord_799516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799552 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_799552 : Nat := 118140960795 + 799552 * 2 ^ 59
def prefixEnd_799552 : Nat := 4983230072969 + 3 ^ 40 * 799552 * 2
def baseEnd_799552 : Nat := 136851494754586994274311

theorem tailTrace_799552 : CollatzResearch.WordTrace tailWord_799552 prefixEnd_799552 136851494754586994274311 := by
  unfold tailWord_799552
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581028599683565727600455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19441371466244754303467273 14581028599683565727600455)
  ·
    refine ⟨21871542899525348591400683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14581028599683565727600455 21871542899525348591400683)
    ·
      refine ⟨32807314349288022887101025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21871542899525348591400683 32807314349288022887101025)
      ·
        refine ⟨24605485761966017165325769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32807314349288022887101025 24605485761966017165325769)
        ·
          refine ⟨18454114321474512873994327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24605485761966017165325769 18454114321474512873994327)
          ·
            refine ⟨27681171482211769310991491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18454114321474512873994327 27681171482211769310991491)
            ·
              refine ⟨41521757223317653966487237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27681171482211769310991491 41521757223317653966487237)
              ·
                refine ⟨7785329479372060118716357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41521757223317653966487237 7785329479372060118716357)
                ·
                  refine ⟨1459749277382261272259317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7785329479372060118716357 1459749277382261272259317)
                  ·
                    refine ⟨136851494754586994274311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1459749277382261272259317 136851494754586994274311)
                    ·
                      rfl

theorem cell23_799552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_799552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799552 prefixEnd_799552 := by exact prefixLift 799552
  have htrace : WordTrace (prefixWord ++ tailWord_799552) baseStart_799552 baseEnd_799552 := by
    simpa [prefixWord, tailWord_799552, baseEnd_799552] using wordTrace_append hprefix tailTrace_799552
  have hstable : (prefixWord ++ tailWord_799552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799552).length < 2 ^ (prefixWord ++ tailWord_799552).sum := by decide
  have hdescent : baseEnd_799552 < baseStart_799552 := by decide
  rcases family_descends (prefixWord ++ tailWord_799552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799559 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 5, 2]
def baseStart_799559 : Nat := 118140960795 + 799559 * 2 ^ 59
def prefixEnd_799559 : Nat := 4983230072969 + 3 ^ 40 * 799559 * 2
def baseEnd_799559 : Nat := 410558078628342455435401

theorem tailTrace_799559 : CollatzResearch.WordTrace tailWord_799559 prefixEnd_799559 410558078628342455435401 := by
  unfold tailWord_799559
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162312510341771650705731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19441541673561181100470487 29162312510341771650705731)
  ·
    refine ⟨43743468765512657476058597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162312510341771650705731 43743468765512657476058597)
    ·
      refine ⟨8201900393533623276760987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43743468765512657476058597 8201900393533623276760987)
      ·
        refine ⟨12302850590300434915141481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201900393533623276760987 12302850590300434915141481)
        ·
          refine ⟨9227137942725326186356111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12302850590300434915141481 9227137942725326186356111)
          ·
            refine ⟨13840706914087989279534167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227137942725326186356111 13840706914087989279534167)
            ·
              refine ⟨20761060371131983919301251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13840706914087989279534167 20761060371131983919301251)
              ·
                refine ⟨31141590556697975878951877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20761060371131983919301251 31141590556697975878951877)
                ·
                  refine ⟨5839048229380870477303477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31141590556697975878951877 5839048229380870477303477)
                  ·
                    refine ⟨547410771504456607247201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5839048229380870477303477 547410771504456607247201)
                    ·
                      refine ⟨410558078628342455435401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547410771504456607247201 410558078628342455435401)
                      ·
                        rfl

theorem cell23_799559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_799559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799559 prefixEnd_799559 := by exact prefixLift 799559
  have htrace : WordTrace (prefixWord ++ tailWord_799559) baseStart_799559 baseEnd_799559 := by
    simpa [prefixWord, tailWord_799559, baseEnd_799559] using wordTrace_append hprefix tailTrace_799559
  have hstable : (prefixWord ++ tailWord_799559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799559).length < 2 ^ (prefixWord ++ tailWord_799559).sum := by decide
  have hdescent : baseEnd_799559 < baseStart_799559 := by decide
  rcases family_descends (prefixWord ++ tailWord_799559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799562 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_799562 : Nat := 118140960795 + 799562 * 2 ^ 59
def prefixEnd_799562 : Nat := 4983230072969 + 3 ^ 40 * 799562 * 2
def baseEnd_799562 : Nat := 410559619070305943697887

theorem tailTrace_799562 : CollatzResearch.WordTrace tailWord_799562 prefixEnd_799562 410559619070305943697887 := by
  unfold tailWord_799562
  simp only [CollatzResearch.WordTrace]
  refine ⟨7290605482332725790766235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19441614619553935442043293 7290605482332725790766235)
  ·
    refine ⟨10935908223499088686149353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7290605482332725790766235 10935908223499088686149353)
    ·
      refine ⟨8201931167624316514612015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10935908223499088686149353 8201931167624316514612015)
      ·
        refine ⟨12302896751436474771918023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201931167624316514612015 12302896751436474771918023)
        ·
          refine ⟨18454345127154712157877035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12302896751436474771918023 18454345127154712157877035)
          ·
            refine ⟨27681517690732068236815553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18454345127154712157877035 27681517690732068236815553)
            ·
              refine ⟨20761138268049051177611665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27681517690732068236815553 20761138268049051177611665)
              ·
                refine ⟨15570853701036788383208749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20761138268049051177611665 15570853701036788383208749)
                ·
                  refine ⟨5839070137888795643703281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15570853701036788383208749 5839070137888795643703281)
                  ·
                    refine ⟨4379302603416596732777461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5839070137888795643703281 4379302603416596732777461)
                    ·
                      refine ⟨410559619070305943697887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4379302603416596732777461 410559619070305943697887)
                      ·
                        rfl

theorem cell23_799562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_799562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799562 prefixEnd_799562 := by exact prefixLift 799562
  have htrace : WordTrace (prefixWord ++ tailWord_799562) baseStart_799562 baseEnd_799562 := by
    simpa [prefixWord, tailWord_799562, baseEnd_799562] using wordTrace_append hprefix tailTrace_799562
  have hstable : (prefixWord ++ tailWord_799562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799562).length < 2 ^ (prefixWord ++ tailWord_799562).sum := by decide
  have hdescent : baseEnd_799562 < baseStart_799562 := by decide
  rcases family_descends (prefixWord ++ tailWord_799562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799569 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_799569 : Nat := 118140960795 + 799569 * 2 ^ 59
def prefixEnd_799569 : Nat := 4983230072969 + 3 ^ 40 * 799569 * 2
def baseEnd_799569 : Nat := 136854404478295805436785

theorem tailTrace_799569 : CollatzResearch.WordTrace tailWord_799569 prefixEnd_799569 136854404478295805436785 := by
  unfold tailWord_799569
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162677240305543358569761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19441784826870362239046507 29162677240305543358569761)
  ·
    refine ⟨21872007930229157518927321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29162677240305543358569761 21872007930229157518927321)
    ·
      refine ⟨16404005947671868139195491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21872007930229157518927321 16404005947671868139195491)
      ·
        refine ⟨24606008921507802208793237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16404005947671868139195491 24606008921507802208793237)
        ·
          refine ⟨1153406668195678228537183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24606008921507802208793237 1153406668195678228537183)
          ·
            refine ⟨1730110002293517342805775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153406668195678228537183 1730110002293517342805775)
            ·
              refine ⟨2595165003440276014208663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730110002293517342805775 2595165003440276014208663)
              ·
                refine ⟨3892747505160414021312995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595165003440276014208663 3892747505160414021312995)
                ·
                  refine ⟨5839121257740621031969493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892747505160414021312995 5839121257740621031969493)
                  ·
                    refine ⟨136854404478295805436785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5839121257740621031969493 136854404478295805436785)
                    ·
                      rfl

theorem cell23_799569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_799569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799569 prefixEnd_799569 := by exact prefixLift 799569
  have htrace : WordTrace (prefixWord ++ tailWord_799569) baseStart_799569 baseEnd_799569 := by
    simpa [prefixWord, tailWord_799569, baseEnd_799569] using wordTrace_append hprefix tailTrace_799569
  have hstable : (prefixWord ++ tailWord_799569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799569).length < 2 ^ (prefixWord ++ tailWord_799569).sum := by decide
  have hdescent : baseEnd_799569 < baseStart_799569 := by decide
  rcases family_descends (prefixWord ++ tailWord_799569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799589 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 4]
def baseStart_799589 : Nat := 118140960795 + 799589 * 2 ^ 59
def prefixEnd_799589 : Nat := 4983230072969 + 3 ^ 40 * 799589 * 2
def baseEnd_799589 : Nat := 410573483047977338060263

theorem tailTrace_799589 : CollatzResearch.WordTrace tailWord_799589 prefixEnd_799589 410573483047977338060263 := by
  unfold tailWord_799589
  simp only [CollatzResearch.WordTrace]
  refine ⟨29163406700233086774297821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19442271133488724516198547 29163406700233086774297821)
  ·
    refine ⟨10936277512587407540361683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29163406700233086774297821 10936277512587407540361683)
    ·
      refine ⟨16404416268881111310542525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10936277512587407540361683 16404416268881111310542525)
      ·
        refine ⟨6151656100830416741453447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16404416268881111310542525 6151656100830416741453447)
        ·
          refine ⟨9227484151245625112180171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6151656100830416741453447 9227484151245625112180171)
          ·
            refine ⟨13841226226868437668270257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9227484151245625112180171 13841226226868437668270257)
            ·
              refine ⟨10380919670151328251202693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13841226226868437668270257 10380919670151328251202693)
              ·
                refine ⟨1946422438153374047100505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10380919670151328251202693 1946422438153374047100505)
                ·
                  refine ⟨1459816828615030535325379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946422438153374047100505 1459816828615030535325379)
                  ·
                    refine ⟨2189725242922545802988069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1459816828615030535325379 2189725242922545802988069)
                    ·
                      refine ⟨410573483047977338060263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2189725242922545802988069 410573483047977338060263)
                      ·
                        rfl

theorem cell23_799589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_799589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799589 prefixEnd_799589 := by exact prefixLift 799589
  have htrace : WordTrace (prefixWord ++ tailWord_799589) baseStart_799589 baseEnd_799589 := by
    simpa [prefixWord, tailWord_799589, baseEnd_799589] using wordTrace_append hprefix tailTrace_799589
  have hstable : (prefixWord ++ tailWord_799589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799589).length < 2 ^ (prefixWord ++ tailWord_799589).sum := by decide
  have hdescent : baseEnd_799589 < baseStart_799589 := by decide
  rcases family_descends (prefixWord ++ tailWord_799589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799606 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4]
def baseStart_799606 : Nat := 118140960795 + 799606 * 2 ^ 59
def prefixEnd_799606 : Nat := 4983230072969 + 3 ^ 40 * 799606 * 2
def baseEnd_799606 : Nat := 410582212219103771547685

theorem tailTrace_799606 : CollatzResearch.WordTrace tailWord_799606 prefixEnd_799606 410582212219103771547685 := by
  unfold tailWord_799606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1822751671323218667354167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19442684494114332451777781 1822751671323218667354167)
  ·
    refine ⟨2734127506984828001031251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1822751671323218667354167 2734127506984828001031251)
    ·
      refine ⟨4101191260477242001546877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734127506984828001031251 4101191260477242001546877)
      ·
        refine ⟨1537946722678965750580079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4101191260477242001546877 1537946722678965750580079)
        ·
          refine ⟨2306920084018448625870119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537946722678965750580079 2306920084018448625870119)
          ·
            refine ⟨3460380126027672938805179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306920084018448625870119 3460380126027672938805179)
            ·
              refine ⟨5190570189041509408207769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460380126027672938805179 5190570189041509408207769)
              ·
                refine ⟨3892927641781132056155827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190570189041509408207769 3892927641781132056155827)
                ·
                  refine ⟨5839391462671698084233741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892927641781132056155827 5839391462671698084233741)
                  ·
                    refine ⟨2189771798501886781587653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5839391462671698084233741 2189771798501886781587653)
                    ·
                      refine ⟨410582212219103771547685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2189771798501886781587653 410582212219103771547685)
                      ·
                        rfl

theorem cell23_799606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_799606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799606 prefixEnd_799606 := by exact prefixLift 799606
  have htrace : WordTrace (prefixWord ++ tailWord_799606) baseStart_799606 baseEnd_799606 := by
    simpa [prefixWord, tailWord_799606, baseEnd_799606] using wordTrace_append hprefix tailTrace_799606
  have hstable : (prefixWord ++ tailWord_799606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799606).length < 2 ^ (prefixWord ++ tailWord_799606).sum := by decide
  have hdescent : baseEnd_799606 < baseStart_799606 := by decide
  rcases family_descends (prefixWord ++ tailWord_799606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799609 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_799609 : Nat := 118140960795 + 799609 * 2 ^ 59
def prefixEnd_799609 : Nat := 4983230072969 + 3 ^ 40 * 799609 * 2
def baseEnd_799609 : Nat := 410583752661067259810171

theorem tailTrace_799609 : CollatzResearch.WordTrace tailWord_799609 prefixEnd_799609 410583752661067259810171 := by
  unfold tailWord_799609
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164136160160630190025881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19442757440107086793350587 29164136160160630190025881)
  ·
    refine ⟨21873102120120472642519411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29164136160160630190025881 21873102120120472642519411)
    ·
      refine ⟨32809653180180708963779117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21873102120120472642519411 32809653180180708963779117)
      ·
        refine ⟨12303619942567765861417169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32809653180180708963779117 12303619942567765861417169)
        ·
          refine ⟨9227714956925824396062877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12303619942567765861417169 9227714956925824396062877)
          ·
            refine ⟨3460393108847184148523579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9227714956925824396062877 3460393108847184148523579)
            ·
              refine ⟨5190589663270776222785369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460393108847184148523579 5190589663270776222785369)
              ·
                refine ⟨3892942247453082167089027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190589663270776222785369 3892942247453082167089027)
                ·
                  refine ⟨5839413371179623250633541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892942247453082167089027 5839413371179623250633541)
                  ·
                    refine ⟨1094890007096179359493789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839413371179623250633541 1094890007096179359493789)
                    ·
                      refine ⟨410583752661067259810171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1094890007096179359493789 410583752661067259810171)
                      ·
                        rfl

theorem cell23_799609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_799609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799609 prefixEnd_799609 := by exact prefixLift 799609
  have htrace : WordTrace (prefixWord ++ tailWord_799609) baseStart_799609 baseEnd_799609 := by
    simpa [prefixWord, tailWord_799609, baseEnd_799609] using wordTrace_append hprefix tailTrace_799609
  have hstable : (prefixWord ++ tailWord_799609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799609).length < 2 ^ (prefixWord ++ tailWord_799609).sum := by decide
  have hdescent : baseEnd_799609 < baseStart_799609 := by decide
  rcases family_descends (prefixWord ++ tailWord_799609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799626 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3]
def baseStart_799626 : Nat := 118140960795 + 799626 * 2 ^ 59
def prefixEnd_799626 : Nat := 4983230072969 + 3 ^ 40 * 799626 * 2
def baseEnd_799626 : Nat := 410592481832193693297593

theorem tailTrace_799626 : CollatzResearch.WordTrace tailWord_799626 prefixEnd_799626 410592481832193693297593 := by
  unfold tailWord_799626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291189050274760523348683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19443170800732694728929821 7291189050274760523348683)
  ·
    refine ⟨10936783575412140785023025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291189050274760523348683 10936783575412140785023025)
    ·
      refine ⟨8202587681559105588767269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10936783575412140785023025 8202587681559105588767269)
      ·
        refine ⟨1537985190292332297893863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8202587681559105588767269 1537985190292332297893863)
        ·
          refine ⟨2306977785438498446840795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537985190292332297893863 2306977785438498446840795)
          ·
            refine ⟨3460466678157747670261193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306977785438498446840795 3460466678157747670261193)
            ·
              refine ⟨2595350008618310752695895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460466678157747670261193 2595350008618310752695895)
              ·
                refine ⟨3893025012927466129043843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595350008618310752695895 3893025012927466129043843)
                ·
                  refine ⟨5839537519391199193565765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3893025012927466129043843 5839537519391199193565765)
                  ·
                    refine ⟨1094913284885849848793581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5839537519391199193565765 1094913284885849848793581)
                    ·
                      refine ⟨410592481832193693297593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1094913284885849848793581 410592481832193693297593)
                      ·
                        rfl

theorem cell23_799626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_799626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799626 prefixEnd_799626 := by exact prefixLift 799626
  have htrace : WordTrace (prefixWord ++ tailWord_799626) baseStart_799626 baseEnd_799626 := by
    simpa [prefixWord, tailWord_799626, baseEnd_799626] using wordTrace_append hprefix tailTrace_799626
  have hstable : (prefixWord ++ tailWord_799626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799626).length < 2 ^ (prefixWord ++ tailWord_799626).sum := by decide
  have hdescent : baseEnd_799626 < baseStart_799626 := by decide
  rcases family_descends (prefixWord ++ tailWord_799626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799713 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_799713 : Nat := 118140960795 + 799713 * 2 ^ 59
def prefixEnd_799713 : Nat := 4983230072969 + 3 ^ 40 * 799713 * 2
def baseEnd_799713 : Nat := 410637154649134852909693

theorem tailTrace_799713 : CollatzResearch.WordTrace tailWord_799713 prefixEnd_799713 410637154649134852909693 := by
  unfold tailWord_799713
  simp only [CollatzResearch.WordTrace]
  refine ⟨29167929351783855951811793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19445286234522570634541195 29167929351783855951811793)
  ·
    refine ⟨21875947013837891963858845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29167929351783855951811793 21875947013837891963858845)
    ·
      refine ⟨8203480130189209486447067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21875947013837891963858845 8203480130189209486447067)
      ·
        refine ⟨12305220195283814229670601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8203480130189209486447067 12305220195283814229670601)
        ·
          refine ⟨9228915146462860672252951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12305220195283814229670601 9228915146462860672252951)
          ·
            refine ⟨13843372719694291008379427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228915146462860672252951 13843372719694291008379427)
            ·
              refine ⟨20765059079541436512569141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843372719694291008379427 20765059079541436512569141)
              ·
                refine ⟨1946724288707009673053357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20765059079541436512569141 1946724288707009673053357)
                ·
                  refine ⟨730021608265128627395009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1946724288707009673053357 730021608265128627395009)
                  ·
                    refine ⟨547516206198846470546257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730021608265128627395009 547516206198846470546257)
                    ·
                      refine ⟨410637154649134852909693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547516206198846470546257 410637154649134852909693)
                      ·
                        rfl

theorem cell23_799713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_799713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799713 prefixEnd_799713 := by exact prefixLift 799713
  have htrace : WordTrace (prefixWord ++ tailWord_799713) baseStart_799713 baseEnd_799713 := by
    simpa [prefixWord, tailWord_799713, baseEnd_799713] using wordTrace_append hprefix tailTrace_799713
  have hstable : (prefixWord ++ tailWord_799713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799713).length < 2 ^ (prefixWord ++ tailWord_799713).sum := by decide
  have hdescent : baseEnd_799713 < baseStart_799713 := by decide
  rcases family_descends (prefixWord ++ tailWord_799713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799769 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_799769 : Nat := 118140960795 + 799769 * 2 ^ 59
def prefixEnd_799769 : Nat := 4983230072969 + 3 ^ 40 * 799769 * 2
def baseEnd_799769 : Nat := 410665909565786633809435

theorem tailTrace_799769 : CollatzResearch.WordTrace tailWord_799769 prefixEnd_799769 410665909565786633809435 := by
  unfold tailWord_799769
  simp only [CollatzResearch.WordTrace]
  refine ⟨29169971839580977515850361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19446647893053985010566907 29169971839580977515850361)
  ·
    refine ⟨21877478879685733136887771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29169971839580977515850361 21877478879685733136887771)
    ·
      refine ⟨32816218319528599705331657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21877478879685733136887771 32816218319528599705331657)
      ·
        refine ⟨24612163739646449778998743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32816218319528599705331657 24612163739646449778998743)
        ·
          refine ⟨36918245609469674668498115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24612163739646449778998743 36918245609469674668498115)
          ·
            refine ⟨55377368414204512002747173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36918245609469674668498115 55377368414204512002747173)
            ·
              refine ⟨10383256577663346000515095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55377368414204512002747173 10383256577663346000515095)
              ·
                refine ⟨15574884866495019000772643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383256577663346000515095 15574884866495019000772643)
                ·
                  refine ⟨23362327299742528501158965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15574884866495019000772643 23362327299742528501158965)
                  ·
                    refine ⟨2190218184350862046983653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23362327299742528501158965 2190218184350862046983653)
                    ·
                      refine ⟨410665909565786633809435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2190218184350862046983653 410665909565786633809435)
                      ·
                        rfl

theorem cell23_799769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_799769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799769 prefixEnd_799769 := by exact prefixLift 799769
  have htrace : WordTrace (prefixWord ++ tailWord_799769) baseStart_799769 baseEnd_799769 := by
    simpa [prefixWord, tailWord_799769, baseEnd_799769] using wordTrace_append hprefix tailTrace_799769
  have hstable : (prefixWord ++ tailWord_799769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799769).length < 2 ^ (prefixWord ++ tailWord_799769).sum := by decide
  have hdescent : baseEnd_799769 < baseStart_799769 := by decide
  rcases family_descends (prefixWord ++ tailWord_799769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799780 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_799780 : Nat := 118140960795 + 799780 * 2 ^ 59
def prefixEnd_799780 : Nat := 4983230072969 + 3 ^ 40 * 799780 * 2
def baseEnd_799780 : Nat := 410671557852986090771885

theorem tailTrace_799780 : CollatzResearch.WordTrace tailWord_799780 prefixEnd_799780 410671557852986090771885 := by
  unfold tailWord_799780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14585186521270563197250397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19446915361694084263000529 14585186521270563197250397)
  ·
    refine ⟨5469444945476461198968899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14585186521270563197250397 5469444945476461198968899)
    ·
      refine ⟨8204167418214691798453349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5469444945476461198968899 8204167418214691798453349)
      ·
        refine ⟨1538281390915254712210003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8204167418214691798453349 1538281390915254712210003)
        ·
          refine ⟨2307422086372882068315005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538281390915254712210003 2307422086372882068315005)
          ·
            refine ⟨865283282389830775618127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2307422086372882068315005 865283282389830775618127)
            ·
              refine ⟨1297924923584746163427191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865283282389830775618127 1297924923584746163427191)
              ·
                refine ⟨1946887385377119245140787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297924923584746163427191 1946887385377119245140787)
                ·
                  refine ⟨2920331078065678867711181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946887385377119245140787 2920331078065678867711181)
                  ·
                    refine ⟨1095124154274629575391693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2920331078065678867711181 1095124154274629575391693)
                    ·
                      refine ⟨410671557852986090771885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1095124154274629575391693 410671557852986090771885)
                      ·
                        rfl

theorem cell23_799780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_799780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799780 prefixEnd_799780 := by exact prefixLift 799780
  have htrace : WordTrace (prefixWord ++ tailWord_799780) baseStart_799780 baseEnd_799780 := by
    simpa [prefixWord, tailWord_799780, baseEnd_799780] using wordTrace_append hprefix tailTrace_799780
  have hstable : (prefixWord ++ tailWord_799780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799780).length < 2 ^ (prefixWord ++ tailWord_799780).sum := by decide
  have hdescent : baseEnd_799780 < baseStart_799780 := by decide
  rcases family_descends (prefixWord ++ tailWord_799780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799820 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_799820 : Nat := 118140960795 + 799820 * 2 ^ 59
def prefixEnd_799820 : Nat := 4983230072969 + 3 ^ 40 * 799820 * 2
def baseEnd_799820 : Nat := 410692097079165934271701

theorem tailTrace_799820 : CollatzResearch.WordTrace tailWord_799820 prefixEnd_799820 410692097079165934271701 := by
  unfold tailWord_799820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14585915981198106612978457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19447887974930808817304609 14585915981198106612978457)
  ·
    refine ⟨10939436985898579959733843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14585915981198106612978457 10939436985898579959733843)
    ·
      refine ⟨16409155478847869939600765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10939436985898579959733843 16409155478847869939600765)
      ·
        refine ⟨6153433304567951227350287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16409155478847869939600765 6153433304567951227350287)
        ·
          refine ⟨9230149956851926841025431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6153433304567951227350287 9230149956851926841025431)
          ·
            refine ⟨13845224935277890261538147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9230149956851926841025431 13845224935277890261538147)
            ·
              refine ⟨20767837402916835392307221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13845224935277890261538147 20767837402916835392307221)
              ·
                refine ⟨973492378261726659014401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20767837402916835392307221 973492378261726659014401)
                ·
                  refine ⟨730119283696294994260801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 973492378261726659014401 730119283696294994260801)
                  ·
                    refine ⟨547589462772221245695601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730119283696294994260801 547589462772221245695601)
                    ·
                      refine ⟨410692097079165934271701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547589462772221245695601 410692097079165934271701)
                      ·
                        rfl

theorem cell23_799820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_799820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799820 prefixEnd_799820 := by exact prefixLift 799820
  have htrace : WordTrace (prefixWord ++ tailWord_799820) baseStart_799820 baseEnd_799820 := by
    simpa [prefixWord, tailWord_799820, baseEnd_799820] using wordTrace_append hprefix tailTrace_799820
  have hstable : (prefixWord ++ tailWord_799820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799820).length < 2 ^ (prefixWord ++ tailWord_799820).sum := by decide
  have hdescent : baseEnd_799820 < baseStart_799820 := by decide
  rcases family_descends (prefixWord ++ tailWord_799820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799873 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_799873 : Nat := 118140960795 + 799873 * 2 ^ 59
def prefixEnd_799873 : Nat := 4983230072969 + 3 ^ 40 * 799873 * 2
def baseEnd_799873 : Nat := 136906437184618075636319

theorem tailTrace_799873 : CollatzResearch.WordTrace tailWord_799873 prefixEnd_799873 136906437184618075636319 := by
  unfold tailWord_799873
  simp only [CollatzResearch.WordTrace]
  refine ⟨29173765031204203277636273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19449176687469468851757515 29173765031204203277636273)
  ·
    refine ⟨21880323773403152458227205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29173765031204203277636273 21880323773403152458227205)
    ·
      refine ⟨4102560707513091085917601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21880323773403152458227205 4102560707513091085917601)
      ·
        refine ⟨3076920530634818314438201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4102560707513091085917601 3076920530634818314438201)
        ·
          refine ⟨2307690397976113735828651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3076920530634818314438201 2307690397976113735828651)
          ·
            refine ⟨3461535596964170603742977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307690397976113735828651 3461535596964170603742977)
            ·
              refine ⟨2596151697723127952807233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461535596964170603742977 2596151697723127952807233)
              ·
                refine ⟨1947113773292345964605425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596151697723127952807233 1947113773292345964605425)
                ·
                  refine ⟨1460335329969259473454069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947113773292345964605425 1460335329969259473454069)
                  ·
                    refine ⟨136906437184618075636319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1460335329969259473454069 136906437184618075636319)
                    ·
                      rfl

theorem cell23_799873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_799873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799873 prefixEnd_799873 := by exact prefixLift 799873
  have htrace : WordTrace (prefixWord ++ tailWord_799873) baseStart_799873 baseEnd_799873 := by
    simpa [prefixWord, tailWord_799873, baseEnd_799873] using wordTrace_append hprefix tailTrace_799873
  have hstable : (prefixWord ++ tailWord_799873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799873).length < 2 ^ (prefixWord ++ tailWord_799873).sum := by decide
  have hdescent : baseEnd_799873 < baseStart_799873 := by decide
  rcases family_descends (prefixWord ++ tailWord_799873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799877 : List Nat := [1, 3, 1, 1, 6, 2, 2, 2, 5]
def baseStart_799877 : Nat := 118140960795 + 799877 * 2 ^ 59
def prefixEnd_799877 : Nat := 4983230072969 + 3 ^ 40 * 799877 * 2
def baseEnd_799877 : Nat := 45635707275163579028771

theorem tailTrace_799877 : CollatzResearch.WordTrace tailWord_799877 prefixEnd_799877 45635707275163579028771 := by
  unfold tailWord_799877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29173910923189711960781885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19449273948793141307187923 29173910923189711960781885)
  ·
    refine ⟨10940216596196141985293207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29173910923189711960781885 10940216596196141985293207)
    ·
      refine ⟨16410324894294212977939811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10940216596196141985293207 16410324894294212977939811)
      ·
        refine ⟨24615487341441319466909717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16410324894294212977939811 24615487341441319466909717)
        ·
          refine ⟨1153850969130061850011393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24615487341441319466909717 1153850969130061850011393)
          ·
            refine ⟨865388226847546387508545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1153850969130061850011393 865388226847546387508545)
            ·
              refine ⟨649041170135659790631409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865388226847546387508545 649041170135659790631409)
              ·
                refine ⟨486780877601744842973557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649041170135659790631409 486780877601744842973557)
                ·
                  refine ⟨45635707275163579028771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 486780877601744842973557 45635707275163579028771)
                  ·
                    rfl

theorem cell23_799877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_799877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799877 prefixEnd_799877 := by exact prefixLift 799877
  have htrace : WordTrace (prefixWord ++ tailWord_799877) baseStart_799877 baseEnd_799877 := by
    simpa [prefixWord, tailWord_799877, baseEnd_799877] using wordTrace_append hprefix tailTrace_799877
  have hstable : (prefixWord ++ tailWord_799877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799877).length < 2 ^ (prefixWord ++ tailWord_799877).sum := by decide
  have hdescent : baseEnd_799877 < baseStart_799877 := by decide
  rcases family_descends (prefixWord ++ tailWord_799877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799933 : List Nat := [1, 4, 1, 2, 1, 1, 5, 2, 6]
def baseStart_799933 : Nat := 118140960795 + 799933 * 2 ^ 59
def prefixEnd_799933 : Nat := 4983230072969 + 3 ^ 40 * 799933 * 2
def baseEnd_799933 : Nat := 45638902265902665795409

theorem tailTrace_799933 : CollatzResearch.WordTrace tailWord_799933 prefixEnd_799933 45638902265902665795409 := by
  unfold tailWord_799933
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175953410986833524820453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19450635607324555683213635 29175953410986833524820453)
  ·
    refine ⟨5470491264560031285903835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29175953410986833524820453 5470491264560031285903835)
    ·
      refine ⟨8205736896840046928855753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5470491264560031285903835 8205736896840046928855753)
      ·
        refine ⟨6154302672630035196641815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8205736896840046928855753 6154302672630035196641815)
        ·
          refine ⟨9231454008945052794962723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154302672630035196641815 9231454008945052794962723)
          ·
            refine ⟨13847181013417579192444085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9231454008945052794962723 13847181013417579192444085)
            ·
              refine ⟨1298173220007898049291633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13847181013417579192444085 1298173220007898049291633)
              ·
                refine ⟨973629915005923536968725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298173220007898049291633 973629915005923536968725)
                ·
                  refine ⟨45638902265902665795409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 973629915005923536968725 45638902265902665795409)
                  ·
                    rfl

theorem cell23_799933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_799933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799933 prefixEnd_799933 := by exact prefixLift 799933
  have htrace : WordTrace (prefixWord ++ tailWord_799933) baseStart_799933 baseEnd_799933 := by
    simpa [prefixWord, tailWord_799933, baseEnd_799933] using wordTrace_append hprefix tailTrace_799933
  have hstable : (prefixWord ++ tailWord_799933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799933).length < 2 ^ (prefixWord ++ tailWord_799933).sum := by decide
  have hdescent : baseEnd_799933 < baseStart_799933 := by decide
  rcases family_descends (prefixWord ++ tailWord_799933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799937 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_799937 : Nat := 118140960795 + 799937 * 2 ^ 59
def prefixEnd_799937 : Nat := 4983230072969 + 3 ^ 40 * 799937 * 2
def baseEnd_799937 : Nat := 136917391438580658836221

theorem tailTrace_799937 : CollatzResearch.WordTrace tailWord_799937 prefixEnd_799937 136917391438580658836221 := by
  unfold tailWord_799937
  simp only [CollatzResearch.WordTrace]
  refine ⟨29176099302972342207966065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19450732868648228138644043 29176099302972342207966065)
  ·
    refine ⟨21882074477229256655974549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29176099302972342207966065 21882074477229256655974549)
    ·
      refine ⟨1025722241120121405748807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21882074477229256655974549 1025722241120121405748807)
      ·
        refine ⟨1538583361680182108623211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025722241120121405748807 1538583361680182108623211)
        ·
          refine ⟨2307875042520273162934817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538583361680182108623211 2307875042520273162934817)
          ·
            refine ⟨1730906281890204872201113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307875042520273162934817 1730906281890204872201113)
            ·
              refine ⟨1298179711417653654150835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730906281890204872201113 1298179711417653654150835)
              ·
                refine ⟨1947269567126480481226253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298179711417653654150835 1947269567126480481226253)
                ·
                  refine ⟨730226087672430180459845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1947269567126480481226253 730226087672430180459845)
                  ·
                    refine ⟨136917391438580658836221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730226087672430180459845 136917391438580658836221)
                    ·
                      rfl

theorem cell23_799937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_799937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799937 prefixEnd_799937 := by exact prefixLift 799937
  have htrace : WordTrace (prefixWord ++ tailWord_799937) baseStart_799937 baseEnd_799937 := by
    simpa [prefixWord, tailWord_799937, baseEnd_799937] using wordTrace_append hprefix tailTrace_799937
  have hstable : (prefixWord ++ tailWord_799937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799937).length < 2 ^ (prefixWord ++ tailWord_799937).sum := by decide
  have hdescent : baseEnd_799937 < baseStart_799937 := by decide
  rcases family_descends (prefixWord ++ tailWord_799937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799988 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_799988 : Nat := 118140960795 + 799988 * 2 ^ 59
def prefixEnd_799988 : Nat := 4983230072969 + 3 ^ 40 * 799988 * 2
def baseEnd_799988 : Nat := 136926120609707092323643

theorem tailTrace_799988 : CollatzResearch.WordTrace tailWord_799988 prefixEnd_799988 136926120609707092323643 := by
  unfold tailWord_799988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14588979712893788959036309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19451972950525051945381745 14588979712893788959036309)
  ·
    refine ⟨683858424041896357454827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14588979712893788959036309 683858424041896357454827)
    ·
      refine ⟨1025787636062844536182241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 683858424041896357454827 1025787636062844536182241)
      ·
        refine ⟨769340727047133402136681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1025787636062844536182241 769340727047133402136681)
        ·
          refine ⟨577005545285350051602511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 769340727047133402136681 577005545285350051602511)
          ·
            refine ⟨865508317928025077403767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577005545285350051602511 865508317928025077403767)
            ·
              refine ⟨1298262476892037616105651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865508317928025077403767 1298262476892037616105651)
              ·
                refine ⟨1947393715338056424158477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298262476892037616105651 1947393715338056424158477)
                ·
                  refine ⟨730272643251771159059429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1947393715338056424158477 730272643251771159059429)
                  ·
                    refine ⟨136926120609707092323643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730272643251771159059429 136926120609707092323643)
                    ·
                      rfl

theorem cell23_799988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_799988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799988 prefixEnd_799988 := by exact prefixLift 799988
  have htrace : WordTrace (prefixWord ++ tailWord_799988) baseStart_799988 baseEnd_799988 := by
    simpa [prefixWord, tailWord_799988, baseEnd_799988] using wordTrace_append hprefix tailTrace_799988
  have hstable : (prefixWord ++ tailWord_799988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799988).length < 2 ^ (prefixWord ++ tailWord_799988).sum := by decide
  have hdescent : baseEnd_799988 < baseStart_799988 := by decide
  rcases family_descends (prefixWord ++ tailWord_799988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799993 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_799993 : Nat := 118140960795 + 799993 * 2 ^ 59
def prefixEnd_799993 : Nat := 4983230072969 + 3 ^ 40 * 799993 * 2
def baseEnd_799993 : Nat := 136926976410797919136135

theorem tailTrace_799993 : CollatzResearch.WordTrace tailWord_799993 prefixEnd_799993 136926976410797919136135 := by
  unfold tailWord_799993
  simp only [CollatzResearch.WordTrace]
  refine ⟨29178141790769463772004633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19452094527179642514669755 29178141790769463772004633)
  ·
    refine ⟨21883606343077097829003475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29178141790769463772004633 21883606343077097829003475)
    ·
      refine ⟨32825409514615646743505213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21883606343077097829003475 32825409514615646743505213)
      ·
        refine ⟨12309528567980867528814455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32825409514615646743505213 12309528567980867528814455)
        ·
          refine ⟨18464292851971301293221683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12309528567980867528814455 18464292851971301293221683)
          ·
            refine ⟨27696439277956951939832525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18464292851971301293221683 27696439277956951939832525)
            ·
              refine ⟨10386164729233856977437197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27696439277956951939832525 10386164729233856977437197)
              ·
                refine ⟨3894811773462696366538949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10386164729233856977437197 3894811773462696366538949)
                ·
                  refine ⟨730277207524255568726053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3894811773462696366538949 730277207524255568726053)
                  ·
                    refine ⟨136926976410797919136135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730277207524255568726053 136926976410797919136135)
                    ·
                      rfl

theorem cell23_799993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_799993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799993 prefixEnd_799993 := by exact prefixLift 799993
  have htrace : WordTrace (prefixWord ++ tailWord_799993) baseStart_799993 baseEnd_799993 := by
    simpa [prefixWord, tailWord_799993, baseEnd_799993] using wordTrace_append hprefix tailTrace_799993
  have hstable : (prefixWord ++ tailWord_799993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799993).length < 2 ^ (prefixWord ++ tailWord_799993).sum := by decide
  have hdescent : baseEnd_799993 < baseStart_799993 := by decide
  rcases family_descends (prefixWord ++ tailWord_799993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_799994 : List Nat := [3, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3]
def baseStart_799994 : Nat := 118140960795 + 799994 * 2 ^ 59
def prefixEnd_799994 : Nat := 4983230072969 + 3 ^ 40 * 799994 * 2
def baseEnd_799994 : Nat := 410781442713048253495901

theorem tailTrace_799994 : CollatzResearch.WordTrace tailWord_799994 prefixEnd_799994 410781442713048253495901 := by
  unfold tailWord_799994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294544565941460235697759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19452118842510560628527357 7294544565941460235697759)
  ·
    refine ⟨10941816848912190353546639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7294544565941460235697759 10941816848912190353546639)
    ·
      refine ⟨16412725273368285530319959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10941816848912190353546639 16412725273368285530319959)
      ·
        refine ⟨24619087910052428295479939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16412725273368285530319959 24619087910052428295479939)
        ·
          refine ⟨36928631865078642443219909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24619087910052428295479939 36928631865078642443219909)
          ·
            refine ⟨6924118474702245458103733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36928631865078642443219909 6924118474702245458103733)
            ·
              refine ⟨649136107003335511697225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6924118474702245458103733 649136107003335511697225)
              ·
                refine ⟨486852080252501633772919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649136107003335511697225 486852080252501633772919)
                ·
                  refine ⟨730278120378752450659379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486852080252501633772919 730278120378752450659379)
                  ·
                    refine ⟨1095417180568128675989069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 730278120378752450659379 1095417180568128675989069)
                    ·
                      refine ⟨410781442713048253495901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1095417180568128675989069 410781442713048253495901)
                      ·
                        rfl

theorem cell23_799994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3].length) (baseStart_799994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_799994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_799994 prefixEnd_799994 := by exact prefixLift 799994
  have htrace : WordTrace (prefixWord ++ tailWord_799994) baseStart_799994 baseEnd_799994 := by
    simpa [prefixWord, tailWord_799994, baseEnd_799994] using wordTrace_append hprefix tailTrace_799994
  have hstable : (prefixWord ++ tailWord_799994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_799994).length < 2 ^ (prefixWord ++ tailWord_799994).sum := by decide
  have hdescent : baseEnd_799994 < baseStart_799994 := by decide
  rcases family_descends (prefixWord ++ tailWord_799994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800003 : List Nat := [1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_800003 : Nat := 118140960795 + 800003 * 2 ^ 59
def prefixEnd_800003 : Nat := 4983230072969 + 3 ^ 40 * 800003 * 2
def baseEnd_800003 : Nat := 410786064038938718283359

theorem tailTrace_800003 : CollatzResearch.WordTrace tailWord_800003 prefixEnd_800003 410786064038938718283359 := by
  unfold tailWord_800003
  simp only [CollatzResearch.WordTrace]
  refine ⟨29178506520733235479868663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19452337680488823653245775 29178506520733235479868663)
  ·
    refine ⟨43767759781099853219802995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29178506520733235479868663 43767759781099853219802995)
    ·
      refine ⟨65651639671649779829704493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43767759781099853219802995 65651639671649779829704493)
      ·
        refine ⟨24619364876868667436139185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65651639671649779829704493 24619364876868667436139185)
        ·
          refine ⟨18464523657651500577104389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24619364876868667436139185 18464523657651500577104389)
          ·
            refine ⟨3462098185809656358207073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18464523657651500577104389 3462098185809656358207073)
            ·
              refine ⟨2596573639357242268655305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462098185809656358207073 2596573639357242268655305)
              ·
                refine ⟨1947430229517931701491479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596573639357242268655305 1947430229517931701491479)
                ·
                  refine ⟨2921145344276897552237219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947430229517931701491479 2921145344276897552237219)
                  ·
                    refine ⟨4381718016415346328355829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2921145344276897552237219 4381718016415346328355829)
                    ·
                      refine ⟨410786064038938718283359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4381718016415346328355829 410786064038938718283359)
                      ·
                        rfl

theorem cell23_800003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_800003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800003 prefixEnd_800003 := by exact prefixLift 800003
  have htrace : WordTrace (prefixWord ++ tailWord_800003) baseStart_800003 baseEnd_800003 := by
    simpa [prefixWord, tailWord_800003, baseEnd_800003] using wordTrace_append hprefix tailTrace_800003
  have hstable : (prefixWord ++ tailWord_800003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800003).length < 2 ^ (prefixWord ++ tailWord_800003).sum := by decide
  have hdescent : baseEnd_800003 < baseStart_800003 := by decide
  rcases family_descends (prefixWord ++ tailWord_800003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800034 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_800034 : Nat := 118140960795 + 800034 * 2 ^ 59
def prefixEnd_800034 : Nat := 4983230072969 + 3 ^ 40 * 800034 * 2
def baseEnd_800034 : Nat := 410801981939228096995717

theorem tailTrace_800034 : CollatzResearch.WordTrace tailWord_800034 prefixEnd_800034 410801981939228096995717 := by
  unfold tailWord_800034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7294909295905231943561789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19453091455747285182831437 7294909295905231943561789)
  ·
    refine ⟨2735590985964461978835671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7294909295905231943561789 2735590985964461978835671)
    ·
      refine ⟨4103386478946692968253507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735590985964461978835671 4103386478946692968253507)
      ·
        refine ⟨6155079718420039452380261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103386478946692968253507 6155079718420039452380261)
        ·
          refine ⟨1154077447203757397321299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6155079718420039452380261 1154077447203757397321299)
          ·
            refine ⟨1731116170805636095981949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154077447203757397321299 1731116170805636095981949)
            ·
              refine ⟨649168564052113535993231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1731116170805636095981949 649168564052113535993231)
              ·
                refine ⟨973752846078170303989847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649168564052113535993231 973752846078170303989847)
                ·
                  refine ⟨1460629269117255455984771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973752846078170303989847 1460629269117255455984771)
                  ·
                    refine ⟨2190943903675883183977157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460629269117255455984771 2190943903675883183977157)
                    ·
                      refine ⟨410801981939228096995717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2190943903675883183977157 410801981939228096995717)
                      ·
                        rfl

theorem cell23_800034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_800034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800034 prefixEnd_800034 := by exact prefixLift 800034
  have htrace : WordTrace (prefixWord ++ tailWord_800034) baseStart_800034 baseEnd_800034 := by
    simpa [prefixWord, tailWord_800034, baseEnd_800034] using wordTrace_append hprefix tailTrace_800034
  have hstable : (prefixWord ++ tailWord_800034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800034).length < 2 ^ (prefixWord ++ tailWord_800034).sum := by decide
  have hdescent : baseEnd_800034 < baseStart_800034 := by decide
  rcases family_descends (prefixWord ++ tailWord_800034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800051 : List Nat := [1, 1, 1, 2, 5, 2, 4, 2, 1, 2, 2]
def baseStart_800051 : Nat := 118140960795 + 800051 * 2 ^ 59
def prefixEnd_800051 : Nat := 4983230072969 + 3 ^ 40 * 800051 * 2
def baseEnd_800051 : Nat := 410810711110354530483139

theorem tailTrace_800051 : CollatzResearch.WordTrace tailWord_800051 prefixEnd_800051 410810711110354530483139 := by
  unfold tailWord_800051
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180257224559339677616007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19453504816372893118410671 29180257224559339677616007)
  ·
    refine ⟨43770385836839009516424011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29180257224559339677616007 43770385836839009516424011)
    ·
      refine ⟨65655578755258514274636017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43770385836839009516424011 65655578755258514274636017)
      ·
        refine ⟨49241684066443885705977013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65655578755258514274636017 49241684066443885705977013)
        ·
          refine ⟨4616407881229114284935345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49241684066443885705977013 4616407881229114284935345)
          ·
            refine ⟨3462305910921835713701509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616407881229114284935345 3462305910921835713701509)
            ·
              refine ⟨649182358297844196319033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3462305910921835713701509 649182358297844196319033)
              ·
                refine ⟨486886768723383147239275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649182358297844196319033 486886768723383147239275)
                ·
                  refine ⟨730330153085074720858913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 486886768723383147239275 730330153085074720858913)
                  ·
                    refine ⟨547747614813806040644185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730330153085074720858913 547747614813806040644185)
                    ·
                      refine ⟨410810711110354530483139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547747614813806040644185 410810711110354530483139)
                      ·
                        rfl

theorem cell23_800051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 2, 1, 2, 2].length) (baseStart_800051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800051 prefixEnd_800051 := by exact prefixLift 800051
  have htrace : WordTrace (prefixWord ++ tailWord_800051) baseStart_800051 baseEnd_800051 := by
    simpa [prefixWord, tailWord_800051, baseEnd_800051] using wordTrace_append hprefix tailTrace_800051
  have hstable : (prefixWord ++ tailWord_800051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800051).length < 2 ^ (prefixWord ++ tailWord_800051).sum := by decide
  have hdescent : baseEnd_800051 < baseStart_800051 := by decide
  rcases family_descends (prefixWord ++ tailWord_800051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800053 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_800053 : Nat := 118140960795 + 800053 * 2 ^ 59
def prefixEnd_800053 : Nat := 4983230072969 + 3 ^ 40 * 800053 * 2
def baseEnd_800053 : Nat := 136937246023887840886043

theorem tailTrace_800053 : CollatzResearch.WordTrace tailWord_800053 prefixEnd_800053 136937246023887840886043 := by
  unfold tailWord_800053
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180330170552094019188813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19453553447034729346125875 29180330170552094019188813)
  ·
    refine ⟨10942623813957035257195805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29180330170552094019188813 10942623813957035257195805)
    ·
      refine ⟨4103483930233888221448427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10942623813957035257195805 4103483930233888221448427)
      ·
        refine ⟨6155225895350832332172641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4103483930233888221448427 6155225895350832332172641)
        ·
          refine ⟨4616419421513124249129481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155225895350832332172641 4616419421513124249129481)
          ·
            refine ⟨3462314566134843186847111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616419421513124249129481 3462314566134843186847111)
            ·
              refine ⟨5193471849202264780270667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462314566134843186847111 5193471849202264780270667)
              ·
                refine ⟨7790207773803397170406001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193471849202264780270667 7790207773803397170406001)
                ·
                  refine ⟨5842655830352547877804501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7790207773803397170406001 5842655830352547877804501)
                  ·
                    refine ⟨136937246023887840886043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5842655830352547877804501 136937246023887840886043)
                    ·
                      rfl

theorem cell23_800053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_800053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800053 prefixEnd_800053 := by exact prefixLift 800053
  have htrace : WordTrace (prefixWord ++ tailWord_800053) baseStart_800053 baseEnd_800053 := by
    simpa [prefixWord, tailWord_800053, baseEnd_800053] using wordTrace_append hprefix tailTrace_800053
  have hstable : (prefixWord ++ tailWord_800053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800053).length < 2 ^ (prefixWord ++ tailWord_800053).sum := by decide
  have hdescent : baseEnd_800053 < baseStart_800053 := by decide
  rcases family_descends (prefixWord ++ tailWord_800053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800057 : List Nat := [1, 2, 1, 6, 3, 1, 1, 8]
def baseStart_800057 : Nat := 118140960795 + 800057 * 2 ^ 59
def prefixEnd_800057 : Nat := 4983230072969 + 3 ^ 40 * 800057 * 2
def baseEnd_800057 : Nat := 15215325629417833592893

theorem tailTrace_800057 : CollatzResearch.WordTrace tailWord_800057 prefixEnd_800057 15215325629417833592893 := by
  unfold tailWord_800057
  simp only [CollatzResearch.WordTrace]
  refine ⟨29180476062537602702334425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19453650708358401801556283 29180476062537602702334425)
  ·
    refine ⟨21885357046903202026750819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29180476062537602702334425 21885357046903202026750819)
    ·
      refine ⟨32828035570354803040126229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21885357046903202026750819 32828035570354803040126229)
      ·
        refine ⟨1538814167360381392505917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32828035570354803040126229 1538814167360381392505917)
        ·
          refine ⟨577055312760143022189719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1538814167360381392505917 577055312760143022189719)
          ·
            refine ⟨865582969140214533284579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577055312760143022189719 865582969140214533284579)
            ·
              refine ⟨1298374453710321799926869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865582969140214533284579 1298374453710321799926869)
              ·
                refine ⟨15215325629417833592893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1298374453710321799926869 15215325629417833592893)
                ·
                  rfl

theorem cell23_800057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 8].length) (baseStart_800057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800057 prefixEnd_800057 := by exact prefixLift 800057
  have htrace : WordTrace (prefixWord ++ tailWord_800057) baseStart_800057 baseEnd_800057 := by
    simpa [prefixWord, tailWord_800057, baseEnd_800057] using wordTrace_append hprefix tailTrace_800057
  have hstable : (prefixWord ++ tailWord_800057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800057).length < 2 ^ (prefixWord ++ tailWord_800057).sum := by decide
  have hdescent : baseEnd_800057 < baseStart_800057 := by decide
  rcases family_descends (prefixWord ++ tailWord_800057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800113 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 7]
def baseStart_800113 : Nat := 118140960795 + 800113 * 2 ^ 59
def prefixEnd_800113 : Nat := 4983230072969 + 3 ^ 40 * 800113 * 2
def baseEnd_800113 : Nat := 45649171878992587545317

theorem tailTrace_800113 : CollatzResearch.WordTrace tailWord_800113 prefixEnd_800113 45649171878992587545317 := by
  unfold tailWord_800113
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182518550334724266372993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19455012366889816177581995 29182518550334724266372993)
  ·
    refine ⟨21886888912751043199779745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29182518550334724266372993 21886888912751043199779745)
    ·
      refine ⟨16415166684563282399834809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21886888912751043199779745 16415166684563282399834809)
      ·
        refine ⟨12311375013422461799876107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16415166684563282399834809 12311375013422461799876107)
        ·
          refine ⟨18467062520133692699814161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12311375013422461799876107 18467062520133692699814161)
          ·
            refine ⟨13850296890100269524860621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18467062520133692699814161 13850296890100269524860621)
            ·
              refine ⟨5193861333787601071822733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13850296890100269524860621 5193861333787601071822733)
              ·
                refine ⟨1947698000170350401933525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193861333787601071822733 1947698000170350401933525)
                ·
                  refine ⟨45649171878992587545317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1947698000170350401933525 45649171878992587545317)
                  ·
                    rfl

theorem cell23_800113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_800113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800113 prefixEnd_800113 := by exact prefixLift 800113
  have htrace : WordTrace (prefixWord ++ tailWord_800113) baseStart_800113 baseEnd_800113 := by
    simpa [prefixWord, tailWord_800113, baseEnd_800113] using wordTrace_append hprefix tailTrace_800113
  have hstable : (prefixWord ++ tailWord_800113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800113).length < 2 ^ (prefixWord ++ tailWord_800113).sum := by decide
  have hdescent : baseEnd_800113 < baseStart_800113 := by decide
  rcases family_descends (prefixWord ++ tailWord_800113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800160 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_800160 : Nat := 118140960795 + 800160 * 2 ^ 59
def prefixEnd_800160 : Nat := 4983230072969 + 3 ^ 40 * 800160 * 2
def baseEnd_800160 : Nat := 136955560167231534673379

theorem tailTrace_800160 : CollatzResearch.WordTrace tailWord_800160 prefixEnd_800160 136955560167231534673379 := by
  unfold tailWord_800160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592116390582225646666967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19456155187442967528889289 14592116390582225646666967)
  ·
    refine ⟨21888174585873338470000451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14592116390582225646666967 21888174585873338470000451)
    ·
      refine ⟨32832261878810007705000677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21888174585873338470000451 32832261878810007705000677)
      ·
        refine ⟨6156049102276876444687627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32832261878810007705000677 6156049102276876444687627)
        ·
          refine ⟨9234073653415314667031441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6156049102276876444687627 9234073653415314667031441)
          ·
            refine ⟨6925555240061486000273581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9234073653415314667031441 6925555240061486000273581)
            ·
              refine ⟨2597083215023057250102593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6925555240061486000273581 2597083215023057250102593)
              ·
                refine ⟨1947812411267292937576945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597083215023057250102593 1947812411267292937576945)
                ·
                  refine ⟨1460859308450469703182709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947812411267292937576945 1460859308450469703182709)
                  ·
                    refine ⟨136955560167231534673379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1460859308450469703182709 136955560167231534673379)
                    ·
                      rfl

theorem cell23_800160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_800160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800160 prefixEnd_800160 := by exact prefixLift 800160
  have htrace : WordTrace (prefixWord ++ tailWord_800160) baseStart_800160 baseEnd_800160 := by
    simpa [prefixWord, tailWord_800160, baseEnd_800160] using wordTrace_append hprefix tailTrace_800160
  have hstable : (prefixWord ++ tailWord_800160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800160).length < 2 ^ (prefixWord ++ tailWord_800160).sum := by decide
  have hdescent : baseEnd_800160 < baseStart_800160 := by decide
  rcases family_descends (prefixWord ++ tailWord_800160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800167 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_800167 : Nat := 118140960795 + 800167 * 2 ^ 59
def prefixEnd_800167 : Nat := 4983230072969 + 3 ^ 40 * 800167 * 2
def baseEnd_800167 : Nat := 410870274866276076632605

theorem tailTrace_800167 : CollatzResearch.WordTrace tailWord_800167 prefixEnd_800167 410870274866276076632605 := by
  unfold tailWord_800167
  simp only [CollatzResearch.WordTrace]
  refine ⟨29184488092139091488838755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19456325394759394325892503 29184488092139091488838755)
  ·
    refine ⟨43776732138208637233258133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29184488092139091488838755 43776732138208637233258133)
    ·
      refine ⟨2052034318978529870308975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43776732138208637233258133 2052034318978529870308975)
      ·
        refine ⟨3078051478467794805463463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052034318978529870308975 3078051478467794805463463)
        ·
          refine ⟨4617077217701692208195195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078051478467794805463463 4617077217701692208195195)
          ·
            refine ⟨6925615826552538312292793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617077217701692208195195 6925615826552538312292793)
            ·
              refine ⟨5194211869914403734219595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6925615826552538312292793 5194211869914403734219595)
              ·
                refine ⟨7791317804871605601329393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5194211869914403734219595 7791317804871605601329393)
                ·
                  refine ⟨5843488353653704200997045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7791317804871605601329393 5843488353653704200997045)
                  ·
                    refine ⟨547827033155034768843473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5843488353653704200997045 547827033155034768843473)
                    ·
                      refine ⟨410870274866276076632605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547827033155034768843473 410870274866276076632605)
                      ·
                        rfl

theorem cell23_800167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_800167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800167 prefixEnd_800167 := by exact prefixLift 800167
  have htrace : WordTrace (prefixWord ++ tailWord_800167) baseStart_800167 baseEnd_800167 := by
    simpa [prefixWord, tailWord_800167, baseEnd_800167] using wordTrace_append hprefix tailTrace_800167
  have hstable : (prefixWord ++ tailWord_800167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800167).length < 2 ^ (prefixWord ++ tailWord_800167).sum := by decide
  have hdescent : baseEnd_800167 < baseStart_800167 := by decide
  rcases family_descends (prefixWord ++ tailWord_800167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800203 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 10]
def baseStart_800203 : Nat := 118140960795 + 800203 * 2 ^ 59
def prefixEnd_800203 : Nat := 4983230072969 + 3 ^ 40 * 800203 * 2
def baseEnd_800203 : Nat := 45654306685537548420271

theorem tailTrace_800203 : CollatzResearch.WordTrace tailWord_800203 prefixEnd_800203 45654306685537548420271 := by
  unfold tailWord_800203
  simp only [CollatzResearch.WordTrace]
  refine ⟨29185801120008669637149263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19457200746672446424766175 29185801120008669637149263)
  ·
    refine ⟨43778701680013004455723895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29185801120008669637149263 43778701680013004455723895)
    ·
      refine ⟨65668052520019506683585843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43778701680013004455723895 65668052520019506683585843)
      ·
        refine ⟨98502078780029260025378765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65668052520019506683585843 98502078780029260025378765)
        ·
          refine ⟨36938279542510972509517037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98502078780029260025378765 36938279542510972509517037)
          ·
            refine ⟨13851854828441614691068889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36938279542510972509517037 13851854828441614691068889)
            ·
              refine ⟨10388891121331211018301667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13851854828441614691068889 10388891121331211018301667)
              ·
                refine ⟨15583336681996816527452501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10388891121331211018301667 15583336681996816527452501)
                ·
                  refine ⟨45654306685537548420271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 15583336681996816527452501 45654306685537548420271)
                  ·
                    rfl

theorem cell23_800203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_800203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800203 prefixEnd_800203 := by exact prefixLift 800203
  have htrace : WordTrace (prefixWord ++ tailWord_800203) baseStart_800203 baseEnd_800203 := by
    simpa [prefixWord, tailWord_800203, baseEnd_800203] using wordTrace_append hprefix tailTrace_800203
  have hstable : (prefixWord ++ tailWord_800203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800203).length < 2 ^ (prefixWord ++ tailWord_800203).sum := by decide
  have hdescent : baseEnd_800203 < baseStart_800203 := by decide
  rcases family_descends (prefixWord ++ tailWord_800203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800214 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_800214 : Nat := 118140960795 + 800214 * 2 ^ 59
def prefixEnd_800214 : Nat := 4983230072969 + 3 ^ 40 * 800214 * 2
def baseEnd_800214 : Nat := 410894408457037392744889

theorem tailTrace_800214 : CollatzResearch.WordTrace tailWord_800214 prefixEnd_800214 410894408457037392744889 := by
  unfold tailWord_800214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824137645185551157237481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19457468215312545677199797 1824137645185551157237481)
  ·
    refine ⟨1368103233889163367928111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1824137645185551157237481 1368103233889163367928111)
    ·
      refine ⟨2052154850833745051892167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368103233889163367928111 2052154850833745051892167)
      ·
        refine ⟨3078232276250617577838251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052154850833745051892167 3078232276250617577838251)
        ·
          refine ⟨4617348414375926366757377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078232276250617577838251 4617348414375926366757377)
          ·
            refine ⟨3463011310781944775068033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617348414375926366757377 3463011310781944775068033)
            ·
              refine ⟨2597258483086458581301025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463011310781944775068033 2597258483086458581301025)
              ·
                refine ⟨1947943862314843935975769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597258483086458581301025 1947943862314843935975769)
                ·
                  refine ⟨1460957896736132951981827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947943862314843935975769 1460957896736132951981827)
                  ·
                    refine ⟨2191436845104199427972741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1460957896736132951981827 2191436845104199427972741)
                    ·
                      refine ⟨410894408457037392744889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2191436845104199427972741 410894408457037392744889)
                      ·
                        rfl

theorem cell23_800214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_800214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800214 prefixEnd_800214 := by exact prefixLift 800214
  have htrace : WordTrace (prefixWord ++ tailWord_800214) baseStart_800214 baseEnd_800214 := by
    simpa [prefixWord, tailWord_800214, baseEnd_800214] using wordTrace_append hprefix tailTrace_800214
  have hstable : (prefixWord ++ tailWord_800214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800214).length < 2 ^ (prefixWord ++ tailWord_800214).sum := by decide
  have hdescent : baseEnd_800214 < baseStart_800214 := by decide
  rcases family_descends (prefixWord ++ tailWord_800214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800217 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_800217 : Nat := 118140960795 + 800217 * 2 ^ 59
def prefixEnd_800217 : Nat := 4983230072969 + 3 ^ 40 * 800217 * 2
def baseEnd_800217 : Nat := 410895948899000881007375

theorem tailTrace_800217 : CollatzResearch.WordTrace tailWord_800217 prefixEnd_800217 410895948899000881007375 := by
  unfold tailWord_800217
  simp only [CollatzResearch.WordTrace]
  refine ⟨29186311741957950028158905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19457541161305300018772603 29186311741957950028158905)
  ·
    refine ⟨21889733806468462521119179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29186311741957950028158905 21889733806468462521119179)
    ·
      refine ⟨32834600709702693781678769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21889733806468462521119179 32834600709702693781678769)
      ·
        refine ⟨24625950532277020336259077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32834600709702693781678769 24625950532277020336259077)
        ·
          refine ⟨4617365724801941313048577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24625950532277020336259077 4617365724801941313048577)
          ·
            refine ⟨3463024293601455984786433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617365724801941313048577 3463024293601455984786433)
            ·
              refine ⟨2597268220201091988589825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463024293601455984786433 2597268220201091988589825)
              ·
                refine ⟨1947951165150818991442369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597268220201091988589825 1947951165150818991442369)
                ·
                  refine ⟨1460963373863114243581777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947951165150818991442369 1460963373863114243581777)
                  ·
                    refine ⟨1095722530397335682686333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1460963373863114243581777 1095722530397335682686333)
                    ·
                      refine ⟨410895948899000881007375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1095722530397335682686333 410895948899000881007375)
                      ·
                        rfl

theorem cell23_800217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_800217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800217 prefixEnd_800217 := by exact prefixLift 800217
  have htrace : WordTrace (prefixWord ++ tailWord_800217) baseStart_800217 baseEnd_800217 := by
    simpa [prefixWord, tailWord_800217, baseEnd_800217] using wordTrace_append hprefix tailTrace_800217
  have hstable : (prefixWord ++ tailWord_800217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800217).length < 2 ^ (prefixWord ++ tailWord_800217).sum := by decide
  have hdescent : baseEnd_800217 < baseStart_800217 := by decide
  rcases family_descends (prefixWord ++ tailWord_800217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800250 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_800250 : Nat := 118140960795 + 800250 * 2 ^ 59
def prefixEnd_800250 : Nat := 4983230072969 + 3 ^ 40 * 800250 * 2
def baseEnd_800250 : Nat := 136970964586866417298241

theorem tailTrace_800250 : CollatzResearch.WordTrace tailWord_800250 prefixEnd_800250 136970964586866417298241 := by
  unfold tailWord_800250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296878837709599166027551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19458343567225597776073469 7296878837709599166027551)
  ·
    refine ⟨10945318256564398749041327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296878837709599166027551 10945318256564398749041327)
    ·
      refine ⟨16417977384846598123561991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10945318256564398749041327 16417977384846598123561991)
      ·
        refine ⟨24626966077269897185342987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16417977384846598123561991 24626966077269897185342987)
        ·
          refine ⟨36940449115904845778014481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24626966077269897185342987 36940449115904845778014481)
          ·
            refine ⟨27705336836928634333510861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36940449115904845778014481 27705336836928634333510861)
            ·
              refine ⟨10389501313848237875066573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27705336836928634333510861 10389501313848237875066573)
              ·
                refine ⟨3896062992693089203149965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10389501313848237875066573 3896062992693089203149965)
                ·
                  refine ⟨1461023622259908451181237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3896062992693089203149965 1461023622259908451181237)
                  ·
                    refine ⟨136970964586866417298241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1461023622259908451181237 136970964586866417298241)
                    ·
                      rfl

theorem cell23_800250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_800250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800250 prefixEnd_800250 := by exact prefixLift 800250
  have htrace : WordTrace (prefixWord ++ tailWord_800250) baseStart_800250 baseEnd_800250 := by
    simpa [prefixWord, tailWord_800250, baseEnd_800250] using wordTrace_append hprefix tailTrace_800250
  have hstable : (prefixWord ++ tailWord_800250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800250).length < 2 ^ (prefixWord ++ tailWord_800250).sum := by decide
  have hdescent : baseEnd_800250 < baseStart_800250 := by decide
  rcases family_descends (prefixWord ++ tailWord_800250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800258 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_800258 : Nat := 118140960795 + 800258 * 2 ^ 59
def prefixEnd_800258 : Nat := 4983230072969 + 3 ^ 40 * 800258 * 2
def baseEnd_800258 : Nat := 136972333868611740198229

theorem tailTrace_800258 : CollatzResearch.WordTrace tailWord_800258 prefixEnd_800258 136972333868611740198229 := by
  unfold tailWord_800258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296951783702353507600357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19458538089872942686934285 7296951783702353507600357)
  ·
    refine ⟨1368178459444191282675067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7296951783702353507600357 1368178459444191282675067)
    ·
      refine ⟨2052267689166286924012601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368178459444191282675067 2052267689166286924012601)
      ·
        refine ⟨1539200766874715193009451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2052267689166286924012601 1539200766874715193009451)
        ·
          refine ⟨2308801150312072789514177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539200766874715193009451 2308801150312072789514177)
          ·
            refine ⟨1731600862734054592135633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2308801150312072789514177 1731600862734054592135633)
            ·
              refine ⟨1298700647050540944101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731600862734054592135633 1298700647050540944101725)
              ·
                refine ⟨487012742643952854038147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1298700647050540944101725 487012742643952854038147)
                ·
                  refine ⟨730519113965929281057221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487012742643952854038147 730519113965929281057221)
                  ·
                    refine ⟨136972333868611740198229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730519113965929281057221 136972333868611740198229)
                    ·
                      rfl

theorem cell23_800258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_800258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800258 prefixEnd_800258 := by exact prefixLift 800258
  have htrace : WordTrace (prefixWord ++ tailWord_800258) baseStart_800258 baseEnd_800258 := by
    simpa [prefixWord, tailWord_800258, baseEnd_800258] using wordTrace_append hprefix tailTrace_800258
  have hstable : (prefixWord ++ tailWord_800258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800258).length < 2 ^ (prefixWord ++ tailWord_800258).sum := by decide
  have hdescent : baseEnd_800258 < baseStart_800258 := by decide
  rcases family_descends (prefixWord ++ tailWord_800258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800327 : List Nat := [1, 1, 4, 1, 5, 2, 9]
def baseStart_800327 : Nat := 118140960795 + 800327 * 2 ^ 59
def prefixEnd_800327 : Nat := 4983230072969 + 3 ^ 40 * 800327 * 2
def baseEnd_800327 : Nat := 5073486811987598155949

theorem tailTrace_800327 : CollatzResearch.WordTrace tailWord_800327 prefixEnd_800327 5073486811987598155949 := by
  unfold tailWord_800327
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190323771559438814663235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19460215847706292543108823 29190323771559438814663235)
  ·
    refine ⟨43785485657339158221994853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29190323771559438814663235 43785485657339158221994853)
    ·
      refine ⟨8209778560751092166624035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43785485657339158221994853 8209778560751092166624035)
      ·
        refine ⟨12314667841126638249936053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8209778560751092166624035 12314667841126638249936053)
        ·
          refine ⟨1154500110105622335931505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12314667841126638249936053 1154500110105622335931505)
          ·
            refine ⟨865875082579216751948629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154500110105622335931505 865875082579216751948629)
            ·
              refine ⟨5073486811987598155949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 865875082579216751948629 5073486811987598155949)
              ·
                rfl

theorem cell23_800327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 9].length) (baseStart_800327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800327 prefixEnd_800327 := by exact prefixLift 800327
  have htrace : WordTrace (prefixWord ++ tailWord_800327) baseStart_800327 baseEnd_800327 := by
    simpa [prefixWord, tailWord_800327, baseEnd_800327] using wordTrace_append hprefix tailTrace_800327
  have hstable : (prefixWord ++ tailWord_800327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800327).length < 2 ^ (prefixWord ++ tailWord_800327).sum := by decide
  have hdescent : baseEnd_800327 < baseStart_800327 := by decide
  rcases family_descends (prefixWord ++ tailWord_800327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800338 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 3, 2, 2]
def baseStart_800338 : Nat := 118140960795 + 800338 * 2 ^ 59
def prefixEnd_800338 : Nat := 4983230072969 + 3 ^ 40 * 800338 * 2
def baseEnd_800338 : Nat := 410958080058194907594319

theorem tailTrace_800338 : CollatzResearch.WordTrace tailWord_800338 prefixEnd_800338 410958080058194907594319 := by
  unfold tailWord_800338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7297681243629896923328417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19460483316346391795542445 7297681243629896923328417)
  ·
    refine ⟨5473260932722422692496313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7297681243629896923328417 5473260932722422692496313)
    ·
      refine ⟨4104945699541817019372235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5473260932722422692496313 4104945699541817019372235)
      ·
        refine ⟨6157418549312725529058353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4104945699541817019372235 6157418549312725529058353)
        ·
          refine ⟨4618063911984544146793765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157418549312725529058353 4618063911984544146793765)
          ·
            refine ⟨865886983497102027523831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4618063911984544146793765 865886983497102027523831)
            ·
              refine ⟨1298830475245653041285747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865886983497102027523831 1298830475245653041285747)
              ·
                refine ⟨1948245712868479561928621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298830475245653041285747 1948245712868479561928621)
                ·
                  refine ⟨730592142325679835723233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1948245712868479561928621 730592142325679835723233)
                  ·
                    refine ⟨547944106744259876792425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730592142325679835723233 547944106744259876792425)
                    ·
                      refine ⟨410958080058194907594319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 547944106744259876792425 410958080058194907594319)
                      ·
                        rfl

theorem cell23_800338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_800338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800338 prefixEnd_800338 := by exact prefixLift 800338
  have htrace : WordTrace (prefixWord ++ tailWord_800338) baseStart_800338 baseEnd_800338 := by
    simpa [prefixWord, tailWord_800338, baseEnd_800338] using wordTrace_append hprefix tailTrace_800338
  have hstable : (prefixWord ++ tailWord_800338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800338).length < 2 ^ (prefixWord ++ tailWord_800338).sum := by decide
  have hdescent : baseEnd_800338 < baseStart_800338 := by decide
  rcases family_descends (prefixWord ++ tailWord_800338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800348 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_800348 : Nat := 118140960795 + 800348 * 2 ^ 59
def prefixEnd_800348 : Nat := 4983230072969 + 3 ^ 40 * 800348 * 2
def baseEnd_800348 : Nat := 136987738288246622823091

theorem tailTrace_800348 : CollatzResearch.WordTrace tailWord_800348 prefixEnd_800348 136987738288246622823091 := by
  unfold tailWord_800348
  simp only [CollatzResearch.WordTrace]
  refine ⟨14595544852241679700588849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19460726469655572934118465 14595544852241679700588849)
  ·
    refine ⟨10946658639181259775441637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14595544852241679700588849 10946658639181259775441637)
    ·
      refine ⟨2052498494846486207895307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10946658639181259775441637 2052498494846486207895307)
      ·
        refine ⟨3078747742269729311842961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052498494846486207895307 3078747742269729311842961)
        ·
          refine ⟨2309060806702296983882221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3078747742269729311842961 2309060806702296983882221)
          ·
            refine ⟨865897802513361368955833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2309060806702296983882221 865897802513361368955833)
            ·
              refine ⟨649423351885021026716875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 865897802513361368955833 649423351885021026716875)
              ·
                refine ⟨974135027827531540075313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649423351885021026716875 974135027827531540075313)
                ·
                  refine ⟨730601270870648655056485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974135027827531540075313 730601270870648655056485)
                  ·
                    refine ⟨136987738288246622823091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730601270870648655056485 136987738288246622823091)
                    ·
                      rfl

theorem cell23_800348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_800348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800348 prefixEnd_800348 := by exact prefixLift 800348
  have htrace : WordTrace (prefixWord ++ tailWord_800348) baseStart_800348 baseEnd_800348 := by
    simpa [prefixWord, tailWord_800348, baseEnd_800348] using wordTrace_append hprefix tailTrace_800348
  have hstable : (prefixWord ++ tailWord_800348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800348).length < 2 ^ (prefixWord ++ tailWord_800348).sum := by decide
  have hdescent : baseEnd_800348 < baseStart_800348 := by decide
  rcases family_descends (prefixWord ++ tailWord_800348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800388 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_800388 : Nat := 118140960795 + 800388 * 2 ^ 59
def prefixEnd_800388 : Nat := 4983230072969 + 3 ^ 40 * 800388 * 2
def baseEnd_800388 : Nat := 410983754090919711969089

theorem tailTrace_800388 : CollatzResearch.WordTrace tailWord_800388 prefixEnd_800388 410983754090919711969089 := by
  unfold tailWord_800388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596274312169223116316909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19461699082892297488422545 14596274312169223116316909)
  ·
    refine ⟨5473602867063458668618841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14596274312169223116316909 5473602867063458668618841)
    ·
      refine ⟨4105202150297594001464131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5473602867063458668618841 4105202150297594001464131)
      ·
        refine ⟨6157803225446391002196197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105202150297594001464131 6157803225446391002196197)
        ·
          refine ⟨1154588104771198312911787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6157803225446391002196197 1154588104771198312911787)
          ·
            refine ⟨1731882157156797469367681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154588104771198312911787 1731882157156797469367681)
            ·
              refine ⟨1298911617867598102025761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731882157156797469367681 1298911617867598102025761)
              ·
                refine ⟨974183713400698576519321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298911617867598102025761 974183713400698576519321)
                ·
                  refine ⟨730637785050523932389491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974183713400698576519321 730637785050523932389491)
                  ·
                    refine ⟨1095956677575785898584237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 730637785050523932389491 1095956677575785898584237)
                    ·
                      refine ⟨410983754090919711969089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1095956677575785898584237 410983754090919711969089)
                      ·
                        rfl

theorem cell23_800388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_800388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800388 prefixEnd_800388 := by exact prefixLift 800388
  have htrace : WordTrace (prefixWord ++ tailWord_800388) baseStart_800388 baseEnd_800388 := by
    simpa [prefixWord, tailWord_800388, baseEnd_800388] using wordTrace_append hprefix tailTrace_800388
  have hstable : (prefixWord ++ tailWord_800388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800388).length < 2 ^ (prefixWord ++ tailWord_800388).sum := by decide
  have hdescent : baseEnd_800388 < baseStart_800388 := by decide
  rcases family_descends (prefixWord ++ tailWord_800388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800400 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 11]
def baseStart_800400 : Nat := 118140960795 + 800400 * 2 ^ 59
def prefixEnd_800400 : Nat := 4983230072969 + 3 ^ 40 * 800400 * 2
def baseEnd_800400 : Nat := 45665546206530407224337

theorem tailTrace_800400 : CollatzResearch.WordTrace tailWord_800400 prefixEnd_800400 45665546206530407224337 := by
  unfold tailWord_800400
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596493150147486141035327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19461990866863314854713769 14596493150147486141035327)
  ·
    refine ⟨21894739725221229211552991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596493150147486141035327 21894739725221229211552991)
    ·
      refine ⟨32842109587831843817329487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894739725221229211552991 32842109587831843817329487)
      ·
        refine ⟨49263164381747765725994231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32842109587831843817329487 49263164381747765725994231)
        ·
          refine ⟨73894746572621648588991347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49263164381747765725994231 73894746572621648588991347)
          ·
            refine ⟨110842119858932472883487021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73894746572621648588991347 110842119858932472883487021)
            ·
              refine ⟨41565794947099677331307633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110842119858932472883487021 41565794947099677331307633)
              ·
                refine ⟨31174346210324757998480725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41565794947099677331307633 31174346210324757998480725)
                ·
                  refine ⟨45665546206530407224337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 31174346210324757998480725 45665546206530407224337)
                  ·
                    rfl

theorem cell23_800400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_800400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800400 prefixEnd_800400 := by exact prefixLift 800400
  have htrace : WordTrace (prefixWord ++ tailWord_800400) baseStart_800400 baseEnd_800400 := by
    simpa [prefixWord, tailWord_800400, baseEnd_800400] using wordTrace_append hprefix tailTrace_800400
  have hstable : (prefixWord ++ tailWord_800400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800400).length < 2 ^ (prefixWord ++ tailWord_800400).sum := by decide
  have hdescent : baseEnd_800400 < baseStart_800400 := by decide
  rcases family_descends (prefixWord ++ tailWord_800400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800407 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_800407 : Nat := 118140960795 + 800407 * 2 ^ 59
def prefixEnd_800407 : Nat := 4983230072969 + 3 ^ 40 * 800407 * 2
def baseEnd_800407 : Nat := 410993510223355137631501

theorem tailTrace_800407 : CollatzResearch.WordTrace tailWord_800407 prefixEnd_800407 410993510223355137631501 := by
  unfold tailWord_800407
  simp only [CollatzResearch.WordTrace]
  refine ⟨29193241611269612477575475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19462161074179741651716983 29193241611269612477575475)
  ·
    refine ⟨43789862416904418716363213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29193241611269612477575475 43789862416904418716363213)
    ·
      refine ⟨16421198406339157018636205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43789862416904418716363213 16421198406339157018636205)
      ·
        refine ⟨6157949402377183881988577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16421198406339157018636205 6157949402377183881988577)
        ·
          refine ⟨4618462051782887911491433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6157949402377183881988577 4618462051782887911491433)
          ·
            refine ⟨3463846538837165933618575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618462051782887911491433 3463846538837165933618575)
            ·
              refine ⟨5195769808255748900427863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463846538837165933618575 5195769808255748900427863)
              ·
                refine ⟨7793654712383623350641795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195769808255748900427863 7793654712383623350641795)
                ·
                  refine ⟨11690482068575435025962693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7793654712383623350641795 11690482068575435025962693)
                  ·
                    refine ⟨2191965387857894067368005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11690482068575435025962693 2191965387857894067368005)
                    ·
                      refine ⟨410993510223355137631501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2191965387857894067368005 410993510223355137631501)
                      ·
                        rfl

theorem cell23_800407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_800407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800407 prefixEnd_800407 := by exact prefixLift 800407
  have htrace : WordTrace (prefixWord ++ tailWord_800407) baseStart_800407 baseEnd_800407 := by
    simpa [prefixWord, tailWord_800407, baseEnd_800407] using wordTrace_append hprefix tailTrace_800407
  have hstable : (prefixWord ++ tailWord_800407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800407).length < 2 ^ (prefixWord ++ tailWord_800407).sum := by decide
  have hdescent : baseEnd_800407 < baseStart_800407 := by decide
  rcases family_descends (prefixWord ++ tailWord_800407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800417 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 9]
def baseStart_800417 : Nat := 118140960795 + 800417 * 2 ^ 59
def prefixEnd_800417 : Nat := 4983230072969 + 3 ^ 40 * 800417 * 2
def baseEnd_800417 : Nat := 45666516114433344278495

theorem tailTrace_800417 : CollatzResearch.WordTrace tailWord_800417 prefixEnd_800417 45666516114433344278495 := by
  unfold tailWord_800417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29193606341233384185439505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19462404227488922790293003 29193606341233384185439505)
  ·
    refine ⟨21895204755925038139079629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29193606341233384185439505 21895204755925038139079629)
    ·
      refine ⟨8210701783471889302154861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21895204755925038139079629 8210701783471889302154861)
      ·
        refine ⟨3079013168801958488308073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8210701783471889302154861 3079013168801958488308073)
        ·
          refine ⟨2309259876601468866231055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3079013168801958488308073 2309259876601468866231055)
          ·
            refine ⟨3463889814902203299346583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309259876601468866231055 3463889814902203299346583)
            ·
              refine ⟨5195834722353304949019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3463889814902203299346583 5195834722353304949019875)
              ·
                refine ⟨7793752083529957423529813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5195834722353304949019875 7793752083529957423529813)
                ·
                  refine ⟨45666516114433344278495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7793752083529957423529813 45666516114433344278495)
                  ·
                    rfl

theorem cell23_800417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_800417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800417 prefixEnd_800417 := by exact prefixLift 800417
  have htrace : WordTrace (prefixWord ++ tailWord_800417) baseStart_800417 baseEnd_800417 := by
    simpa [prefixWord, tailWord_800417, baseEnd_800417] using wordTrace_append hprefix tailTrace_800417
  have hstable : (prefixWord ++ tailWord_800417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800417).length < 2 ^ (prefixWord ++ tailWord_800417).sum := by decide
  have hdescent : baseEnd_800417 < baseStart_800417 := by decide
  rcases family_descends (prefixWord ++ tailWord_800417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800434 : List Nat := [3, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_800434 : Nat := 118140960795 + 800434 * 2 ^ 59
def prefixEnd_800434 : Nat := 4983230072969 + 3 ^ 40 * 800434 * 2
def baseEnd_800434 : Nat := 45667486022336281332653

theorem tailTrace_800434 : CollatzResearch.WordTrace tailWord_800434 prefixEnd_800434 45667486022336281332653 := by
  unfold tailWord_800434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7298556595542949022202089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19462817588114530725872237 7298556595542949022202089)
  ·
    refine ⟨5473917446657211766651567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7298556595542949022202089 5473917446657211766651567)
    ·
      refine ⟨8210876169985817649977351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5473917446657211766651567 8210876169985817649977351)
      ·
        refine ⟨12316314254978726474966027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8210876169985817649977351 12316314254978726474966027)
        ·
          refine ⟨18474471382468089712449041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12316314254978726474966027 18474471382468089712449041)
          ·
            refine ⟨13855853536851067284336781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18474471382468089712449041 13855853536851067284336781)
            ·
              refine ⟨5195945076319150231626293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13855853536851067284336781 5195945076319150231626293)
              ·
                refine ⟨487119850904920334214965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5195945076319150231626293 487119850904920334214965)
                ·
                  refine ⟨45667486022336281332653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487119850904920334214965 45667486022336281332653)
                  ·
                    rfl

theorem cell23_800434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_800434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800434 prefixEnd_800434 := by exact prefixLift 800434
  have htrace : WordTrace (prefixWord ++ tailWord_800434) baseStart_800434 baseEnd_800434 := by
    simpa [prefixWord, tailWord_800434, baseEnd_800434] using wordTrace_append hprefix tailTrace_800434
  have hstable : (prefixWord ++ tailWord_800434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800434).length < 2 ^ (prefixWord ++ tailWord_800434).sum := by decide
  have hdescent : baseEnd_800434 < baseStart_800434 := by decide
  rcases family_descends (prefixWord ++ tailWord_800434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800444 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_800444 : Nat := 118140960795 + 800444 * 2 ^ 59
def prefixEnd_800444 : Nat := 4983230072969 + 3 ^ 40 * 800444 * 2
def baseEnd_800444 : Nat := 411012509007571492868831

theorem tailTrace_800444 : CollatzResearch.WordTrace tailWord_800444 prefixEnd_800444 411012509007571492868831 := by
  unfold tailWord_800444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14597295556067783898336193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19463060741423711864448257 14597295556067783898336193)
  ·
    refine ⟨10947971667050837923752145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14597295556067783898336193 10947971667050837923752145)
    ·
      refine ⟨8210978750288128442814109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10947971667050837923752145 8210978750288128442814109)
      ·
        refine ⟨3079117031358048166055291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8210978750288128442814109 3079117031358048166055291)
        ·
          refine ⟨4618675547037072249082937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079117031358048166055291 4618675547037072249082937)
          ·
            refine ⟨3464006660277804186812203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618675547037072249082937 3464006660277804186812203)
            ·
              refine ⟨5196009990416706280218305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464006660277804186812203 5196009990416706280218305)
              ·
                refine ⟨3897007492812529710163729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5196009990416706280218305 3897007492812529710163729)
                ·
                  refine ⟨2922755619609397282622797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3897007492812529710163729 2922755619609397282622797)
                  ·
                    refine ⟨1096033357353523980983549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2922755619609397282622797 1096033357353523980983549)
                    ·
                      refine ⟨411012509007571492868831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1096033357353523980983549 411012509007571492868831)
                      ·
                        rfl

theorem cell23_800444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_800444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800444 prefixEnd_800444 := by exact prefixLift 800444
  have htrace : WordTrace (prefixWord ++ tailWord_800444) baseStart_800444 baseEnd_800444 := by
    simpa [prefixWord, tailWord_800444, baseEnd_800444] using wordTrace_append hprefix tailTrace_800444
  have hstable : (prefixWord ++ tailWord_800444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800444).length < 2 ^ (prefixWord ++ tailWord_800444).sum := by decide
  have hdescent : baseEnd_800444 < baseStart_800444 := by decide
  rcases family_descends (prefixWord ++ tailWord_800444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800447 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 4, 5]
def baseStart_800447 : Nat := 118140960795 + 800447 * 2 ^ 59
def prefixEnd_800447 : Nat := 4983230072969 + 3 ^ 40 * 800447 * 2
def baseEnd_800447 : Nat := 137004683149844993710439

theorem tailTrace_800447 : CollatzResearch.WordTrace tailWord_800447 prefixEnd_800447 137004683149844993710439 := by
  unfold tailWord_800447
  simp only [CollatzResearch.WordTrace]
  refine ⟨29194700531124699309031595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19463133687416466206021063 29194700531124699309031595)
  ·
    refine ⟨43792050796687048963547393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29194700531124699309031595 43792050796687048963547393)
    ·
      refine ⟨32844038097515286722660545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43792050796687048963547393 32844038097515286722660545)
      ·
        refine ⟨24633028573136465041995409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32844038097515286722660545 24633028573136465041995409)
        ·
          refine ⟨18474771429852348781496557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24633028573136465041995409 18474771429852348781496557)
          ·
            refine ⟨6928039286194630793061209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18474771429852348781496557 6928039286194630793061209)
            ·
              refine ⟨5196029464645973094795907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6928039286194630793061209 5196029464645973094795907)
              ·
                refine ⟨7794044196968959642193861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196029464645973094795907 7794044196968959642193861)
                ·
                  refine ⟨1461383286931679932911349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7794044196968959642193861 1461383286931679932911349)
                  ·
                    refine ⟨137004683149844993710439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1461383286931679932911349 137004683149844993710439)
                    ·
                      rfl

theorem cell23_800447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_800447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800447 prefixEnd_800447 := by exact prefixLift 800447
  have htrace : WordTrace (prefixWord ++ tailWord_800447) baseStart_800447 baseEnd_800447 := by
    simpa [prefixWord, tailWord_800447, baseEnd_800447] using wordTrace_append hprefix tailTrace_800447
  have hstable : (prefixWord ++ tailWord_800447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800447).length < 2 ^ (prefixWord ++ tailWord_800447).sum := by decide
  have hdescent : baseEnd_800447 < baseStart_800447 := by decide
  rcases family_descends (prefixWord ++ tailWord_800447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800484 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_800484 : Nat := 118140960795 + 800484 * 2 ^ 59
def prefixEnd_800484 : Nat := 4983230072969 + 3 ^ 40 * 800484 * 2
def baseEnd_800484 : Nat := 411033048233751336368647

theorem tailTrace_800484 : CollatzResearch.WordTrace tailWord_800484 prefixEnd_800484 411033048233751336368647 := by
  unfold tailWord_800484
  simp only [CollatzResearch.WordTrace]
  refine ⟨14598025015995327314064253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19464033354660436418752337 14598025015995327314064253)
  ·
    refine ⟨5474259380998247742774095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14598025015995327314064253 5474259380998247742774095)
    ·
      refine ⟨8211389071497371614161143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474259380998247742774095 8211389071497371614161143)
      ·
        refine ⟨12317083607246057421241715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8211389071497371614161143 12317083607246057421241715)
        ·
          refine ⟨18475625410869086131862573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12317083607246057421241715 18475625410869086131862573)
          ·
            refine ⟨6928359529075907299448465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18475625410869086131862573 6928359529075907299448465)
            ·
              refine ⟨5196269646806930474586349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6928359529075907299448465 5196269646806930474586349)
              ·
                refine ⟨1948601117552598927969881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196269646806930474586349 1948601117552598927969881)
                ·
                  refine ⟨1461450838164449195977411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948601117552598927969881 1461450838164449195977411)
                  ·
                    refine ⟨2192176257246673793966117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461450838164449195977411 2192176257246673793966117)
                    ·
                      refine ⟨411033048233751336368647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2192176257246673793966117 411033048233751336368647)
                      ·
                        rfl

theorem cell23_800484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_800484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800484 prefixEnd_800484 := by exact prefixLift 800484
  have htrace : WordTrace (prefixWord ++ tailWord_800484) baseStart_800484 baseEnd_800484 := by
    simpa [prefixWord, tailWord_800484, baseEnd_800484] using wordTrace_append hprefix tailTrace_800484
  have hstable : (prefixWord ++ tailWord_800484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800484).length < 2 ^ (prefixWord ++ tailWord_800484).sum := by decide
  have hdescent : baseEnd_800484 < baseStart_800484 := by decide
  rcases family_descends (prefixWord ++ tailWord_800484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800511 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 1, 4]
def baseStart_800511 : Nat := 118140960795 + 800511 * 2 ^ 59
def prefixEnd_800511 : Nat := 4983230072969 + 3 ^ 40 * 800511 * 2
def baseEnd_800511 : Nat := 137015637403807576910341

theorem tailTrace_800511 : CollatzResearch.WordTrace tailWord_800511 prefixEnd_800511 137015637403807576910341 := by
  unfold tailWord_800511
  simp only [CollatzResearch.WordTrace]
  refine ⟨29197034802892838239361387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19464689868595225492907591 29197034802892838239361387)
  ·
    refine ⟨43795552204339257359042081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29197034802892838239361387 43795552204339257359042081)
    ·
      refine ⟨32846664153254443019281561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43795552204339257359042081 32846664153254443019281561)
      ·
        refine ⟨24634998114940832264461171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32846664153254443019281561 24634998114940832264461171)
        ·
          refine ⟨36952497172411248396691757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24634998114940832264461171 36952497172411248396691757)
          ·
            refine ⟨13857186439654218148759409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36952497172411248396691757 13857186439654218148759409)
            ·
              refine ⟨10392889829740663611569557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13857186439654218148759409 10392889829740663611569557)
              ·
                refine ⟨487166710769093606792323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10392889829740663611569557 487166710769093606792323)
                ·
                  refine ⟨730750066153640410188485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487166710769093606792323 730750066153640410188485)
                  ·
                    refine ⟨137015637403807576910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730750066153640410188485 137015637403807576910341)
                    ·
                      rfl

theorem cell23_800511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 4].length) (baseStart_800511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800511 prefixEnd_800511 := by exact prefixLift 800511
  have htrace : WordTrace (prefixWord ++ tailWord_800511) baseStart_800511 baseEnd_800511 := by
    simpa [prefixWord, tailWord_800511, baseEnd_800511] using wordTrace_append hprefix tailTrace_800511
  have hstable : (prefixWord ++ tailWord_800511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800511).length < 2 ^ (prefixWord ++ tailWord_800511).sum := by decide
  have hdescent : baseEnd_800511 < baseStart_800511 := by decide
  rcases family_descends (prefixWord ++ tailWord_800511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800558 : List Nat := [4, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_800558 : Nat := 118140960795 + 800558 * 2 ^ 59
def prefixEnd_800558 : Nat := 4983230072969 + 3 ^ 40 * 800558 * 2
def baseEnd_800558 : Nat := 45674560644687116315923

theorem tailTrace_800558 : CollatzResearch.WordTrace tailWord_800558 prefixEnd_800558 45674560644687116315923 := by
  unfold tailWord_800558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649843629215320658290291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19465832689148376844214885 3649843629215320658290291)
  ·
    refine ⟨5474765443822980987435437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649843629215320658290291 5474765443822980987435437)
    ·
      refine ⟨2053037041433617870288289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5474765443822980987435437 2053037041433617870288289)
      ·
        refine ⟨1539777781075213402716217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2053037041433617870288289 1539777781075213402716217)
        ·
          refine ⟨1154833335806410052037163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539777781075213402716217 1154833335806410052037163)
          ·
            refine ⟨1732250003709615078055745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154833335806410052037163 1732250003709615078055745)
            ·
              refine ⟨1299187502782211308541809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732250003709615078055745 1299187502782211308541809)
              ·
                refine ⟨974390627086658481406357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299187502782211308541809 974390627086658481406357)
                ·
                  refine ⟨45674560644687116315923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 974390627086658481406357 45674560644687116315923)
                  ·
                    rfl

theorem cell23_800558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_800558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800558 prefixEnd_800558 := by exact prefixLift 800558
  have htrace : WordTrace (prefixWord ++ tailWord_800558) baseStart_800558 baseEnd_800558 := by
    simpa [prefixWord, tailWord_800558, baseEnd_800558] using wordTrace_append hprefix tailTrace_800558
  have hstable : (prefixWord ++ tailWord_800558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800558).length < 2 ^ (prefixWord ++ tailWord_800558).sum := by decide
  have hdescent : baseEnd_800558 < baseStart_800558 := by decide
  rcases family_descends (prefixWord ++ tailWord_800558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800584 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_800584 : Nat := 118140960795 + 800584 * 2 ^ 59
def prefixEnd_800584 : Nat := 4983230072969 + 3 ^ 40 * 800584 * 2
def baseEnd_800584 : Nat := 137028132099733648372729

theorem tailTrace_800584 : CollatzResearch.WordTrace tailWord_800584 prefixEnd_800584 137028132099733648372729 := by
  unfold tailWord_800584
  simp only [CollatzResearch.WordTrace]
  refine ⟨14599848665814185853384403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19466464887752247804512537 14599848665814185853384403)
  ·
    refine ⟨21899772998721278780076605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14599848665814185853384403 21899772998721278780076605)
    ·
      refine ⟨8212414874520479542528727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21899772998721278780076605 8212414874520479542528727)
      ·
        refine ⟨12318622311780719313793091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8212414874520479542528727 12318622311780719313793091)
        ·
          refine ⟨18477933467671078970689637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318622311780719313793091 18477933467671078970689637)
          ·
            refine ⟨3464612525188327307004307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18477933467671078970689637 3464612525188327307004307)
            ·
              refine ⟨5196918787782490960506461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464612525188327307004307 5196918787782490960506461)
              ·
                refine ⟨1948844545418434110189923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5196918787782490960506461 1948844545418434110189923)
                ·
                  refine ⟨2923266818127651165284885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948844545418434110189923 2923266818127651165284885)
                  ·
                    refine ⟨137028132099733648372729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2923266818127651165284885 137028132099733648372729)
                    ·
                      rfl

theorem cell23_800584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_800584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800584 prefixEnd_800584 := by exact prefixLift 800584
  have htrace : WordTrace (prefixWord ++ tailWord_800584) baseStart_800584 baseEnd_800584 := by
    simpa [prefixWord, tailWord_800584, baseEnd_800584] using wordTrace_append hprefix tailTrace_800584
  have hstable : (prefixWord ++ tailWord_800584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800584).length < 2 ^ (prefixWord ++ tailWord_800584).sum := by decide
  have hdescent : baseEnd_800584 < baseStart_800584 := by decide
  rcases family_descends (prefixWord ++ tailWord_800584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800608 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4]
def baseStart_800608 : Nat := 118140960795 + 800608 * 2 ^ 59
def prefixEnd_800608 : Nat := 4983230072969 + 3 ^ 40 * 800608 * 2
def baseEnd_800608 : Nat := 411096719834908851218077

theorem tailTrace_800608 : CollatzResearch.WordTrace tailWord_800608 prefixEnd_800608 411096719834908851218077 := by
  unfold tailWord_800608
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600286341770711902821239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19467048455694282537094985 14600286341770711902821239)
  ·
    refine ⟨21900429512656067854231859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14600286341770711902821239 21900429512656067854231859)
    ·
      refine ⟨32850644268984101781347789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21900429512656067854231859 32850644268984101781347789)
      ·
        refine ⟨12318991600869038168005421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32850644268984101781347789 12318991600869038168005421)
        ·
          refine ⟨4619621850325889313002033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12318991600869038168005421 4619621850325889313002033)
          ·
            refine ⟨3464716387744416984751525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619621850325889313002033 3464716387744416984751525)
            ·
              refine ⟨649634322702078184640911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3464716387744416984751525 649634322702078184640911)
              ·
                refine ⟨974451484053117276961367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649634322702078184640911 974451484053117276961367)
                ·
                  refine ⟨1461677226079675915442051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974451484053117276961367 1461677226079675915442051)
                  ·
                    refine ⟨2192515839119513873163077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461677226079675915442051 2192515839119513873163077)
                    ·
                      refine ⟨411096719834908851218077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2192515839119513873163077 411096719834908851218077)
                      ·
                        rfl

theorem cell23_800608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_800608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800608 prefixEnd_800608 := by exact prefixLift 800608
  have htrace : WordTrace (prefixWord ++ tailWord_800608) baseStart_800608 baseEnd_800608 := by
    simpa [prefixWord, tailWord_800608, baseEnd_800608] using wordTrace_append hprefix tailTrace_800608
  have hstable : (prefixWord ++ tailWord_800608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800608).length < 2 ^ (prefixWord ++ tailWord_800608).sum := by decide
  have hdescent : baseEnd_800608 < baseStart_800608 := by decide
  rcases family_descends (prefixWord ++ tailWord_800608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800625 : List Nat := [1, 2, 2, 2, 1, 3, 1, 6, 1, 2, 2]
def baseStart_800625 : Nat := 118140960795 + 800625 * 2 ^ 59
def prefixEnd_800625 : Nat := 4983230072969 + 3 ^ 40 * 800625 * 2
def baseEnd_800625 : Nat := 411105449006035284705499

theorem tailTrace_800625 : CollatzResearch.WordTrace tailWord_800625 prefixEnd_800625 411105449006035284705499 := by
  unfold tailWord_800625
  simp only [CollatzResearch.WordTrace]
  refine ⟨29201192724479835709011329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19467461816319890472674219 29201192724479835709011329)
  ·
    refine ⟨21900894543359876781758497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29201192724479835709011329 21900894543359876781758497)
    ·
      refine ⟨16425670907519907586318873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21900894543359876781758497 16425670907519907586318873)
      ·
        refine ⟨12319253180639930689739155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16425670907519907586318873 12319253180639930689739155)
        ·
          refine ⟨18478879770959896034608733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319253180639930689739155 18478879770959896034608733)
          ·
            refine ⟨6929579914109961012978275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18478879770959896034608733 6929579914109961012978275)
            ·
              refine ⟨10394369871164941519467413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6929579914109961012978275 10394369871164941519467413)
              ·
                refine ⟨487236087710856633725035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10394369871164941519467413 487236087710856633725035)
                ·
                  refine ⟨730854131566284950587553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487236087710856633725035 730854131566284950587553)
                  ·
                    refine ⟨548140598674713712940665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730854131566284950587553 548140598674713712940665)
                    ·
                      refine ⟨411105449006035284705499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548140598674713712940665 411105449006035284705499)
                      ·
                        rfl

theorem cell23_800625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 1, 2, 2].length) (baseStart_800625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800625 prefixEnd_800625 := by exact prefixLift 800625
  have htrace : WordTrace (prefixWord ++ tailWord_800625) baseStart_800625 baseEnd_800625 := by
    simpa [prefixWord, tailWord_800625, baseEnd_800625] using wordTrace_append hprefix tailTrace_800625
  have hstable : (prefixWord ++ tailWord_800625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800625).length < 2 ^ (prefixWord ++ tailWord_800625).sum := by decide
  have hdescent : baseEnd_800625 < baseStart_800625 := by decide
  rcases family_descends (prefixWord ++ tailWord_800625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800638 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 1, 1, 6]
def baseStart_800638 : Nat := 118140960795 + 800638 * 2 ^ 59
def prefixEnd_800638 : Nat := 4983230072969 + 3 ^ 40 * 800638 * 2
def baseEnd_800638 : Nat := 411112124254543733842939

theorem tailTrace_800638 : CollatzResearch.WordTrace tailWord_800638 prefixEnd_800638 411112124254543733842939 := by
  unfold tailWord_800638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650208359179092366154321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19467777915621825952823045 3650208359179092366154321)
  ·
    refine ⟨2737656269384319274615741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3650208359179092366154321 2737656269384319274615741)
    ·
      refine ⟨1026621101019119727980903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2737656269384319274615741 1026621101019119727980903)
      ·
        refine ⟨1539931651528679591971355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026621101019119727980903 1539931651528679591971355)
        ·
          refine ⟨2309897477293019387957033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1539931651528679591971355 2309897477293019387957033)
          ·
            refine ⟨1732423107969764540967775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309897477293019387957033 1732423107969764540967775)
            ·
              refine ⟨2598634661954646811451663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732423107969764540967775 2598634661954646811451663)
              ·
                refine ⟨3897951992931970217177495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598634661954646811451663 3897951992931970217177495)
                ·
                  refine ⟨5846927989397955325766243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897951992931970217177495 5846927989397955325766243)
                  ·
                    refine ⟨8770391984096932988649365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5846927989397955325766243 8770391984096932988649365)
                    ·
                      refine ⟨411112124254543733842939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8770391984096932988649365 411112124254543733842939)
                      ·
                        rfl

theorem cell23_800638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_800638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800638 prefixEnd_800638 := by exact prefixLift 800638
  have htrace : WordTrace (prefixWord ++ tailWord_800638) baseStart_800638 baseEnd_800638 := by
    simpa [prefixWord, tailWord_800638, baseEnd_800638] using wordTrace_append hprefix tailTrace_800638
  have hstable : (prefixWord ++ tailWord_800638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800638).length < 2 ^ (prefixWord ++ tailWord_800638).sum := by decide
  have hdescent : baseEnd_800638 < baseStart_800638 := by decide
  rcases family_descends (prefixWord ++ tailWord_800638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800644 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_800644 : Nat := 118140960795 + 800644 * 2 ^ 59
def prefixEnd_800644 : Nat := 4983230072969 + 3 ^ 40 * 800644 * 2
def baseEnd_800644 : Nat := 137038401712823570122637

theorem tailTrace_800644 : CollatzResearch.WordTrace tailWord_800644 prefixEnd_800644 137038401712823570122637 := by
  unfold tailWord_800644
  simp only [CollatzResearch.WordTrace]
  refine ⟨14600942855705500976976493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19467923807607334635968657 14600942855705500976976493)
  ·
    refine ⟨5475353570889562866366185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14600942855705500976976493 5475353570889562866366185)
    ·
      refine ⟨4106515178167172149774639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5475353570889562866366185 4106515178167172149774639)
      ·
        refine ⟨6159772767250758224661959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106515178167172149774639 6159772767250758224661959)
        ·
          refine ⟨9239659150876137336992939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6159772767250758224661959 9239659150876137336992939)
          ·
            refine ⟨13859488726314206005489409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9239659150876137336992939 13859488726314206005489409)
            ·
              refine ⟨10394616544735654504117057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13859488726314206005489409 10394616544735654504117057)
              ·
                refine ⟨7795962408551740878087793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10394616544735654504117057 7795962408551740878087793)
                ·
                  refine ⟨5846971806413805658565845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7795962408551740878087793 5846971806413805658565845)
                  ·
                    refine ⟨137038401712823570122637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5846971806413805658565845 137038401712823570122637)
                    ·
                      rfl

theorem cell23_800644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_800644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800644 prefixEnd_800644 := by exact prefixLift 800644
  have htrace : WordTrace (prefixWord ++ tailWord_800644) baseStart_800644 baseEnd_800644 := by
    simpa [prefixWord, tailWord_800644, baseEnd_800644] using wordTrace_append hprefix tailTrace_800644
  have hstable : (prefixWord ++ tailWord_800644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800644).length < 2 ^ (prefixWord ++ tailWord_800644).sum := by decide
  have hdescent : baseEnd_800644 < baseStart_800644 := by decide
  rcases family_descends (prefixWord ++ tailWord_800644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800648 : List Nat := [2, 1, 3, 3, 3, 2, 2, 7]
def baseStart_800648 : Nat := 118140960795 + 800648 * 2 ^ 59
def prefixEnd_800648 : Nat := 4983230072969 + 3 ^ 40 * 800648 * 2
def baseEnd_800648 : Nat := 15226565150410692396959

theorem tailTrace_800648 : CollatzResearch.WordTrace tailWord_800648 prefixEnd_800648 15226565150410692396959 := by
  unfold tailWord_800648
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601015801698255318549299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19468021068931007091399065 14601015801698255318549299)
  ·
    refine ⟨21901523702547382977823949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14601015801698255318549299 21901523702547382977823949)
    ·
      refine ⟨8213071388455268616683981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21901523702547382977823949 8213071388455268616683981)
      ·
        refine ⟨3079901770670725731256493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8213071388455268616683981 3079901770670725731256493)
        ·
          refine ⟨1154963164001522149221185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3079901770670725731256493 1154963164001522149221185)
          ·
            refine ⟨866222373001141611915889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154963164001522149221185 866222373001141611915889)
            ·
              refine ⟨649666779750856208936917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866222373001141611915889 649666779750856208936917)
              ·
                refine ⟨15226565150410692396959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 649666779750856208936917 15226565150410692396959)
                ·
                  rfl

theorem cell23_800648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 7].length) (baseStart_800648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800648 prefixEnd_800648 := by exact prefixLift 800648
  have htrace : WordTrace (prefixWord ++ tailWord_800648) baseStart_800648 baseEnd_800648 := by
    simpa [prefixWord, tailWord_800648, baseEnd_800648] using wordTrace_append hprefix tailTrace_800648
  have hstable : (prefixWord ++ tailWord_800648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800648).length < 2 ^ (prefixWord ++ tailWord_800648).sum := by decide
  have hdescent : baseEnd_800648 < baseStart_800648 := by decide
  rcases family_descends (prefixWord ++ tailWord_800648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800662 : List Nat := [5, 3, 1, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_800662 : Nat := 118140960795 + 800662 * 2 ^ 59
def prefixEnd_800662 : Nat := 4983230072969 + 3 ^ 40 * 800662 * 2
def baseEnd_800662 : Nat := 411124447790251639942829

theorem tailTrace_800662 : CollatzResearch.WordTrace tailWord_800662 prefixEnd_800662 411124447790251639942829 := by
  unfold tailWord_800662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825158889084111939256765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19468361483563860685405493 1825158889084111939256765)
  ·
    refine ⟨684434583406541977221287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1825158889084111939256765 684434583406541977221287)
    ·
      refine ⟨1026651875109812965831931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684434583406541977221287 1026651875109812965831931)
      ·
        refine ⟨1539977812664719448747897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026651875109812965831931 1539977812664719448747897)
        ·
          refine ⟨1154983359498539586560923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539977812664719448747897 1154983359498539586560923)
          ·
            refine ⟨1732475039247809379841385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154983359498539586560923 1732475039247809379841385)
            ·
              refine ⟨1299356279435857034881039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732475039247809379841385 1299356279435857034881039)
              ·
                refine ⟨1949034419153785552321559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299356279435857034881039 1949034419153785552321559)
                ·
                  refine ⟨2923551628730678328482339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949034419153785552321559 2923551628730678328482339)
                  ·
                    refine ⟨4385327443096017492723509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923551628730678328482339 4385327443096017492723509)
                    ·
                      refine ⟨411124447790251639942829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4385327443096017492723509 411124447790251639942829)
                      ·
                        rfl

theorem cell23_800662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_800662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800662 prefixEnd_800662 := by exact prefixLift 800662
  have htrace : WordTrace (prefixWord ++ tailWord_800662) baseStart_800662 baseEnd_800662 := by
    simpa [prefixWord, tailWord_800662, baseEnd_800662] using wordTrace_append hprefix tailTrace_800662
  have hstable : (prefixWord ++ tailWord_800662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800662).length < 2 ^ (prefixWord ++ tailWord_800662).sum := by decide
  have hdescent : baseEnd_800662 < baseStart_800662 := by decide
  rcases family_descends (prefixWord ++ tailWord_800662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800681 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 4, 2]
def baseStart_800681 : Nat := 118140960795 + 800681 * 2 ^ 59
def prefixEnd_800681 : Nat := 4983230072969 + 3 ^ 40 * 800681 * 2
def baseEnd_800681 : Nat := 411134203922687065605241

theorem tailTrace_800681 : CollatzResearch.WordTrace tailWord_800681 prefixEnd_800681 411134203922687065605241 := by
  unfold tailWord_800681
  simp only [CollatzResearch.WordTrace]
  refine ⟨29203235212276957273049897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19468823474851304848699931 29203235212276957273049897)
  ·
    refine ⟨21902426409207717954787423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29203235212276957273049897 21902426409207717954787423)
    ·
      refine ⟨32853639613811576932181135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21902426409207717954787423 32853639613811576932181135)
      ·
        refine ⟨49280459420717365398271703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32853639613811576932181135 49280459420717365398271703)
        ·
          refine ⟨73920689131076048097407555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49280459420717365398271703 73920689131076048097407555)
          ·
            refine ⟨110881033696614072146111333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73920689131076048097407555 110881033696614072146111333)
            ·
              refine ⟨20790193818115138527395875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110881033696614072146111333 20790193818115138527395875)
              ·
                refine ⟨31185290727172707791093813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20790193818115138527395875 31185290727172707791093813)
                ·
                  refine ⟨2923621005672441355415045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31185290727172707791093813 2923621005672441355415045)
                  ·
                    refine ⟨548178938563582754140321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2923621005672441355415045 548178938563582754140321)
                    ·
                      refine ⟨411134203922687065605241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548178938563582754140321 411134203922687065605241)
                      ·
                        rfl

theorem cell23_800681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 4, 2].length) (baseStart_800681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800681 prefixEnd_800681 := by exact prefixLift 800681
  have htrace : WordTrace (prefixWord ++ tailWord_800681) baseStart_800681 baseEnd_800681 := by
    simpa [prefixWord, tailWord_800681, baseEnd_800681] using wordTrace_append hprefix tailTrace_800681
  have hstable : (prefixWord ++ tailWord_800681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800681).length < 2 ^ (prefixWord ++ tailWord_800681).sum := by decide
  have hdescent : baseEnd_800681 < baseStart_800681 := by decide
  rcases family_descends (prefixWord ++ tailWord_800681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800684 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_800684 : Nat := 118140960795 + 800684 * 2 ^ 59
def prefixEnd_800684 : Nat := 4983230072969 + 3 ^ 40 * 800684 * 2
def baseEnd_800684 : Nat := 411135744364650553867727

theorem tailTrace_800684 : CollatzResearch.WordTrace tailWord_800684 prefixEnd_800684 411135744364650553867727 := by
  unfold tailWord_800684
  simp only [CollatzResearch.WordTrace]
  refine ⟨14601672315633044392704553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19468896420844059190272737 14601672315633044392704553)
  ·
    refine ⟨10951254236724783294528415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14601672315633044392704553 10951254236724783294528415)
    ·
      refine ⟨16426881355087174941792623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951254236724783294528415 16426881355087174941792623)
      ·
        refine ⟨24640322032630762412688935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16426881355087174941792623 24640322032630762412688935)
        ·
          refine ⟨36960483048946143619033403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24640322032630762412688935 36960483048946143619033403)
          ·
            refine ⟨55440724573419215428550105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36960483048946143619033403 55440724573419215428550105)
            ·
              refine ⟨41580543430064411571412579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55440724573419215428550105 41580543430064411571412579)
              ·
                refine ⟨62370815145096617357118869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41580543430064411571412579 62370815145096617357118869)
                ·
                  refine ⟨2923631959926403938614947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62370815145096617357118869 2923631959926403938614947)
                  ·
                    refine ⟨4385447939889605907922421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923631959926403938614947 4385447939889605907922421)
                    ·
                      refine ⟨411135744364650553867727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4385447939889605907922421 411135744364650553867727)
                      ·
                        rfl

theorem cell23_800684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_800684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800684 prefixEnd_800684 := by exact prefixLift 800684
  have htrace : WordTrace (prefixWord ++ tailWord_800684) baseStart_800684 baseEnd_800684 := by
    simpa [prefixWord, tailWord_800684, baseEnd_800684] using wordTrace_append hprefix tailTrace_800684
  have hstable : (prefixWord ++ tailWord_800684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800684).length < 2 ^ (prefixWord ++ tailWord_800684).sum := by decide
  have hdescent : baseEnd_800684 < baseStart_800684 := by decide
  rcases family_descends (prefixWord ++ tailWord_800684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800686 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_800686 : Nat := 118140960795 + 800686 * 2 ^ 59
def prefixEnd_800686 : Nat := 4983230072969 + 3 ^ 40 * 800686 * 2
def baseEnd_800686 : Nat := 137045590441986515347573

theorem tailTrace_800686 : CollatzResearch.WordTrace tailWord_800686 prefixEnd_800686 137045590441986515347573 := by
  unfold tailWord_800686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650427197157355390872739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19468945051505895417987941 3650427197157355390872739)
  ·
    refine ⟨5475640795736033086309109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3650427197157355390872739 5475640795736033086309109)
    ·
      refine ⟨513341324600253101841479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5475640795736033086309109 513341324600253101841479)
      ·
        refine ⟨770011986900379652762219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513341324600253101841479 770011986900379652762219)
        ·
          refine ⟨1155017980350569479143329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770011986900379652762219 1155017980350569479143329)
          ·
            refine ⟨866263485262927109357497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155017980350569479143329 866263485262927109357497)
            ·
              refine ⟨649697613947195332018123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866263485262927109357497 649697613947195332018123)
              ·
                refine ⟨974546420920792998027185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649697613947195332018123 974546420920792998027185)
                ·
                  refine ⟨730909815690594748520389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974546420920792998027185 730909815690594748520389)
                  ·
                    refine ⟨137045590441986515347573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 730909815690594748520389 137045590441986515347573)
                    ·
                      rfl

theorem cell23_800686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_800686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800686 prefixEnd_800686 := by exact prefixLift 800686
  have htrace : WordTrace (prefixWord ++ tailWord_800686) baseStart_800686 baseEnd_800686 := by
    simpa [prefixWord, tailWord_800686, baseEnd_800686] using wordTrace_append hprefix tailTrace_800686
  have hstable : (prefixWord ++ tailWord_800686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800686).length < 2 ^ (prefixWord ++ tailWord_800686).sum := by decide
  have hdescent : baseEnd_800686 < baseStart_800686 := by decide
  rcases family_descends (prefixWord ++ tailWord_800686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800698 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2]
def baseStart_800698 : Nat := 118140960795 + 800698 * 2 ^ 59
def prefixEnd_800698 : Nat := 4983230072969 + 3 ^ 40 * 800698 * 2
def baseEnd_800698 : Nat := 411142933093813499092663

theorem tailTrace_800698 : CollatzResearch.WordTrace tailWord_800698 prefixEnd_800698 411142933093813499092663 := by
  unfold tailWord_800698
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300963813303842294104687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19469236835476912784279165 7300963813303842294104687)
  ·
    refine ⟨10951445719955763441157031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7300963813303842294104687 10951445719955763441157031)
    ·
      refine ⟨16427168579933645161735547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10951445719955763441157031 16427168579933645161735547)
      ·
        refine ⟨24640752869900467742603321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16427168579933645161735547 24640752869900467742603321)
        ·
          refine ⟨18480564652425350806952491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24640752869900467742603321 18480564652425350806952491)
          ·
            refine ⟨27720846978638026210428737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18480564652425350806952491 27720846978638026210428737)
            ·
              refine ⟨20790635233978519657821553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27720846978638026210428737 20790635233978519657821553)
              ·
                refine ⟨15592976425483889743366165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20790635233978519657821553 15592976425483889743366165)
                ·
                  refine ⟨730920769944557331720289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15592976425483889743366165 730920769944557331720289)
                  ·
                    refine ⟨548190577458417998790217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 730920769944557331720289 548190577458417998790217)
                    ·
                      refine ⟨411142933093813499092663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548190577458417998790217 411142933093813499092663)
                      ·
                        rfl

theorem cell23_800698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2].length) (baseStart_800698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800698 prefixEnd_800698 := by exact prefixLift 800698
  have htrace : WordTrace (prefixWord ++ tailWord_800698) baseStart_800698 baseEnd_800698 := by
    simpa [prefixWord, tailWord_800698, baseEnd_800698] using wordTrace_append hprefix tailTrace_800698
  have hstable : (prefixWord ++ tailWord_800698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800698).length < 2 ^ (prefixWord ++ tailWord_800698).sum := by decide
  have hdescent : baseEnd_800698 < baseStart_800698 := by decide
  rcases family_descends (prefixWord ++ tailWord_800698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800701 : List Nat := [1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 5]
def baseStart_800701 : Nat := 118140960795 + 800701 * 2 ^ 59
def prefixEnd_800701 : Nat := 4983230072969 + 3 ^ 40 * 800701 * 2
def baseEnd_800701 : Nat := 411144473535776987355149

theorem tailTrace_800701 : CollatzResearch.WordTrace tailWord_800701 prefixEnd_800701 411144473535776987355149 := by
  unfold tailWord_800701
  simp only [CollatzResearch.WordTrace]
  refine ⟨29203964672204500688777957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19469309781469667125851971 29203964672204500688777957)
  ·
    refine ⟨5475743376038343879145867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29203964672204500688777957 5475743376038343879145867)
    ·
      refine ⟨8213615064057515818718801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475743376038343879145867 8213615064057515818718801)
      ·
        refine ⟨6160211298043136864039101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8213615064057515818718801 6160211298043136864039101)
        ·
          refine ⟨2310079236766176324014663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6160211298043136864039101 2310079236766176324014663)
          ·
            refine ⟨3465118855149264486021995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310079236766176324014663 3465118855149264486021995)
            ·
              refine ⟨5197678282723896729032993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465118855149264486021995 5197678282723896729032993)
              ·
                refine ⟨3898258712042922546774745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5197678282723896729032993 3898258712042922546774745)
                ·
                  refine ⟨2923694034032191910081059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3898258712042922546774745 2923694034032191910081059)
                  ·
                    refine ⟨4385541051048287865121589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2923694034032191910081059 4385541051048287865121589)
                    ·
                      refine ⟨411144473535776987355149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4385541051048287865121589 411144473535776987355149)
                      ·
                        rfl

theorem cell23_800701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_800701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800701 prefixEnd_800701 := by exact prefixLift 800701
  have htrace : WordTrace (prefixWord ++ tailWord_800701) baseStart_800701 baseEnd_800701 := by
    simpa [prefixWord, tailWord_800701, baseEnd_800701] using wordTrace_append hprefix tailTrace_800701
  have hstable : (prefixWord ++ tailWord_800701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800701).length < 2 ^ (prefixWord ++ tailWord_800701).sum := by decide
  have hdescent : baseEnd_800701 < baseStart_800701 := by decide
  rcases family_descends (prefixWord ++ tailWord_800701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800702 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2]
def baseStart_800702 : Nat := 118140960795 + 800702 * 2 ^ 59
def prefixEnd_800702 : Nat := 4983230072969 + 3 ^ 40 * 800702 * 2
def baseEnd_800702 : Nat := 411144987016431483442645

theorem tailTrace_800702 : CollatzResearch.WordTrace tailWord_800702 prefixEnd_800702 411144987016431483442645 := by
  unfold tailWord_800702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3650500143150109732445545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19469334096800585239709573 3650500143150109732445545)
  ·
    refine ⟨2737875107362582299334159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3650500143150109732445545 2737875107362582299334159)
    ·
      refine ⟨4106812661043873449001239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2737875107362582299334159 4106812661043873449001239)
      ·
        refine ⟨6160218991565810173501859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4106812661043873449001239 6160218991565810173501859)
        ·
          refine ⟨9240328487348715260252789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6160218991565810173501859 9240328487348715260252789)
          ·
            refine ⟨866280795688942055648699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9240328487348715260252789 866280795688942055648699)
            ·
              refine ⟨1299421193533413083473049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866280795688942055648699 1299421193533413083473049)
              ·
                refine ⟨974565895150059812604787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299421193533413083473049 974565895150059812604787)
                ·
                  refine ⟨1461848842725089718907181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974565895150059812604787 1461848842725089718907181)
                  ·
                    refine ⟨548193316021908644590193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461848842725089718907181 548193316021908644590193)
                    ·
                      refine ⟨411144987016431483442645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548193316021908644590193 411144987016431483442645)
                      ·
                        rfl

theorem cell23_800702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_800702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800702 prefixEnd_800702 := by exact prefixLift 800702
  have htrace : WordTrace (prefixWord ++ tailWord_800702) baseStart_800702 baseEnd_800702 := by
    simpa [prefixWord, tailWord_800702, baseEnd_800702] using wordTrace_append hprefix tailTrace_800702
  have hstable : (prefixWord ++ tailWord_800702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800702).length < 2 ^ (prefixWord ++ tailWord_800702).sum := by decide
  have hdescent : baseEnd_800702 < baseStart_800702 := by decide
  rcases family_descends (prefixWord ++ tailWord_800702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800704 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 9]
def baseStart_800704 : Nat := 118140960795 + 800704 * 2 ^ 59
def prefixEnd_800704 : Nat := 4983230072969 + 3 ^ 40 * 800704 * 2
def baseEnd_800704 : Nat := 45682890441971163957515

theorem tailTrace_800704 : CollatzResearch.WordTrace tailWord_800704 prefixEnd_800704 45682890441971163957515 := by
  unfold tailWord_800704
  simp only [CollatzResearch.WordTrace]
  refine ⟨14602037045596816100568583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19469382727462421467424777 14602037045596816100568583)
  ·
    refine ⟨21903055568395224150852875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14602037045596816100568583 21903055568395224150852875)
    ·
      refine ⟨32854583352592836226279313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21903055568395224150852875 32854583352592836226279313)
      ·
        refine ⟨24640937514444627169709485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32854583352592836226279313 24640937514444627169709485)
        ·
          refine ⟨9240351567916735188641057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24640937514444627169709485 9240351567916735188641057)
          ·
            refine ⟨6930263675937551391480793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9240351567916735188641057 6930263675937551391480793)
            ·
              refine ⟨5197697756953163543610595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6930263675937551391480793 5197697756953163543610595)
              ·
                refine ⟨7796546635429745315415893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5197697756953163543610595 7796546635429745315415893)
                ·
                  refine ⟨45682890441971163957515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7796546635429745315415893 45682890441971163957515)
                  ·
                    rfl

theorem cell23_800704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_800704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800704 prefixEnd_800704 := by exact prefixLift 800704
  have htrace : WordTrace (prefixWord ++ tailWord_800704) baseStart_800704 baseEnd_800704 := by
    simpa [prefixWord, tailWord_800704, baseEnd_800704] using wordTrace_append hprefix tailTrace_800704
  have hstable : (prefixWord ++ tailWord_800704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800704).length < 2 ^ (prefixWord ++ tailWord_800704).sum := by decide
  have hdescent : baseEnd_800704 < baseStart_800704 := by decide
  rcases family_descends (prefixWord ++ tailWord_800704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800772 : List Nat := [2, 3, 2, 4, 1, 1, 2, 3, 5]
def baseStart_800772 : Nat := 118140960795 + 800772 * 2 ^ 59
def prefixEnd_800772 : Nat := 4983230072969 + 3 ^ 40 * 800772 * 2
def baseEnd_800772 : Nat := 45686770073582912174147

theorem tailTrace_800772 : CollatzResearch.WordTrace tailWord_800772 prefixEnd_800772 45686770073582912174147 := by
  unfold tailWord_800772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14603277127473639907306285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19471036169964853209741713 14603277127473639907306285)
  ·
    refine ⟨5476228922802614965239857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14603277127473639907306285 5476228922802614965239857)
    ·
      refine ⟨4107171692101961223929893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5476228922802614965239857 4107171692101961223929893)
      ·
        refine ⟨770094692269117729486855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4107171692101961223929893 770094692269117729486855)
        ·
          refine ⟨1155142038403676594230283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770094692269117729486855 1155142038403676594230283)
          ·
            refine ⟨1732713057605514891345425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155142038403676594230283 1732713057605514891345425)
            ·
              refine ⟨1299534793204136168509069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732713057605514891345425 1299534793204136168509069)
              ·
                refine ⟨487325547451551063190901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299534793204136168509069 487325547451551063190901)
                ·
                  refine ⟨45686770073582912174147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487325547451551063190901 45686770073582912174147)
                  ·
                    rfl

theorem cell23_800772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_800772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800772 prefixEnd_800772 := by exact prefixLift 800772
  have htrace : WordTrace (prefixWord ++ tailWord_800772) baseStart_800772 baseEnd_800772 := by
    simpa [prefixWord, tailWord_800772, baseEnd_800772] using wordTrace_append hprefix tailTrace_800772
  have hstable : (prefixWord ++ tailWord_800772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800772).length < 2 ^ (prefixWord ++ tailWord_800772).sum := by decide
  have hdescent : baseEnd_800772 < baseStart_800772 := by decide
  rcases family_descends (prefixWord ++ tailWord_800772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800832 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 1, 4]
def baseStart_800832 : Nat := 118140960795 + 800832 * 2 ^ 59
def prefixEnd_800832 : Nat := 4983230072969 + 3 ^ 40 * 800832 * 2
def baseEnd_800832 : Nat := 137070579833838658272349

theorem tailTrace_800832 : CollatzResearch.WordTrace tailWord_800832 prefixEnd_800832 137070579833838658272349 := by
  unfold tailWord_800832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14604371317364955030898375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19472495089819940041197833 14604371317364955030898375)
  ·
    refine ⟨21906556976047432546347563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14604371317364955030898375 21906556976047432546347563)
    ·
      refine ⟨32859835464071148819521345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21906556976047432546347563 32859835464071148819521345)
      ·
        refine ⟨24644876598053361614641009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32859835464071148819521345 24644876598053361614641009)
        ·
          refine ⟨18483657448540021210980757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24644876598053361614641009 18483657448540021210980757)
          ·
            refine ⟨866421442900313494264723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18483657448540021210980757 866421442900313494264723)
            ·
              refine ⟨1299632164350470241397085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866421442900313494264723 1299632164350470241397085)
              ·
                refine ⟨487362061631426340523907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1299632164350470241397085 487362061631426340523907)
                ·
                  refine ⟨731043092447139510785861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487362061631426340523907 731043092447139510785861)
                  ·
                    refine ⟨137070579833838658272349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731043092447139510785861 137070579833838658272349)
                    ·
                      rfl

theorem cell23_800832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_800832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800832 prefixEnd_800832 := by exact prefixLift 800832
  have htrace : WordTrace (prefixWord ++ tailWord_800832) baseStart_800832 baseEnd_800832 := by
    simpa [prefixWord, tailWord_800832, baseEnd_800832] using wordTrace_append hprefix tailTrace_800832
  have hstable : (prefixWord ++ tailWord_800832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800832).length < 2 ^ (prefixWord ++ tailWord_800832).sum := by decide
  have hdescent : baseEnd_800832 < baseStart_800832 := by decide
  rcases family_descends (prefixWord ++ tailWord_800832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800855 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 3]
def baseStart_800855 : Nat := 118140960795 + 800855 * 2 ^ 59
def prefixEnd_800855 : Nat := 4983230072969 + 3 ^ 40 * 800855 * 2
def baseEnd_800855 : Nat := 411223549556569384829441

theorem tailTrace_800855 : CollatzResearch.WordTrace tailWord_800855 prefixEnd_800855 411223549556569384829441 := by
  unfold tailWord_800855
  simp only [CollatzResearch.WordTrace]
  refine ⟨29209581513646584989884019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19473054342431056659922679 29209581513646584989884019)
  ·
    refine ⟨43814372270469877484826029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29209581513646584989884019 43814372270469877484826029)
    ·
      refine ⟨16430389601426204056809761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43814372270469877484826029 16430389601426204056809761)
      ·
        refine ⟨12322792201069653042607321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16430389601426204056809761 12322792201069653042607321)
        ·
          refine ⟨9242094150802239781955491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12322792201069653042607321 9242094150802239781955491)
          ·
            refine ⟨13863141226203359672933237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9242094150802239781955491 13863141226203359672933237)
            ·
              refine ⟨1299669489956564969337491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13863141226203359672933237 1299669489956564969337491)
              ·
                refine ⟨1949504234934847454006237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299669489956564969337491 1949504234934847454006237)
                ·
                  refine ⟨731064088100567795252339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1949504234934847454006237 731064088100567795252339)
                  ·
                    refine ⟨1096596132150851692878509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 731064088100567795252339 1096596132150851692878509)
                    ·
                      refine ⟨411223549556569384829441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1096596132150851692878509 411223549556569384829441)
                      ·
                        rfl

theorem cell23_800855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_800855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800855 prefixEnd_800855 := by exact prefixLift 800855
  have htrace : WordTrace (prefixWord ++ tailWord_800855) baseStart_800855 baseEnd_800855 := by
    simpa [prefixWord, tailWord_800855, baseEnd_800855] using wordTrace_append hprefix tailTrace_800855
  have hstable : (prefixWord ++ tailWord_800855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800855).length < 2 ^ (prefixWord ++ tailWord_800855).sum := by decide
  have hdescent : baseEnd_800855 < baseStart_800855 := by decide
  rcases family_descends (prefixWord ++ tailWord_800855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800882 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 2, 3, 2]
def baseStart_800882 : Nat := 118140960795 + 800882 * 2 ^ 59
def prefixEnd_800882 : Nat := 4983230072969 + 3 ^ 40 * 800882 * 2
def baseEnd_800882 : Nat := 411237413534240779191817

theorem tailTrace_800882 : CollatzResearch.WordTrace tailWord_800882 prefixEnd_800882 411237413534240779191817 := by
  unfold tailWord_800882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302641571137192150279225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19473710856365845734077933 7302641571137192150279225)
  ·
    refine ⟨5476981178352894112709419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7302641571137192150279225 5476981178352894112709419)
    ·
      refine ⟨8215471767529341169064129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5476981178352894112709419 8215471767529341169064129)
      ·
        refine ⟨6161603825647005876798097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8215471767529341169064129 6161603825647005876798097)
        ·
          refine ⟨4621202869235254407598573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161603825647005876798097 4621202869235254407598573)
          ·
            refine ⟨1732951075963220402849465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4621202869235254407598573 1732951075963220402849465)
            ·
              refine ⟨1299713306972415302137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732951075963220402849465 1299713306972415302137099)
              ·
                refine ⟨1949569960458622953205649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299713306972415302137099 1949569960458622953205649)
                ·
                  refine ⟨1462177470343967214904237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1949569960458622953205649 1462177470343967214904237)
                  ·
                    refine ⟨548316551378987705589089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462177470343967214904237 548316551378987705589089)
                    ·
                      refine ⟨411237413534240779191817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548316551378987705589089 411237413534240779191817)
                      ·
                        rfl

theorem cell23_800882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_800882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800882 prefixEnd_800882 := by exact prefixLift 800882
  have htrace : WordTrace (prefixWord ++ tailWord_800882) baseStart_800882 baseEnd_800882 := by
    simpa [prefixWord, tailWord_800882, baseEnd_800882] using wordTrace_append hprefix tailTrace_800882
  have hstable : (prefixWord ++ tailWord_800882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800882).length < 2 ^ (prefixWord ++ tailWord_800882).sum := by decide
  have hdescent : baseEnd_800882 < baseStart_800882 := by decide
  rcases family_descends (prefixWord ++ tailWord_800882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800901 : List Nat := [1, 3, 1, 1, 5, 12]
def baseStart_800901 : Nat := 118140960795 + 800901 * 2 ^ 59
def prefixEnd_800901 : Nat := 4983230072969 + 3 ^ 40 * 800901 * 2
def baseEnd_800901 : Nat := 1692375183813482324503

theorem tailTrace_800901 : CollatzResearch.WordTrace tailWord_800901 prefixEnd_800901 1692375183813482324503 := by
  unfold tailWord_800901
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211259271479934846058557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474172847653289897372371 29211259271479934846058557)
  ·
    refine ⟨10954222226804975567271959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29211259271479934846058557 10954222226804975567271959)
    ·
      refine ⟨16431333340207463350907939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10954222226804975567271959 16431333340207463350907939)
      ·
        refine ⟨24647000010311195026361909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16431333340207463350907939 24647000010311195026361909)
        ·
          refine ⟨2310656250966674533721429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24647000010311195026361909 2310656250966674533721429)
          ·
            refine ⟨1692375183813482324503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 2310656250966674533721429 1692375183813482324503)
            ·
              rfl

theorem cell23_800901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 12].length) (baseStart_800901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800901 prefixEnd_800901 := by exact prefixLift 800901
  have htrace : WordTrace (prefixWord ++ tailWord_800901) baseStart_800901 baseEnd_800901 := by
    simpa [prefixWord, tailWord_800901, baseEnd_800901] using wordTrace_append hprefix tailTrace_800901
  have hstable : (prefixWord ++ tailWord_800901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800901).length < 2 ^ (prefixWord ++ tailWord_800901).sum := by decide
  have hdescent : baseEnd_800901 < baseStart_800901 := by decide
  rcases family_descends (prefixWord ++ tailWord_800901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800905 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_800905 : Nat := 118140960795 + 800905 * 2 ^ 59
def prefixEnd_800905 : Nat := 4983230072969 + 3 ^ 40 * 800905 * 2
def baseEnd_800905 : Nat := 137083074529764729734737

theorem tailTrace_800905 : CollatzResearch.WordTrace tailWord_800905 prefixEnd_800905 137083074529764729734737 := by
  unfold tailWord_800905
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211405163465443529204169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474270108976962352802779 29211405163465443529204169)
  ·
    refine ⟨21908553872599082646903127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29211405163465443529204169 21908553872599082646903127)
    ·
      refine ⟨32862830808898623970354691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908553872599082646903127 32862830808898623970354691)
      ·
        refine ⟨49294246213347935955532037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32862830808898623970354691 49294246213347935955532037)
        ·
          refine ⟨9242671165002737991662257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49294246213347935955532037 9242671165002737991662257)
          ·
            refine ⟨6932003373752053493746693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9242671165002737991662257 6932003373752053493746693)
            ·
              refine ⟨1299750632578510030077505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6932003373752053493746693 1299750632578510030077505)
              ·
                refine ⟨974812974433882522558129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299750632578510030077505 974812974433882522558129)
                ·
                  refine ⟨731109730825411891918597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 974812974433882522558129 731109730825411891918597)
                  ·
                    refine ⟨137083074529764729734737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731109730825411891918597 137083074529764729734737)
                    ·
                      rfl

theorem cell23_800905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_800905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800905 prefixEnd_800905 := by exact prefixLift 800905
  have htrace : WordTrace (prefixWord ++ tailWord_800905) baseStart_800905 baseEnd_800905 := by
    simpa [prefixWord, tailWord_800905, baseEnd_800905] using wordTrace_append hprefix tailTrace_800905
  have hstable : (prefixWord ++ tailWord_800905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800905).length < 2 ^ (prefixWord ++ tailWord_800905).sum := by decide
  have hdescent : baseEnd_800905 < baseStart_800905 := by decide
  rcases family_descends (prefixWord ++ tailWord_800905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800906 : List Nat := [3, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3]
def baseStart_800906 : Nat := 118140960795 + 800906 * 2 ^ 59
def prefixEnd_800906 : Nat := 4983230072969 + 3 ^ 40 * 800906 * 2
def baseEnd_800906 : Nat := 411249737069948685291707

theorem tailTrace_800906 : CollatzResearch.WordTrace tailWord_800906 prefixEnd_800906 411249737069948685291707 := by
  unfold tailWord_800906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7302860409115455174997643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19474294424307880466660381 7302860409115455174997643)
  ·
    refine ⟨10954290613673182762496465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7302860409115455174997643 10954290613673182762496465)
    ·
      refine ⟨8215717960254887071872349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10954290613673182762496465 8215717960254887071872349)
      ·
        refine ⟨3080894235095582651952131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8215717960254887071872349 3080894235095582651952131)
        ·
          refine ⟨4621341352643373977928197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080894235095582651952131 4621341352643373977928197)
          ·
            refine ⟨866501503620632620861537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4621341352643373977928197 866501503620632620861537)
            ·
              refine ⟨649876127715474465646153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866501503620632620861537 649876127715474465646153)
              ·
                refine ⟨487407095786605849234615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 649876127715474465646153 487407095786605849234615)
                ·
                  refine ⟨731110643679908773851923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487407095786605849234615 731110643679908773851923)
                  ·
                    refine ⟨1096665965519863160777885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 731110643679908773851923 1096665965519863160777885)
                    ·
                      refine ⟨411249737069948685291707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1096665965519863160777885 411249737069948685291707)
                      ·
                        rfl

theorem cell23_800906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_800906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800906 prefixEnd_800906 := by exact prefixLift 800906
  have htrace : WordTrace (prefixWord ++ tailWord_800906) baseStart_800906 baseEnd_800906 := by
    simpa [prefixWord, tailWord_800906, baseEnd_800906] using wordTrace_append hprefix tailTrace_800906
  have hstable : (prefixWord ++ tailWord_800906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800906).length < 2 ^ (prefixWord ++ tailWord_800906).sum := by decide
  have hdescent : baseEnd_800906 < baseStart_800906 := by decide
  rcases family_descends (prefixWord ++ tailWord_800906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800921 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_800921 : Nat := 118140960795 + 800921 * 2 ^ 59
def prefixEnd_800921 : Nat := 4983230072969 + 3 ^ 40 * 800921 * 2
def baseEnd_800921 : Nat := 411257439279766126604137

theorem tailTrace_800921 : CollatzResearch.WordTrace tailWord_800921 prefixEnd_800921 411257439279766126604137 := by
  unfold tailWord_800921
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211988731407478261786617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474659154271652174524411 29211988731407478261786617)
  ·
    refine ⟨21908991548555608696339963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29211988731407478261786617 21908991548555608696339963)
    ·
      refine ⟨32863487322833413044509945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21908991548555608696339963 32863487322833413044509945)
      ·
        refine ⟨24647615492125059783382459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32863487322833413044509945 24647615492125059783382459)
        ·
          refine ⟨36971423238187589675073689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24647615492125059783382459 36971423238187589675073689)
          ·
            refine ⟨27728567428640692256305267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36971423238187589675073689 27728567428640692256305267)
            ·
              refine ⟨41592851142961038384457901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27728567428640692256305267 41592851142961038384457901)
              ·
                refine ⟨15597319178610389394171713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41592851142961038384457901 15597319178610389394171713)
                ·
                  refine ⟨11697989383957792045628785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15597319178610389394171713 11697989383957792045628785)
                  ·
                    refine ⟨8773492037968344034221589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11697989383957792045628785 8773492037968344034221589)
                    ·
                      refine ⟨411257439279766126604137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8773492037968344034221589 411257439279766126604137)
                      ·
                        rfl

theorem cell23_800921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_800921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800921 prefixEnd_800921 := by exact prefixLift 800921
  have htrace : WordTrace (prefixWord ++ tailWord_800921) baseStart_800921 baseEnd_800921 := by
    simpa [prefixWord, tailWord_800921, baseEnd_800921] using wordTrace_append hprefix tailTrace_800921
  have hstable : (prefixWord ++ tailWord_800921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800921).length < 2 ^ (prefixWord ++ tailWord_800921).sum := by decide
  have hdescent : baseEnd_800921 < baseStart_800921 := by decide
  rcases family_descends (prefixWord ++ tailWord_800921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800925 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 4]
def baseStart_800925 : Nat := 118140960795 + 800925 * 2 ^ 59
def prefixEnd_800925 : Nat := 4983230072969 + 3 ^ 40 * 800925 * 2
def baseEnd_800925 : Nat := 411259493202384110954119

theorem tailTrace_800925 : CollatzResearch.WordTrace tailWord_800925 prefixEnd_800925 411259493202384110954119 := by
  unfold tailWord_800925
  simp only [CollatzResearch.WordTrace]
  refine ⟨29212134623392986944932229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19474756415595324629954819 29212134623392986944932229)
  ·
    refine ⟨5477275241886185052174793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29212134623392986944932229 5477275241886185052174793)
    ·
      refine ⟨4107956431414638789131095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5477275241886185052174793 4107956431414638789131095)
      ·
        refine ⟨6161934647121958183696643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107956431414638789131095 6161934647121958183696643)
        ·
          refine ⟨9242901970682937275544965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6161934647121958183696643 9242901970682937275544965)
          ·
            refine ⟨1733044119503050739164681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9242901970682937275544965 1733044119503050739164681)
            ·
              refine ⟨1299783089627288054373511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733044119503050739164681 1299783089627288054373511)
              ·
                refine ⟨1949674634440932081560267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299783089627288054373511 1949674634440932081560267)
                ·
                  refine ⟨2924511951661398122340401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949674634440932081560267 2924511951661398122340401)
                  ·
                    refine ⟨2193383963746048591755301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2924511951661398122340401 2193383963746048591755301)
                    ·
                      refine ⟨411259493202384110954119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2193383963746048591755301 411259493202384110954119)
                      ·
                        rfl

theorem cell23_800925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_800925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800925 prefixEnd_800925 := by exact prefixLift 800925
  have htrace : WordTrace (prefixWord ++ tailWord_800925) baseStart_800925 baseEnd_800925 := by
    simpa [prefixWord, tailWord_800925, baseEnd_800925] using wordTrace_append hprefix tailTrace_800925
  have hstable : (prefixWord ++ tailWord_800925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800925).length < 2 ^ (prefixWord ++ tailWord_800925).sum := by decide
  have hdescent : baseEnd_800925 < baseStart_800925 := by decide
  rcases family_descends (prefixWord ++ tailWord_800925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800949 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 3]
def baseStart_800949 : Nat := 118140960795 + 800949 * 2 ^ 59
def prefixEnd_800949 : Nat := 4983230072969 + 3 ^ 40 * 800949 * 2
def baseEnd_800949 : Nat := 411271816738092017054009

theorem tailTrace_800949 : CollatzResearch.WordTrace tailWord_800949 prefixEnd_800949 411271816738092017054009 := by
  unfold tailWord_800949
  simp only [CollatzResearch.WordTrace]
  refine ⟨29213009975306039043805901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19475339983537359362537267 29213009975306039043805901)
  ·
    refine ⟨10954878740739764641427213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29213009975306039043805901 10954878740739764641427213)
    ·
      refine ⟨4108079527777411740535205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10954878740739764641427213 4108079527777411740535205)
      ·
        refine ⟨770264911458264701350351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4108079527777411740535205 770264911458264701350351)
        ·
          refine ⟨1155397367187397052025527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770264911458264701350351 1155397367187397052025527)
          ·
            refine ⟨1733096050781095578038291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155397367187397052025527 1733096050781095578038291)
            ·
              refine ⟨2599644076171643367057437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733096050781095578038291 2599644076171643367057437)
              ·
                refine ⟨974866528564366262646539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2599644076171643367057437 974866528564366262646539)
                ·
                  refine ⟨1462299792846549393969809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974866528564366262646539 1462299792846549393969809)
                  ·
                    refine ⟨1096724844634912045477357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462299792846549393969809 1096724844634912045477357)
                    ·
                      refine ⟨411271816738092017054009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1096724844634912045477357 411271816738092017054009)
                      ·
                        rfl

theorem cell23_800949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_800949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800949 prefixEnd_800949 := by exact prefixLift 800949
  have htrace : WordTrace (prefixWord ++ tailWord_800949) baseStart_800949 baseEnd_800949 := by
    simpa [prefixWord, tailWord_800949, baseEnd_800949] using wordTrace_append hprefix tailTrace_800949
  have hstable : (prefixWord ++ tailWord_800949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800949).length < 2 ^ (prefixWord ++ tailWord_800949).sum := by decide
  have hdescent : baseEnd_800949 < baseStart_800949 := by decide
  rcases family_descends (prefixWord ++ tailWord_800949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_800989 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_800989 : Nat := 118140960795 + 800989 * 2 ^ 59
def prefixEnd_800989 : Nat := 4983230072969 + 3 ^ 40 * 800989 * 2
def baseEnd_800989 : Nat := 411292355964271860553825

theorem tailTrace_800989 : CollatzResearch.WordTrace tailWord_800989 prefixEnd_800989 411292355964271860553825 := by
  unfold tailWord_800989
  simp only [CollatzResearch.WordTrace]
  refine ⟨29214468895161125875262021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19476312596774083916841347 29214468895161125875262021)
  ·
    refine ⟨5477712917842711101611629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29214468895161125875262021 5477712917842711101611629)
    ·
      refine ⟨2054142344191016663104361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5477712917842711101611629 2054142344191016663104361)
      ·
        refine ⟨1540606758143262497328271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2054142344191016663104361 1540606758143262497328271)
        ·
          refine ⟨2310910137214893745992407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1540606758143262497328271 2310910137214893745992407)
          ·
            refine ⟨3466365205822340618988611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310910137214893745992407 3466365205822340618988611)
            ·
              refine ⟨5199547808733510928482917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466365205822340618988611 5199547808733510928482917)
              ·
                refine ⟨974915214137533299090547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5199547808733510928482917 974915214137533299090547)
                ·
                  refine ⟨1462372821206299948635821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974915214137533299090547 1462372821206299948635821)
                  ·
                    refine ⟨548389807952362480738433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462372821206299948635821 548389807952362480738433)
                    ·
                      refine ⟨411292355964271860553825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548389807952362480738433 411292355964271860553825)
                      ·
                        rfl

theorem cell23_800989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_800989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_800989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_800989 prefixEnd_800989 := by exact prefixLift 800989
  have htrace : WordTrace (prefixWord ++ tailWord_800989) baseStart_800989 baseEnd_800989 := by
    simpa [prefixWord, tailWord_800989, baseEnd_800989] using wordTrace_append hprefix tailTrace_800989
  have hstable : (prefixWord ++ tailWord_800989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_800989).length < 2 ^ (prefixWord ++ tailWord_800989).sum := by decide
  have hdescent : baseEnd_800989 < baseStart_800989 := by decide
  rcases family_descends (prefixWord ++ tailWord_800989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801002 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2]
def baseStart_801002 : Nat := 118140960795 + 801002 * 2 ^ 59
def prefixEnd_801002 : Nat := 4983230072969 + 3 ^ 40 * 801002 * 2
def baseEnd_801002 : Nat := 411299031212780309691265

theorem tailTrace_801002 : CollatzResearch.WordTrace tailWord_801002 prefixEnd_801002 411299031212780309691265 := by
  unfold tailWord_801002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303735761028507273871315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19476628696076019396990173 7303735761028507273871315)
  ·
    refine ⟨10955603641542760910806973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7303735761028507273871315 10955603641542760910806973)
    ·
      refine ⟨4108351365578535341552615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10955603641542760910806973 4108351365578535341552615)
      ·
        refine ⟨6162527048367803012328923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108351365578535341552615 6162527048367803012328923)
        ·
          refine ⟨9243790572551704518493385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162527048367803012328923 9243790572551704518493385)
          ·
            refine ⟨6932842929413778388870039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9243790572551704518493385 6932842929413778388870039)
            ·
              refine ⟨10399264394120667583305059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932842929413778388870039 10399264394120667583305059)
              ·
                refine ⟨15598896591181001374957589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399264394120667583305059 15598896591181001374957589)
                ·
                  refine ⟨731198277711609439451137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 15598896591181001374957589 731198277711609439451137)
                  ·
                    refine ⟨548398708283707079588353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 731198277711609439451137 548398708283707079588353)
                    ·
                      refine ⟨411299031212780309691265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548398708283707079588353 411299031212780309691265)
                      ·
                        rfl

theorem cell23_801002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_801002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801002 prefixEnd_801002 := by exact prefixLift 801002
  have htrace : WordTrace (prefixWord ++ tailWord_801002) baseStart_801002 baseEnd_801002 := by
    simpa [prefixWord, tailWord_801002, baseEnd_801002] using wordTrace_append hprefix tailTrace_801002
  have hstable : (prefixWord ++ tailWord_801002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801002).length < 2 ^ (prefixWord ++ tailWord_801002).sum := by decide
  have hdescent : baseEnd_801002 < baseStart_801002 := by decide
  rcases family_descends (prefixWord ++ tailWord_801002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801048 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_801048 : Nat := 118140960795 + 801048 * 2 ^ 59
def prefixEnd_801048 : Nat := 4983230072969 + 3 ^ 40 * 801048 * 2
def baseEnd_801048 : Nat := 411322651322887129716053

theorem tailTrace_801048 : CollatzResearch.WordTrace tailWord_801048 prefixEnd_801048 411322651322887129716053 := by
  unfold tailWord_801048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608310400973689475829899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19477747201298252634439865 14608310400973689475829899)
  ·
    refine ⟨21912465601460534213744849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14608310400973689475829899 21912465601460534213744849)
    ·
      refine ⟨16434349201095400660308637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21912465601460534213744849 16434349201095400660308637)
      ·
        refine ⟨6162880950410775247615739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16434349201095400660308637 6162880950410775247615739)
        ·
          refine ⟨9244321425616162871423609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162880950410775247615739 9244321425616162871423609)
          ·
            refine ⟨6933241069212122153567707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244321425616162871423609 6933241069212122153567707)
            ·
              refine ⟨10399861603818183230351561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933241069212122153567707 10399861603818183230351561)
              ·
                refine ⟨7799896202863637422763671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10399861603818183230351561 7799896202863637422763671)
                ·
                  refine ⟨11699844304295456134145507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7799896202863637422763671 11699844304295456134145507)
                  ·
                    refine ⟨17549766456443184201218261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11699844304295456134145507 17549766456443184201218261)
                    ·
                      refine ⟨411322651322887129716053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17549766456443184201218261 411322651322887129716053)
                      ·
                        rfl

theorem cell23_801048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_801048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801048 prefixEnd_801048 := by exact prefixLift 801048
  have htrace : WordTrace (prefixWord ++ tailWord_801048) baseStart_801048 baseEnd_801048 := by
    simpa [prefixWord, tailWord_801048, baseEnd_801048] using wordTrace_append hprefix tailTrace_801048
  have hstable : (prefixWord ++ tailWord_801048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801048).length < 2 ^ (prefixWord ++ tailWord_801048).sum := by decide
  have hdescent : baseEnd_801048 < baseStart_801048 := by decide
  rcases family_descends (prefixWord ++ tailWord_801048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801055 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 2, 5]
def baseStart_801055 : Nat := 118140960795 + 801055 * 2 ^ 59
def prefixEnd_801055 : Nat := 4983230072969 + 3 ^ 40 * 801055 * 2
def baseEnd_801055 : Nat := 137108748562489534109507

theorem tailTrace_801055 : CollatzResearch.WordTrace tailWord_801055 prefixEnd_801055 137108748562489534109507 := by
  unfold tailWord_801055
  simp only [CollatzResearch.WordTrace]
  refine ⟨29216876112922019147164619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19477917408614679431443079 29216876112922019147164619)
  ·
    refine ⟨43825314169383028720746929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29216876112922019147164619 43825314169383028720746929)
    ·
      refine ⟨32868985627037271540560197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43825314169383028720746929 32868985627037271540560197)
      ·
        refine ⟨6162934805069488413855037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32868985627037271540560197 6162934805069488413855037)
        ·
          refine ⟨2311100551901058155195639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6162934805069488413855037 2311100551901058155195639)
          ·
            refine ⟨3466650827851587232793459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311100551901058155195639 3466650827851587232793459)
            ·
              refine ⟨5199976241777380849190189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3466650827851587232793459 5199976241777380849190189)
              ·
                refine ⟨1949991090666517818446321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199976241777380849190189 1949991090666517818446321)
                ·
                  refine ⟨1462493317999888363834741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1949991090666517818446321 1462493317999888363834741)
                  ·
                    refine ⟨137108748562489534109507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1462493317999888363834741 137108748562489534109507)
                    ·
                      rfl

theorem cell23_801055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_801055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801055 prefixEnd_801055 := by exact prefixLift 801055
  have htrace : WordTrace (prefixWord ++ tailWord_801055) baseStart_801055 baseEnd_801055 := by
    simpa [prefixWord, tailWord_801055, baseEnd_801055] using wordTrace_append hprefix tailTrace_801055
  have hstable : (prefixWord ++ tailWord_801055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801055).length < 2 ^ (prefixWord ++ tailWord_801055).sum := by decide
  have hdescent : baseEnd_801055 < baseStart_801055 := by decide
  rcases family_descends (prefixWord ++ tailWord_801055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801075 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4]
def baseStart_801075 : Nat := 118140960795 + 801075 * 2 ^ 59
def prefixEnd_801075 : Nat := 4983230072969 + 3 ^ 40 * 801075 * 2
def baseEnd_801075 : Nat := 411336515300558524078429

theorem tailTrace_801075 : CollatzResearch.WordTrace tailWord_801075 prefixEnd_801075 411336515300558524078429 := by
  unfold tailWord_801075
  simp only [CollatzResearch.WordTrace]
  refine ⟨29217605572849562562892679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19478403715233041708595119 29217605572849562562892679)
  ·
    refine ⟨43826408359274343844339019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29217605572849562562892679 43826408359274343844339019)
    ·
      refine ⟨65739612538911515766508529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43826408359274343844339019 65739612538911515766508529)
      ·
        refine ⟨49304709404183636824881397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65739612538911515766508529 49304709404183636824881397)
        ·
          refine ⟨4622316506642215952332631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49304709404183636824881397 4622316506642215952332631)
          ·
            refine ⟨6933474759963323928498947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622316506642215952332631 6933474759963323928498947)
            ·
              refine ⟨10400212139944985892748421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6933474759963323928498947 10400212139944985892748421)
              ·
                refine ⟨1950039776239684854890329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10400212139944985892748421 1950039776239684854890329)
                ·
                  refine ⟨1462529832179763641167747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950039776239684854890329 1462529832179763641167747)
                  ·
                    refine ⟨2193794748269645461751621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1462529832179763641167747 2193794748269645461751621)
                    ·
                      refine ⟨411336515300558524078429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2193794748269645461751621 411336515300558524078429)
                      ·
                        rfl

theorem cell23_801075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_801075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801075 prefixEnd_801075 := by exact prefixLift 801075
  have htrace : WordTrace (prefixWord ++ tailWord_801075) baseStart_801075 baseEnd_801075 := by
    simpa [prefixWord, tailWord_801075, baseEnd_801075] using wordTrace_append hprefix tailTrace_801075
  have hstable : (prefixWord ++ tailWord_801075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801075).length < 2 ^ (prefixWord ++ tailWord_801075).sum := by decide
  have hdescent : baseEnd_801075 < baseStart_801075 := by decide
  rcases family_descends (prefixWord ++ tailWord_801075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801076 : List Nat := [2, 5, 1, 1, 1, 4, 2, 2, 5]
def baseStart_801076 : Nat := 118140960795 + 801076 * 2 ^ 59
def prefixEnd_801076 : Nat := 4983230072969 + 3 ^ 40 * 801076 * 2
def baseEnd_801076 : Nat := 45704114309023668907325

theorem tailTrace_801076 : CollatzResearch.WordTrace tailWord_801076 prefixEnd_801076 45704114309023668907325 := by
  unfold tailWord_801076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14608821022922969866839541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19478428030563959822452721 14608821022922969866839541)
  ·
    refine ⟨1369576970899028425016207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14608821022922969866839541 1369576970899028425016207)
    ·
      refine ⟨2054365456348542637524311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1369576970899028425016207 2054365456348542637524311)
      ·
        refine ⟨3081548184522813956286467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2054365456348542637524311 3081548184522813956286467)
        ·
          refine ⟨4622322276784220934429701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081548184522813956286467 4622322276784220934429701)
          ·
            refine ⟨866685426897041425205569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4622322276784220934429701 866685426897041425205569)
            ·
              refine ⟨650014070172781068904177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866685426897041425205569 650014070172781068904177)
              ·
                refine ⟨487510552629585801678133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650014070172781068904177 487510552629585801678133)
                ·
                  refine ⟨45704114309023668907325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 487510552629585801678133 45704114309023668907325)
                  ·
                    rfl

theorem cell23_801076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_801076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801076 prefixEnd_801076 := by exact prefixLift 801076
  have htrace : WordTrace (prefixWord ++ tailWord_801076) baseStart_801076 baseEnd_801076 := by
    simpa [prefixWord, tailWord_801076, baseEnd_801076] using wordTrace_append hprefix tailTrace_801076
  have hstable : (prefixWord ++ tailWord_801076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801076).length < 2 ^ (prefixWord ++ tailWord_801076).sum := by decide
  have hdescent : baseEnd_801076 < baseStart_801076 := by decide
  rcases family_descends (prefixWord ++ tailWord_801076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801088 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_801088 : Nat := 118140960795 + 801088 * 2 ^ 59
def prefixEnd_801088 : Nat := 4983230072969 + 3 ^ 40 * 801088 * 2
def baseEnd_801088 : Nat := 411343190549066973215869

theorem tailTrace_801088 : CollatzResearch.WordTrace tailWord_801088 prefixEnd_801088 411343190549066973215869 := by
  unfold tailWord_801088
  simp only [CollatzResearch.WordTrace]
  refine ⟨14609039860901232891557959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19478719814534977188743945 14609039860901232891557959)
  ·
    refine ⟨21913559791351849337336939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14609039860901232891557959 21913559791351849337336939)
    ·
      refine ⟨32870339687027774006005409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21913559791351849337336939 32870339687027774006005409)
      ·
        refine ⟨24652754765270830504504057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32870339687027774006005409 24652754765270830504504057)
        ·
          refine ⟨18489566073953122878378043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24652754765270830504504057 18489566073953122878378043)
          ·
            refine ⟨27734349110929684317567065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489566073953122878378043 27734349110929684317567065)
            ·
              refine ⟨20800761833197263238175299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27734349110929684317567065 20800761833197263238175299)
              ·
                refine ⟨31201142749795894857262949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20800761833197263238175299 31201142749795894857262949)
                ·
                  refine ⟨5850214265586730285736803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31201142749795894857262949 5850214265586730285736803)
                  ·
                    refine ⟨8775321398380095428605205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5850214265586730285736803 8775321398380095428605205)
                    ·
                      refine ⟨411343190549066973215869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8775321398380095428605205 411343190549066973215869)
                      ·
                        rfl

theorem cell23_801088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_801088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801088 prefixEnd_801088 := by exact prefixLift 801088
  have htrace : WordTrace (prefixWord ++ tailWord_801088) baseStart_801088 baseEnd_801088 := by
    simpa [prefixWord, tailWord_801088, baseEnd_801088] using wordTrace_append hprefix tailTrace_801088
  have hstable : (prefixWord ++ tailWord_801088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801088).length < 2 ^ (prefixWord ++ tailWord_801088).sum := by decide
  have hdescent : baseEnd_801088 < baseStart_801088 := by decide
  rcases family_descends (prefixWord ++ tailWord_801088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801095 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_801095 : Nat := 118140960795 + 801095 * 2 ^ 59
def prefixEnd_801095 : Nat := 4983230072969 + 3 ^ 40 * 801095 * 2
def baseEnd_801095 : Nat := 411346784913648445828337

theorem tailTrace_801095 : CollatzResearch.WordTrace tailWord_801095 prefixEnd_801095 411346784913648445828337 := by
  unfold tailWord_801095
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218335032777105978620739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19478890021851403985747159 29218335032777105978620739)
  ·
    refine ⟨43827502549165658967931109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29218335032777105978620739 43827502549165658967931109)
    ·
      refine ⟨8217656727968561056487083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43827502549165658967931109 8217656727968561056487083)
      ·
        refine ⟨12326485091952841584730625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217656727968561056487083 12326485091952841584730625)
        ·
          refine ⟨9244863818964631188547969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12326485091952841584730625 9244863818964631188547969)
          ·
            refine ⟨6933647864223473391410977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9244863818964631188547969 6933647864223473391410977)
            ·
              refine ⟨5200235898167605043558233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6933647864223473391410977 5200235898167605043558233)
              ·
                refine ⟨3900176923625703782668675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200235898167605043558233 3900176923625703782668675)
                ·
                  refine ⟨5850265385438555674003013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900176923625703782668675 5850265385438555674003013)
                  ·
                    refine ⟨1096924759769729188875565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5850265385438555674003013 1096924759769729188875565)
                    ·
                      refine ⟨411346784913648445828337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1096924759769729188875565 411346784913648445828337)
                      ·
                        rfl

theorem cell23_801095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_801095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801095 prefixEnd_801095 := by exact prefixLift 801095
  have htrace : WordTrace (prefixWord ++ tailWord_801095) baseStart_801095 baseEnd_801095 := by
    simpa [prefixWord, tailWord_801095, baseEnd_801095] using wordTrace_append hprefix tailTrace_801095
  have hstable : (prefixWord ++ tailWord_801095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801095).length < 2 ^ (prefixWord ++ tailWord_801095).sum := by decide
  have hdescent : baseEnd_801095 < baseStart_801095 := by decide
  rcases family_descends (prefixWord ++ tailWord_801095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801098 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 12]
def baseStart_801098 : Nat := 118140960795 + 801098 * 2 ^ 59
def prefixEnd_801098 : Nat := 4983230072969 + 3 ^ 40 * 801098 * 2
def baseEnd_801098 : Nat := 45705369483956881565647

theorem tailTrace_801098 : CollatzResearch.WordTrace tailWord_801098 prefixEnd_801098 45705369483956881565647 := by
  unfold tailWord_801098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304611112941559372744987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19478962967844158327319965 7304611112941559372744987)
  ·
    refine ⟨10956916669412339059117481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304611112941559372744987 10956916669412339059117481)
    ·
      refine ⟨8217687502059254294338111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10956916669412339059117481 8217687502059254294338111)
      ·
        refine ⟨12326531253088881441507167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8217687502059254294338111 12326531253088881441507167)
        ·
          refine ⟨18489796879633322162260751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12326531253088881441507167 18489796879633322162260751)
          ·
            refine ⟨27734695319449983243391127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18489796879633322162260751 27734695319449983243391127)
            ·
              refine ⟨41602042979174974865086691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27734695319449983243391127 41602042979174974865086691)
              ·
                refine ⟨62403064468762462297630037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41602042979174974865086691 62403064468762462297630037)
                ·
                  refine ⟨45705369483956881565647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 62403064468762462297630037 45705369483956881565647)
                  ·
                    rfl

theorem cell23_801098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 12].length) (baseStart_801098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801098 prefixEnd_801098 := by exact prefixLift 801098
  have htrace : WordTrace (prefixWord ++ tailWord_801098) baseStart_801098 baseEnd_801098 := by
    simpa [prefixWord, tailWord_801098, baseEnd_801098] using wordTrace_append hprefix tailTrace_801098
  have hstable : (prefixWord ++ tailWord_801098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801098).length < 2 ^ (prefixWord ++ tailWord_801098).sum := by decide
  have hdescent : baseEnd_801098 < baseStart_801098 := by decide
  rcases family_descends (prefixWord ++ tailWord_801098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801109 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 4]
def baseStart_801109 : Nat := 118140960795 + 801109 * 2 ^ 59
def prefixEnd_801109 : Nat := 4983230072969 + 3 ^ 40 * 801109 * 2
def baseEnd_801109 : Nat := 411353973642811391053273

theorem tailTrace_801109 : CollatzResearch.WordTrace tailWord_801109 prefixEnd_801109 411353973642811391053273 := by
  unfold tailWord_801109
  simp only [CollatzResearch.WordTrace]
  refine ⟨29218845654726386369630381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19479230436484257579753587 29218845654726386369630381)
  ·
    refine ⟨10957067120522394888611393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29218845654726386369630381 10957067120522394888611393)
    ·
      refine ⟨8217800340391796166458545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10957067120522394888611393 8217800340391796166458545)
      ·
        refine ⟨6163350255293847124843909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217800340391796166458545 6163350255293847124843909)
        ·
          refine ⟨1155628172867596335908233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6163350255293847124843909 1155628172867596335908233)
          ·
            refine ⟨866721129650697251931175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1155628172867596335908233 866721129650697251931175)
            ·
              refine ⟨1300081694476045877896763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866721129650697251931175 1300081694476045877896763)
              ·
                refine ⟨1950122541714068816845145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300081694476045877896763 1950122541714068816845145)
                ·
                  refine ⟨1462591906285551612633859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950122541714068816845145 1462591906285551612633859)
                  ·
                    refine ⟨2193887859428327418950789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1462591906285551612633859 2193887859428327418950789)
                    ·
                      refine ⟨411353973642811391053273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2193887859428327418950789 411353973642811391053273)
                      ·
                        rfl

theorem cell23_801109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_801109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801109 prefixEnd_801109 := by exact prefixLift 801109
  have htrace : WordTrace (prefixWord ++ tailWord_801109) baseStart_801109 baseEnd_801109 := by
    simpa [prefixWord, tailWord_801109, baseEnd_801109] using wordTrace_append hprefix tailTrace_801109
  have hstable : (prefixWord ++ tailWord_801109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801109).length < 2 ^ (prefixWord ++ tailWord_801109).sum := by decide
  have hdescent : baseEnd_801109 < baseStart_801109 := by decide
  rcases family_descends (prefixWord ++ tailWord_801109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801175 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 6]
def baseStart_801175 : Nat := 118140960795 + 801175 * 2 ^ 59
def prefixEnd_801175 : Nat := 4983230072969 + 3 ^ 40 * 801175 * 2
def baseEnd_801175 : Nat := 137129287788669377609323

theorem tailTrace_801175 : CollatzResearch.WordTrace tailWord_801175 prefixEnd_801175 137129287788669377609323 := by
  unfold tailWord_801175
  simp only [CollatzResearch.WordTrace]
  refine ⟨29221252872487279641532979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19480835248324853094355319 29221252872487279641532979)
  ·
    refine ⟨43831879308730919462299469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29221252872487279641532979 43831879308730919462299469)
    ·
      refine ⟨16436954740774094798362301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43831879308730919462299469 16436954740774094798362301)
      ·
        refine ⟨6163858027790285549385863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16436954740774094798362301 6163858027790285549385863)
        ·
          refine ⟨9245787041685428324078795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163858027790285549385863 9245787041685428324078795)
          ·
            refine ⟨13868680562528142486118193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245787041685428324078795 13868680562528142486118193)
            ·
              refine ⟨10401510421896106864588645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13868680562528142486118193 10401510421896106864588645)
              ·
                refine ⟨1950283204105520037110371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10401510421896106864588645 1950283204105520037110371)
                ·
                  refine ⟨2925424806158280055665557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950283204105520037110371 2925424806158280055665557)
                  ·
                    refine ⟨137129287788669377609323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2925424806158280055665557 137129287788669377609323)
                    ·
                      rfl

theorem cell23_801175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_801175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801175 prefixEnd_801175 := by exact prefixLift 801175
  have htrace : WordTrace (prefixWord ++ tailWord_801175) baseStart_801175 baseEnd_801175 := by
    simpa [prefixWord, tailWord_801175, baseEnd_801175] using wordTrace_append hprefix tailTrace_801175
  have hstable : (prefixWord ++ tailWord_801175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801175).length < 2 ^ (prefixWord ++ tailWord_801175).sum := by decide
  have hdescent : baseEnd_801175 < baseStart_801175 := by decide
  rcases family_descends (prefixWord ++ tailWord_801175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801202 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3]
def baseStart_801202 : Nat := 118140960795 + 801202 * 2 ^ 59
def prefixEnd_801202 : Nat := 4983230072969 + 3 ^ 40 * 801202 * 2
def baseEnd_801202 : Nat := 411401727343679527190345

theorem tailTrace_801202 : CollatzResearch.WordTrace tailWord_801202 prefixEnd_801202 411401727343679527190345 := by
  unfold tailWord_801202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305559410847365813191465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19481491762259642168510573 7305559410847365813191465)
  ·
    refine ⟨5479169558135524359893599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7305559410847365813191465 5479169558135524359893599)
    ·
      refine ⟨8218754337203286539840399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479169558135524359893599 8218754337203286539840399)
      ·
        refine ⟨12328131505804929809760599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8218754337203286539840399 12328131505804929809760599)
        ·
          refine ⟨18492197258707394714640899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12328131505804929809760599 18492197258707394714640899)
          ·
            refine ⟨27738295888061092071961349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492197258707394714640899 27738295888061092071961349)
            ·
              refine ⟨5200930479011454763492753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27738295888061092071961349 5200930479011454763492753)
              ·
                refine ⟨3900697859258591072619565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5200930479011454763492753 3900697859258591072619565)
                ·
                  refine ⟨1462761697221971652232337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3900697859258591072619565 1462761697221971652232337)
                  ·
                    refine ⟨1097071272916478739174253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1462761697221971652232337 1097071272916478739174253)
                    ·
                      refine ⟨411401727343679527190345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097071272916478739174253 411401727343679527190345)
                      ·
                        rfl

theorem cell23_801202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_801202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801202 prefixEnd_801202 := by exact prefixLift 801202
  have htrace : WordTrace (prefixWord ++ tailWord_801202) baseStart_801202 baseEnd_801202 := by
    simpa [prefixWord, tailWord_801202, baseEnd_801202] using wordTrace_append hprefix tailTrace_801202
  have hstable : (prefixWord ++ tailWord_801202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801202).length < 2 ^ (prefixWord ++ tailWord_801202).sum := by decide
  have hdescent : baseEnd_801202 < baseStart_801202 := by decide
  rcases family_descends (prefixWord ++ tailWord_801202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801209 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_801209 : Nat := 118140960795 + 801209 * 2 ^ 59
def prefixEnd_801209 : Nat := 4983230072969 + 3 ^ 40 * 801209 * 2
def baseEnd_801209 : Nat := 137135107236086999934271

theorem tailTrace_801209 : CollatzResearch.WordTrace tailWord_801209 prefixEnd_801209 137135107236086999934271 := by
  unfold tailWord_801209
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222492954364103448270681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19481661969576068965513787 29222492954364103448270681)
  ·
    refine ⟨21916869715773077586203011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29222492954364103448270681 21916869715773077586203011)
    ·
      refine ⟨32875304573659616379304517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21916869715773077586203011 32875304573659616379304517)
      ·
        refine ⟨6164119607561178071119597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32875304573659616379304517 6164119607561178071119597)
        ·
          refine ⟨2311544852835441776669849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6164119607561178071119597 2311544852835441776669849)
          ·
            refine ⟨1733658639626581332502387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2311544852835441776669849 1733658639626581332502387)
            ·
              refine ⟨2600487959439871998753581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733658639626581332502387 2600487959439871998753581)
              ·
                refine ⟨975182984789951999532593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600487959439871998753581 975182984789951999532593)
                ·
                  refine ⟨731387238592463999649445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975182984789951999532593 731387238592463999649445)
                  ·
                    refine ⟨137135107236086999934271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731387238592463999649445 137135107236086999934271)
                    ·
                      rfl

theorem cell23_801209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_801209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801209 prefixEnd_801209 := by exact prefixLift 801209
  have htrace : WordTrace (prefixWord ++ tailWord_801209) baseStart_801209 baseEnd_801209 := by
    simpa [prefixWord, tailWord_801209, baseEnd_801209] using wordTrace_append hprefix tailTrace_801209
  have hstable : (prefixWord ++ tailWord_801209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801209).length < 2 ^ (prefixWord ++ tailWord_801209).sum := by decide
  have hdescent : baseEnd_801209 < baseStart_801209 := by decide
  rcases family_descends (prefixWord ++ tailWord_801209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801212 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_801212 : Nat := 118140960795 + 801212 * 2 ^ 59
def prefixEnd_801212 : Nat := 4983230072969 + 3 ^ 40 * 801212 * 2
def baseEnd_801212 : Nat := 411406862150224488065299

theorem tailTrace_801212 : CollatzResearch.WordTrace tailWord_801212 prefixEnd_801212 411406862150224488065299 := by
  unfold tailWord_801212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611301186676617480314945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19481734915568823307086593 14611301186676617480314945)
  ·
    refine ⟨10958475890007463110236209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14611301186676617480314945 10958475890007463110236209)
    ·
      refine ⟨8218856917505597332677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10958475890007463110236209 8218856917505597332677157)
      ·
        refine ⟨1541035672032299499876967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8218856917505597332677157 1541035672032299499876967)
        ·
          refine ⟨2311553508048449249815451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541035672032299499876967 2311553508048449249815451)
          ·
            refine ⟨3467330262072673874723177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311553508048449249815451 3467330262072673874723177)
            ·
              refine ⟨2600497696554505406042383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467330262072673874723177 2600497696554505406042383)
              ·
                refine ⟨3900746544831758109063575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600497696554505406042383 3900746544831758109063575)
                ·
                  refine ⟨5851119817247637163595363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900746544831758109063575 5851119817247637163595363)
                  ·
                    refine ⟨8776679725871455745393045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5851119817247637163595363 8776679725871455745393045)
                    ·
                      refine ⟨411406862150224488065299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8776679725871455745393045 411406862150224488065299)
                      ·
                        rfl

theorem cell23_801212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_801212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801212 prefixEnd_801212 := by exact prefixLift 801212
  have htrace : WordTrace (prefixWord ++ tailWord_801212) baseStart_801212 baseEnd_801212 := by
    simpa [prefixWord, tailWord_801212, baseEnd_801212] using wordTrace_append hprefix tailTrace_801212
  have hstable : (prefixWord ++ tailWord_801212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801212).length < 2 ^ (prefixWord ++ tailWord_801212).sum := by decide
  have hdescent : baseEnd_801212 < baseStart_801212 := by decide
  rcases family_descends (prefixWord ++ tailWord_801212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801266 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 3, 3]
def baseStart_801266 : Nat := 118140960795 + 801266 * 2 ^ 59
def prefixEnd_801266 : Nat := 4983230072969 + 3 ^ 40 * 801266 * 2
def baseEnd_801266 : Nat := 411434590105567276790051

theorem tailTrace_801266 : CollatzResearch.WordTrace tailWord_801266 prefixEnd_801266 411434590105567276790051 := by
  unfold tailWord_801266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306142978789400545773913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19483047943438401455397101 7306142978789400545773913)
  ·
    refine ⟨5479607234092050409330435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306142978789400545773913 5479607234092050409330435)
    ·
      refine ⟨8219410851138075613995653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479607234092050409330435 8219410851138075613995653)
      ·
        refine ⟨1541139534588389177624185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8219410851138075613995653 1541139534588389177624185)
        ·
          refine ⟨1155854650941291883218139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1541139534588389177624185 1155854650941291883218139)
          ·
            refine ⟨1733781976411937824827209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155854650941291883218139 1733781976411937824827209)
            ·
              refine ⟨1300336482308953368620407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733781976411937824827209 1300336482308953368620407)
              ·
                refine ⟨1950504723463430052930611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300336482308953368620407 1950504723463430052930611)
                ·
                  refine ⟨2925757085195145079395917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950504723463430052930611 2925757085195145079395917)
                  ·
                    refine ⟨1097158906948179404773469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2925757085195145079395917 1097158906948179404773469)
                    ·
                      refine ⟨411434590105567276790051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097158906948179404773469 411434590105567276790051)
                      ·
                        rfl

theorem cell23_801266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_801266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801266 prefixEnd_801266 := by exact prefixLift 801266
  have htrace : WordTrace (prefixWord ++ tailWord_801266) baseStart_801266 baseEnd_801266 := by
    simpa [prefixWord, tailWord_801266, baseEnd_801266] using wordTrace_append hprefix tailTrace_801266
  have hstable : (prefixWord ++ tailWord_801266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801266).length < 2 ^ (prefixWord ++ tailWord_801266).sum := by decide
  have hdescent : baseEnd_801266 < baseStart_801266 := by decide
  rcases family_descends (prefixWord ++ tailWord_801266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801300 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_801300 : Nat := 118140960795 + 801300 * 2 ^ 59
def prefixEnd_801300 : Nat := 4983230072969 + 3 ^ 40 * 801300 * 2
def baseEnd_801300 : Nat := 411452048447820143764895

theorem tailTrace_801300 : CollatzResearch.WordTrace tailWord_801300 prefixEnd_801300 411452048447820143764895 := by
  unfold tailWord_801300
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612905998517212994916677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19483874664689617326555569 14612905998517212994916677)
  ·
    refine ⟨2739919874721977436546877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14612905998517212994916677 2739919874721977436546877)
    ·
      refine ⟨1027469953020741538705079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2739919874721977436546877 1027469953020741538705079)
      ·
        refine ⟨1541204929531112308057619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027469953020741538705079 1541204929531112308057619)
        ·
          refine ⟨2311807394296668462086429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541204929531112308057619 2311807394296668462086429)
          ·
            refine ⟨866927772861250673282411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2311807394296668462086429 866927772861250673282411)
            ·
              refine ⟨1300391659291876009923617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 866927772861250673282411 1300391659291876009923617)
              ·
                refine ⟨975293744468907007442713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300391659291876009923617 975293744468907007442713)
                ·
                  refine ⟨731470308351680255582035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975293744468907007442713 731470308351680255582035)
                  ·
                    refine ⟨1097205462527520383373053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 731470308351680255582035 1097205462527520383373053)
                    ·
                      refine ⟨411452048447820143764895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097205462527520383373053 411452048447820143764895)
                      ·
                        rfl

theorem cell23_801300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_801300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801300 prefixEnd_801300 := by exact prefixLift 801300
  have htrace : WordTrace (prefixWord ++ tailWord_801300) baseStart_801300 baseEnd_801300 := by
    simpa [prefixWord, tailWord_801300, baseEnd_801300] using wordTrace_append hprefix tailTrace_801300
  have hstable : (prefixWord ++ tailWord_801300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801300).length < 2 ^ (prefixWord ++ tailWord_801300).sum := by decide
  have hdescent : baseEnd_801300 < baseStart_801300 := by decide
  rcases family_descends (prefixWord ++ tailWord_801300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801305 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_801305 : Nat := 118140960795 + 801305 * 2 ^ 59
def prefixEnd_801305 : Nat := 4983230072969 + 3 ^ 40 * 801305 * 2
def baseEnd_801305 : Nat := 411454615851092624202371

theorem tailTrace_801305 : CollatzResearch.WordTrace tailWord_801305 prefixEnd_801305 411454615851092624202371 := by
  unfold tailWord_801305
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225994362016311843765369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19483996241344207895843579 29225994362016311843765369)
  ·
    refine ⟨21919495771512233882824027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29225994362016311843765369 21919495771512233882824027)
    ·
      refine ⟨32879243657268350824236041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21919495771512233882824027 32879243657268350824236041)
      ·
        refine ⟨24659432742951263118177031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32879243657268350824236041 24659432742951263118177031)
        ·
          refine ⟨36989149114426894677265547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24659432742951263118177031 36989149114426894677265547)
          ·
            refine ⟨55483723671640342015898321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36989149114426894677265547 55483723671640342015898321)
            ·
              refine ⟨41612792753730256511923741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55483723671640342015898321 41612792753730256511923741)
              ·
                refine ⟨15604797282648846191971403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41612792753730256511923741 15604797282648846191971403)
                ·
                  refine ⟨23407195923973269287957105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15604797282648846191971403 23407195923973269287957105)
                  ·
                    refine ⟨17555396942979951965967829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23407195923973269287957105 17555396942979951965967829)
                    ·
                      refine ⟨411454615851092624202371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 17555396942979951965967829 411454615851092624202371)
                      ·
                        rfl

theorem cell23_801305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_801305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801305 prefixEnd_801305 := by exact prefixLift 801305
  have htrace : WordTrace (prefixWord ++ tailWord_801305) baseStart_801305 baseEnd_801305 := by
    simpa [prefixWord, tailWord_801305, baseEnd_801305] using wordTrace_append hprefix tailTrace_801305
  have hstable : (prefixWord ++ tailWord_801305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801305).length < 2 ^ (prefixWord ++ tailWord_801305).sum := by decide
  have hdescent : baseEnd_801305 < baseStart_801305 := by decide
  rcases family_descends (prefixWord ++ tailWord_801305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801374 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_801374 : Nat := 118140960795 + 801374 * 2 ^ 59
def prefixEnd_801374 : Nat := 4983230072969 + 3 ^ 40 * 801374 * 2
def baseEnd_801374 : Nat := 411490046016252854239555

theorem tailTrace_801374 : CollatzResearch.WordTrace tailWord_801374 prefixEnd_801374 411490046016252854239555 := by
  unfold tailWord_801374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653563874845792078503397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19485673999177557752018117 3653563874845792078503397)
  ·
    refine ⟨685043226533586014719387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3653563874845792078503397 685043226533586014719387)
    ·
      refine ⟨1027564839800379022079081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685043226533586014719387 1027564839800379022079081)
      ·
        refine ⟨770673629850284266559311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1027564839800379022079081 770673629850284266559311)
        ·
          refine ⟨1156010444775426399838967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770673629850284266559311 1156010444775426399838967)
          ·
            refine ⟨1734015667163139599758451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156010444775426399838967 1734015667163139599758451)
            ·
              refine ⟨2601023500744709399637677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734015667163139599758451 2601023500744709399637677)
              ·
                refine ⟨975383812779266024864129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2601023500744709399637677 975383812779266024864129)
                ·
                  refine ⟨731537859584449518648097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975383812779266024864129 731537859584449518648097)
                  ·
                    refine ⟨548653394688337138986073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 731537859584449518648097 548653394688337138986073)
                    ·
                      refine ⟨411490046016252854239555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548653394688337138986073 411490046016252854239555)
                      ·
                        rfl

theorem cell23_801374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_801374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801374 prefixEnd_801374 := by exact prefixLift 801374
  have htrace : WordTrace (prefixWord ++ tailWord_801374) baseStart_801374 baseEnd_801374 := by
    simpa [prefixWord, tailWord_801374, baseEnd_801374] using wordTrace_append hprefix tailTrace_801374
  have hstable : (prefixWord ++ tailWord_801374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801374).length < 2 ^ (prefixWord ++ tailWord_801374).sum := by decide
  have hdescent : baseEnd_801374 < baseStart_801374 := by decide
  rcases family_descends (prefixWord ++ tailWord_801374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801379 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 6, 2]
def baseStart_801379 : Nat := 118140960795 + 801379 * 2 ^ 59
def prefixEnd_801379 : Nat := 4983230072969 + 3 ^ 40 * 801379 * 2
def baseEnd_801379 : Nat := 411492613419525334677031

theorem tailTrace_801379 : CollatzResearch.WordTrace tailWord_801379 prefixEnd_801379 411492613419525334677031 := by
  unfold tailWord_801379
  simp only [CollatzResearch.WordTrace]
  refine ⟨29228693363748222481959191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19485795575832148321306127 29228693363748222481959191)
  ·
    refine ⟨43843040045622333722938787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29228693363748222481959191 43843040045622333722938787)
    ·
      refine ⟨65764560068433500584408181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43843040045622333722938787 65764560068433500584408181)
      ·
        refine ⟨6165427506415640679788267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65764560068433500584408181 6165427506415640679788267)
        ·
          refine ⟨9248141259623461019682401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165427506415640679788267 9248141259623461019682401)
          ·
            refine ⟨6936105944717595764761801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9248141259623461019682401 6936105944717595764761801)
            ·
              refine ⟨5202079458538196823571351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936105944717595764761801 5202079458538196823571351)
              ·
                refine ⟨7803119187807295235357027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202079458538196823571351 7803119187807295235357027)
                ·
                  refine ⟨11704678781710942853035541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803119187807295235357027 11704678781710942853035541)
                  ·
                    refine ⟨548656817892700446236041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11704678781710942853035541 548656817892700446236041)
                    ·
                      refine ⟨411492613419525334677031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548656817892700446236041 411492613419525334677031)
                      ·
                        rfl

theorem cell23_801379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_801379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801379 prefixEnd_801379 := by exact prefixLift 801379
  have htrace : WordTrace (prefixWord ++ tailWord_801379) baseStart_801379 baseEnd_801379 := by
    simpa [prefixWord, tailWord_801379, baseEnd_801379] using wordTrace_append hprefix tailTrace_801379
  have hstable : (prefixWord ++ tailWord_801379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801379).length < 2 ^ (prefixWord ++ tailWord_801379).sum := by decide
  have hdescent : baseEnd_801379 < baseStart_801379 := by decide
  rcases family_descends (prefixWord ++ tailWord_801379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801399 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_801399 : Nat := 118140960795 + 801399 * 2 ^ 59
def prefixEnd_801399 : Nat := 4983230072969 + 3 ^ 40 * 801399 * 2
def baseEnd_801399 : Nat := 411502883032615256426939

theorem tailTrace_801399 : CollatzResearch.WordTrace tailWord_801399 prefixEnd_801399 411502883032615256426939 := by
  unfold tailWord_801399
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229422823675765897687251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19486281882450510598458167 29229422823675765897687251)
  ·
    refine ⟨43844134235513648846530877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29229422823675765897687251 43844134235513648846530877)
    ·
      refine ⟨16441550338317618317449079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43844134235513648846530877 16441550338317618317449079)
      ·
        refine ⟨24662325507476427476173619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16441550338317618317449079 24662325507476427476173619)
        ·
          refine ⟨36993488261214641214260429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24662325507476427476173619 36993488261214641214260429)
          ·
            refine ⟨13872558097955490455347661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36993488261214641214260429 13872558097955490455347661)
            ·
              refine ⟨5202209286733308920755373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13872558097955490455347661 5202209286733308920755373)
              ·
                refine ⟨1950828482524990845283265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5202209286733308920755373 1950828482524990845283265)
                ·
                  refine ⟨1463121361893743133962449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950828482524990845283265 1463121361893743133962449)
                  ·
                    refine ⟨1097341021420307350471837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463121361893743133962449 1097341021420307350471837)
                    ·
                      refine ⟨411502883032615256426939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097341021420307350471837 411502883032615256426939)
                      ·
                        rfl

theorem cell23_801399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_801399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801399 prefixEnd_801399 := by exact prefixLift 801399
  have htrace : WordTrace (prefixWord ++ tailWord_801399) baseStart_801399 baseEnd_801399 := by
    simpa [prefixWord, tailWord_801399, baseEnd_801399] using wordTrace_append hprefix tailTrace_801399
  have hstable : (prefixWord ++ tailWord_801399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801399).length < 2 ^ (prefixWord ++ tailWord_801399).sum := by decide
  have hdescent : baseEnd_801399 < baseStart_801399 := by decide
  rcases family_descends (prefixWord ++ tailWord_801399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801489 : List Nat := [1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_801489 : Nat := 118140960795 + 801489 * 2 ^ 59
def prefixEnd_801489 : Nat := 4983230072969 + 3 ^ 40 * 801489 * 2
def baseEnd_801489 : Nat := 411549096291519904301525

theorem tailTrace_801489 : CollatzResearch.WordTrace tailWord_801489 prefixEnd_801489 411549096291519904301525 := by
  unfold tailWord_801489
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232705393349711268463521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19488470262233140845642347 29232705393349711268463521)
  ·
    refine ⟨21924529045012283451347641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29232705393349711268463521 21924529045012283451347641)
    ·
      refine ⟨16443396783759212588510731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21924529045012283451347641 16443396783759212588510731)
      ·
        refine ⟨24665095175638818882766097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16443396783759212588510731 24665095175638818882766097)
        ·
          refine ⟨18498821381729114162074573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24665095175638818882766097 18498821381729114162074573)
          ·
            refine ⟨6937058018148417810777965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18498821381729114162074573 6937058018148417810777965)
            ·
              refine ⟨2601396756805656679041737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6937058018148417810777965 2601396756805656679041737)
              ·
                refine ⟨1951047567604242509281303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601396756805656679041737 1951047567604242509281303)
                ·
                  refine ⟨2926571351406363763921955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951047567604242509281303 2926571351406363763921955)
                  ·
                    refine ⟨4389857027109545645882933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2926571351406363763921955 4389857027109545645882933)
                    ·
                      refine ⟨411549096291519904301525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4389857027109545645882933 411549096291519904301525)
                      ·
                        rfl

theorem cell23_801489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_801489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801489 prefixEnd_801489 := by exact prefixLift 801489
  have htrace : WordTrace (prefixWord ++ tailWord_801489) baseStart_801489 baseEnd_801489 := by
    simpa [prefixWord, tailWord_801489, baseEnd_801489] using wordTrace_append hprefix tailTrace_801489
  have hstable : (prefixWord ++ tailWord_801489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801489).length < 2 ^ (prefixWord ++ tailWord_801489).sum := by decide
  have hdescent : baseEnd_801489 < baseStart_801489 := by decide
  rcases family_descends (prefixWord ++ tailWord_801489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801496 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_801496 : Nat := 118140960795 + 801496 * 2 ^ 59
def prefixEnd_801496 : Nat := 4983230072969 + 3 ^ 40 * 801496 * 2
def baseEnd_801496 : Nat := 137184230218700458971331

theorem tailTrace_801496 : CollatzResearch.WordTrace tailWord_801496 prefixEnd_801496 137184230218700458971331 := by
  unfold tailWord_801496
  simp only [CollatzResearch.WordTrace]
  refine ⟨14616480352162175731984171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19488640469549567642645561 14616480352162175731984171)
  ·
    refine ⟨21924720528243263597976257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14616480352162175731984171 21924720528243263597976257)
    ·
      refine ⟨16443540396182447698482193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21924720528243263597976257 16443540396182447698482193)
      ·
        refine ⟨12332655297136835773861645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16443540396182447698482193 12332655297136835773861645)
        ·
          refine ⟨4624745736426313415198117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12332655297136835773861645 4624745736426313415198117)
          ·
            refine ⟨867139825579933765349647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4624745736426313415198117 867139825579933765349647)
            ·
              refine ⟨1300709738369900648024471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867139825579933765349647 1300709738369900648024471)
              ·
                refine ⟨1951064607554850972036707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300709738369900648024471 1951064607554850972036707)
                ·
                  refine ⟨2926596911332276458055061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951064607554850972036707 2926596911332276458055061)
                  ·
                    refine ⟨137184230218700458971331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2926596911332276458055061 137184230218700458971331)
                    ·
                      rfl

theorem cell23_801496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_801496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801496 prefixEnd_801496 := by exact prefixLift 801496
  have htrace : WordTrace (prefixWord ++ tailWord_801496) baseStart_801496 baseEnd_801496 := by
    simpa [prefixWord, tailWord_801496, baseEnd_801496] using wordTrace_append hprefix tailTrace_801496
  have hstable : (prefixWord ++ tailWord_801496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801496).length < 2 ^ (prefixWord ++ tailWord_801496).sum := by decide
  have hdescent : baseEnd_801496 < baseStart_801496 := by decide
  rcases family_descends (prefixWord ++ tailWord_801496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801503 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 3, 2, 2]
def baseStart_801503 : Nat := 118140960795 + 801503 * 2 ^ 59
def prefixEnd_801503 : Nat := 4983230072969 + 3 ^ 40 * 801503 * 2
def baseEnd_801503 : Nat := 411556285020682849526461

theorem tailTrace_801503 : CollatzResearch.WordTrace tailWord_801503 prefixEnd_801503 411556285020682849526461 := by
  unfold tailWord_801503
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233216015298991659473163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19488810676865994439648775 29233216015298991659473163)
  ·
    refine ⟨43849824022948487489209745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29233216015298991659473163 43849824022948487489209745)
    ·
      refine ⟨32887368017211365616907309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43849824022948487489209745 32887368017211365616907309)
      ·
        refine ⟨12332763006454262106340241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32887368017211365616907309 12332763006454262106340241)
        ·
          refine ⟨9249572254840696579755181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12332763006454262106340241 9249572254840696579755181)
          ·
            refine ⟨3468589595565261217408193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9249572254840696579755181 3468589595565261217408193)
            ·
              refine ⟨2601442196673945913056145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468589595565261217408193 2601442196673945913056145)
              ·
                refine ⟨1951081647505459434792109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601442196673945913056145 1951081647505459434792109)
                ·
                  refine ⟨731655617814547288047041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1951081647505459434792109 731655617814547288047041)
                  ·
                    refine ⟨548741713360910466035281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 731655617814547288047041 548741713360910466035281)
                    ·
                      refine ⟨411556285020682849526461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548741713360910466035281 411556285020682849526461)
                      ·
                        rfl

theorem cell23_801503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 3, 2, 2].length) (baseStart_801503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801503 prefixEnd_801503 := by exact prefixLift 801503
  have htrace : WordTrace (prefixWord ++ tailWord_801503) baseStart_801503 baseEnd_801503 := by
    simpa [prefixWord, tailWord_801503, baseEnd_801503] using wordTrace_append hprefix tailTrace_801503
  have hstable : (prefixWord ++ tailWord_801503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801503).length < 2 ^ (prefixWord ++ tailWord_801503).sum := by decide
  have hdescent : baseEnd_801503 < baseStart_801503 := by decide
  rcases family_descends (prefixWord ++ tailWord_801503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801509 : List Nat := [1, 3, 1, 4, 1, 3, 1, 9]
def baseStart_801509 : Nat := 118140960795 + 801509 * 2 ^ 59
def prefixEnd_801509 : Nat := 4983230072969 + 3 ^ 40 * 801509 * 2
def baseEnd_801509 : Nat := 15242939477948512075979

theorem tailTrace_801509 : CollatzResearch.WordTrace tailWord_801509 prefixEnd_801509 15242939477948512075979 := by
  unfold tailWord_801509
  simp only [CollatzResearch.WordTrace]
  refine ⟨29233434853277254684191581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19488956568851503122794387 29233434853277254684191581)
  ·
    refine ⟨10962538069978970506571843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29233434853277254684191581 10962538069978970506571843)
    ·
      refine ⟨16443807104968455759857765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10962538069978970506571843 16443807104968455759857765)
      ·
        refine ⟨3083213832181585454973331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16443807104968455759857765 3083213832181585454973331)
        ·
          refine ⟨4624820748272378182459997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083213832181585454973331 4624820748272378182459997)
          ·
            refine ⟨1734307780602141818422499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4624820748272378182459997 1734307780602141818422499)
            ·
              refine ⟨2601461670903212727633749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734307780602141818422499 2601461670903212727633749)
              ·
                refine ⟨15242939477948512075979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2601461670903212727633749 15242939477948512075979)
                ·
                  rfl

theorem cell23_801509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 9].length) (baseStart_801509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801509 prefixEnd_801509 := by exact prefixLift 801509
  have htrace : WordTrace (prefixWord ++ tailWord_801509) baseStart_801509 baseEnd_801509 := by
    simpa [prefixWord, tailWord_801509, baseEnd_801509] using wordTrace_append hprefix tailTrace_801509
  have hstable : (prefixWord ++ tailWord_801509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801509).length < 2 ^ (prefixWord ++ tailWord_801509).sum := by decide
  have hdescent : baseEnd_801509 < baseStart_801509 := by decide
  rcases family_descends (prefixWord ++ tailWord_801509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801579 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3]
def baseStart_801579 : Nat := 118140960795 + 801579 * 2 ^ 59
def prefixEnd_801579 : Nat := 4983230072969 + 3 ^ 40 * 801579 * 2
def baseEnd_801579 : Nat := 411595309550424552176111

theorem tailTrace_801579 : CollatzResearch.WordTrace tailWord_801579 prefixEnd_801579 411595309550424552176111 := by
  unfold tailWord_801579
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235987963023656639239791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19490658642015771092826527 29235987963023656639239791)
  ·
    refine ⟨43853981944535484958859687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29235987963023656639239791 43853981944535484958859687)
    ·
      refine ⟨65780972916803227438289531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43853981944535484958859687 65780972916803227438289531)
      ·
        refine ⟨98671459375204841157434297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65780972916803227438289531 98671459375204841157434297)
        ·
          refine ⟨74003594531403630868075723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98671459375204841157434297 74003594531403630868075723)
          ·
            refine ⟨111005391797105446302113585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74003594531403630868075723 111005391797105446302113585)
            ·
              refine ⟨83254043847829084726585189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111005391797105446302113585 83254043847829084726585189)
              ·
                refine ⟨15610133221467953386234723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83254043847829084726585189 15610133221467953386234723)
                ·
                  refine ⟨23415199832201930079352085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15610133221467953386234723 23415199832201930079352085)
                  ·
                    refine ⟨1097587492134465472469629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23415199832201930079352085 1097587492134465472469629)
                    ·
                      refine ⟨411595309550424552176111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097587492134465472469629 411595309550424552176111)
                      ·
                        rfl

theorem cell23_801579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].length) (baseStart_801579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801579 prefixEnd_801579 := by exact prefixLift 801579
  have htrace : WordTrace (prefixWord ++ tailWord_801579) baseStart_801579 baseEnd_801579 := by
    simpa [prefixWord, tailWord_801579, baseEnd_801579] using wordTrace_append hprefix tailTrace_801579
  have hstable : (prefixWord ++ tailWord_801579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801579).length < 2 ^ (prefixWord ++ tailWord_801579).sum := by decide
  have hdescent : baseEnd_801579 < baseStart_801579 := by decide
  rcases family_descends (prefixWord ++ tailWord_801579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801580 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_801580 : Nat := 118140960795 + 801580 * 2 ^ 59
def prefixEnd_801580 : Nat := 4983230072969 + 3 ^ 40 * 801580 * 2
def baseEnd_801580 : Nat := 411595823031079048263607

theorem tailTrace_801580 : CollatzResearch.WordTrace tailWord_801580 prefixEnd_801580 411595823031079048263607 := by
  unfold tailWord_801580
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618012218010016905013097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19490682957346689206684129 14618012218010016905013097)
  ·
    refine ⟨10963509163507512678759823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14618012218010016905013097 10963509163507512678759823)
    ·
      refine ⟨16445263745261269018139735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963509163507512678759823 16445263745261269018139735)
      ·
        refine ⟨24667895617891903527209603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445263745261269018139735 24667895617891903527209603)
        ·
          refine ⟨37001843426837855290814405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24667895617891903527209603 37001843426837855290814405)
          ·
            refine ⟨6937845642532097867027701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37001843426837855290814405 6937845642532097867027701)
            ·
              refine ⟨650423028987384175033847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6937845642532097867027701 650423028987384175033847)
              ·
                refine ⟨975634543481076262550771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650423028987384175033847 975634543481076262550771)
                ·
                  refine ⟨1463451815221614393826157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975634543481076262550771 1463451815221614393826157)
                  ·
                    refine ⟨548794430708105397684809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463451815221614393826157 548794430708105397684809)
                    ·
                      refine ⟨411595823031079048263607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548794430708105397684809 411595823031079048263607)
                      ·
                        rfl

theorem cell23_801580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_801580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801580 prefixEnd_801580 := by exact prefixLift 801580
  have htrace : WordTrace (prefixWord ++ tailWord_801580) baseStart_801580 baseEnd_801580 := by
    simpa [prefixWord, tailWord_801580, baseEnd_801580] using wordTrace_append hprefix tailTrace_801580
  have hstable : (prefixWord ++ tailWord_801580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801580).length < 2 ^ (prefixWord ++ tailWord_801580).sum := by decide
  have hdescent : baseEnd_801580 < baseStart_801580 := by decide
  rcases family_descends (prefixWord ++ tailWord_801580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801588 : List Nat := [2, 5, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_801588 : Nat := 118140960795 + 801588 * 2 ^ 59
def prefixEnd_801588 : Nat := 4983230072969 + 3 ^ 40 * 801588 * 2
def baseEnd_801588 : Nat := 411599930876315016963571

theorem tailTrace_801588 : CollatzResearch.WordTrace tailWord_801588 prefixEnd_801588 411599930876315016963571 := by
  unfold tailWord_801588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14618158109995525588158709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19490877479994034117544945 14618158109995525588158709)
  ·
    refine ⟨1370452322812080523889879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14618158109995525588158709 1370452322812080523889879)
    ·
      refine ⟨2055678484218120785834819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370452322812080523889879 2055678484218120785834819)
      ·
        refine ⟨3083517726327181178752229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055678484218120785834819 3083517726327181178752229)
        ·
          refine ⟨578159573686346471016043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3083517726327181178752229 578159573686346471016043)
          ·
            refine ⟨867239360529519706524065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 578159573686346471016043 867239360529519706524065)
            ·
              refine ⟨650429520397139779893049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867239360529519706524065 650429520397139779893049)
              ·
                refine ⟨487822140297854834919787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650429520397139779893049 487822140297854834919787)
                ·
                  refine ⟨731733210446782252379681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487822140297854834919787 731733210446782252379681)
                  ·
                    refine ⟨548799907835086689284761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 731733210446782252379681 548799907835086689284761)
                    ·
                      refine ⟨411599930876315016963571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548799907835086689284761 411599930876315016963571)
                      ·
                        rfl

theorem cell23_801588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_801588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801588 prefixEnd_801588 := by exact prefixLift 801588
  have htrace : WordTrace (prefixWord ++ tailWord_801588) baseStart_801588 baseEnd_801588 := by
    simpa [prefixWord, tailWord_801588, baseEnd_801588] using wordTrace_append hprefix tailTrace_801588
  have hstable : (prefixWord ++ tailWord_801588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801588).length < 2 ^ (prefixWord ++ tailWord_801588).sum := by decide
  have hdescent : baseEnd_801588 < baseStart_801588 := by decide
  rcases family_descends (prefixWord ++ tailWord_801588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_801776 : Nat := 118140960795 + 801776 * 2 ^ 59
def prefixEnd_801776 : Nat := 4983230072969 + 3 ^ 40 * 801776 * 2
def baseEnd_801776 : Nat := 411696465239360281412705

theorem tailTrace_801776 : CollatzResearch.WordTrace tailWord_801776 prefixEnd_801776 411696465239360281412705 := by
  unfold tailWord_801776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621586571654979642080591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19495448762206639522774121 14621586571654979642080591)
  ·
    refine ⟨21932379857482469463120887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14621586571654979642080591 21932379857482469463120887)
    ·
      refine ⟨32898569786223704194681331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21932379857482469463120887 32898569786223704194681331)
      ·
        refine ⟨49347854679335556292021997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32898569786223704194681331 49347854679335556292021997)
        ·
          refine ⟨18505445504750833609508249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49347854679335556292021997 18505445504750833609508249)
          ·
            refine ⟨13879084128563125207131187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18505445504750833609508249 13879084128563125207131187)
            ·
              refine ⟨20818626192844687810696781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13879084128563125207131187 20818626192844687810696781)
              ·
                refine ⟨7806984822316757929011293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20818626192844687810696781 7806984822316757929011293)
                ·
                  refine ⟨2927619308368784223379235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7806984822316757929011293 2927619308368784223379235)
                  ·
                    refine ⟨4391428962553176335068853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927619308368784223379235 4391428962553176335068853)
                    ·
                      refine ⟨411696465239360281412705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4391428962553176335068853 411696465239360281412705)
                      ·
                        rfl

theorem cell23_801776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_801776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801776 prefixEnd_801776 := by exact prefixLift 801776
  have htrace : WordTrace (prefixWord ++ tailWord_801776) baseStart_801776 baseEnd_801776 := by
    simpa [prefixWord, tailWord_801776, baseEnd_801776] using wordTrace_append hprefix tailTrace_801776
  have hstable : (prefixWord ++ tailWord_801776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801776).length < 2 ^ (prefixWord ++ tailWord_801776).sum := by decide
  have hdescent : baseEnd_801776 < baseStart_801776 := by decide
  rcases family_descends (prefixWord ++ tailWord_801776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801786 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6]
def baseStart_801786 : Nat := 118140960795 + 801786 * 2 ^ 59
def prefixEnd_801786 : Nat := 4983230072969 + 3 ^ 40 * 801786 * 2
def baseEnd_801786 : Nat := 411701600045905242287659

theorem tailTrace_801786 : CollatzResearch.WordTrace tailWord_801786 prefixEnd_801786 411701600045905242287659 := by
  unfold tailWord_801786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310884468318432748006303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19495691915515820661350141 7310884468318432748006303)
  ·
    refine ⟨10966326702477649122009455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7310884468318432748006303 10966326702477649122009455)
    ·
      refine ⟨16449490053716473683014183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10966326702477649122009455 16449490053716473683014183)
      ·
        refine ⟨24674235080574710524521275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449490053716473683014183 24674235080574710524521275)
        ·
          refine ⟨37011352620862065786781913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674235080574710524521275 37011352620862065786781913)
          ·
            refine ⟨27758514465646549340086435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37011352620862065786781913 27758514465646549340086435)
            ·
              refine ⟨41637771698469824010129653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27758514465646549340086435 41637771698469824010129653)
              ·
                refine ⟨3903541096731546000949655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41637771698469824010129653 3903541096731546000949655)
                ·
                  refine ⟨5855311645097319001424483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903541096731546000949655 5855311645097319001424483)
                  ·
                    refine ⟨8782967467645978502136725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855311645097319001424483 8782967467645978502136725)
                    ·
                      refine ⟨411701600045905242287659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8782967467645978502136725 411701600045905242287659)
                      ·
                        rfl

theorem cell23_801786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_801786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801786 prefixEnd_801786 := by exact prefixLift 801786
  have htrace : WordTrace (prefixWord ++ tailWord_801786) baseStart_801786 baseEnd_801786 := by
    simpa [prefixWord, tailWord_801786, baseEnd_801786] using wordTrace_append hprefix tailTrace_801786
  have hstable : (prefixWord ++ tailWord_801786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801786).length < 2 ^ (prefixWord ++ tailWord_801786).sum := by decide
  have hdescent : baseEnd_801786 < baseStart_801786 := by decide
  rcases family_descends (prefixWord ++ tailWord_801786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801794 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 5, 2]
def baseStart_801794 : Nat := 118140960795 + 801794 * 2 ^ 59
def prefixEnd_801794 : Nat := 4983230072969 + 3 ^ 40 * 801794 * 2
def baseEnd_801794 : Nat := 411705707891141210987623

theorem tailTrace_801794 : CollatzResearch.WordTrace tailWord_801794 prefixEnd_801794 411705707891141210987623 := by
  unfold tailWord_801794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310957414311187089579109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19495886438163165572210957 7310957414311187089579109)
  ·
    refine ⟨1370804515183347579296083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7310957414311187089579109 1370804515183347579296083)
    ·
      refine ⟨2056206772775021368944125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370804515183347579296083 2056206772775021368944125)
      ·
        refine ⟨771077539790633013354047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2056206772775021368944125 771077539790633013354047)
        ·
          refine ⟨1156616309685949520031071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771077539790633013354047 1156616309685949520031071)
          ·
            refine ⟨1734924464528924280046607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156616309685949520031071 1734924464528924280046607)
            ·
              refine ⟨2602386696793386420069911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734924464528924280046607 2602386696793386420069911)
              ·
                refine ⟨3903580045190079630104867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602386696793386420069911 3903580045190079630104867)
                ·
                  refine ⟨5855370067785119445157301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903580045190079630104867 5855370067785119445157301)
                  ·
                    refine ⟨548940943854854947983497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5855370067785119445157301 548940943854854947983497)
                    ·
                      refine ⟨411705707891141210987623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548940943854854947983497 411705707891141210987623)
                      ·
                        rfl

theorem cell23_801794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_801794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801794 prefixEnd_801794 := by exact prefixLift 801794
  have htrace : WordTrace (prefixWord ++ tailWord_801794) baseStart_801794 baseEnd_801794 := by
    simpa [prefixWord, tailWord_801794, baseEnd_801794] using wordTrace_append hprefix tailTrace_801794
  have hstable : (prefixWord ++ tailWord_801794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801794).length < 2 ^ (prefixWord ++ tailWord_801794).sum := by decide
  have hdescent : baseEnd_801794 < baseStart_801794 := by decide
  rcases family_descends (prefixWord ++ tailWord_801794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801803 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_801803 : Nat := 118140960795 + 801803 * 2 ^ 59
def prefixEnd_801803 : Nat := 4983230072969 + 3 ^ 40 * 801803 * 2
def baseEnd_801803 : Nat := 411710329217031675775081

theorem tailTrace_801803 : CollatzResearch.WordTrace tailWord_801803 prefixEnd_801803 411710329217031675775081 := by
  unfold tailWord_801803
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244157914212142895394063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19496105276141428596929375 29244157914212142895394063)
  ·
    refine ⟨43866236871318214343091095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29244157914212142895394063 43866236871318214343091095)
    ·
      refine ⟨65799355306977321514636643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43866236871318214343091095 65799355306977321514636643)
      ·
        refine ⟨98699032960465982271954965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65799355306977321514636643 98699032960465982271954965)
        ·
          refine ⟨4626517170021842918997889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98699032960465982271954965 4626517170021842918997889)
          ·
            refine ⟨3469887877516382189248417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626517170021842918997889 3469887877516382189248417)
            ·
              refine ⟨2602415908137286641936313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469887877516382189248417 2602415908137286641936313)
              ·
                refine ⟨1951811931102964981452235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602415908137286641936313 1951811931102964981452235)
                ·
                  refine ⟨2927717896654447472178353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951811931102964981452235 2927717896654447472178353)
                  ·
                    refine ⟨2195788422490835604133765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927717896654447472178353 2195788422490835604133765)
                    ·
                      refine ⟨411710329217031675775081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2195788422490835604133765 411710329217031675775081)
                      ·
                        rfl

theorem cell23_801803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_801803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801803 prefixEnd_801803 := by exact prefixLift 801803
  have htrace : WordTrace (prefixWord ++ tailWord_801803) baseStart_801803 baseEnd_801803 := by
    simpa [prefixWord, tailWord_801803, baseEnd_801803] using wordTrace_append hprefix tailTrace_801803
  have hstable : (prefixWord ++ tailWord_801803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801803).length < 2 ^ (prefixWord ++ tailWord_801803).sum := by decide
  have hdescent : baseEnd_801803 < baseStart_801803 := by decide
  rcases family_descends (prefixWord ++ tailWord_801803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801834 : List Nat := [3, 1, 4, 1, 3, 1, 3, 1, 2, 4]
def baseStart_801834 : Nat := 118140960795 + 801834 * 2 ^ 59
def prefixEnd_801834 : Nat := 4983230072969 + 3 ^ 40 * 801834 * 2
def baseEnd_801834 : Nat := 137242082372440351495813

theorem tailTrace_801834 : CollatzResearch.WordTrace tailWord_801834 prefixEnd_801834 137242082372440351495813 := by
  unfold tailWord_801834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311322144274958797443139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19496859051399890126515037 7311322144274958797443139)
  ·
    refine ⟨10966983216412438196164709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7311322144274958797443139 10966983216412438196164709)
    ·
      refine ⟨2056309353077332161780883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10966983216412438196164709 2056309353077332161780883)
      ·
        refine ⟨3084464029615998242671325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2056309353077332161780883 3084464029615998242671325)
        ·
          refine ⟨1156674011105999341001747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3084464029615998242671325 1156674011105999341001747)
          ·
            refine ⟨1735011016658999011502621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156674011105999341001747 1735011016658999011502621)
            ·
              refine ⟨650629131247124629313483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1735011016658999011502621 650629131247124629313483)
              ·
                refine ⟨975943696870686943970225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 650629131247124629313483 975943696870686943970225)
                ·
                  refine ⟨731957772653015207977669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 975943696870686943970225 731957772653015207977669)
                  ·
                    refine ⟨137242082372440351495813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 731957772653015207977669 137242082372440351495813)
                    ·
                      rfl

theorem cell23_801834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_801834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801834 prefixEnd_801834 := by exact prefixLift 801834
  have htrace : WordTrace (prefixWord ++ tailWord_801834) baseStart_801834 baseEnd_801834 := by
    simpa [prefixWord, tailWord_801834, baseEnd_801834] using wordTrace_append hprefix tailTrace_801834
  have hstable : (prefixWord ++ tailWord_801834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801834).length < 2 ^ (prefixWord ++ tailWord_801834).sum := by decide
  have hdescent : baseEnd_801834 < baseStart_801834 := by decide
  rcases family_descends (prefixWord ++ tailWord_801834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801844 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_801844 : Nat := 118140960795 + 801844 * 2 ^ 59
def prefixEnd_801844 : Nat := 4983230072969 + 3 ^ 40 * 801844 * 2
def baseEnd_801844 : Nat := 411731381923866015362393

theorem tailTrace_801844 : CollatzResearch.WordTrace tailWord_801844 prefixEnd_801844 411731381923866015362393 := by
  unfold tailWord_801844
  simp only [CollatzResearch.WordTrace]
  refine ⟨14622826653531803448818293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19497102204709071265091057 14622826653531803448818293)
  ·
    refine ⟨1370889998768606573326715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14622826653531803448818293 1370889998768606573326715)
    ·
      refine ⟨2056334998152909859990073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370889998768606573326715 2056334998152909859990073)
      ·
        refine ⟨1542251248614682394992555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056334998152909859990073 1542251248614682394992555)
        ·
          refine ⟨2313376872922023592488833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542251248614682394992555 2313376872922023592488833)
          ·
            refine ⟨1735032654691517694366625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2313376872922023592488833 1735032654691517694366625)
            ·
              refine ⟨1301274491018638270774969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735032654691517694366625 1301274491018638270774969)
              ·
                refine ⟨975955868263978703081227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301274491018638270774969 975955868263978703081227)
                ·
                  refine ⟨1463933802395968054621841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975955868263978703081227 1463933802395968054621841)
                  ·
                    refine ⟨1097950351796976040966381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1463933802395968054621841 1097950351796976040966381)
                    ·
                      refine ⟨411731381923866015362393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1097950351796976040966381 411731381923866015362393)
                      ·
                        rfl

theorem cell23_801844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_801844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801844 prefixEnd_801844 := by exact prefixLift 801844
  have htrace : WordTrace (prefixWord ++ tailWord_801844) baseStart_801844 baseEnd_801844 := by
    simpa [prefixWord, tailWord_801844, baseEnd_801844] using wordTrace_append hprefix tailTrace_801844
  have hstable : (prefixWord ++ tailWord_801844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801844).length < 2 ^ (prefixWord ++ tailWord_801844).sum := by decide
  have hdescent : baseEnd_801844 < baseStart_801844 := by decide
  rcases family_descends (prefixWord ++ tailWord_801844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801850 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2]
def baseStart_801850 : Nat := 118140960795 + 801850 * 2 ^ 59
def prefixEnd_801850 : Nat := 4983230072969 + 3 ^ 40 * 801850 * 2
def baseEnd_801850 : Nat := 411734462807792991887365

theorem tailTrace_801850 : CollatzResearch.WordTrace tailWord_801850 prefixEnd_801850 411734462807792991887365 := by
  unfold tailWord_801850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7311468036260467480588751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19497248096694579948236669 7311468036260467480588751)
  ·
    refine ⟨10967202054390701220883127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7311468036260467480588751 10967202054390701220883127)
    ·
      refine ⟨16450803081586051831324691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10967202054390701220883127 16450803081586051831324691)
      ·
        refine ⟨24676204622379077746987037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16450803081586051831324691 24676204622379077746987037)
        ·
          refine ⟨9253576733392154155120139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24676204622379077746987037 9253576733392154155120139)
          ·
            refine ⟨13880365100088231232680209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253576733392154155120139 13880365100088231232680209)
            ·
              refine ⟨10410273825066173424510157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13880365100088231232680209 10410273825066173424510157)
              ·
                refine ⟨3903852684399815034191309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10410273825066173424510157 3903852684399815034191309)
                ·
                  refine ⟨1463944756649930637821741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3903852684399815034191309 1463944756649930637821741)
                  ·
                    refine ⟨548979283743723989183153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463944756649930637821741 548979283743723989183153)
                    ·
                      refine ⟨411734462807792991887365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 548979283743723989183153 411734462807792991887365)
                      ·
                        rfl

theorem cell23_801850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2].length) (baseStart_801850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801850 prefixEnd_801850 := by exact prefixLift 801850
  have htrace : WordTrace (prefixWord ++ tailWord_801850) baseStart_801850 baseEnd_801850 := by
    simpa [prefixWord, tailWord_801850, baseEnd_801850] using wordTrace_append hprefix tailTrace_801850
  have hstable : (prefixWord ++ tailWord_801850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801850).length < 2 ^ (prefixWord ++ tailWord_801850).sum := by decide
  have hdescent : baseEnd_801850 < baseStart_801850 := by decide
  rcases family_descends (prefixWord ++ tailWord_801850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801853 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 5]
def baseStart_801853 : Nat := 118140960795 + 801853 * 2 ^ 59
def prefixEnd_801853 : Nat := 4983230072969 + 3 ^ 40 * 801853 * 2
def baseEnd_801853 : Nat := 411736003249756480149851

theorem tailTrace_801853 : CollatzResearch.WordTrace tailWord_801853 prefixEnd_801853 411736003249756480149851 := by
  unfold tailWord_801853
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245981564031001434714213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19497321042687334289809475 29245981564031001434714213)
  ·
    refine ⟨5483621543255812769008915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29245981564031001434714213 5483621543255812769008915)
    ·
      refine ⟨8225432314883719153513373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5483621543255812769008915 8225432314883719153513373)
      ·
        refine ⟨3084537118081394682567515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8225432314883719153513373 3084537118081394682567515)
        ·
          refine ⟨4626805677122092023851273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084537118081394682567515 4626805677122092023851273)
          ·
            refine ⟨3470104257841569017888455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626805677122092023851273 3470104257841569017888455)
            ·
              refine ⟨5205156386762353526832683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470104257841569017888455 5205156386762353526832683)
              ·
                refine ⟨7807734580143530290249025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205156386762353526832683 7807734580143530290249025)
                ·
                  refine ⟨5855800935107647717686769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807734580143530290249025 5855800935107647717686769)
                  ·
                    refine ⟨4391850701330735788265077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855800935107647717686769 4391850701330735788265077)
                    ·
                      refine ⟨411736003249756480149851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4391850701330735788265077 411736003249756480149851)
                      ·
                        rfl

theorem cell23_801853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_801853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801853 prefixEnd_801853 := by exact prefixLift 801853
  have htrace : WordTrace (prefixWord ++ tailWord_801853) baseStart_801853 baseEnd_801853 := by
    simpa [prefixWord, tailWord_801853, baseEnd_801853] using wordTrace_append hprefix tailTrace_801853
  have hstable : (prefixWord ++ tailWord_801853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801853).length < 2 ^ (prefixWord ++ tailWord_801853).sum := by decide
  have hdescent : baseEnd_801853 < baseStart_801853 := by decide
  rcases family_descends (prefixWord ++ tailWord_801853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801893 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_801893 : Nat := 118140960795 + 801893 * 2 ^ 59
def prefixEnd_801893 : Nat := 4983230072969 + 3 ^ 40 * 801893 * 2
def baseEnd_801893 : Nat := 411756542475936323649667

theorem tailTrace_801893 : CollatzResearch.WordTrace tailWord_801893 prefixEnd_801893 411756542475936323649667 := by
  unfold tailWord_801893
  simp only [CollatzResearch.WordTrace]
  refine ⟨29247440483886088266170333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19498293655924058844113555 29247440483886088266170333)
  ·
    refine ⟨10967790181457283099813875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29247440483886088266170333 10967790181457283099813875)
    ·
      refine ⟨16451685272185924649720813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10967790181457283099813875 16451685272185924649720813)
      ·
        refine ⟨6169381977069721743645305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16451685272185924649720813 6169381977069721743645305)
        ·
          refine ⟨4627036482802291307733979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6169381977069721743645305 4627036482802291307733979)
          ·
            refine ⟨6940554724203436961600969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627036482802291307733979 6940554724203436961600969)
            ·
              refine ⟨5205416043152577721200727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940554724203436961600969 5205416043152577721200727)
              ·
                refine ⟨7808124064728866581801091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205416043152577721200727 7808124064728866581801091)
                ·
                  refine ⟨11712186097093299872701637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7808124064728866581801091 11712186097093299872701637)
                  ·
                    refine ⟨2196034893204993726131557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11712186097093299872701637 2196034893204993726131557)
                    ·
                      refine ⟨411756542475936323649667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2196034893204993726131557 411756542475936323649667)
                      ·
                        rfl

theorem cell23_801893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_801893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801893 prefixEnd_801893 := by exact prefixLift 801893
  have htrace : WordTrace (prefixWord ++ tailWord_801893) baseStart_801893 baseEnd_801893 := by
    simpa [prefixWord, tailWord_801893, baseEnd_801893] using wordTrace_append hprefix tailTrace_801893
  have hstable : (prefixWord ++ tailWord_801893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801893).length < 2 ^ (prefixWord ++ tailWord_801893).sum := by decide
  have hdescent : baseEnd_801893 < baseStart_801893 := by decide
  rcases family_descends (prefixWord ++ tailWord_801893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801930 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3]
def baseStart_801930 : Nat := 118140960795 + 801930 * 2 ^ 59
def prefixEnd_801930 : Nat := 4983230072969 + 3 ^ 40 * 801930 * 2
def baseEnd_801930 : Nat := 411775541260152678886997

theorem tailTrace_801930 : CollatzResearch.WordTrace tailWord_801930 prefixEnd_801930 411775541260152678886997 := by
  unfold tailWord_801930
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312197496188010896316811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19499193323168029056844829 7312197496188010896316811)
  ·
    refine ⟨10968296244282016344475217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312197496188010896316811 10968296244282016344475217)
    ·
      refine ⟨8226222183211512258356413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10968296244282016344475217 8226222183211512258356413)
      ·
        refine ⟨3084833318704317096883655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8226222183211512258356413 3084833318704317096883655)
        ·
          refine ⟨4627249978056475645325483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084833318704317096883655 4627249978056475645325483)
          ·
            refine ⟨6940874967084713467988225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627249978056475645325483 6940874967084713467988225)
            ·
              refine ⟨5205656225313535100991169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940874967084713467988225 5205656225313535100991169)
              ·
                refine ⟨3904242168985151325743377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205656225313535100991169 3904242168985151325743377)
                ·
                  refine ⟨2928181626738863494307533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3904242168985151325743377 2928181626738863494307533)
                  ·
                    refine ⟨1098068110027073810365325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2928181626738863494307533 1098068110027073810365325)
                    ·
                      refine ⟨411775541260152678886997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098068110027073810365325 411775541260152678886997)
                      ·
                        rfl

theorem cell23_801930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_801930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801930 prefixEnd_801930 := by exact prefixLift 801930
  have htrace : WordTrace (prefixWord ++ tailWord_801930) baseStart_801930 baseEnd_801930 := by
    simpa [prefixWord, tailWord_801930, baseEnd_801930] using wordTrace_append hprefix tailTrace_801930
  have hstable : (prefixWord ++ tailWord_801930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801930).length < 2 ^ (prefixWord ++ tailWord_801930).sum := by decide
  have hdescent : baseEnd_801930 < baseStart_801930 := by decide
  rcases family_descends (prefixWord ++ tailWord_801930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801970 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_801970 : Nat := 118140960795 + 801970 * 2 ^ 59
def prefixEnd_801970 : Nat := 4983230072969 + 3 ^ 40 * 801970 * 2
def baseEnd_801970 : Nat := 411796080486332522386813

theorem tailTrace_801970 : CollatzResearch.WordTrace tailWord_801970 prefixEnd_801970 411796080486332522386813 := by
  unfold tailWord_801970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312562226151782604180841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19500165936404753611148909 7312562226151782604180841)
  ·
    refine ⟨5484421669613836953135631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7312562226151782604180841 5484421669613836953135631)
    ·
      refine ⟨8226632504420755429703447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5484421669613836953135631 8226632504420755429703447)
      ·
        refine ⟨12339948756631133144555171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8226632504420755429703447 12339948756631133144555171)
        ·
          refine ⟨18509923134946699716832757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339948756631133144555171 18509923134946699716832757)
          ·
            refine ⟨1735305293901253098453071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18509923134946699716832757 1735305293901253098453071)
            ·
              refine ⟨2602957940851879647679607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735305293901253098453071 2602957940851879647679607)
              ·
                refine ⟨3904436911277819471519411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602957940851879647679607 3904436911277819471519411)
                ·
                  refine ⟨5856655366916729207279117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904436911277819471519411 5856655366916729207279117)
                  ·
                    refine ⟨2196245762593773452729669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5856655366916729207279117 2196245762593773452729669)
                    ·
                      refine ⟨411796080486332522386813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2196245762593773452729669 411796080486332522386813)
                      ·
                        rfl

theorem cell23_801970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_801970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801970 prefixEnd_801970 := by exact prefixLift 801970
  have htrace : WordTrace (prefixWord ++ tailWord_801970) baseStart_801970 baseEnd_801970 := by
    simpa [prefixWord, tailWord_801970, baseEnd_801970] using wordTrace_append hprefix tailTrace_801970
  have hstable : (prefixWord ++ tailWord_801970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801970).length < 2 ^ (prefixWord ++ tailWord_801970).sum := by decide
  have hdescent : baseEnd_801970 < baseStart_801970 := by decide
  rcases family_descends (prefixWord ++ tailWord_801970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_801983 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_801983 : Nat := 118140960795 + 801983 * 2 ^ 59
def prefixEnd_801983 : Nat := 4983230072969 + 3 ^ 40 * 801983 * 2
def baseEnd_801983 : Nat := 411802755734840971524253

theorem tailTrace_801983 : CollatzResearch.WordTrace tailWord_801983 prefixEnd_801983 411802755734840971524253 := by
  unfold tailWord_801983
  simp only [CollatzResearch.WordTrace]
  refine ⟨29250723053560033636946603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19500482035706689091297735 29250723053560033636946603)
  ·
    refine ⟨43876084580340050455419905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29250723053560033636946603 43876084580340050455419905)
    ·
      refine ⟨32907063435255037841564929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43876084580340050455419905 32907063435255037841564929)
      ·
        refine ⟨24680297576441278381173697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32907063435255037841564929 24680297576441278381173697)
        ·
          refine ⟨18510223182330958785880273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24680297576441278381173697 18510223182330958785880273)
          ·
            refine ⟨13882667386748219089410205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18510223182330958785880273 13882667386748219089410205)
            ·
              refine ⟨5206000270030582158528827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13882667386748219089410205 5206000270030582158528827)
              ·
                refine ⟨7809000405045873237793241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206000270030582158528827 7809000405045873237793241)
                ·
                  refine ⟨5856750303784404928344931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7809000405045873237793241 5856750303784404928344931)
                  ·
                    refine ⟨8785125455676607392517397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856750303784404928344931 8785125455676607392517397)
                    ·
                      refine ⟨411802755734840971524253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8785125455676607392517397 411802755734840971524253)
                      ·
                        rfl

theorem cell23_801983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_801983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_801983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_801983 prefixEnd_801983 := by exact prefixLift 801983
  have htrace : WordTrace (prefixWord ++ tailWord_801983) baseStart_801983 baseEnd_801983 := by
    simpa [prefixWord, tailWord_801983, baseEnd_801983] using wordTrace_append hprefix tailTrace_801983
  have hstable : (prefixWord ++ tailWord_801983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_801983).length < 2 ^ (prefixWord ++ tailWord_801983).sum := by decide
  have hdescent : baseEnd_801983 < baseStart_801983 := by decide
  rcases family_descends (prefixWord ++ tailWord_801983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802031 : List Nat := [1, 1, 2, 1, 7, 2, 1, 3, 1, 4]
def baseStart_802031 : Nat := 118140960795 + 802031 * 2 ^ 59
def prefixEnd_802031 : Nat := 4983230072969 + 3 ^ 40 * 802031 * 2
def baseEnd_802031 : Nat := 137275800935418927908011

theorem tailTrace_802031 : CollatzResearch.WordTrace tailWord_802031 prefixEnd_802031 137275800935418927908011 := by
  unfold tailWord_802031
  simp only [CollatzResearch.WordTrace]
  refine ⟨29252473757386137834693947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19501649171590758556462631 29252473757386137834693947)
  ·
    refine ⟨43878710636079206752040921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29252473757386137834693947 43878710636079206752040921)
    ·
      refine ⟨32909032977059405064030691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43878710636079206752040921 32909032977059405064030691)
      ·
        refine ⟨49363549465589107596046037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32909032977059405064030691 49363549465589107596046037)
        ·
          refine ⟨1156958190599744709282329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49363549465589107596046037 1156958190599744709282329)
          ·
            refine ⟨867718642949808531961747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1156958190599744709282329 867718642949808531961747)
            ·
              refine ⟨1301577964424712797942621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867718642949808531961747 1301577964424712797942621)
              ·
                refine ⟨488091736659267299228483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1301577964424712797942621 488091736659267299228483)
                ·
                  refine ⟨732137604988900948842725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488091736659267299228483 732137604988900948842725)
                  ·
                    refine ⟨137275800935418927908011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732137604988900948842725 137275800935418927908011)
                    ·
                      rfl

theorem cell23_802031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_802031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802031 prefixEnd_802031 := by exact prefixLift 802031
  have htrace : WordTrace (prefixWord ++ tailWord_802031) baseStart_802031 baseEnd_802031 := by
    simpa [prefixWord, tailWord_802031, baseEnd_802031] using wordTrace_append hprefix tailTrace_802031
  have hstable : (prefixWord ++ tailWord_802031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802031).length < 2 ^ (prefixWord ++ tailWord_802031).sum := by decide
  have hdescent : baseEnd_802031 < baseStart_802031 := by decide
  rcases family_descends (prefixWord ++ tailWord_802031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802047 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 4, 3, 2]
def baseStart_802047 : Nat := 118140960795 + 802047 * 2 ^ 59
def prefixEnd_802047 : Nat := 4983230072969 + 3 ^ 40 * 802047 * 2
def baseEnd_802047 : Nat := 411835618496728721123959

theorem tailTrace_802047 : CollatzResearch.WordTrace tailWord_802047 prefixEnd_802047 411835618496728721123959 := by
  unfold tailWord_802047
  simp only [CollatzResearch.WordTrace]
  refine ⟨29253057325328172567276395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19502038216885448378184263 29253057325328172567276395)
  ·
    refine ⟨43879585987992258850914593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29253057325328172567276395 43879585987992258850914593)
    ·
      refine ⟨32909689490994194138185945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43879585987992258850914593 32909689490994194138185945)
      ·
        refine ⟨24682267118245645603639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32909689490994194138185945 24682267118245645603639459)
        ·
          refine ⟨37023400677368468405459189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24682267118245645603639459 37023400677368468405459189)
          ·
            refine ⟨3470943813503293913011799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37023400677368468405459189 3470943813503293913011799)
            ·
              refine ⟨5206415720254940869517699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470943813503293913011799 5206415720254940869517699)
              ·
                refine ⟨7809623580382411304276549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206415720254940869517699 7809623580382411304276549)
                ·
                  refine ⟨1464304421321702119551853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7809623580382411304276549 1464304421321702119551853)
                  ·
                    refine ⟨549114157995638294831945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464304421321702119551853 549114157995638294831945)
                    ·
                      refine ⟨411835618496728721123959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549114157995638294831945 411835618496728721123959)
                      ·
                        rfl

theorem cell23_802047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4, 3, 2].length) (baseStart_802047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802047 prefixEnd_802047 := by exact prefixLift 802047
  have htrace : WordTrace (prefixWord ++ tailWord_802047) baseStart_802047 baseEnd_802047 := by
    simpa [prefixWord, tailWord_802047, baseEnd_802047] using wordTrace_append hprefix tailTrace_802047
  have hstable : (prefixWord ++ tailWord_802047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802047).length < 2 ^ (prefixWord ++ tailWord_802047).sum := by decide
  have hdescent : baseEnd_802047 < baseStart_802047 := by decide
  rcases family_descends (prefixWord ++ tailWord_802047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802074 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 1, 5]
def baseStart_802074 : Nat := 118140960795 + 802074 * 2 ^ 59
def prefixEnd_802074 : Nat := 4983230072969 + 3 ^ 40 * 802074 * 2
def baseEnd_802074 : Nat := 137283160824800038495445

theorem tailTrace_802074 : CollatzResearch.WordTrace tailWord_802074 prefixEnd_802074 137283160824800038495445 := by
  unfold tailWord_802074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313510524057589044627319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19502694730820237452339517 7313510524057589044627319)
  ·
    refine ⟨10970265786086383566940979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313510524057589044627319 10970265786086383566940979)
    ·
      refine ⟨16455398679129575350411469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970265786086383566940979 16455398679129575350411469)
      ·
        refine ⟨6170774504673590756404301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16455398679129575350411469 6170774504673590756404301)
        ·
          refine ⟨2314040439252596533651613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6170774504673590756404301 2314040439252596533651613)
          ·
            refine ⟨867765164719723700119355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2314040439252596533651613 867765164719723700119355)
            ·
              refine ⟨1301647747079585550179033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867765164719723700119355 1301647747079585550179033)
              ·
                refine ⟨976235810309689162634275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301647747079585550179033 976235810309689162634275)
                ·
                  refine ⟨1464353715464533743951413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976235810309689162634275 1464353715464533743951413)
                  ·
                    refine ⟨137283160824800038495445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1464353715464533743951413 137283160824800038495445)
                    ·
                      rfl

theorem cell23_802074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 5].length) (baseStart_802074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802074 prefixEnd_802074 := by exact prefixLift 802074
  have htrace : WordTrace (prefixWord ++ tailWord_802074) baseStart_802074 baseEnd_802074 := by
    simpa [prefixWord, tailWord_802074, baseEnd_802074] using wordTrace_append hprefix tailTrace_802074
  have hstable : (prefixWord ++ tailWord_802074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802074).length < 2 ^ (prefixWord ++ tailWord_802074).sum := by decide
  have hdescent : baseEnd_802074 < baseStart_802074 := by decide
  rcases family_descends (prefixWord ++ tailWord_802074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802097 : List Nat := [1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_802097 : Nat := 118140960795 + 802097 * 2 ^ 59
def prefixEnd_802097 : Nat := 4983230072969 + 3 ^ 40 * 802097 * 2
def baseEnd_802097 : Nat := 411861292529453525498729

theorem tailTrace_802097 : CollatzResearch.WordTrace tailWord_802097 prefixEnd_802097 411861292529453525498729 := by
  unfold tailWord_802097
  simp only [CollatzResearch.WordTrace]
  refine ⟨29254880975147031106596545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19503253983431354071064363 29254880975147031106596545)
  ·
    refine ⟨21941160731360273329947409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29254880975147031106596545 21941160731360273329947409)
    ·
      refine ⟨16455870548520204997460557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21941160731360273329947409 16455870548520204997460557)
      ·
        refine ⟨6170951455695076874047709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16455870548520204997460557 6170951455695076874047709)
        ·
          refine ⟨2314106795885653827767891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6170951455695076874047709 2314106795885653827767891)
          ·
            refine ⟨3471160193828480741651837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314106795885653827767891 3471160193828480741651837)
            ·
              refine ⟨1301685072685680278119439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3471160193828480741651837 1301685072685680278119439)
              ·
                refine ⟨1952527609028520417179159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301685072685680278119439 1952527609028520417179159)
                ·
                  refine ⟨2928791413542780625768739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952527609028520417179159 2928791413542780625768739)
                  ·
                    refine ⟨4393187120314170938653109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928791413542780625768739 4393187120314170938653109)
                    ·
                      refine ⟨411861292529453525498729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4393187120314170938653109 411861292529453525498729)
                      ·
                        rfl

theorem cell23_802097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_802097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802097 prefixEnd_802097 := by exact prefixLift 802097
  have htrace : WordTrace (prefixWord ++ tailWord_802097) baseStart_802097 baseEnd_802097 := by
    simpa [prefixWord, tailWord_802097, baseEnd_802097] using wordTrace_append hprefix tailTrace_802097
  have hstable : (prefixWord ++ tailWord_802097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802097).length < 2 ^ (prefixWord ++ tailWord_802097).sum := by decide
  have hdescent : baseEnd_802097 < baseStart_802097 := by decide
  rcases family_descends (prefixWord ++ tailWord_802097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802105 : List Nat := [1, 2, 1, 6, 2, 2, 2, 2, 1, 1, 3]
def baseStart_802105 : Nat := 118140960795 + 802105 * 2 ^ 59
def prefixEnd_802105 : Nat := 4983230072969 + 3 ^ 40 * 802105 * 2
def baseEnd_802105 : Nat := 411865400374689494198693

theorem tailTrace_802105 : CollatzResearch.WordTrace tailWord_802105 prefixEnd_802105 411865400374689494198693 := by
  unfold tailWord_802105
  simp only [CollatzResearch.WordTrace]
  refine ⟨29255172759118048472887769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19503448506078698981925179 29255172759118048472887769)
  ·
    refine ⟨21941379569338536354665827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29255172759118048472887769 21941379569338536354665827)
    ·
      refine ⟨32912069354007804531998741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21941379569338536354665827 32912069354007804531998741)
      ·
        refine ⟨1542753250969115837437441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32912069354007804531998741 1542753250969115837437441)
        ·
          refine ⟨1157064938226836878078081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542753250969115837437441 1157064938226836878078081)
          ·
            refine ⟨867798703670127658558561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157064938226836878078081 867798703670127658558561)
            ·
              refine ⟨650849027752595743918921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 867798703670127658558561 650849027752595743918921)
              ·
                refine ⟨488136770814446807939191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650849027752595743918921 488136770814446807939191)
                ·
                  refine ⟨732205156221670211908787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488136770814446807939191 732205156221670211908787)
                  ·
                    refine ⟨1098307734332505317863181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732205156221670211908787 1098307734332505317863181)
                    ·
                      refine ⟨411865400374689494198693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098307734332505317863181 411865400374689494198693)
                      ·
                        rfl

theorem cell23_802105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_802105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802105 prefixEnd_802105 := by exact prefixLift 802105
  have htrace : WordTrace (prefixWord ++ tailWord_802105) baseStart_802105 baseEnd_802105 := by
    simpa [prefixWord, tailWord_802105, baseEnd_802105] using wordTrace_append hprefix tailTrace_802105
  have hstable : (prefixWord ++ tailWord_802105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802105).length < 2 ^ (prefixWord ++ tailWord_802105).sum := by decide
  have hdescent : baseEnd_802105 < baseStart_802105 := by decide
  rcases family_descends (prefixWord ++ tailWord_802105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802130 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 7]
def baseStart_802130 : Nat := 118140960795 + 802130 * 2 ^ 59
def prefixEnd_802130 : Nat := 4983230072969 + 3 ^ 40 * 802130 * 2
def baseEnd_802130 : Nat := 137292745797017298795359

theorem tailTrace_802130 : CollatzResearch.WordTrace tailWord_802130 prefixEnd_802130 137292745797017298795359 := by
  unfold tailWord_802130
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314021146006869435636961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19504056389351651828365229 7314021146006869435636961)
  ·
    refine ⟨5485515859505152076727721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7314021146006869435636961 5485515859505152076727721)
    ·
      refine ⟨4114136894628864057545791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5485515859505152076727721 4114136894628864057545791)
      ·
        refine ⟨6171205341943296086318687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114136894628864057545791 6171205341943296086318687)
        ·
          refine ⟨9256808012914944129478031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171205341943296086318687 9256808012914944129478031)
          ·
            refine ⟨13885212019372416194217047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256808012914944129478031 13885212019372416194217047)
            ·
              refine ⟨20827818029058624291325571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13885212019372416194217047 20827818029058624291325571)
              ·
                refine ⟨31241727043587936436988357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20827818029058624291325571 31241727043587936436988357)
                ·
                  refine ⟨5857823820672738081935317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31241727043587936436988357 5857823820672738081935317)
                  ·
                    refine ⟨137292745797017298795359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5857823820672738081935317 137292745797017298795359)
                    ·
                      rfl

theorem cell23_802130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_802130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802130 prefixEnd_802130 := by exact prefixLift 802130
  have htrace : WordTrace (prefixWord ++ tailWord_802130) baseStart_802130 baseEnd_802130 := by
    simpa [prefixWord, tailWord_802130, baseEnd_802130] using wordTrace_append hprefix tailTrace_802130
  have hstable : (prefixWord ++ tailWord_802130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802130).length < 2 ^ (prefixWord ++ tailWord_802130).sum := by decide
  have hdescent : baseEnd_802130 < baseStart_802130 := by decide
  rcases family_descends (prefixWord ++ tailWord_802130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802160 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_802160 : Nat := 118140960795 + 802160 * 2 ^ 59
def prefixEnd_802160 : Nat := 4983230072969 + 3 ^ 40 * 802160 * 2
def baseEnd_802160 : Nat := 137297880603562259670313

theorem tailTrace_802160 : CollatzResearch.WordTrace tailWord_802160 prefixEnd_802160 137297880603562259670313 := by
  unfold tailWord_802160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14628589386959396433069967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19504785849279195244093289 14628589386959396433069967)
  ·
    refine ⟨21942884080439094649604951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14628589386959396433069967 21942884080439094649604951)
    ·
      refine ⟨32914326120658641974407427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21942884080439094649604951 32914326120658641974407427)
      ·
        refine ⟨49371489180987962961611141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32914326120658641974407427 49371489180987962961611141)
        ·
          refine ⟨9257154221435243055302089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49371489180987962961611141 9257154221435243055302089)
          ·
            refine ⟨6942865666076432291476567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9257154221435243055302089 6942865666076432291476567)
            ·
              refine ⟨10414298499114648437214851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942865666076432291476567 10414298499114648437214851)
              ·
                refine ⟨15621447748671972655822277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10414298499114648437214851 15621447748671972655822277)
                ·
                  refine ⟨2929021452875994872966677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15621447748671972655822277 2929021452875994872966677)
                  ·
                    refine ⟨137297880603562259670313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2929021452875994872966677 137297880603562259670313)
                    ·
                      rfl

theorem cell23_802160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_802160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802160 prefixEnd_802160 := by exact prefixLift 802160
  have htrace : WordTrace (prefixWord ++ tailWord_802160) baseStart_802160 baseEnd_802160 := by
    simpa [prefixWord, tailWord_802160, baseEnd_802160] using wordTrace_append hprefix tailTrace_802160
  have hstable : (prefixWord ++ tailWord_802160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802160).length < 2 ^ (prefixWord ++ tailWord_802160).sum := by decide
  have hdescent : baseEnd_802160 < baseStart_802160 := by decide
  rcases family_descends (prefixWord ++ tailWord_802160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802170 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5]
def baseStart_802170 : Nat := 118140960795 + 802170 * 2 ^ 59
def prefixEnd_802170 : Nat := 4983230072969 + 3 ^ 40 * 802170 * 2
def baseEnd_802170 : Nat := 411898776617231739885893

theorem tailTrace_802170 : CollatzResearch.WordTrace tailWord_802170 prefixEnd_802170 411898776617231739885893 := by
  unfold tailWord_802170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314385875970641143500991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19505029002588376382669309 7314385875970641143500991)
  ·
    refine ⟨10971578813955961715251487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7314385875970641143500991 10971578813955961715251487)
    ·
      refine ⟨16457368220933942572877231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10971578813955961715251487 16457368220933942572877231)
      ·
        refine ⟨24686052331400913859315847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16457368220933942572877231 24686052331400913859315847)
        ·
          refine ⟨37029078497101370788973771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24686052331400913859315847 37029078497101370788973771)
          ·
            refine ⟨55543617745652056183460657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37029078497101370788973771 55543617745652056183460657)
            ·
              refine ⟨41657713309239042137595493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55543617745652056183460657 41657713309239042137595493)
              ·
                refine ⟨7810821245482320400799155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41657713309239042137595493 7810821245482320400799155)
                ·
                  refine ⟨11716231868223480601198733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7810821245482320400799155 11716231868223480601198733)
                  ·
                    refine ⟨4393586950583805225449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11716231868223480601198733 4393586950583805225449525)
                    ·
                      refine ⟨411898776617231739885893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4393586950583805225449525 411898776617231739885893)
                      ·
                        rfl

theorem cell23_802170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_802170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802170 prefixEnd_802170 := by exact prefixLift 802170
  have htrace : WordTrace (prefixWord ++ tailWord_802170) baseStart_802170 baseEnd_802170 := by
    simpa [prefixWord, tailWord_802170, baseEnd_802170] using wordTrace_append hprefix tailTrace_802170
  have hstable : (prefixWord ++ tailWord_802170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802170).length < 2 ^ (prefixWord ++ tailWord_802170).sum := by decide
  have hdescent : baseEnd_802170 < baseStart_802170 := by decide
  rcases family_descends (prefixWord ++ tailWord_802170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802178 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 3, 3]
def baseStart_802178 : Nat := 118140960795 + 802178 * 2 ^ 59
def prefixEnd_802178 : Nat := 4983230072969 + 3 ^ 40 * 802178 * 2
def baseEnd_802178 : Nat := 411902884462467708585857

theorem tailTrace_802178 : CollatzResearch.WordTrace tailWord_802178 prefixEnd_802178 411902884462467708585857 := by
  unfold tailWord_802178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7314458821963395485073797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19505223525235721293530125 7314458821963395485073797)
  ·
    refine ⟨1371461029118136653451337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7314458821963395485073797 1371461029118136653451337)
    ·
      refine ⟨1028595771838602490088503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1371461029118136653451337 1028595771838602490088503)
      ·
        refine ⟨1542893657757903735132755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028595771838602490088503 1542893657757903735132755)
        ·
          refine ⟨2314340486636855602699133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542893657757903735132755 2314340486636855602699133)
          ·
            refine ⟨867877682488820851012175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2314340486636855602699133 867877682488820851012175)
            ·
              refine ⟨1301816523733231276518263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867877682488820851012175 1301816523733231276518263)
              ·
                refine ⟨1952724785599846914777395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301816523733231276518263 1952724785599846914777395)
                ·
                  refine ⟨2929087178399770372166093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952724785599846914777395 2929087178399770372166093)
                  ·
                    refine ⟨1098407691899913889562285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2929087178399770372166093 1098407691899913889562285)
                    ·
                      refine ⟨411902884462467708585857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098407691899913889562285 411902884462467708585857)
                      ·
                        rfl

theorem cell23_802178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_802178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802178 prefixEnd_802178 := by exact prefixLift 802178
  have htrace : WordTrace (prefixWord ++ tailWord_802178) baseStart_802178 baseEnd_802178 := by
    simpa [prefixWord, tailWord_802178, baseEnd_802178] using wordTrace_append hprefix tailTrace_802178
  have hstable : (prefixWord ++ tailWord_802178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802178).length < 2 ^ (prefixWord ++ tailWord_802178).sum := by decide
  have hdescent : baseEnd_802178 < baseStart_802178 := by decide
  rcases family_descends (prefixWord ++ tailWord_802178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802237 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_802237 : Nat := 118140960795 + 802237 * 2 ^ 59
def prefixEnd_802237 : Nat := 4983230072969 + 3 ^ 40 * 802237 * 2
def baseEnd_802237 : Nat := 137311059940360992582695

theorem tailTrace_802237 : CollatzResearch.WordTrace tailWord_802237 prefixEnd_802237 137311059940360992582695 := by
  unfold tailWord_802237
  simp only [CollatzResearch.WordTrace]
  refine ⟨29259987194639835016692965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19506658129759890011128643 29259987194639835016692965)
  ·
    refine ⟨5486247598994969065629931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29259987194639835016692965 5486247598994969065629931)
    ·
      refine ⟨8229371398492453598444897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5486247598994969065629931 8229371398492453598444897)
      ·
        refine ⟨6172028548869340198833673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8229371398492453598444897 6172028548869340198833673)
        ·
          refine ⟨4629021411652005149125255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6172028548869340198833673 4629021411652005149125255)
          ·
            refine ⟨6943532117478007723687883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629021411652005149125255 6943532117478007723687883)
            ·
              refine ⟨10415298176217011585531825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943532117478007723687883 10415298176217011585531825)
              ·
                refine ⟨7811473632162758689148869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10415298176217011585531825 7811473632162758689148869)
                ·
                  refine ⟨1464651306030517254215413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7811473632162758689148869 1464651306030517254215413)
                  ·
                    refine ⟨137311059940360992582695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1464651306030517254215413 137311059940360992582695)
                    ·
                      rfl

theorem cell23_802237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_802237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802237 prefixEnd_802237 := by exact prefixLift 802237
  have htrace : WordTrace (prefixWord ++ tailWord_802237) baseStart_802237 baseEnd_802237 := by
    simpa [prefixWord, tailWord_802237, baseEnd_802237] using wordTrace_append hprefix tailTrace_802237
  have hstable : (prefixWord ++ tailWord_802237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802237).length < 2 ^ (prefixWord ++ tailWord_802237).sum := by decide
  have hdescent : baseEnd_802237 < baseStart_802237 := by decide
  rcases family_descends (prefixWord ++ tailWord_802237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802307 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3]
def baseStart_802307 : Nat := 118140960795 + 802307 * 2 ^ 59
def prefixEnd_802307 : Nat := 4983230072969 + 3 ^ 40 * 802307 * 2
def baseEnd_802307 : Nat := 411969123466897703872763

theorem tailTrace_802307 : CollatzResearch.WordTrace tailWord_802307 prefixEnd_802307 411969123466897703872763 := by
  unfold tailWord_802307
  simp only [CollatzResearch.WordTrace]
  refine ⟨29262540304386236971741175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19508360202924157981160783 29262540304386236971741175)
  ·
    refine ⟨43893810456579355457611763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29262540304386236971741175 43893810456579355457611763)
    ·
      refine ⟨65840715684869033186417645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43893810456579355457611763 65840715684869033186417645)
      ·
        refine ⟨24690268381825887444906617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65840715684869033186417645 24690268381825887444906617)
        ·
          refine ⟨18517701286369415583679963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24690268381825887444906617 18517701286369415583679963)
          ·
            refine ⟨27776551929554123375519945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18517701286369415583679963 27776551929554123375519945)
            ·
              refine ⟨20832413947165592531639959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27776551929554123375519945 20832413947165592531639959)
              ·
                refine ⟨31248620920748388797459939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20832413947165592531639959 31248620920748388797459939)
                ·
                  refine ⟨46872931381122583196189909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31248620920748388797459939 46872931381122583196189909)
                  ·
                    refine ⟨1098584329245060543660701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46872931381122583196189909 1098584329245060543660701)
                    ·
                      refine ⟨411969123466897703872763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098584329245060543660701 411969123466897703872763)
                      ·
                        rfl

theorem cell23_802307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_802307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802307 prefixEnd_802307 := by exact prefixLift 802307
  have htrace : WordTrace (prefixWord ++ tailWord_802307) baseStart_802307 baseEnd_802307 := by
    simpa [prefixWord, tailWord_802307, baseEnd_802307] using wordTrace_append hprefix tailTrace_802307
  have hstable : (prefixWord ++ tailWord_802307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802307).length < 2 ^ (prefixWord ++ tailWord_802307).sum := by decide
  have hdescent : baseEnd_802307 < baseStart_802307 := by decide
  rcases family_descends (prefixWord ++ tailWord_802307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802308 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_802308 : Nat := 118140960795 + 802308 * 2 ^ 59
def prefixEnd_802308 : Nat := 4983230072969 + 3 ^ 40 * 802308 * 2
def baseEnd_802308 : Nat := 411969636947552199960259

theorem tailTrace_802308 : CollatzResearch.WordTrace tailWord_802308 prefixEnd_802308 411969636947552199960259 := by
  unfold tailWord_802308
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631288388691307071263789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19508384518255076095018385 14631288388691307071263789)
  ·
    refine ⟨5486733145759240151723921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14631288388691307071263789 5486733145759240151723921)
    ·
      refine ⟨4115049859319430113792941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5486733145759240151723921 4115049859319430113792941)
      ·
        refine ⟨1543143697244786292672353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4115049859319430113792941 1543143697244786292672353)
        ·
          refine ⟨1157357772933589719504265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543143697244786292672353 1157357772933589719504265)
          ·
            refine ⟨868018329700192289628199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157357772933589719504265 868018329700192289628199)
            ·
              refine ⟨1302027494550288434442299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868018329700192289628199 1302027494550288434442299)
              ·
                refine ⟨1953041241825432651663449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302027494550288434442299 1953041241825432651663449)
                ·
                  refine ⟨1464780931369074488747587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953041241825432651663449 1464780931369074488747587)
                  ·
                    refine ⟨2197171397053611733121381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1464780931369074488747587 2197171397053611733121381)
                    ·
                      refine ⟨411969636947552199960259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2197171397053611733121381 411969636947552199960259)
                      ·
                        rfl

theorem cell23_802308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_802308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802308 prefixEnd_802308 := by exact prefixLift 802308
  have htrace : WordTrace (prefixWord ++ tailWord_802308) baseStart_802308 baseEnd_802308 := by
    simpa [prefixWord, tailWord_802308, baseEnd_802308] using wordTrace_append hprefix tailTrace_802308
  have hstable : (prefixWord ++ tailWord_802308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802308).length < 2 ^ (prefixWord ++ tailWord_802308).sum := by decide
  have hdescent : baseEnd_802308 < baseStart_802308 := by decide
  rcases family_descends (prefixWord ++ tailWord_802308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802311 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_802311 : Nat := 118140960795 + 802311 * 2 ^ 59
def prefixEnd_802311 : Nat := 4983230072969 + 3 ^ 40 * 802311 * 2
def baseEnd_802311 : Nat := 411971177389515688222745

theorem tailTrace_802311 : CollatzResearch.WordTrace tailWord_802311 prefixEnd_802311 411971177389515688222745 := by
  unfold tailWord_802311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29262686196371745654886787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19508457464247830436591191 29262686196371745654886787)
  ·
    refine ⟨43894029294557618482330181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29262686196371745654886787 43894029294557618482330181)
    ·
      refine ⟨8230130492729553465436909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43894029294557618482330181 8230130492729553465436909)
      ·
        refine ⟨3086298934773582549538841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8230130492729553465436909 3086298934773582549538841)
        ·
          refine ⟨2314724201080186912154131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086298934773582549538841 2314724201080186912154131)
          ·
            refine ⟨3472086301620280368231197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314724201080186912154131 3472086301620280368231197)
            ·
              refine ⟨1302032363107605138086699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3472086301620280368231197 1302032363107605138086699)
              ·
                refine ⟨1953048544661407707130049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302032363107605138086699 1953048544661407707130049)
                ·
                  refine ⟨1464786408496055780347537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953048544661407707130049 1464786408496055780347537)
                  ·
                    refine ⟨1098589806372041835260653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464786408496055780347537 1098589806372041835260653)
                    ·
                      refine ⟨411971177389515688222745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098589806372041835260653 411971177389515688222745)
                      ·
                        rfl

theorem cell23_802311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_802311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802311 prefixEnd_802311 := by exact prefixLift 802311
  have htrace : WordTrace (prefixWord ++ tailWord_802311) baseStart_802311 baseEnd_802311 := by
    simpa [prefixWord, tailWord_802311, baseEnd_802311] using wordTrace_append hprefix tailTrace_802311
  have hstable : (prefixWord ++ tailWord_802311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802311).length < 2 ^ (prefixWord ++ tailWord_802311).sum := by decide
  have hdescent : baseEnd_802311 < baseStart_802311 := by decide
  rcases family_descends (prefixWord ++ tailWord_802311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802361 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_802361 : Nat := 118140960795 + 802361 * 2 ^ 59
def prefixEnd_802361 : Nat := 4983230072969 + 3 ^ 40 * 802361 * 2
def baseEnd_802361 : Nat := 137332283807413497532505

theorem tailTrace_802361 : CollatzResearch.WordTrace tailWord_802361 prefixEnd_802361 137332283807413497532505 := by
  unfold tailWord_802361
  simp only [CollatzResearch.WordTrace]
  refine ⟨29264509846190604194206937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19509673230793736129471291 29264509846190604194206937)
  ·
    refine ⟨21948382384642953145655203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29264509846190604194206937 21948382384642953145655203)
    ·
      refine ⟨32922573576964429718482805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21948382384642953145655203 32922573576964429718482805)
      ·
        refine ⟨3086491272840415286107763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32922573576964429718482805 3086491272840415286107763)
        ·
          refine ⟨4629736909260622929161645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086491272840415286107763 4629736909260622929161645)
          ·
            refine ⟨1736151340972733598435617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4629736909260622929161645 1736151340972733598435617)
            ·
              refine ⟨1302113505729550198826713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736151340972733598435617 1302113505729550198826713)
              ·
                refine ⟨976585129297162649120035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302113505729550198826713 976585129297162649120035)
                ·
                  refine ⟨1464877693945743973680053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976585129297162649120035 1464877693945743973680053)
                  ·
                    refine ⟨137332283807413497532505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1464877693945743973680053 137332283807413497532505)
                    ·
                      rfl

theorem cell23_802361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_802361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802361 prefixEnd_802361 := by exact prefixLift 802361
  have htrace : WordTrace (prefixWord ++ tailWord_802361) baseStart_802361 baseEnd_802361 := by
    simpa [prefixWord, tailWord_802361, baseEnd_802361] using wordTrace_append hprefix tailTrace_802361
  have hstable : (prefixWord ++ tailWord_802361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802361).length < 2 ^ (prefixWord ++ tailWord_802361).sum := by decide
  have hdescent : baseEnd_802361 < baseStart_802361 := by decide
  rcases family_descends (prefixWord ++ tailWord_802361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802384 : List Nat := [2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_802384 : Nat := 118140960795 + 802384 * 2 ^ 59
def prefixEnd_802384 : Nat := 4983230072969 + 3 ^ 40 * 802384 * 2
def baseEnd_802384 : Nat := 412008661477293902609909

theorem tailTrace_802384 : CollatzResearch.WordTrace tailWord_802384 prefixEnd_802384 412008661477293902609909 := by
  unfold tailWord_802384
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632674362553639561147103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19510232483404852748196137 14632674362553639561147103)
  ·
    refine ⟨21949011543830459341720655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14632674362553639561147103 21949011543830459341720655)
    ·
      refine ⟨32923517315745689012580983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21949011543830459341720655 32923517315745689012580983)
      ·
        refine ⟨49385275973618533518871475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32923517315745689012580983 49385275973618533518871475)
        ·
          refine ⟨74077913960427800278307213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49385275973618533518871475 74077913960427800278307213)
          ·
            refine ⟨27779217735160425104365205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74077913960427800278307213 27779217735160425104365205)
            ·
              refine ⟨1302150831335644926767119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27779217735160425104365205 1302150831335644926767119)
              ·
                refine ⟨1953226247003467390150679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302150831335644926767119 1953226247003467390150679)
                ·
                  refine ⟨2929839370505201085226019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953226247003467390150679 2929839370505201085226019)
                  ·
                    refine ⟨4394759055757801627839029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929839370505201085226019 4394759055757801627839029)
                    ·
                      refine ⟨412008661477293902609909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4394759055757801627839029 412008661477293902609909)
                      ·
                        rfl

theorem cell23_802384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_802384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802384 prefixEnd_802384 := by exact prefixLift 802384
  have htrace : WordTrace (prefixWord ++ tailWord_802384) baseStart_802384 baseEnd_802384 := by
    simpa [prefixWord, tailWord_802384, baseEnd_802384] using wordTrace_append hprefix tailTrace_802384
  have hstable : (prefixWord ++ tailWord_802384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802384).length < 2 ^ (prefixWord ++ tailWord_802384).sum := by decide
  have hdescent : baseEnd_802384 < baseStart_802384 := by decide
  rcases family_descends (prefixWord ++ tailWord_802384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802404 : List Nat := [2, 3, 1, 1, 2, 4, 2, 8]
def baseStart_802404 : Nat := 118140960795 + 802404 * 2 ^ 59
def prefixEnd_802404 : Nat := 4983230072969 + 3 ^ 40 * 802404 * 2
def baseEnd_802404 : Nat := 15259960410754956457771

theorem tailTrace_802404 : CollatzResearch.WordTrace tailWord_802404 prefixEnd_802404 15259960410754956457771 := by
  unfold tailWord_802404
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633039092517411269011133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19510718790023215025348177 14633039092517411269011133)
  ·
    refine ⟨5487389659694029225879175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14633039092517411269011133 5487389659694029225879175)
    ·
      refine ⟨8231084489541043838818763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487389659694029225879175 8231084489541043838818763)
      ·
        refine ⟨12346626734311565758228145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231084489541043838818763 12346626734311565758228145)
        ·
          refine ⟨9259970050733674318671109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12346626734311565758228145 9259970050733674318671109)
          ·
            refine ⟨1736244384512563934750833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9259970050733674318671109 1736244384512563934750833)
            ·
              refine ⟨1302183288384422951063125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736244384512563934750833 1302183288384422951063125)
              ·
                refine ⟨15259960410754956457771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1302183288384422951063125 15259960410754956457771)
                ·
                  rfl

theorem cell23_802404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 8].length) (baseStart_802404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802404 prefixEnd_802404 := by exact prefixLift 802404
  have htrace : WordTrace (prefixWord ++ tailWord_802404) baseStart_802404 baseEnd_802404 := by
    simpa [prefixWord, tailWord_802404, baseEnd_802404] using wordTrace_append hprefix tailTrace_802404
  have hstable : (prefixWord ++ tailWord_802404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802404).length < 2 ^ (prefixWord ++ tailWord_802404).sum := by decide
  have hdescent : baseEnd_802404 < baseStart_802404 := by decide
  rcases family_descends (prefixWord ++ tailWord_802404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802408 : List Nat := [2, 1, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_802408 : Nat := 118140960795 + 802408 * 2 ^ 59
def prefixEnd_802408 : Nat := 4983230072969 + 3 ^ 40 * 802408 * 2
def baseEnd_802408 : Nat := 137340328337667269569933

theorem tailTrace_802408 : CollatzResearch.WordTrace tailWord_802408 prefixEnd_802408 137340328337667269569933 := by
  unfold tailWord_802408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633112038510165610583939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19510816051346887480778585 14633112038510165610583939)
  ·
    refine ⟨21949668057765248415875909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633112038510165610583939 21949668057765248415875909)
    ·
      refine ⟨4115562760830984077976733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21949668057765248415875909 4115562760830984077976733)
      ·
        refine ⟨1543336035311619029241275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4115562760830984077976733 1543336035311619029241275)
        ·
          refine ⟨2315004052967428543861913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1543336035311619029241275 2315004052967428543861913)
          ·
            refine ⟨1736253039725571407896435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315004052967428543861913 1736253039725571407896435)
            ·
              refine ⟨2604379559588357111844653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736253039725571407896435 2604379559588357111844653)
              ·
                refine ⟨976642334845633916941745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604379559588357111844653 976642334845633916941745)
                ·
                  refine ⟨732481751134225437706309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976642334845633916941745 732481751134225437706309)
                  ·
                    refine ⟨137340328337667269569933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732481751134225437706309 137340328337667269569933)
                    ·
                      rfl

theorem cell23_802408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_802408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802408 prefixEnd_802408 := by exact prefixLift 802408
  have htrace : WordTrace (prefixWord ++ tailWord_802408) baseStart_802408 baseEnd_802408 := by
    simpa [prefixWord, tailWord_802408, baseEnd_802408] using wordTrace_append hprefix tailTrace_802408
  have hstable : (prefixWord ++ tailWord_802408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802408).length < 2 ^ (prefixWord ++ tailWord_802408).sum := by decide
  have hdescent : baseEnd_802408 < baseStart_802408 := by decide
  rcases family_descends (prefixWord ++ tailWord_802408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802418 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_802418 : Nat := 118140960795 + 802418 * 2 ^ 59
def prefixEnd_802418 : Nat := 4983230072969 + 3 ^ 40 * 802418 * 2
def baseEnd_802418 : Nat := 412026119819546769584753

theorem tailTrace_802418 : CollatzResearch.WordTrace tailWord_802418 prefixEnd_802418 412026119819546769584753 := by
  unfold tailWord_802418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316647201746025732257977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19511059204656068619354605 7316647201746025732257977)
  ·
    refine ⟨5487485401309519299193483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316647201746025732257977 5487485401309519299193483)
    ·
      refine ⟨8231228101964278948790225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487485401309519299193483 8231228101964278948790225)
      ·
        refine ⟨6173421076473209211592669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8231228101964278948790225 6173421076473209211592669)
        ·
          refine ⟨2315032903677453454347251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6173421076473209211592669 2315032903677453454347251)
          ·
            refine ⟨3472549355516180181520877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315032903677453454347251 3472549355516180181520877)
            ·
              refine ⟨1302206008318567568070329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3472549355516180181520877 1302206008318567568070329)
              ·
                refine ⟨976654506238925676052747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302206008318567568070329 976654506238925676052747)
                ·
                  refine ⟨1464981759358388514079121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976654506238925676052747 1464981759358388514079121)
                  ·
                    refine ⟨1098736319518791385559341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1464981759358388514079121 1098736319518791385559341)
                    ·
                      refine ⟨412026119819546769584753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098736319518791385559341 412026119819546769584753)
                      ·
                        rfl

theorem cell23_802418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_802418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802418 prefixEnd_802418 := by exact prefixLift 802418
  have htrace : WordTrace (prefixWord ++ tailWord_802418) baseStart_802418 baseEnd_802418 := by
    simpa [prefixWord, tailWord_802418, baseEnd_802418] using wordTrace_append hprefix tailTrace_802418
  have hstable : (prefixWord ++ tailWord_802418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802418).length < 2 ^ (prefixWord ++ tailWord_802418).sum := by decide
  have hdescent : baseEnd_802418 < baseStart_802418 := by decide
  rcases family_descends (prefixWord ++ tailWord_802418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802464 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_802464 : Nat := 118140960795 + 802464 * 2 ^ 59
def prefixEnd_802464 : Nat := 4983230072969 + 3 ^ 40 * 802464 * 2
def baseEnd_802464 : Nat := 137349913309884529869847

theorem tailTrace_802464 : CollatzResearch.WordTrace tailWord_802464 prefixEnd_802464 137349913309884529869847 := by
  unfold tailWord_802464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14634133282408726392603223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19512177709878301856804297 14634133282408726392603223)
  ·
    refine ⟨21951199923613089588904835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14634133282408726392603223 21951199923613089588904835)
    ·
      refine ⟨32926799885419634383357253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21951199923613089588904835 32926799885419634383357253)
      ·
        refine ⟨6173774978516181446879485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32926799885419634383357253 6173774978516181446879485)
        ·
          refine ⟨2315165616943568042579807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6173774978516181446879485 2315165616943568042579807)
          ·
            refine ⟨3472748425415352063869711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315165616943568042579807 3472748425415352063869711)
            ·
              refine ⟨5209122638123028095804567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472748425415352063869711 5209122638123028095804567)
              ·
                refine ⟨7813683957184542143706851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209122638123028095804567 7813683957184542143706851)
                ·
                  refine ⟨11720525935776813215560277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813683957184542143706851 11720525935776813215560277)
                  ·
                    refine ⟨137349913309884529869847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11720525935776813215560277 137349913309884529869847)
                    ·
                      rfl

theorem cell23_802464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_802464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802464 prefixEnd_802464 := by exact prefixLift 802464
  have htrace : WordTrace (prefixWord ++ tailWord_802464) baseStart_802464 baseEnd_802464 := by
    simpa [prefixWord, tailWord_802464, baseEnd_802464] using wordTrace_append hprefix tailTrace_802464
  have hstable : (prefixWord ++ tailWord_802464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802464).length < 2 ^ (prefixWord ++ tailWord_802464).sum := by decide
  have hdescent : baseEnd_802464 < baseStart_802464 := by decide
  rcases family_descends (prefixWord ++ tailWord_802464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802492 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_802492 : Nat := 118140960795 + 802492 * 2 ^ 59
def prefixEnd_802492 : Nat := 4983230072969 + 3 ^ 40 * 802492 * 2
def baseEnd_802492 : Nat := 412064117387979480059413

theorem tailTrace_802492 : CollatzResearch.WordTrace tailWord_802492 prefixEnd_802492 412064117387979480059413 := by
  unfold tailWord_802492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14634643904358006783612865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19512858539144009044817153 14634643904358006783612865)
  ·
    refine ⟨10975982928268505087709649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14634643904358006783612865 10975982928268505087709649)
    ·
      refine ⟨8231987196201378815782237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10975982928268505087709649 8231987196201378815782237)
      ·
        refine ⟨3086995198575517055918339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8231987196201378815782237 3086995198575517055918339)
        ·
          refine ⟨4630492797863275583877509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086995198575517055918339 4630492797863275583877509)
          ·
            refine ⟨868217399599364171977033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4630492797863275583877509 868217399599364171977033)
            ·
              refine ⟨651163049699523128982775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868217399599364171977033 651163049699523128982775)
              ·
                refine ⟨976744574549284693474163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651163049699523128982775 976744574549284693474163)
                ·
                  refine ⟨1465116861823927040211245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976744574549284693474163 1465116861823927040211245)
                  ·
                    refine ⟨549418823183972640079217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465116861823927040211245 549418823183972640079217)
                    ·
                      refine ⟨412064117387979480059413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549418823183972640079217 412064117387979480059413)
                      ·
                        rfl

theorem cell23_802492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_802492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802492 prefixEnd_802492 := by exact prefixLift 802492
  have htrace : WordTrace (prefixWord ++ tailWord_802492) baseStart_802492 baseEnd_802492 := by
    simpa [prefixWord, tailWord_802492, baseEnd_802492] using wordTrace_append hprefix tailTrace_802492
  have hstable : (prefixWord ++ tailWord_802492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802492).length < 2 ^ (prefixWord ++ tailWord_802492).sum := by decide
  have hdescent : baseEnd_802492 < baseStart_802492 := by decide
  rcases family_descends (prefixWord ++ tailWord_802492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802521 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_802521 : Nat := 118140960795 + 802521 * 2 ^ 59
def prefixEnd_802521 : Nat := 4983230072969 + 3 ^ 40 * 802521 * 2
def baseEnd_802521 : Nat := 412079008326959866596779

theorem tailTrace_802521 : CollatzResearch.WordTrace tailWord_802521 prefixEnd_802521 412079008326959866596779 := by
  unfold tailWord_802521
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270345525610951520031417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19513563683740634346687611 29270345525610951520031417)
  ·
    refine ⟨21952759144208213640023563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29270345525610951520031417 21952759144208213640023563)
    ·
      refine ⟨32929138716312320460035345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21952759144208213640023563 32929138716312320460035345)
      ·
        refine ⟨24696854037234240345026509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32929138716312320460035345 24696854037234240345026509)
        ·
          refine ⟨9261320263962840129384941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24696854037234240345026509 9261320263962840129384941)
          ·
            refine ⟨3472995098986065048519353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9261320263962840129384941 3472995098986065048519353)
            ·
              refine ⟨2604746324239548786389515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472995098986065048519353 2604746324239548786389515)
              ·
                refine ⟨3907119486359323179584273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604746324239548786389515 3907119486359323179584273)
                ·
                  refine ⟨2930339614769492384688205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3907119486359323179584273 2930339614769492384688205)
                  ·
                    refine ⟨1098877355538559644258077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2930339614769492384688205 1098877355538559644258077)
                    ·
                      refine ⟨412079008326959866596779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1098877355538559644258077 412079008326959866596779)
                      ·
                        rfl

theorem cell23_802521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_802521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802521 prefixEnd_802521 := by exact prefixLift 802521
  have htrace : WordTrace (prefixWord ++ tailWord_802521) baseStart_802521 baseEnd_802521 := by
    simpa [prefixWord, tailWord_802521, baseEnd_802521] using wordTrace_append hprefix tailTrace_802521
  have hstable : (prefixWord ++ tailWord_802521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802521).length < 2 ^ (prefixWord ++ tailWord_802521).sum := by decide
  have hdescent : baseEnd_802521 < baseStart_802521 := by decide
  rcases family_descends (prefixWord ++ tailWord_802521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802522 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2]
def baseStart_802522 : Nat := 118140960795 + 802522 * 2 ^ 59
def prefixEnd_802522 : Nat := 4983230072969 + 3 ^ 40 * 802522 * 2
def baseEnd_802522 : Nat := 412079521807614362684275

theorem tailTrace_802522 : CollatzResearch.WordTrace tailWord_802522 prefixEnd_802522 412079521807614362684275 := by
  unfold tailWord_802522
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317595499651832172704455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19513587999071552460545213 7317595499651832172704455)
  ·
    refine ⟨10976393249477748259056683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7317595499651832172704455 10976393249477748259056683)
    ·
      refine ⟨16464589874216622388585025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10976393249477748259056683 16464589874216622388585025)
      ·
        refine ⟨12348442405662466791438769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16464589874216622388585025 12348442405662466791438769)
        ·
          refine ⟨9261331804246850093579077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12348442405662466791438769 9261331804246850093579077)
          ·
            refine ⟨1736499713296284392546077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9261331804246850093579077 1736499713296284392546077)
            ·
              refine ⟨651187392486106647204779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1736499713296284392546077 651187392486106647204779)
              ·
                refine ⟨976781088729159970807169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651187392486106647204779 976781088729159970807169)
                ·
                  refine ⟨732585816546869978105377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976781088729159970807169 732585816546869978105377)
                  ·
                    refine ⟨549439362410152483579033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 732585816546869978105377 549439362410152483579033)
                    ·
                      refine ⟨412079521807614362684275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549439362410152483579033 412079521807614362684275)
                      ·
                        rfl

theorem cell23_802522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_802522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802522 prefixEnd_802522 := by exact prefixLift 802522
  have htrace : WordTrace (prefixWord ++ tailWord_802522) baseStart_802522 baseEnd_802522 := by
    simpa [prefixWord, tailWord_802522, baseEnd_802522] using wordTrace_append hprefix tailTrace_802522
  have hstable : (prefixWord ++ tailWord_802522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802522).length < 2 ^ (prefixWord ++ tailWord_802522).sum := by decide
  have hdescent : baseEnd_802522 < baseStart_802522 := by decide
  rcases family_descends (prefixWord ++ tailWord_802522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802541 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_802541 : Nat := 118140960795 + 802541 * 2 ^ 59
def prefixEnd_802541 : Nat := 4983230072969 + 3 ^ 40 * 802541 * 2
def baseEnd_802541 : Nat := 137363092646683262782229

theorem tailTrace_802541 : CollatzResearch.WordTrace tailWord_802541 prefixEnd_802541 137363092646683262782229 := by
  unfold tailWord_802541
  simp only [CollatzResearch.WordTrace]
  refine ⟨29271074985538494935759477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19514049990358996623839651 29271074985538494935759477)
  ·
    refine ⟨2744163279894233900227451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29271074985538494935759477 2744163279894233900227451)
    ·
      refine ⟨4116244919841350850341177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744163279894233900227451 4116244919841350850341177)
      ·
        refine ⟨3087183689881013137755883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116244919841350850341177 3087183689881013137755883)
        ·
          refine ⟨4630775534821519706633825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087183689881013137755883 4630775534821519706633825)
          ·
            refine ⟨3473081651116139779975369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4630775534821519706633825 3473081651116139779975369)
            ·
              refine ⟨2604811238337104834981527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473081651116139779975369 2604811238337104834981527)
              ·
                refine ⟨3907216857505657252472291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604811238337104834981527 3907216857505657252472291)
                ·
                  refine ⟨5860825286258485878708437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907216857505657252472291 5860825286258485878708437)
                  ·
                    refine ⟨137363092646683262782229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5860825286258485878708437 137363092646683262782229)
                    ·
                      rfl

theorem cell23_802541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_802541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802541 prefixEnd_802541 := by exact prefixLift 802541
  have htrace : WordTrace (prefixWord ++ tailWord_802541) baseStart_802541 baseEnd_802541 := by
    simpa [prefixWord, tailWord_802541, baseEnd_802541] using wordTrace_append hprefix tailTrace_802541
  have hstable : (prefixWord ++ tailWord_802541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802541).length < 2 ^ (prefixWord ++ tailWord_802541).sum := by decide
  have hdescent : baseEnd_802541 < baseStart_802541 := by decide
  rcases family_descends (prefixWord ++ tailWord_802541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802561 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_802561 : Nat := 118140960795 + 802561 * 2 ^ 59
def prefixEnd_802561 : Nat := 4983230072969 + 3 ^ 40 * 802561 * 2
def baseEnd_802561 : Nat := 412099547553139710096595

theorem tailTrace_802561 : CollatzResearch.WordTrace tailWord_802561 prefixEnd_802561 412099547553139710096595 := by
  unfold tailWord_802561
  simp only [CollatzResearch.WordTrace]
  refine ⟨29271804445466038351487537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19514536296977358900991691 29271804445466038351487537)
  ·
    refine ⟨21953853334099528763615653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29271804445466038351487537 21953853334099528763615653)
    ·
      refine ⟨4116347500143661643177935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21953853334099528763615653 4116347500143661643177935)
      ·
        refine ⟨6174521250215492464766903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116347500143661643177935 6174521250215492464766903)
        ·
          refine ⟨9261781875323238697150355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174521250215492464766903 9261781875323238697150355)
          ·
            refine ⟨13892672812984858045725533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9261781875323238697150355 13892672812984858045725533)
            ·
              refine ⟨5209752304869321767147075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13892672812984858045725533 5209752304869321767147075)
              ·
                refine ⟨7814628457303982650720613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209752304869321767147075 7814628457303982650720613)
                ·
                  refine ⟨1465242835744496747010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7814628457303982650720613 1465242835744496747010115)
                  ·
                    refine ⟨2197864253616745120515173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1465242835744496747010115 2197864253616745120515173)
                    ·
                      refine ⟨412099547553139710096595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2197864253616745120515173 412099547553139710096595)
                      ·
                        rfl

theorem cell23_802561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_802561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802561 prefixEnd_802561 := by exact prefixLift 802561
  have htrace : WordTrace (prefixWord ++ tailWord_802561) baseStart_802561 baseEnd_802561 := by
    simpa [prefixWord, tailWord_802561, baseEnd_802561] using wordTrace_append hprefix tailTrace_802561
  have hstable : (prefixWord ++ tailWord_802561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802561).length < 2 ^ (prefixWord ++ tailWord_802561).sum := by decide
  have hdescent : baseEnd_802561 < baseStart_802561 := by decide
  rcases family_descends (prefixWord ++ tailWord_802561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802573 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_802573 : Nat := 118140960795 + 802573 * 2 ^ 59
def prefixEnd_802573 : Nat := 4983230072969 + 3 ^ 40 * 802573 * 2
def baseEnd_802573 : Nat := 412105709320993663146541

theorem tailTrace_802573 : CollatzResearch.WordTrace tailWord_802573 prefixEnd_802573 412105709320993663146541 := by
  unfold tailWord_802573
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272242121422564400924373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19514828080948376267282915 29272242121422564400924373)
  ·
    refine ⟨686068174720841353146665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29272242121422564400924373 686068174720841353146665)
    ·
      refine ⟨514551131040631014859999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 686068174720841353146665 514551131040631014859999)
      ·
        refine ⟨771826696560946522289999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514551131040631014859999 771826696560946522289999)
        ·
          refine ⟨1157740044841419783434999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771826696560946522289999 1157740044841419783434999)
          ·
            refine ⟨1736610067262129675152499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157740044841419783434999 1736610067262129675152499)
            ·
              refine ⟨2604915100893194512728749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736610067262129675152499 2604915100893194512728749)
              ·
                refine ⟨976843162834947942273281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2604915100893194512728749 976843162834947942273281)
                ·
                  refine ⟨732632372126210956704961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 976843162834947942273281 732632372126210956704961)
                  ·
                    refine ⟨549474279094658217528721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 732632372126210956704961 549474279094658217528721)
                    ·
                      refine ⟨412105709320993663146541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549474279094658217528721 412105709320993663146541)
                      ·
                        rfl

theorem cell23_802573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_802573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802573 prefixEnd_802573 := by exact prefixLift 802573
  have htrace : WordTrace (prefixWord ++ tailWord_802573) baseStart_802573 baseEnd_802573 := by
    simpa [prefixWord, tailWord_802573, baseEnd_802573] using wordTrace_append hprefix tailTrace_802573
  have hstable : (prefixWord ++ tailWord_802573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802573).length < 2 ^ (prefixWord ++ tailWord_802573).sum := by decide
  have hdescent : baseEnd_802573 < baseStart_802573 := by decide
  rcases family_descends (prefixWord ++ tailWord_802573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802618 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_802618 : Nat := 118140960795 + 802618 * 2 ^ 59
def prefixEnd_802618 : Nat := 4983230072969 + 3 ^ 40 * 802618 * 2
def baseEnd_802618 : Nat := 45792090661160665231537

theorem tailTrace_802618 : CollatzResearch.WordTrace tailWord_802618 prefixEnd_802618 45792090661160665231537 := by
  unfold tailWord_802618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318470851564884271578127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19515922270839691390875005 7318470851564884271578127)
  ·
    refine ⟨10977706277347326407367191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318470851564884271578127 10977706277347326407367191)
    ·
      refine ⟨16466559416020989611050787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10977706277347326407367191 16466559416020989611050787)
      ·
        refine ⟨24699839124031484416576181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16466559416020989611050787 24699839124031484416576181)
        ·
          refine ⟨2315609917877951664054017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24699839124031484416576181 2315609917877951664054017)
          ·
            refine ⟨1736707438408463748040513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315609917877951664054017 1736707438408463748040513)
            ·
              refine ⟨1302530578806347811030385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1736707438408463748040513 1302530578806347811030385)
              ·
                refine ⟨976897934104760858272789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302530578806347811030385 976897934104760858272789)
                ·
                  refine ⟨45792090661160665231537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 976897934104760858272789 45792090661160665231537)
                  ·
                    rfl

theorem cell23_802618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_802618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802618 prefixEnd_802618 := by exact prefixLift 802618
  have htrace : WordTrace (prefixWord ++ tailWord_802618) baseStart_802618 baseEnd_802618 := by
    simpa [prefixWord, tailWord_802618, baseEnd_802618] using wordTrace_append hprefix tailTrace_802618
  have hstable : (prefixWord ++ tailWord_802618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802618).length < 2 ^ (prefixWord ++ tailWord_802618).sum := by decide
  have hdescent : baseEnd_802618 < baseStart_802618 := by decide
  rcases family_descends (prefixWord ++ tailWord_802618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802622 : List Nat := [4, 2, 1, 2, 2, 2, 1, 4, 1, 4]
def baseStart_802622 : Nat := 118140960795 + 802622 * 2 ^ 59
def prefixEnd_802622 : Nat := 4983230072969 + 3 ^ 40 * 802622 * 2
def baseEnd_802622 : Nat := 137376956624354657144605

theorem tailTrace_802622 : CollatzResearch.WordTrace tailWord_802622 prefixEnd_802622 137376956624354657144605 := by
  unfold tailWord_802622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659253662280630721182265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19516019532163363846305413 3659253662280630721182265)
  ·
    refine ⟨2744440246710473040886699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3659253662280630721182265 2744440246710473040886699)
    ·
      refine ⟨4116660370065709561330049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744440246710473040886699 4116660370065709561330049)
      ·
        refine ⟨3087495277549282170997537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116660370065709561330049 3087495277549282170997537)
        ·
          refine ⟨2315621458161961628248153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087495277549282170997537 2315621458161961628248153)
          ·
            refine ⟨1736716093621471221186115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2315621458161961628248153 1736716093621471221186115)
            ·
              refine ⟨2605074140432206831779173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736716093621471221186115 2605074140432206831779173)
              ·
                refine ⟨488451401331038780958595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2605074140432206831779173 488451401331038780958595)
                ·
                  refine ⟨732677101996558171437893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488451401331038780958595 732677101996558171437893)
                  ·
                    refine ⟨137376956624354657144605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732677101996558171437893 137376956624354657144605)
                    ·
                      rfl

theorem cell23_802622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_802622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802622 prefixEnd_802622 := by exact prefixLift 802622
  have htrace : WordTrace (prefixWord ++ tailWord_802622) baseStart_802622 baseEnd_802622 := by
    simpa [prefixWord, tailWord_802622, baseEnd_802622] using wordTrace_append hprefix tailTrace_802622
  have hstable : (prefixWord ++ tailWord_802622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802622).length < 2 ^ (prefixWord ++ tailWord_802622).sum := by decide
  have hdescent : baseEnd_802622 < baseStart_802622 := by decide
  rcases family_descends (prefixWord ++ tailWord_802622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802631 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 3, 5]
def baseStart_802631 : Nat := 118140960795 + 802631 * 2 ^ 59
def prefixEnd_802631 : Nat := 4983230072969 + 3 ^ 40 * 802631 * 2
def baseEnd_802631 : Nat := 137378497066318145407091

theorem tailTrace_802631 : CollatzResearch.WordTrace tailWord_802631 prefixEnd_802631 137378497066318145407091 := by
  unfold tailWord_802631
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274357555212440306535747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19516238370141626871023831 29274357555212440306535747)
  ·
    refine ⟨43911536332818660459803621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29274357555212440306535747 43911536332818660459803621)
    ·
      refine ⟨8233413062403498836213179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43911536332818660459803621 8233413062403498836213179)
      ·
        refine ⟨12350119593605248254319769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233413062403498836213179 12350119593605248254319769)
        ·
          refine ⟨9262589695203936190739827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12350119593605248254319769 9262589695203936190739827)
          ·
            refine ⟨13893884542805904286109741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262589695203936190739827 13893884542805904286109741)
            ·
              refine ⟨5210206703552214107291153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13893884542805904286109741 5210206703552214107291153)
              ·
                refine ⟨3907655027664160580468365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210206703552214107291153 3907655027664160580468365)
                ·
                  refine ⟨1465370635374060217675637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3907655027664160580468365 1465370635374060217675637)
                  ·
                    refine ⟨137378497066318145407091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1465370635374060217675637 137378497066318145407091)
                    ·
                      rfl

theorem cell23_802631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_802631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802631 prefixEnd_802631 := by exact prefixLift 802631
  have htrace : WordTrace (prefixWord ++ tailWord_802631) baseStart_802631 baseEnd_802631 := by
    simpa [prefixWord, tailWord_802631, baseEnd_802631] using wordTrace_append hprefix tailTrace_802631
  have hstable : (prefixWord ++ tailWord_802631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802631).length < 2 ^ (prefixWord ++ tailWord_802631).sum := by decide
  have hdescent : baseEnd_802631 < baseStart_802631 := by decide
  rcases family_descends (prefixWord ++ tailWord_802631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802645 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 3]
def baseStart_802645 : Nat := 118140960795 + 802645 * 2 ^ 59
def prefixEnd_802645 : Nat := 4983230072969 + 3 ^ 40 * 802645 * 2
def baseEnd_802645 : Nat := 412142679928117381446209

theorem tailTrace_802645 : CollatzResearch.WordTrace tailWord_802645 prefixEnd_802645 412142679928117381446209 := by
  unfold tailWord_802645
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274868177161720697545389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19516578784774480465030259 29274868177161720697545389)
  ·
    refine ⟨10978075566435645261579521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29274868177161720697545389 10978075566435645261579521)
    ·
      refine ⟨8233556674826733946184641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10978075566435645261579521 8233556674826733946184641)
      ·
        refine ⟨6175167506120050459638481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8233556674826733946184641 6175167506120050459638481)
        ·
          refine ⟨4631375629590037844728861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175167506120050459638481 4631375629590037844728861)
          ·
            refine ⟨1736765861096264191773323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4631375629590037844728861 1736765861096264191773323)
            ·
              refine ⟨2605148791644396287659985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736765861096264191773323 2605148791644396287659985)
              ·
                refine ⟨1953861593733297215744989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605148791644396287659985 1953861593733297215744989)
                ·
                  refine ⟨732698097649986455904371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1953861593733297215744989 732698097649986455904371)
                  ·
                    refine ⟨1099047146474979683856557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732698097649986455904371 1099047146474979683856557)
                    ·
                      refine ⟨412142679928117381446209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1099047146474979683856557 412142679928117381446209)
                      ·
                        rfl

theorem cell23_802645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_802645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802645 prefixEnd_802645 := by exact prefixLift 802645
  have htrace : WordTrace (prefixWord ++ tailWord_802645) baseStart_802645 baseEnd_802645 := by
    simpa [prefixWord, tailWord_802645, baseEnd_802645] using wordTrace_append hprefix tailTrace_802645
  have hstable : (prefixWord ++ tailWord_802645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802645).length < 2 ^ (prefixWord ++ tailWord_802645).sum := by decide
  have hdescent : baseEnd_802645 < baseStart_802645 := by decide
  rcases family_descends (prefixWord ++ tailWord_802645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802655 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 2, 3, 2]
def baseStart_802655 : Nat := 118140960795 + 802655 * 2 ^ 59
def prefixEnd_802655 : Nat := 4983230072969 + 3 ^ 40 * 802655 * 2
def baseEnd_802655 : Nat := 412147814734662342321163

theorem tailTrace_802655 : CollatzResearch.WordTrace tailWord_802655 prefixEnd_802655 412147814734662342321163 := by
  unfold tailWord_802655
  simp only [CollatzResearch.WordTrace]
  refine ⟨29275232907125492405409419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19516821938083661603606279 29275232907125492405409419)
  ·
    refine ⟨43912849360688238608114129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29275232907125492405409419 43912849360688238608114129)
    ·
      refine ⟨32934637020516178956085597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43912849360688238608114129 32934637020516178956085597)
      ·
        refine ⟨12350488882693567108532099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32934637020516178956085597 12350488882693567108532099)
        ·
          refine ⟨18525733324040350662798149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12350488882693567108532099 18525733324040350662798149)
          ·
            refine ⟨3473574998257565749274653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18525733324040350662798149 3473574998257565749274653)
            ·
              refine ⟨1302590624346587155977995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3473574998257565749274653 1302590624346587155977995)
              ·
                refine ⟨1953885936519880733966993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302590624346587155977995 1953885936519880733966993)
                ·
                  refine ⟨1465414452389910550475245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953885936519880733966993 1465414452389910550475245)
                  ·
                    refine ⟨549530419646216456428217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465414452389910550475245 549530419646216456428217)
                    ·
                      refine ⟨412147814734662342321163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549530419646216456428217 412147814734662342321163)
                      ·
                        rfl

theorem cell23_802655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 2, 3, 2].length) (baseStart_802655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802655 prefixEnd_802655 := by exact prefixLift 802655
  have htrace : WordTrace (prefixWord ++ tailWord_802655) baseStart_802655 baseEnd_802655 := by
    simpa [prefixWord, tailWord_802655, baseEnd_802655] using wordTrace_append hprefix tailTrace_802655
  have hstable : (prefixWord ++ tailWord_802655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802655).length < 2 ^ (prefixWord ++ tailWord_802655).sum := by decide
  have hdescent : baseEnd_802655 < baseStart_802655 := by decide
  rcases family_descends (prefixWord ++ tailWord_802655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802681 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_802681 : Nat := 118140960795 + 802681 * 2 ^ 59
def prefixEnd_802681 : Nat := 4983230072969 + 3 ^ 40 * 802681 * 2
def baseEnd_802681 : Nat := 412161165231679240596043

theorem tailTrace_802681 : CollatzResearch.WordTrace tailWord_802681 prefixEnd_802681 412161165231679240596043 := by
  unfold tailWord_802681
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276181205031298845855897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19517454136687532563903931 29276181205031298845855897)
  ·
    refine ⟨21957135903773474134391923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29276181205031298845855897 21957135903773474134391923)
    ·
      refine ⟨32935703855660211201587885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21957135903773474134391923 32935703855660211201587885)
      ·
        refine ⟨12350888945872579200595457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32935703855660211201587885 12350888945872579200595457)
        ·
          refine ⟨9263166709404434400446593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12350888945872579200595457 9263166709404434400446593)
          ·
            refine ⟨6947375032053325800334945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9263166709404434400446593 6947375032053325800334945)
            ·
              refine ⟨5210531274039994350251209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947375032053325800334945 5210531274039994350251209)
              ·
                refine ⟨3907898455529995762688407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210531274039994350251209 3907898455529995762688407)
                ·
                  refine ⟨5861847683294993644032611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907898455529995762688407 5861847683294993644032611)
                  ·
                    refine ⟨8792771524942490466048917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861847683294993644032611 8792771524942490466048917)
                    ·
                      refine ⟨412161165231679240596043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 8792771524942490466048917 412161165231679240596043)
                      ·
                        rfl

theorem cell23_802681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_802681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802681 prefixEnd_802681 := by exact prefixLift 802681
  have htrace : WordTrace (prefixWord ++ tailWord_802681) baseStart_802681 baseEnd_802681 := by
    simpa [prefixWord, tailWord_802681, baseEnd_802681] using wordTrace_append hprefix tailTrace_802681
  have hstable : (prefixWord ++ tailWord_802681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802681).length < 2 ^ (prefixWord ++ tailWord_802681).sum := by decide
  have hdescent : baseEnd_802681 < baseStart_802681 := by decide
  rcases family_descends (prefixWord ++ tailWord_802681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802695 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 6]
def baseStart_802695 : Nat := 118140960795 + 802695 * 2 ^ 59
def prefixEnd_802695 : Nat := 4983230072969 + 3 ^ 40 * 802695 * 2
def baseEnd_802695 : Nat := 137389451320280728606993

theorem tailTrace_802695 : CollatzResearch.WordTrace tailWord_802695 prefixEnd_802695 137389451320280728606993 := by
  unfold tailWord_802695
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276691826980579236865539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19517794551320386157910359 29276691826980579236865539)
  ·
    refine ⟨43915037740470868855298309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29276691826980579236865539 43915037740470868855298309)
    ·
      refine ⟨8234069576338287910368433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43915037740470868855298309 8234069576338287910368433)
      ·
        refine ⟨6175552182253715932776325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234069576338287910368433 6175552182253715932776325)
        ·
          refine ⟨1157916034172571737395561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6175552182253715932776325 1157916034172571737395561)
          ·
            refine ⟨868437025629428803046671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1157916034172571737395561 868437025629428803046671)
            ·
              refine ⟨1302655538444143204570007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868437025629428803046671 1302655538444143204570007)
              ·
                refine ⟨1953983307666214806855011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302655538444143204570007 1953983307666214806855011)
                ·
                  refine ⟨2930974961499322210282517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953983307666214806855011 2930974961499322210282517)
                  ·
                    refine ⟨137389451320280728606993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2930974961499322210282517 137389451320280728606993)
                    ·
                      rfl

theorem cell23_802695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_802695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802695 prefixEnd_802695 := by exact prefixLift 802695
  have htrace : WordTrace (prefixWord ++ tailWord_802695) baseStart_802695 baseEnd_802695 := by
    simpa [prefixWord, tailWord_802695, baseEnd_802695] using wordTrace_append hprefix tailTrace_802695
  have hstable : (prefixWord ++ tailWord_802695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802695).length < 2 ^ (prefixWord ++ tailWord_802695).sum := by decide
  have hdescent : baseEnd_802695 < baseStart_802695 := by decide
  rcases family_descends (prefixWord ++ tailWord_802695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802708 : List Nat := [2, 4, 2, 1, 1, 3, 1, 9]
def baseStart_802708 : Nat := 118140960795 + 802708 * 2 ^ 59
def prefixEnd_802708 : Nat := 4983230072969 + 3 ^ 40 * 802708 * 2
def baseEnd_802708 : Nat := 15265741822568542035497

theorem tailTrace_802708 : CollatzResearch.WordTrace tailWord_802708 prefixEnd_802708 15265741822568542035497 := by
  unfold tailWord_802708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638582987966741228544389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19518110650622321638059185 14638582987966741228544389)
  ·
    refine ⟨2744734310243763980352073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14638582987966741228544389 2744734310243763980352073)
    ·
      refine ⟨2058550732682822985264055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744734310243763980352073 2058550732682822985264055)
      ·
        refine ⟨3087826099024234477896083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058550732682822985264055 3087826099024234477896083)
        ·
          refine ⟨4631739148536351716844125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087826099024234477896083 4631739148536351716844125)
          ·
            refine ⟨1736902180701131893816547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4631739148536351716844125 1736902180701131893816547)
            ·
              refine ⟨2605353271051697840724821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736902180701131893816547 2605353271051697840724821)
              ·
                refine ⟨15265741822568542035497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2605353271051697840724821 15265741822568542035497)
                ·
                  rfl

theorem cell23_802708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 9].length) (baseStart_802708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802708 prefixEnd_802708 := by exact prefixLift 802708
  have htrace : WordTrace (prefixWord ++ tailWord_802708) baseStart_802708 baseEnd_802708 := by
    simpa [prefixWord, tailWord_802708, baseEnd_802708] using wordTrace_append hprefix tailTrace_802708
  have hstable : (prefixWord ++ tailWord_802708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802708).length < 2 ^ (prefixWord ++ tailWord_802708).sum := by decide
  have hdescent : baseEnd_802708 < baseStart_802708 := by decide
  rcases family_descends (prefixWord ++ tailWord_802708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802735 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 3]
def baseStart_802735 : Nat := 118140960795 + 802735 * 2 ^ 59
def prefixEnd_802735 : Nat := 4983230072969 + 3 ^ 40 * 802735 * 2
def baseEnd_802735 : Nat := 412188893187022029320795

theorem tailTrace_802735 : CollatzResearch.WordTrace tailWord_802735 prefixEnd_802735 412188893187022029320795 := by
  unfold tailWord_802735
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278150746835666068321659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19518767164557110712214439 29278150746835666068321659)
  ·
    refine ⟨43917226120253499102482489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29278150746835666068321659 43917226120253499102482489)
    ·
      refine ⟨32937919590190124326861867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43917226120253499102482489 32937919590190124326861867)
      ·
        refine ⟨49406879385285186490292801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32937919590190124326861867 49406879385285186490292801)
        ·
          refine ⟨37055159538963889867719601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49406879385285186490292801 37055159538963889867719601)
          ·
            refine ⟨27791369654222917400789701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37055159538963889867719601 27791369654222917400789701)
            ·
              refine ⟨5210881810166797012648069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27791369654222917400789701 5210881810166797012648069)
              ·
                refine ⟨977040339406274439871513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5210881810166797012648069 977040339406274439871513)
                ·
                  refine ⟨732780254554705829903635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 977040339406274439871513 732780254554705829903635)
                  ·
                    refine ⟨1099170381832058744855453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732780254554705829903635 1099170381832058744855453)
                    ·
                      refine ⟨412188893187022029320795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1099170381832058744855453 412188893187022029320795)
                      ·
                        rfl

theorem cell23_802735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 1, 3].length) (baseStart_802735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802735 prefixEnd_802735 := by exact prefixLift 802735
  have htrace : WordTrace (prefixWord ++ tailWord_802735) baseStart_802735 baseEnd_802735 := by
    simpa [prefixWord, tailWord_802735, baseEnd_802735] using wordTrace_append hprefix tailTrace_802735
  have hstable : (prefixWord ++ tailWord_802735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802735).length < 2 ^ (prefixWord ++ tailWord_802735).sum := by decide
  have hdescent : baseEnd_802735 < baseStart_802735 := by decide
  rcases family_descends (prefixWord ++ tailWord_802735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802745 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 3, 3, 2]
def baseStart_802745 : Nat := 118140960795 + 802745 * 2 ^ 59
def prefixEnd_802745 : Nat := 4983230072969 + 3 ^ 40 * 802745 * 2
def baseEnd_802745 : Nat := 412194027993566990195749

theorem tailTrace_802745 : CollatzResearch.WordTrace tailWord_802745 prefixEnd_802745 412194027993566990195749 := by
  unfold tailWord_802745
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278515476799437776185689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19519010317866291850790459 29278515476799437776185689)
  ·
    refine ⟨21958886607599578332139267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29278515476799437776185689 21958886607599578332139267)
    ·
      refine ⟨32938329911399367498208901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21958886607599578332139267 32938329911399367498208901)
      ·
        refine ⟨6175936858387381405914169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32938329911399367498208901 6175936858387381405914169)
        ·
          refine ⟨4631952643790536054435627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175936858387381405914169 4631952643790536054435627)
          ·
            refine ⟨6947928965685804081653441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631952643790536054435627 6947928965685804081653441)
            ·
              refine ⟨5210946724264353061240081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947928965685804081653441 5210946724264353061240081)
              ·
                refine ⟨3908210043198264795930061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210946724264353061240081 3908210043198264795930061)
                ·
                  refine ⟨1465578766199349298473773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3908210043198264795930061 1465578766199349298473773)
                  ·
                    refine ⟨549592037324755986927665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465578766199349298473773 549592037324755986927665)
                    ·
                      refine ⟨412194027993566990195749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549592037324755986927665 412194027993566990195749)
                      ·
                        rfl

theorem cell23_802745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_802745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802745 prefixEnd_802745 := by exact prefixLift 802745
  have htrace : WordTrace (prefixWord ++ tailWord_802745) baseStart_802745 baseEnd_802745 := by
    simpa [prefixWord, tailWord_802745, baseEnd_802745] using wordTrace_append hprefix tailTrace_802745
  have hstable : (prefixWord ++ tailWord_802745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802745).length < 2 ^ (prefixWord ++ tailWord_802745).sum := by decide
  have hdescent : baseEnd_802745 < baseStart_802745 := by decide
  rcases family_descends (prefixWord ++ tailWord_802745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802751 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 8]
def baseStart_802751 : Nat := 118140960795 + 802751 * 2 ^ 59
def prefixEnd_802751 : Nat := 4983230072969 + 3 ^ 40 * 802751 * 2
def baseEnd_802751 : Nat := 137399036292497988906907

theorem tailTrace_802751 : CollatzResearch.WordTrace tailWord_802751 prefixEnd_802751 137399036292497988906907 := by
  unfold tailWord_802751
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278734314777700800904107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19519156209851800533936071 29278734314777700800904107)
  ·
    refine ⟨43918101472166551201356161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29278734314777700800904107 43918101472166551201356161)
    ·
      refine ⟨32938576104124913401017121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43918101472166551201356161 32938576104124913401017121)
      ·
        refine ⟨24703932078093685050762841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32938576104124913401017121 24703932078093685050762841)
        ·
          refine ⟨18527949058570263788072131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24703932078093685050762841 18527949058570263788072131)
          ·
            refine ⟨27791923587855395682108197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527949058570263788072131 27791923587855395682108197)
            ·
              refine ⟨5210985672722886690395287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27791923587855395682108197 5210985672722886690395287)
              ·
                refine ⟨7816478509084330035592931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210985672722886690395287 7816478509084330035592931)
                ·
                  refine ⟨11724717763626495053389397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7816478509084330035592931 11724717763626495053389397)
                  ·
                    refine ⟨137399036292497988906907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11724717763626495053389397 137399036292497988906907)
                    ·
                      rfl

theorem cell23_802751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_802751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802751 prefixEnd_802751 := by exact prefixLift 802751
  have htrace : WordTrace (prefixWord ++ tailWord_802751) baseStart_802751 baseEnd_802751 := by
    simpa [prefixWord, tailWord_802751, baseEnd_802751] using wordTrace_append hprefix tailTrace_802751
  have hstable : (prefixWord ++ tailWord_802751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802751).length < 2 ^ (prefixWord ++ tailWord_802751).sum := by decide
  have hdescent : baseEnd_802751 < baseStart_802751 := by decide
  rcases family_descends (prefixWord ++ tailWord_802751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802761 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_802761 : Nat := 118140960795 + 802761 * 2 ^ 59
def prefixEnd_802761 : Nat := 4983230072969 + 3 ^ 40 * 802761 * 2
def baseEnd_802761 : Nat := 412202243684038927595675

theorem tailTrace_802761 : CollatzResearch.WordTrace tailWord_802761 prefixEnd_802761 412202243684038927595675 := by
  unfold tailWord_802761
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279099044741472508768137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19519399363160981672512091 29279099044741472508768137)
  ·
    refine ⟨21959324283556104381576103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29279099044741472508768137 21959324283556104381576103)
    ·
      refine ⟨32938986425334156572364155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21959324283556104381576103 32938986425334156572364155)
      ·
        refine ⟨49408479638001234858546233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32938986425334156572364155 49408479638001234858546233)
        ·
          refine ⟨37056359728500926143909675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49408479638001234858546233 37056359728500926143909675)
          ·
            refine ⟨55584539592751389215864513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37056359728500926143909675 55584539592751389215864513)
            ·
              refine ⟨41688404694563541911898385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55584539592751389215864513 41688404694563541911898385)
              ·
                refine ⟨31266303520922656433923789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41688404694563541911898385 31266303520922656433923789)
                ·
                  refine ⟨11724863820345996162721421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31266303520922656433923789 11724863820345996162721421)
                  ·
                    refine ⟨4396823932629748561020533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11724863820345996162721421 4396823932629748561020533)
                    ·
                      refine ⟨412202243684038927595675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4396823932629748561020533 412202243684038927595675)
                      ·
                        rfl

theorem cell23_802761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_802761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802761 prefixEnd_802761 := by exact prefixLift 802761
  have htrace : WordTrace (prefixWord ++ tailWord_802761) baseStart_802761 baseEnd_802761 := by
    simpa [prefixWord, tailWord_802761, baseEnd_802761] using wordTrace_append hprefix tailTrace_802761
  have hstable : (prefixWord ++ tailWord_802761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802761).length < 2 ^ (prefixWord ++ tailWord_802761).sum := by decide
  have hdescent : baseEnd_802761 < baseStart_802761 := by decide
  rcases family_descends (prefixWord ++ tailWord_802761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802762 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2]
def baseStart_802762 : Nat := 118140960795 + 802762 * 2 ^ 59
def prefixEnd_802762 : Nat := 4983230072969 + 3 ^ 40 * 802762 * 2
def baseEnd_802762 : Nat := 412202757164693423683171

theorem tailTrace_802762 : CollatzResearch.WordTrace tailWord_802762 prefixEnd_802762 412202757164693423683171 := by
  unfold tailWord_802762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319783879434462419888635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19519423678491899786369693 7319783879434462419888635)
  ·
    refine ⟨10979675819151693629832953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319783879434462419888635 10979675819151693629832953)
    ·
      refine ⟨8234756864363770222374715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10979675819151693629832953 8234756864363770222374715)
      ·
        refine ⟨12352135296545655333562073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234756864363770222374715 12352135296545655333562073)
        ·
          refine ⟨9264101472409241500171555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12352135296545655333562073 9264101472409241500171555)
          ·
            refine ⟨13896152208613862250257333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264101472409241500171555 13896152208613862250257333)
            ·
              refine ⟨1302764269557549585961625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13896152208613862250257333 1302764269557549585961625)
              ·
                refine ⟨977073202168162189471219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302764269557549585961625 977073202168162189471219)
                ·
                  refine ⟨1465609803252243284206829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977073202168162189471219 1465609803252243284206829)
                  ·
                    refine ⟨549603676219591231577561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465609803252243284206829 549603676219591231577561)
                    ·
                      refine ⟨412202757164693423683171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549603676219591231577561 412202757164693423683171)
                      ·
                        rfl

theorem cell23_802762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_802762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802762 prefixEnd_802762 := by exact prefixLift 802762
  have htrace : WordTrace (prefixWord ++ tailWord_802762) baseStart_802762 baseEnd_802762 := by
    simpa [prefixWord, tailWord_802762, baseEnd_802762] using wordTrace_append hprefix tailTrace_802762
  have hstable : (prefixWord ++ tailWord_802762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802762).length < 2 ^ (prefixWord ++ tailWord_802762).sum := by decide
  have hdescent : baseEnd_802762 < baseStart_802762 := by decide
  rcases family_descends (prefixWord ++ tailWord_802762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802775 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 4, 2]
def baseStart_802775 : Nat := 118140960795 + 802775 * 2 ^ 59
def prefixEnd_802775 : Nat := 4983230072969 + 3 ^ 40 * 802775 * 2
def baseEnd_802775 : Nat := 412209432413201872820611

theorem tailTrace_802775 : CollatzResearch.WordTrace tailWord_802775 prefixEnd_802775 412209432413201872820611 := by
  unfold tailWord_802775
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279609666690752899777779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19519739777793835266518519 29279609666690752899777779)
  ·
    refine ⟨43919414500036129349666669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29279609666690752899777779 43919414500036129349666669)
    ·
      refine ⟨16469780437513548506125001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43919414500036129349666669 16469780437513548506125001)
      ·
        refine ⟨12352335328135161379593751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16469780437513548506125001 12352335328135161379593751)
        ·
          refine ⟨18528502992202742069390627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12352335328135161379593751 18528502992202742069390627)
          ·
            refine ⟨27792754488304113104085941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18528502992202742069390627 27792754488304113104085941)
            ·
              refine ⟨2605570733278510603508057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27792754488304113104085941 2605570733278510603508057)
              ·
                refine ⟨1954178049958882952631043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2605570733278510603508057 1954178049958882952631043)
                ·
                  refine ⟨2931267074938324428946565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954178049958882952631043 2931267074938324428946565)
                  ·
                    refine ⟨549612576550935830427481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931267074938324428946565 549612576550935830427481)
                    ·
                      refine ⟨412209432413201872820611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549612576550935830427481 412209432413201872820611)
                      ·
                        rfl

theorem cell23_802775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 4, 2].length) (baseStart_802775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802775 prefixEnd_802775 := by exact prefixLift 802775
  have htrace : WordTrace (prefixWord ++ tailWord_802775) baseStart_802775 baseEnd_802775 := by
    simpa [prefixWord, tailWord_802775, baseEnd_802775] using wordTrace_append hprefix tailTrace_802775
  have hstable : (prefixWord ++ tailWord_802775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802775).length < 2 ^ (prefixWord ++ tailWord_802775).sum := by decide
  have hdescent : baseEnd_802775 < baseStart_802775 := by decide
  rcases family_descends (prefixWord ++ tailWord_802775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802786 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_802786 : Nat := 118140960795 + 802786 * 2 ^ 59
def prefixEnd_802786 : Nat := 4983230072969 + 3 ^ 40 * 802786 * 2
def baseEnd_802786 : Nat := 412215080700401329783061

theorem tailTrace_802786 : CollatzResearch.WordTrace tailWord_802786 prefixEnd_802786 412215080700401329783061 := by
  unfold tailWord_802786
  simp only [CollatzResearch.WordTrace]
  refine ⟨7320002717412725444607053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19520007246433934518952141 7320002717412725444607053)
  ·
    refine ⟨2745001019029772041727645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7320002717412725444607053 2745001019029772041727645)
    ·
      refine ⟨1029375382136164515647867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2745001019029772041727645 1029375382136164515647867)
      ·
        refine ⟨1544063073204246773471801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029375382136164515647867 1544063073204246773471801)
        ·
          refine ⟨1158047304903185080103851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544063073204246773471801 1158047304903185080103851)
          ·
            refine ⟨1737070957354777620155777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158047304903185080103851 1737070957354777620155777)
            ·
              refine ⟨1302803218016083215116833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737070957354777620155777 1302803218016083215116833)
              ·
                refine ⟨977102413512062411337625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302803218016083215116833 977102413512062411337625)
                ·
                  refine ⟨732826810134046808503219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 977102413512062411337625 732826810134046808503219)
                  ·
                    refine ⟨1099240215201070212754829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 732826810134046808503219 1099240215201070212754829)
                    ·
                      refine ⟨412215080700401329783061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1099240215201070212754829 412215080700401329783061)
                      ·
                        rfl

theorem cell23_802786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_802786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802786 prefixEnd_802786 := by exact prefixLift 802786
  have htrace : WordTrace (prefixWord ++ tailWord_802786) baseStart_802786 baseEnd_802786 := by
    simpa [prefixWord, tailWord_802786, baseEnd_802786] using wordTrace_append hprefix tailTrace_802786
  have hstable : (prefixWord ++ tailWord_802786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802786).length < 2 ^ (prefixWord ++ tailWord_802786).sum := by decide
  have hdescent : baseEnd_802786 < baseStart_802786 := by decide
  rcases family_descends (prefixWord ++ tailWord_802786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802788 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_802788 : Nat := 118140960795 + 802788 * 2 ^ 59
def prefixEnd_802788 : Nat := 4983230072969 + 3 ^ 40 * 802788 * 2
def baseEnd_802788 : Nat := 412216107661710321958051

theorem tailTrace_802788 : CollatzResearch.WordTrace tailWord_802788 prefixEnd_802788 412216107661710321958051 := by
  unfold tailWord_802788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640041907821828060000509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19520055877095770746667345 14640041907821828060000509)
  ·
    refine ⟨5490015715433185522500191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14640041907821828060000509 5490015715433185522500191)
    ·
      refine ⟨8235023573149778283750287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490015715433185522500191 8235023573149778283750287)
      ·
        refine ⟨12352535359724667425625431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8235023573149778283750287 12352535359724667425625431)
        ·
          refine ⟨18528803039587001138438147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12352535359724667425625431 18528803039587001138438147)
          ·
            refine ⟨27793204559380501707657221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18528803039587001138438147 27793204559380501707657221)
            ·
              refine ⟨5211225854883844070185729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27793204559380501707657221 5211225854883844070185729)
              ·
                refine ⟨3908419391162883052639297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211225854883844070185729 3908419391162883052639297)
                ·
                  refine ⟨2931314543372162289479473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3908419391162883052639297 2931314543372162289479473)
                  ·
                    refine ⟨2198485907529121717109605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931314543372162289479473 2198485907529121717109605)
                    ·
                      refine ⟨412216107661710321958051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2198485907529121717109605 412216107661710321958051)
                      ·
                        rfl

theorem cell23_802788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_802788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802788 prefixEnd_802788 := by exact prefixLift 802788
  have htrace : WordTrace (prefixWord ++ tailWord_802788) baseStart_802788 baseEnd_802788 := by
    simpa [prefixWord, tailWord_802788, baseEnd_802788] using wordTrace_append hprefix tailTrace_802788
  have hstable : (prefixWord ++ tailWord_802788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802788).length < 2 ^ (prefixWord ++ tailWord_802788).sum := by decide
  have hdescent : baseEnd_802788 < baseStart_802788 := by decide
  rcases family_descends (prefixWord ++ tailWord_802788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802808 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_802808 : Nat := 118140960795 + 802808 * 2 ^ 59
def prefixEnd_802808 : Nat := 4983230072969 + 3 ^ 40 * 802808 * 2
def baseEnd_802808 : Nat := 412226377274800243707959

theorem tailTrace_802808 : CollatzResearch.WordTrace tailWord_802808 prefixEnd_802808 412226377274800243707959 := by
  unfold tailWord_802808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640406637785599767864539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19520542183714133023819385 14640406637785599767864539)
  ·
    refine ⟨21960609956678399651796809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14640406637785599767864539 21960609956678399651796809)
    ·
      refine ⟨16470457467508799738847607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21960609956678399651796809 16470457467508799738847607)
      ·
        refine ⟨24705686201263199608271411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16470457467508799738847607 24705686201263199608271411)
        ·
          refine ⟨37058529301894799412407117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24705686201263199608271411 37058529301894799412407117)
          ·
            refine ⟨13896948488210549779652669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37058529301894799412407117 13896948488210549779652669)
            ·
              refine ⟨5211355683078956167369751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13896948488210549779652669 5211355683078956167369751)
              ·
                refine ⟨7817033524618434251054627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211355683078956167369751 7817033524618434251054627)
                ·
                  refine ⟨11725550286927651376581941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817033524618434251054627 11725550286927651376581941)
                  ·
                    refine ⟨1099270339399467316554557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11725550286927651376581941 1099270339399467316554557)
                    ·
                      refine ⟨412226377274800243707959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1099270339399467316554557 412226377274800243707959)
                      ·
                        rfl

theorem cell23_802808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_802808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802808 prefixEnd_802808 := by exact prefixLift 802808
  have htrace : WordTrace (prefixWord ++ tailWord_802808) baseStart_802808 baseEnd_802808 := by
    simpa [prefixWord, tailWord_802808, baseEnd_802808] using wordTrace_append hprefix tailTrace_802808
  have hstable : (prefixWord ++ tailWord_802808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802808).length < 2 ^ (prefixWord ++ tailWord_802808).sum := by decide
  have hdescent : baseEnd_802808 < baseStart_802808 := by decide
  rcases family_descends (prefixWord ++ tailWord_802808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802828 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_802828 : Nat := 118140960795 + 802828 * 2 ^ 59
def prefixEnd_802828 : Nat := 4983230072969 + 3 ^ 40 * 802828 * 2
def baseEnd_802828 : Nat := 137412215629296721819289

theorem tailTrace_802828 : CollatzResearch.WordTrace tailWord_802828 prefixEnd_802828 137412215629296721819289 := by
  unfold tailWord_802828
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640771367749371475728569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19521028490332495300971425 14640771367749371475728569)
  ·
    refine ⟨10980578525812028606796427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14640771367749371475728569 10980578525812028606796427)
    ·
      refine ⟨16470867788718042910194641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10980578525812028606796427 16470867788718042910194641)
      ·
        refine ⟨12353150841538532182645981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16470867788718042910194641 12353150841538532182645981)
        ·
          refine ⟨4632431565576949568492243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12353150841538532182645981 4632431565576949568492243)
          ·
            refine ⟨6948647348365424352738365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632431565576949568492243 6948647348365424352738365)
            ·
              refine ⟨2605742755637034132276887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6948647348365424352738365 2605742755637034132276887)
              ·
                refine ⟨3908614133455551198415331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605742755637034132276887 3908614133455551198415331)
                ·
                  refine ⟨5862921200183326797622997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908614133455551198415331 5862921200183326797622997)
                  ·
                    refine ⟨137412215629296721819289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5862921200183326797622997 137412215629296721819289)
                    ·
                      rfl

theorem cell23_802828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_802828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802828 prefixEnd_802828 := by exact prefixLift 802828
  have htrace : WordTrace (prefixWord ++ tailWord_802828) baseStart_802828 baseEnd_802828 := by
    simpa [prefixWord, tailWord_802828, baseEnd_802828] using wordTrace_append hprefix tailTrace_802828
  have hstable : (prefixWord ++ tailWord_802828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802828).length < 2 ^ (prefixWord ++ tailWord_802828).sum := by decide
  have hdescent : baseEnd_802828 < baseStart_802828 := by decide
  rcases family_descends (prefixWord ++ tailWord_802828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802885 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 3]
def baseStart_802885 : Nat := 118140960795 + 802885 * 2 ^ 59
def prefixEnd_802885 : Nat := 4983230072969 + 3 ^ 40 * 802885 * 2
def baseEnd_802885 : Nat := 412265915285196442445105

theorem tailTrace_802885 : CollatzResearch.WordTrace tailWord_802885 prefixEnd_802885 412265915285196442445105 := by
  unfold tailWord_802885
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283621696292241686282109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19522414464194827790854739 29283621696292241686282109)
  ·
    refine ⟨10981358136109590632355791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29283621696292241686282109 10981358136109590632355791)
    ·
      refine ⟨16472037204164385948533687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10981358136109590632355791 16472037204164385948533687)
      ·
        refine ⟨24708055806246578922800531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16472037204164385948533687 24708055806246578922800531)
        ·
          refine ⟨37062083709369868384200797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24708055806246578922800531 37062083709369868384200797)
          ·
            refine ⟨13898281391013700644075299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37062083709369868384200797 13898281391013700644075299)
            ·
              refine ⟨20847422086520550966112949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13898281391013700644075299 20847422086520550966112949)
              ·
                refine ⟨1954445820611301653073089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20847422086520550966112949 1954445820611301653073089)
                ·
                  refine ⟨1465834365458476239804817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954445820611301653073089 1465834365458476239804817)
                  ·
                    refine ⟨1099375774093857179853613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1465834365458476239804817 1099375774093857179853613)
                    ·
                      refine ⟨412265915285196442445105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1099375774093857179853613 412265915285196442445105)
                      ·
                        rfl

theorem cell23_802885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 3].length) (baseStart_802885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802885 prefixEnd_802885 := by exact prefixLift 802885
  have htrace : WordTrace (prefixWord ++ tailWord_802885) baseStart_802885 baseEnd_802885 := by
    simpa [prefixWord, tailWord_802885, baseEnd_802885] using wordTrace_append hprefix tailTrace_802885
  have hstable : (prefixWord ++ tailWord_802885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802885).length < 2 ^ (prefixWord ++ tailWord_802885).sum := by decide
  have hdescent : baseEnd_802885 < baseStart_802885 := by decide
  rcases family_descends (prefixWord ++ tailWord_802885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802909 : List Nat := [1, 4, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_802909 : Nat := 118140960795 + 802909 * 2 ^ 59
def prefixEnd_802909 : Nat := 4983230072969 + 3 ^ 40 * 802909 * 2
def baseEnd_802909 : Nat := 137426079606968116181665

theorem tailTrace_802909 : CollatzResearch.WordTrace tailWord_802909 prefixEnd_802909 137426079606968116181665 := by
  unfold tailWord_802909
  simp only [CollatzResearch.WordTrace]
  refine ⟨29284497048205293785155781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19522998032136862523437187 29284497048205293785155781)
  ·
    refine ⟨5490843196538492584716709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29284497048205293785155781 5490843196538492584716709)
    ·
      refine ⟨1029533099350967359634383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5490843196538492584716709 1029533099350967359634383)
      ·
        refine ⟨1544299649026451039451575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1029533099350967359634383 1544299649026451039451575)
        ·
          refine ⟨2316449473539676559177363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544299649026451039451575 2316449473539676559177363)
          ·
            refine ⟨3474674210309514838766045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316449473539676559177363 3474674210309514838766045)
            ·
              refine ⟨1303002828866068064537267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3474674210309514838766045 1303002828866068064537267)
              ·
                refine ⟨1954504243299102096805901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303002828866068064537267 1954504243299102096805901)
                ·
                  refine ⟨732939091237163286302213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1954504243299102096805901 732939091237163286302213)
                  ·
                    refine ⟨137426079606968116181665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 732939091237163286302213 137426079606968116181665)
                    ·
                      rfl

theorem cell23_802909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_802909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802909 prefixEnd_802909 := by exact prefixLift 802909
  have htrace : WordTrace (prefixWord ++ tailWord_802909) baseStart_802909 baseEnd_802909 := by
    simpa [prefixWord, tailWord_802909, baseEnd_802909] using wordTrace_append hprefix tailTrace_802909
  have hstable : (prefixWord ++ tailWord_802909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802909).length < 2 ^ (prefixWord ++ tailWord_802909).sum := by decide
  have hdescent : baseEnd_802909 < baseStart_802909 := by decide
  rcases family_descends (prefixWord ++ tailWord_802909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802922 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 6]
def baseStart_802922 : Nat := 118140960795 + 802922 * 2 ^ 59
def prefixEnd_802922 : Nat := 4983230072969 + 3 ^ 40 * 802922 * 2
def baseEnd_802922 : Nat := 45809434896601421964715

theorem tailTrace_802922 : CollatzResearch.WordTrace tailWord_802922 prefixEnd_802922 45809434896601421964715 := by
  unfold tailWord_802922
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321242799289549251344755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19523314131438798003586013 7321242799289549251344755)
  ·
    refine ⟨10981864198934323877017133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321242799289549251344755 10981864198934323877017133)
    ·
      refine ⟨4118199074600371453881425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10981864198934323877017133 4118199074600371453881425)
      ·
        refine ⟨3088649305950278590411069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4118199074600371453881425 3088649305950278590411069)
        ·
          refine ⟨1158243489731354471404151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3088649305950278590411069 1158243489731354471404151)
          ·
            refine ⟨1737365234597031707106227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158243489731354471404151 1737365234597031707106227)
            ·
              refine ⟨2606047851895547560659341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737365234597031707106227 2606047851895547560659341)
              ·
                refine ⟨977267944460830335247253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606047851895547560659341 977267944460830335247253)
                ·
                  refine ⟨45809434896601421964715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 977267944460830335247253 45809434896601421964715)
                  ·
                    rfl

theorem cell23_802922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 6].length) (baseStart_802922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802922 prefixEnd_802922 := by exact prefixLift 802922
  have htrace : WordTrace (prefixWord ++ tailWord_802922) baseStart_802922 baseEnd_802922 := by
    simpa [prefixWord, tailWord_802922, baseEnd_802922] using wordTrace_append hprefix tailTrace_802922
  have hstable : (prefixWord ++ tailWord_802922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802922).length < 2 ^ (prefixWord ++ tailWord_802922).sum := by decide
  have hdescent : baseEnd_802922 < baseStart_802922 := by decide
  rcases family_descends (prefixWord ++ tailWord_802922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802935 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 3, 5]
def baseStart_802935 : Nat := 118140960795 + 802935 * 2 ^ 59
def prefixEnd_802935 : Nat := 4983230072969 + 3 ^ 40 * 802935 * 2
def baseEnd_802935 : Nat := 137430529772640415606625

theorem tailTrace_802935 : CollatzResearch.WordTrace tailWord_802935 prefixEnd_802935 137430529772640415606625 := by
  unfold tailWord_802935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29285445346111100225602259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19523630230740733483734839 29285445346111100225602259)
  ·
    refine ⟨43928168019166650338403389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29285445346111100225602259 43928168019166650338403389)
    ·
      refine ⟨16473063007187493876901271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43928168019166650338403389 16473063007187493876901271)
      ·
        refine ⟨24709594510781240815351907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16473063007187493876901271 24709594510781240815351907)
        ·
          refine ⟨37064391766171861223027861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24709594510781240815351907 37064391766171861223027861)
          ·
            refine ⟨1737393364039305994829431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37064391766171861223027861 1737393364039305994829431)
            ·
              refine ⟨2606090046058958992244147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1737393364039305994829431 2606090046058958992244147)
              ·
                refine ⟨3909135069088438488366221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606090046058958992244147 3909135069088438488366221)
                ·
                  refine ⟨1465925650908164433137333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3909135069088438488366221 1465925650908164433137333)
                  ·
                    refine ⟨137430529772640415606625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1465925650908164433137333 137430529772640415606625)
                    ·
                      rfl

theorem cell23_802935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_802935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802935 prefixEnd_802935 := by exact prefixLift 802935
  have htrace : WordTrace (prefixWord ++ tailWord_802935) baseStart_802935 baseEnd_802935 := by
    simpa [prefixWord, tailWord_802935, baseEnd_802935] using wordTrace_append hprefix tailTrace_802935
  have hstable : (prefixWord ++ tailWord_802935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802935).length < 2 ^ (prefixWord ++ tailWord_802935).sum := by decide
  have hdescent : baseEnd_802935 < baseStart_802935 := by decide
  rcases family_descends (prefixWord ++ tailWord_802935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_802993 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_802993 : Nat := 118140960795 + 802993 * 2 ^ 59
def prefixEnd_802993 : Nat := 4983230072969 + 3 ^ 40 * 802993 * 2
def baseEnd_802993 : Nat := 412321371195882019894609

theorem tailTrace_802993 : CollatzResearch.WordTrace tailWord_802993 prefixEnd_802993 412321371195882019894609 := by
  unfold tailWord_802993
  simp only [CollatzResearch.WordTrace]
  refine ⟨29287560779900976131213633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19525040519933984087475755 29287560779900976131213633)
  ·
    refine ⟨21965670584925732098410225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29287560779900976131213633 21965670584925732098410225)
    ·
      refine ⟨16474252938694299073807669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21965670584925732098410225 16474252938694299073807669)
      ·
        refine ⟨1544461213002590538169469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16474252938694299073807669 1544461213002590538169469)
        ·
          refine ⟨579172954875971451813551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1544461213002590538169469 579172954875971451813551)
          ·
            refine ⟨868759432313957177720327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579172954875971451813551 868759432313957177720327)
            ·
              refine ⟨1303139148470935766580491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868759432313957177720327 1303139148470935766580491)
              ·
                refine ⟨1954708722706403649870737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303139148470935766580491 1954708722706403649870737)
                ·
                  refine ⟨1466031542029802737403053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954708722706403649870737 1466031542029802737403053)
                  ·
                    refine ⟨549761828261176026526145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466031542029802737403053 549761828261176026526145)
                    ·
                      refine ⟨412321371195882019894609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549761828261176026526145 412321371195882019894609)
                      ·
                        rfl

theorem cell23_802993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_802993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_802993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_802993 prefixEnd_802993 := by exact prefixLift 802993
  have htrace : WordTrace (prefixWord ++ tailWord_802993) baseStart_802993 baseEnd_802993 := by
    simpa [prefixWord, tailWord_802993, baseEnd_802993] using wordTrace_append hprefix tailTrace_802993
  have hstable : (prefixWord ++ tailWord_802993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_802993).length < 2 ^ (prefixWord ++ tailWord_802993).sum := by decide
  have hdescent : baseEnd_802993 < baseStart_802993 := by decide
  rcases family_descends (prefixWord ++ tailWord_802993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803096 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_803096 : Nat := 118140960795 + 803096 * 2 ^ 59
def prefixEnd_803096 : Nat := 4983230072969 + 3 ^ 40 * 803096 * 2
def baseEnd_803096 : Nat := 412374259703295116906635

theorem tailTrace_803096 : CollatzResearch.WordTrace tailWord_803096 prefixEnd_803096 412374259703295116906635 := by
  unfold tailWord_803096
  simp only [CollatzResearch.WordTrace]
  refine ⟨14645658749263912361106571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19527544999018549814808761 14645658749263912361106571)
  ·
    refine ⟨21968488123895868541659857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14645658749263912361106571 21968488123895868541659857)
    ·
      refine ⟨16476366092921901406244893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21968488123895868541659857 16476366092921901406244893)
      ·
        refine ⟨6178637284845713027341835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16476366092921901406244893 6178637284845713027341835)
        ·
          refine ⟨9267955927268569541012753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178637284845713027341835 9267955927268569541012753)
          ·
            refine ⟨6950966945451427155759565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9267955927268569541012753 6950966945451427155759565)
            ·
              refine ⟨2606612604544285183409837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6950966945451427155759565 2606612604544285183409837)
              ·
                refine ⟨977479726704106943778689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2606612604544285183409837 977479726704106943778689)
                ·
                  refine ⟨733109795028080207834017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 977479726704106943778689 733109795028080207834017)
                  ·
                    refine ⟨549832346271060155875513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 733109795028080207834017 549832346271060155875513)
                    ·
                      refine ⟨412374259703295116906635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 549832346271060155875513 412374259703295116906635)
                      ·
                        rfl

theorem cell23_803096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_803096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803096 prefixEnd_803096 := by exact prefixLift 803096
  have htrace : WordTrace (prefixWord ++ tailWord_803096) baseStart_803096 baseEnd_803096 := by
    simpa [prefixWord, tailWord_803096, baseEnd_803096] using wordTrace_append hprefix tailTrace_803096
  have hstable : (prefixWord ++ tailWord_803096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803096).length < 2 ^ (prefixWord ++ tailWord_803096).sum := by decide
  have hdescent : baseEnd_803096 < baseStart_803096 := by decide
  rcases family_descends (prefixWord ++ tailWord_803096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803132 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_803132 : Nat := 118140960795 + 803132 * 2 ^ 59
def prefixEnd_803132 : Nat := 4983230072969 + 3 ^ 40 * 803132 * 2
def baseEnd_803132 : Nat := 137464248335618992018823

theorem tailTrace_803132 : CollatzResearch.WordTrace tailWord_803132 prefixEnd_803132 137464248335618992018823 := by
  unfold tailWord_803132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14646315263198701435261825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19528420350931601913682433 14646315263198701435261825)
  ·
    refine ⟨10984736447399026076446369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14646315263198701435261825 10984736447399026076446369)
    ·
      refine ⟨8238552335549269557334777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10984736447399026076446369 8238552335549269557334777)
      ·
        refine ⟨6178914251661952168001083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8238552335549269557334777 6178914251661952168001083)
        ·
          refine ⟨9268371377492928252001625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178914251661952168001083 9268371377492928252001625)
          ·
            refine ⟨6951278533119696189001219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9268371377492928252001625 6951278533119696189001219)
            ·
              refine ⟨10426917799679544283501829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951278533119696189001219 10426917799679544283501829)
              ·
                refine ⟨1955047087439914553156593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10426917799679544283501829 1955047087439914553156593)
                ·
                  refine ⟨1466285315579935914867445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955047087439914553156593 1466285315579935914867445)
                  ·
                    refine ⟨137464248335618992018823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1466285315579935914867445 137464248335618992018823)
                    ·
                      rfl

theorem cell23_803132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_803132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803132 prefixEnd_803132 := by exact prefixLift 803132
  have htrace : WordTrace (prefixWord ++ tailWord_803132) baseStart_803132 baseEnd_803132 := by
    simpa [prefixWord, tailWord_803132, baseEnd_803132] using wordTrace_append hprefix tailTrace_803132
  have hstable : (prefixWord ++ tailWord_803132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803132).length < 2 ^ (prefixWord ++ tailWord_803132).sum := by decide
  have hdescent : baseEnd_803132 < baseStart_803132 := by decide
  rcases family_descends (prefixWord ++ tailWord_803132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803145 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_803145 : Nat := 118140960795 + 803145 * 2 ^ 59
def prefixEnd_803145 : Nat := 4983230072969 + 3 ^ 40 * 803145 * 2
def baseEnd_803145 : Nat := 137466473418455141731303

theorem tailTrace_803145 : CollatzResearch.WordTrace tailWord_803145 prefixEnd_803145 137466473418455141731303 := by
  unfold tailWord_803145
  simp only [CollatzResearch.WordTrace]
  refine ⟨29293104675350306090746889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19528736450233537393831259 29293104675350306090746889)
  ·
    refine ⟨21969828506512729568060167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29293104675350306090746889 21969828506512729568060167)
    ·
      refine ⟨32954742759769094352090251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21969828506512729568060167 32954742759769094352090251)
      ·
        refine ⟨49432114139653641528135377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32954742759769094352090251 49432114139653641528135377)
        ·
          refine ⟨37074085604740231146101533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49432114139653641528135377 37074085604740231146101533)
          ·
            refine ⟨13902782101777586679788075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37074085604740231146101533 13902782101777586679788075)
            ·
              refine ⟨20854173152666380019682113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902782101777586679788075 20854173152666380019682113)
              ·
                refine ⟨15640629864499785014761585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20854173152666380019682113 15640629864499785014761585)
                ·
                  refine ⟨11730472398374838761071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15640629864499785014761585 11730472398374838761071189)
                  ·
                    refine ⟨137466473418455141731303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11730472398374838761071189 137466473418455141731303)
                    ·
                      rfl

theorem cell23_803145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_803145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803145 prefixEnd_803145 := by exact prefixLift 803145
  have htrace : WordTrace (prefixWord ++ tailWord_803145) baseStart_803145 baseEnd_803145 := by
    simpa [prefixWord, tailWord_803145, baseEnd_803145] using wordTrace_append hprefix tailTrace_803145
  have hstable : (prefixWord ++ tailWord_803145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803145).length < 2 ^ (prefixWord ++ tailWord_803145).sum := by decide
  have hdescent : baseEnd_803145 < baseStart_803145 := by decide
  rcases family_descends (prefixWord ++ tailWord_803145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803230 : List Nat := [4, 3, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_803230 : Nat := 118140960795 + 803230 * 2 ^ 59
def prefixEnd_803230 : Nat := 4983230072969 + 3 ^ 40 * 803230 * 2
def baseEnd_803230 : Nat := 137481022036999197543673

theorem tailTrace_803230 : CollatzResearch.WordTrace tailWord_803230 prefixEnd_803230 137481022036999197543673 := by
  unfold tailWord_803230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662025610005295700948893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19530803253361577071727429 3662025610005295700948893)
  ·
    refine ⟨1373259603751985887855835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3662025610005295700948893 1373259603751985887855835)
    ·
      refine ⟨2059889405627978831783753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373259603751985887855835 2059889405627978831783753)
      ·
        refine ⟨1544917054220984123837815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059889405627978831783753 1544917054220984123837815)
        ·
          refine ⟨2317375581331476185756723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544917054220984123837815 2317375581331476185756723)
          ·
            refine ⟨3476063371997214278635085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317375581331476185756723 3476063371997214278635085)
            ·
              refine ⟨1303523764498955354488157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3476063371997214278635085 1303523764498955354488157)
              ·
                refine ⟨488821411687108257933059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1303523764498955354488157 488821411687108257933059)
                ·
                  refine ⟨733232117530662386899589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488821411687108257933059 733232117530662386899589)
                  ·
                    refine ⟨137481022036999197543673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 733232117530662386899589 137481022036999197543673)
                    ·
                      rfl

theorem cell23_803230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_803230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803230 prefixEnd_803230 := by exact prefixLift 803230
  have htrace : WordTrace (prefixWord ++ tailWord_803230) baseStart_803230 baseEnd_803230 := by
    simpa [prefixWord, tailWord_803230, baseEnd_803230] using wordTrace_append hprefix tailTrace_803230
  have hstable : (prefixWord ++ tailWord_803230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803230).length < 2 ^ (prefixWord ++ tailWord_803230).sum := by decide
  have hdescent : baseEnd_803230 < baseStart_803230 := by decide
  rcases family_descends (prefixWord ++ tailWord_803230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803276 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_803276 : Nat := 118140960795 + 803276 * 2 ^ 59
def prefixEnd_803276 : Nat := 4983230072969 + 3 ^ 40 * 803276 * 2
def baseEnd_803276 : Nat := 412466686221104412655807

theorem tailTrace_803276 : CollatzResearch.WordTrace tailWord_803276 prefixEnd_803276 412466686221104412655807 := by
  unfold tailWord_803276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14648941318937857731882841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19531921758583810309177121 14648941318937857731882841)
  ·
    refine ⟨10986705989203393298912131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14648941318937857731882841 10986705989203393298912131)
    ·
      refine ⟨16480058983805089948368197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10986705989203393298912131 16480058983805089948368197)
      ·
        refine ⟨3090011059463454365319037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16480058983805089948368197 3090011059463454365319037)
        ·
          refine ⟨1158754147298795386994639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3090011059463454365319037 1158754147298795386994639)
          ·
            refine ⟨1738131220948193080491959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158754147298795386994639 1738131220948193080491959)
            ·
              refine ⟨2607196831422289620737939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738131220948193080491959 2607196831422289620737939)
              ·
                refine ⟨3910795247133434431106909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607196831422289620737939 3910795247133434431106909)
                ·
                  refine ⟨1466548217675037911665091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3910795247133434431106909 1466548217675037911665091)
                  ·
                    refine ⟨2199822326512556867497637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466548217675037911665091 2199822326512556867497637)
                    ·
                      refine ⟨412466686221104412655807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2199822326512556867497637 412466686221104412655807)
                      ·
                        rfl

theorem cell23_803276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_803276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803276 prefixEnd_803276 := by exact prefixLift 803276
  have htrace : WordTrace (prefixWord ++ tailWord_803276) baseStart_803276 baseEnd_803276 := by
    simpa [prefixWord, tailWord_803276, baseEnd_803276] using wordTrace_append hprefix tailTrace_803276
  have hstable : (prefixWord ++ tailWord_803276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803276).length < 2 ^ (prefixWord ++ tailWord_803276).sum := by decide
  have hdescent : baseEnd_803276 < baseStart_803276 := by decide
  rcases family_descends (prefixWord ++ tailWord_803276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803286 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_803286 : Nat := 118140960795 + 803286 * 2 ^ 59
def prefixEnd_803286 : Nat := 4983230072969 + 3 ^ 40 * 803286 * 2
def baseEnd_803286 : Nat := 137490607009216457843587

theorem tailTrace_803286 : CollatzResearch.WordTrace tailWord_803286 prefixEnd_803286 137490607009216457843587 := by
  unfold tailWord_803286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831140460489967948226857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19532164911892991447753141 1831140460489967948226857)
  ·
    refine ⟨1373355345367475961170143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1831140460489967948226857 1373355345367475961170143)
    ·
      refine ⟨2060033018051213941755215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373355345367475961170143 2060033018051213941755215)
      ·
        refine ⟨3090049527076820912632823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060033018051213941755215 3090049527076820912632823)
        ·
          refine ⟨4635074290615231368949235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090049527076820912632823 4635074290615231368949235)
          ·
            refine ⟨6952611435922847053423853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635074290615231368949235 6952611435922847053423853)
            ·
              refine ⟨2607229288471067645033945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6952611435922847053423853 2607229288471067645033945)
              ·
                refine ⟨1955421966353300733775459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607229288471067645033945 1955421966353300733775459)
                ·
                  refine ⟨2933132949529951100663189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955421966353300733775459 2933132949529951100663189)
                  ·
                    refine ⟨137490607009216457843587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2933132949529951100663189 137490607009216457843587)
                    ·
                      rfl

theorem cell23_803286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_803286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803286 prefixEnd_803286 := by exact prefixLift 803286
  have htrace : WordTrace (prefixWord ++ tailWord_803286) baseStart_803286 baseEnd_803286 := by
    simpa [prefixWord, tailWord_803286, baseEnd_803286] using wordTrace_append hprefix tailTrace_803286
  have hstable : (prefixWord ++ tailWord_803286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803286).length < 2 ^ (prefixWord ++ tailWord_803286).sum := by decide
  have hdescent : baseEnd_803286 < baseStart_803286 := by decide
  rcases family_descends (prefixWord ++ tailWord_803286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803289 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_803289 : Nat := 118140960795 + 803289 * 2 ^ 59
def prefixEnd_803289 : Nat := 4983230072969 + 3 ^ 40 * 803289 * 2
def baseEnd_803289 : Nat := 412473361469612861793247

theorem tailTrace_803289 : CollatzResearch.WordTrace tailWord_803289 prefixEnd_803289 412473361469612861793247 := by
  unfold tailWord_803289
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298356786828618683988921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532237857885745789325947 29298356786828618683988921)
  ·
    refine ⟨21973767590121464012991691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29298356786828618683988921 21973767590121464012991691)
    ·
      refine ⟨32960651385182196019487537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21973767590121464012991691 32960651385182196019487537)
      ·
        refine ⟨24720488538886647014615653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32960651385182196019487537 24720488538886647014615653)
        ·
          refine ⟨4635091601041246315240435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24720488538886647014615653 4635091601041246315240435)
          ·
            refine ⟨6952637401561869472860653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635091601041246315240435 6952637401561869472860653)
            ·
              refine ⟨2607239025585701052322745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6952637401561869472860653 2607239025585701052322745)
              ·
                refine ⟨1955429269189275789242059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2607239025585701052322745 1955429269189275789242059)
                ·
                  refine ⟨2933143903783913683863089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1955429269189275789242059 2933143903783913683863089)
                  ·
                    refine ⟨2199857927837935262897317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933143903783913683863089 2199857927837935262897317)
                    ·
                      refine ⟨412473361469612861793247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2199857927837935262897317 412473361469612861793247)
                      ·
                        rfl

theorem cell23_803289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_803289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803289 prefixEnd_803289 := by exact prefixLift 803289
  have htrace : WordTrace (prefixWord ++ tailWord_803289) baseStart_803289 baseEnd_803289 := by
    simpa [prefixWord, tailWord_803289, baseEnd_803289] using wordTrace_append hprefix tailTrace_803289
  have hstable : (prefixWord ++ tailWord_803289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803289).length < 2 ^ (prefixWord ++ tailWord_803289).sum := by decide
  have hdescent : baseEnd_803289 < baseStart_803289 := by decide
  rcases family_descends (prefixWord ++ tailWord_803289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803293 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 1, 1, 4]
def baseStart_803293 : Nat := 118140960795 + 803293 * 2 ^ 59
def prefixEnd_803293 : Nat := 4983230072969 + 3 ^ 40 * 803293 * 2
def baseEnd_803293 : Nat := 412475415392230846143229

theorem tailTrace_803293 : CollatzResearch.WordTrace tailWord_803293 prefixEnd_803293 412475415392230846143229 := by
  unfold tailWord_803293
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298502678814127367134533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532335119209418244756355 29298502678814127367134533)
  ·
    refine ⟨5493469252277648881337725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29298502678814127367134533 5493469252277648881337725)
    ·
      refine ⟨2060050969604118330501647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5493469252277648881337725 2060050969604118330501647)
      ·
        refine ⟨3090076454406177495752471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2060050969604118330501647 3090076454406177495752471)
        ·
          refine ⟨4635114681609266243628707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3090076454406177495752471 4635114681609266243628707)
          ·
            refine ⟨6952672022413899365443061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4635114681609266243628707 6952672022413899365443061)
            ·
              refine ⟨651813002101303065510287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6952672022413899365443061 651813002101303065510287)
              ·
                refine ⟨977719503151954598265431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651813002101303065510287 977719503151954598265431)
                ·
                  refine ⟨1466579254727931897398147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977719503151954598265431 1466579254727931897398147)
                  ·
                    refine ⟨2199868882091897846097221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466579254727931897398147 2199868882091897846097221)
                    ·
                      refine ⟨412475415392230846143229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2199868882091897846097221 412475415392230846143229)
                      ·
                        rfl

theorem cell23_803293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_803293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803293 prefixEnd_803293 := by exact prefixLift 803293
  have htrace : WordTrace (prefixWord ++ tailWord_803293) baseStart_803293 baseEnd_803293 := by
    simpa [prefixWord, tailWord_803293, baseEnd_803293] using wordTrace_append hprefix tailTrace_803293
  have hstable : (prefixWord ++ tailWord_803293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803293).length < 2 ^ (prefixWord ++ tailWord_803293).sum := by decide
  have hdescent : baseEnd_803293 < baseStart_803293 := by decide
  rcases family_descends (prefixWord ++ tailWord_803293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803299 : List Nat := [1, 1, 1, 6, 4, 10]
def baseStart_803299 : Nat := 118140960795 + 803299 * 2 ^ 59
def prefixEnd_803299 : Nat := 4983230072969 + 3 ^ 40 * 803299 * 2
def baseEnd_803299 : Nat := 1697442371506822315507

theorem tailTrace_803299 : CollatzResearch.WordTrace tailWord_803299 prefixEnd_803299 1697442371506822315507 := by
  unfold tailWord_803299
  simp only [CollatzResearch.WordTrace]
  refine ⟨29298721516792390391852951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19532481011194926927901967 29298721516792390391852951)
  ·
    refine ⟨43948082275188585587779427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29298721516792390391852951 43948082275188585587779427)
    ·
      refine ⟨65922123412782878381669141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43948082275188585587779427 65922123412782878381669141)
      ·
        refine ⟨3090099534974197424140741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65922123412782878381669141 3090099534974197424140741)
        ·
          refine ⟨579393662807662017026389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3090099534974197424140741 579393662807662017026389)
          ·
            refine ⟨1697442371506822315507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 579393662807662017026389 1697442371506822315507)
            ·
              rfl

theorem cell23_803299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 10].length) (baseStart_803299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803299 prefixEnd_803299 := by exact prefixLift 803299
  have htrace : WordTrace (prefixWord ++ tailWord_803299) baseStart_803299 baseEnd_803299 := by
    simpa [prefixWord, tailWord_803299, baseEnd_803299] using wordTrace_append hprefix tailTrace_803299
  have hstable : (prefixWord ++ tailWord_803299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803299).length < 2 ^ (prefixWord ++ tailWord_803299).sum := by decide
  have hdescent : baseEnd_803299 < baseStart_803299 := by decide
  rcases family_descends (prefixWord ++ tailWord_803299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803312 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_803312 : Nat := 118140960795 + 803312 * 2 ^ 59
def prefixEnd_803312 : Nat := 4983230072969 + 3 ^ 40 * 803312 * 2
def baseEnd_803312 : Nat := 137495057174888757268547

theorem tailTrace_803312 : CollatzResearch.WordTrace tailWord_803312 prefixEnd_803312 137495057174888757268547 := by
  unfold tailWord_803312
  simp only [CollatzResearch.WordTrace]
  refine ⟨14649597832872646806038095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19532797110496862408050793 14649597832872646806038095)
  ·
    refine ⟨21974396749308970209057143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14649597832872646806038095 21974396749308970209057143)
    ·
      refine ⟨32961595123963455313585715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21974396749308970209057143 32961595123963455313585715)
      ·
        refine ⟨49442392685945182970378573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32961595123963455313585715 49442392685945182970378573)
        ·
          refine ⟨18540897257229443613891965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49442392685945182970378573 18540897257229443613891965)
          ·
            refine ⟨6952836471461041355209487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18540897257229443613891965 6952836471461041355209487)
            ·
              refine ⟨10429254707191562032814231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952836471461041355209487 10429254707191562032814231)
              ·
                refine ⟨15643882060787343049221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10429254707191562032814231 15643882060787343049221347)
                ·
                  refine ⟨23465823091181014573832021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15643882060787343049221347 23465823091181014573832021)
                  ·
                    refine ⟨137495057174888757268547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 23465823091181014573832021 137495057174888757268547)
                    ·
                      rfl

theorem cell23_803312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_803312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803312 prefixEnd_803312 := by exact prefixLift 803312
  have htrace : WordTrace (prefixWord ++ tailWord_803312) baseStart_803312 baseEnd_803312 := by
    simpa [prefixWord, tailWord_803312, baseEnd_803312] using wordTrace_append hprefix tailTrace_803312
  have hstable : (prefixWord ++ tailWord_803312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803312).length < 2 ^ (prefixWord ++ tailWord_803312).sum := by decide
  have hdescent : baseEnd_803312 < baseStart_803312 := by decide
  rcases family_descends (prefixWord ++ tailWord_803312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803379 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_803379 : Nat := 118140960795 + 803379 * 2 ^ 59
def prefixEnd_803379 : Nat := 4983230072969 + 3 ^ 40 * 803379 * 2
def baseEnd_803379 : Nat := 412519574728517509667833

theorem tailTrace_803379 : CollatzResearch.WordTrace tailWord_803379 prefixEnd_803379 412519574728517509667833 := by
  unfold tailWord_803379
  simp only [CollatzResearch.WordTrace]
  refine ⟨29301639356502564054765191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19534426237668376036510127 29301639356502564054765191)
  ·
    refine ⟨43952459034753846082147787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29301639356502564054765191 43952459034753846082147787)
    ·
      refine ⟨65928688552130769123221681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43952459034753846082147787 65928688552130769123221681)
      ·
        refine ⟨49446516414098076842416261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65928688552130769123221681 49446516414098076842416261)
        ·
          refine ⟨9271221827643389407953049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49446516414098076842416261 9271221827643389407953049)
          ·
            refine ⟨6953416370732542055964787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9271221827643389407953049 6953416370732542055964787)
            ·
              refine ⟨10430124556098813083947181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6953416370732542055964787 10430124556098813083947181)
              ·
                refine ⟨3911296708537054906480193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10430124556098813083947181 3911296708537054906480193)
                ·
                  refine ⟨2933472531402791179860145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3911296708537054906480193 2933472531402791179860145)
                  ·
                    refine ⟨2200104398552093384895109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2933472531402791179860145 2200104398552093384895109)
                    ·
                      refine ⟨412519574728517509667833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2200104398552093384895109 412519574728517509667833)
                      ·
                        rfl

theorem cell23_803379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_803379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803379 prefixEnd_803379 := by exact prefixLift 803379
  have htrace : WordTrace (prefixWord ++ tailWord_803379) baseStart_803379 baseEnd_803379 := by
    simpa [prefixWord, tailWord_803379, baseEnd_803379] using wordTrace_append hprefix tailTrace_803379
  have hstable : (prefixWord ++ tailWord_803379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803379).length < 2 ^ (prefixWord ++ tailWord_803379).sum := by decide
  have hdescent : baseEnd_803379 < baseStart_803379 := by decide
  rcases family_descends (prefixWord ++ tailWord_803379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803439 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_803439 : Nat := 118140960795 + 803439 * 2 ^ 59
def prefixEnd_803439 : Nat := 4983230072969 + 3 ^ 40 * 803439 * 2
def baseEnd_803439 : Nat := 412550383567787274917557

theorem tailTrace_803439 : CollatzResearch.WordTrace tailWord_803439 prefixEnd_803439 412550383567787274917557 := by
  unfold tailWord_803439
  simp only [CollatzResearch.WordTrace]
  refine ⟨29303827736285194301949371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19535885157523462867966247 29303827736285194301949371)
  ·
    refine ⟨43955741604427791452924057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29303827736285194301949371 43955741604427791452924057)
    ·
      refine ⟨32966806203320843589693043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43955741604427791452924057 32966806203320843589693043)
      ·
        refine ⟨49450209304981265384539565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32966806203320843589693043 49450209304981265384539565)
        ·
          refine ⟨18543828489367974519202337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49450209304981265384539565 18543828489367974519202337)
          ·
            refine ⟨13907871367025980889401753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18543828489367974519202337 13907871367025980889401753)
            ·
              refine ⟨10430903525269485667051315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13907871367025980889401753 10430903525269485667051315)
              ·
                refine ⟨15646355287904228500576973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10430903525269485667051315 15646355287904228500576973)
                ·
                  refine ⟨5867383232964085687716365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15646355287904228500576973 5867383232964085687716365)
                  ·
                    refine ⟨2200268712361532132893637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5867383232964085687716365 2200268712361532132893637)
                    ·
                      refine ⟨412550383567787274917557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2200268712361532132893637 412550383567787274917557)
                      ·
                        rfl

theorem cell23_803439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_803439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803439 prefixEnd_803439 := by exact prefixLift 803439
  have htrace : WordTrace (prefixWord ++ tailWord_803439) baseStart_803439 baseEnd_803439 := by
    simpa [prefixWord, tailWord_803439, baseEnd_803439] using wordTrace_append hprefix tailTrace_803439
  have hstable : (prefixWord ++ tailWord_803439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803439).length < 2 ^ (prefixWord ++ tailWord_803439).sum := by decide
  have hdescent : baseEnd_803439 < baseStart_803439 := by decide
  rcases family_descends (prefixWord ++ tailWord_803439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803453 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_803453 : Nat := 118140960795 + 803453 * 2 ^ 59
def prefixEnd_803453 : Nat := 4983230072969 + 3 ^ 40 * 803453 * 2
def baseEnd_803453 : Nat := 137519190765650073380831

theorem tailTrace_803453 : CollatzResearch.WordTrace tailWord_803453 prefixEnd_803453 137519190765650073380831 := by
  unfold tailWord_803453
  simp only [CollatzResearch.WordTrace]
  refine ⟨29304338358234474692959013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19536225572156316461972675 29304338358234474692959013)
  ·
    refine ⟨5494563442168964004929815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29304338358234474692959013 5494563442168964004929815)
    ·
      refine ⟨8241845163253446007394723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5494563442168964004929815 8241845163253446007394723)
      ·
        refine ⟨12362767744880169011092085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8241845163253446007394723 12362767744880169011092085)
        ·
          refine ⟨1159009476082515844789883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12362767744880169011092085 1159009476082515844789883)
          ·
            refine ⟨1738514214123773767184825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159009476082515844789883 1738514214123773767184825)
            ·
              refine ⟨1303885660592830325388619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738514214123773767184825 1303885660592830325388619)
              ·
                refine ⟨1955828490889245488082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303885660592830325388619 1955828490889245488082929)
                ·
                  refine ⟨1466871368166934116062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955828490889245488082929 1466871368166934116062197)
                  ·
                    refine ⟨137519190765650073380831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1466871368166934116062197 137519190765650073380831)
                    ·
                      rfl

theorem cell23_803453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_803453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803453 prefixEnd_803453 := by exact prefixLift 803453
  have htrace : WordTrace (prefixWord ++ tailWord_803453) baseStart_803453 baseEnd_803453 := by
    simpa [prefixWord, tailWord_803453, baseEnd_803453] using wordTrace_append hprefix tailTrace_803453
  have hstable : (prefixWord ++ tailWord_803453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803453).length < 2 ^ (prefixWord ++ tailWord_803453).sum := by decide
  have hdescent : baseEnd_803453 < baseStart_803453 := by decide
  rcases family_descends (prefixWord ++ tailWord_803453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803456 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_803456 : Nat := 118140960795 + 803456 * 2 ^ 59
def prefixEnd_803456 : Nat := 4983230072969 + 3 ^ 40 * 803456 * 2
def baseEnd_803456 : Nat := 412559112738913708404979

theorem tailTrace_803456 : CollatzResearch.WordTrace tailWord_803456 prefixEnd_803456 412559112738913708404979 := by
  unfold tailWord_803456
  simp only [CollatzResearch.WordTrace]
  refine ⟨14652223888611803102659111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19536298518149070803545481 14652223888611803102659111)
  ·
    refine ⟨21978335832917704653988667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14652223888611803102659111 21978335832917704653988667)
    ·
      refine ⟨32967503749376556980983001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21978335832917704653988667 32967503749376556980983001)
      ·
        refine ⟨24725627812032417735737251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32967503749376556980983001 24725627812032417735737251)
        ·
          refine ⟨37088441718048626603605877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24725627812032417735737251 37088441718048626603605877)
          ·
            refine ⟨3477041411067058744088051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37088441718048626603605877 3477041411067058744088051)
            ·
              refine ⟨5215562116600588116132077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477041411067058744088051 5215562116600588116132077)
              ·
                refine ⟨1955835793725220543549529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5215562116600588116132077 1955835793725220543549529)
                ·
                  refine ⟨1466876845293915407662147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1955835793725220543549529 1466876845293915407662147)
                  ·
                    refine ⟨2200315267940873111493221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466876845293915407662147 2200315267940873111493221)
                    ·
                      refine ⟨412559112738913708404979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2200315267940873111493221 412559112738913708404979)
                      ·
                        rfl

theorem cell23_803456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_803456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803456 prefixEnd_803456 := by exact prefixLift 803456
  have htrace : WordTrace (prefixWord ++ tailWord_803456) baseStart_803456 baseEnd_803456 := by
    simpa [prefixWord, tailWord_803456, baseEnd_803456] using wordTrace_append hprefix tailTrace_803456
  have hstable : (prefixWord ++ tailWord_803456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803456).length < 2 ^ (prefixWord ++ tailWord_803456).sum := by decide
  have hdescent : baseEnd_803456 < baseStart_803456 := by decide
  rcases family_descends (prefixWord ++ tailWord_803456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803560 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_803560 : Nat := 118140960795 + 803560 * 2 ^ 59
def prefixEnd_803560 : Nat := 4983230072969 + 3 ^ 40 * 803560 * 2
def baseEnd_803560 : Nat := 137537504908993767168167

theorem tailTrace_803560 : CollatzResearch.WordTrace tailWord_803560 prefixEnd_803560 137537504908993767168167 := by
  unfold tailWord_803560
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654120484423415983552067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19538827312564554644736089 14654120484423415983552067)
  ·
    refine ⟨21981180726635123975328101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654120484423415983552067 21981180726635123975328101)
    ·
      refine ⟨4121471386244085745374019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21981180726635123975328101 4121471386244085745374019)
      ·
        refine ⟨6182207079366128618061029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4121471386244085745374019 6182207079366128618061029)
        ·
          refine ⟨1159163827381149115886443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6182207079366128618061029 1159163827381149115886443)
          ·
            refine ⟨1738745741071723673829665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159163827381149115886443 1738745741071723673829665)
            ·
              refine ⟨1304059305803792755372249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738745741071723673829665 1304059305803792755372249)
              ·
                refine ⟨978044479352844566529187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304059305803792755372249 978044479352844566529187)
                ·
                  refine ⟨1467066719029266849793781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978044479352844566529187 1467066719029266849793781)
                  ·
                    refine ⟨137537504908993767168167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1467066719029266849793781 137537504908993767168167)
                    ·
                      rfl

theorem cell23_803560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_803560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803560 prefixEnd_803560 := by exact prefixLift 803560
  have htrace : WordTrace (prefixWord ++ tailWord_803560) baseStart_803560 baseEnd_803560 := by
    simpa [prefixWord, tailWord_803560, baseEnd_803560] using wordTrace_append hprefix tailTrace_803560
  have hstable : (prefixWord ++ tailWord_803560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803560).length < 2 ^ (prefixWord ++ tailWord_803560).sum := by decide
  have hdescent : baseEnd_803560 < baseStart_803560 := by decide
  rcases family_descends (prefixWord ++ tailWord_803560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803576 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_803576 : Nat := 118140960795 + 803576 * 2 ^ 59
def prefixEnd_803576 : Nat := 4983230072969 + 3 ^ 40 * 803576 * 2
def baseEnd_803576 : Nat := 412620730417453238904427

theorem tailTrace_803576 : CollatzResearch.WordTrace tailWord_803576 prefixEnd_803576 412620730417453238904427 := by
  unfold tailWord_803576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14654412268394433349843291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19539216357859244466457721 14654412268394433349843291)
  ·
    refine ⟨21981618402591650024764937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14654412268394433349843291 21981618402591650024764937)
    ·
      refine ⟨16486213801943737518573703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21981618402591650024764937 16486213801943737518573703)
      ·
        refine ⟨24729320702915606277860555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16486213801943737518573703 24729320702915606277860555)
        ·
          refine ⟨37093981054373409416790833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24729320702915606277860555 37093981054373409416790833)
          ·
            refine ⟨27820485790780057062593125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37093981054373409416790833 27820485790780057062593125)
            ·
              refine ⟨5216341085771260699236211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27820485790780057062593125 5216341085771260699236211)
              ·
                refine ⟨7824511628656891048854317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216341085771260699236211 7824511628656891048854317)
                ·
                  refine ⟨2934191860746334143320369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7824511628656891048854317 2934191860746334143320369)
                  ·
                    refine ⟨2200643895559750607490277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2934191860746334143320369 2200643895559750607490277)
                    ·
                      refine ⟨412620730417453238904427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2200643895559750607490277 412620730417453238904427)
                      ·
                        rfl

theorem cell23_803576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_803576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803576 prefixEnd_803576 := by exact prefixLift 803576
  have htrace : WordTrace (prefixWord ++ tailWord_803576) baseStart_803576 baseEnd_803576 := by
    simpa [prefixWord, tailWord_803576, baseEnd_803576] using wordTrace_append hprefix tailTrace_803576
  have hstable : (prefixWord ++ tailWord_803576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803576).length < 2 ^ (prefixWord ++ tailWord_803576).sum := by decide
  have hdescent : baseEnd_803576 < baseStart_803576 := by decide
  rcases family_descends (prefixWord ++ tailWord_803576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803630 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_803630 : Nat := 118140960795 + 803630 * 2 ^ 59
def prefixEnd_803630 : Nat := 4983230072969 + 3 ^ 40 * 803630 * 2
def baseEnd_803630 : Nat := 412648458372796027629179

theorem tailTrace_803630 : CollatzResearch.WordTrace tailWord_803630 prefixEnd_803630 412648458372796027629179 := by
  unfold tailWord_803630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3663849259824154240269043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19540529385728822614768229 3663849259824154240269043)
  ·
    refine ⟨5495773889736231360403565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3663849259824154240269043 5495773889736231360403565)
    ·
      refine ⟨2060915208651086760151337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5495773889736231360403565 2060915208651086760151337)
      ·
        refine ⟨1545686406488315070113503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2060915208651086760151337 1545686406488315070113503)
        ·
          refine ⟨2318529609732472605170255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1545686406488315070113503 2318529609732472605170255)
          ·
            refine ⟨3477794414598708907755383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318529609732472605170255 3477794414598708907755383)
            ·
              refine ⟨5216691621898063361633075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3477794414598708907755383 5216691621898063361633075)
              ·
                refine ⟨7825037432847095042449613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5216691621898063361633075 7825037432847095042449613)
                ·
                  refine ⟨2934389037317660640918605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7825037432847095042449613 2934389037317660640918605)
                  ·
                    refine ⟨1100395888994122740344477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934389037317660640918605 1100395888994122740344477)
                    ·
                      refine ⟨412648458372796027629179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1100395888994122740344477 412648458372796027629179)
                      ·
                        rfl

theorem cell23_803630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_803630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803630 prefixEnd_803630 := by exact prefixLift 803630
  have htrace : WordTrace (prefixWord ++ tailWord_803630) baseStart_803630 baseEnd_803630 := by
    simpa [prefixWord, tailWord_803630, baseEnd_803630] using wordTrace_append hprefix tailTrace_803630
  have hstable : (prefixWord ++ tailWord_803630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803630).length < 2 ^ (prefixWord ++ tailWord_803630).sum := by decide
  have hdescent : baseEnd_803630 < baseStart_803630 := by decide
  rcases family_descends (prefixWord ++ tailWord_803630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803647 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 3]
def baseStart_803647 : Nat := 118140960795 + 803647 * 2 ^ 59
def prefixEnd_803647 : Nat := 4983230072969 + 3 ^ 40 * 803647 * 2
def baseEnd_803647 : Nat := 412657187543922461116601

theorem tailTrace_803647 : CollatzResearch.WordTrace tailWord_803647 prefixEnd_803647 412657187543922461116601 := by
  unfold tailWord_803647
  simp only [CollatzResearch.WordTrace]
  refine ⟨29311414119531645825521195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19540942746354430550347463 29311414119531645825521195)
  ·
    refine ⟨43967121179297468738281793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29311414119531645825521195 43967121179297468738281793)
    ·
      refine ⟨32975340884473101553711345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43967121179297468738281793 32975340884473101553711345)
      ·
        refine ⟨24731505663354826165283509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32975340884473101553711345 24731505663354826165283509)
        ·
          refine ⟨2318578655939514952995329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24731505663354826165283509 2318578655939514952995329)
          ·
            refine ⟨1738933991954636214746497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2318578655939514952995329 1738933991954636214746497)
            ·
              refine ⟨1304200493965977161059873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1738933991954636214746497 1304200493965977161059873)
              ·
                refine ⟨978150370474482870794905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1304200493965977161059873 978150370474482870794905)
                ·
                  refine ⟨733612777855862153096179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978150370474482870794905 733612777855862153096179)
                  ·
                    refine ⟨1100419166783793229644269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733612777855862153096179 1100419166783793229644269)
                    ·
                      refine ⟨412657187543922461116601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1100419166783793229644269 412657187543922461116601)
                      ·
                        rfl

theorem cell23_803647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_803647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803647 prefixEnd_803647 := by exact prefixLift 803647
  have htrace : WordTrace (prefixWord ++ tailWord_803647) baseStart_803647 baseEnd_803647 := by
    simpa [prefixWord, tailWord_803647, baseEnd_803647] using wordTrace_append hprefix tailTrace_803647
  have hstable : (prefixWord ++ tailWord_803647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803647).length < 2 ^ (prefixWord ++ tailWord_803647).sum := by decide
  have hdescent : baseEnd_803647 < baseStart_803647 := by decide
  rcases family_descends (prefixWord ++ tailWord_803647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803654 : List Nat := [6, 1, 1, 2, 3, 1, 1, 8]
def baseStart_803654 : Nat := 118140960795 + 803654 * 2 ^ 59
def prefixEnd_803654 : Nat := 4983230072969 + 3 ^ 40 * 803654 * 2
def baseEnd_803654 : Nat := 15283732663277923471447

theorem tailTrace_803654 : CollatzResearch.WordTrace tailWord_803654 prefixEnd_803654 15283732663277923471447 := by
  unfold tailWord_803654
  simp only [CollatzResearch.WordTrace]
  refine ⟨915989669703321438157063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19541112953670857347350677 915989669703321438157063)
  ·
    refine ⟨1373984504554982157235595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 915989669703321438157063 1373984504554982157235595)
    ·
      refine ⟨2060976756832473235853393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1373984504554982157235595 2060976756832473235853393)
      ·
        refine ⟨1545732567624354926890045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2060976756832473235853393 1545732567624354926890045)
        ·
          refine ⟨579649712859133097583767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1545732567624354926890045 579649712859133097583767)
          ·
            refine ⟨869474569288699646375651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579649712859133097583767 869474569288699646375651)
            ·
              refine ⟨1304211853933049469563477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869474569288699646375651 1304211853933049469563477)
              ·
                refine ⟨15283732663277923471447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1304211853933049469563477 15283732663277923471447)
                ·
                  rfl

theorem cell23_803654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_803654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803654 prefixEnd_803654 := by exact prefixLift 803654
  have htrace : WordTrace (prefixWord ++ tailWord_803654) baseStart_803654 baseEnd_803654 := by
    simpa [prefixWord, tailWord_803654, baseEnd_803654] using wordTrace_append hprefix tailTrace_803654
  have hstable : (prefixWord ++ tailWord_803654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803654).length < 2 ^ (prefixWord ++ tailWord_803654).sum := by decide
  have hdescent : baseEnd_803654 < baseStart_803654 := by decide
  rcases family_descends (prefixWord ++ tailWord_803654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803720 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_803720 : Nat := 118140960795 + 803720 * 2 ^ 59
def prefixEnd_803720 : Nat := 4983230072969 + 3 ^ 40 * 803720 * 2
def baseEnd_803720 : Nat := 412694671631700675503765

theorem tailTrace_803720 : CollatzResearch.WordTrace tailWord_803720 prefixEnd_803720 412694671631700675503765 := by
  unfold tailWord_803720
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657038324133589646464307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19542717765511452861952409 14657038324133589646464307)
  ·
    refine ⟨21985557486200384469696461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14657038324133589646464307 21985557486200384469696461)
    ·
      refine ⟨8244584057325144176136173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21985557486200384469696461 8244584057325144176136173)
      ·
        refine ⟨3091719021496929066051065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8244584057325144176136173 3091719021496929066051065)
        ·
          refine ⟨2318789266122696799538299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3091719021496929066051065 2318789266122696799538299)
          ·
            refine ⟨3478183899184045199307449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2318789266122696799538299 3478183899184045199307449)
            ·
              refine ⟨2608637924388033899480587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3478183899184045199307449 2608637924388033899480587)
              ·
                refine ⟨3912956886582050849220881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2608637924388033899480587 3912956886582050849220881)
                ·
                  refine ⟨2934717664936538136915661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3912956886582050849220881 2934717664936538136915661)
                  ·
                    refine ⟨1100519124351201801343373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2934717664936538136915661 1100519124351201801343373)
                    ·
                      refine ⟨412694671631700675503765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1100519124351201801343373 412694671631700675503765)
                      ·
                        rfl

theorem cell23_803720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_803720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803720 prefixEnd_803720 := by exact prefixLift 803720
  have htrace : WordTrace (prefixWord ++ tailWord_803720) baseStart_803720 baseEnd_803720 := by
    simpa [prefixWord, tailWord_803720, baseEnd_803720] using wordTrace_append hprefix tailTrace_803720
  have hstable : (prefixWord ++ tailWord_803720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803720).length < 2 ^ (prefixWord ++ tailWord_803720).sum := by decide
  have hdescent : baseEnd_803720 < baseStart_803720 := by decide
  rcases family_descends (prefixWord ++ tailWord_803720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3]
def baseStart_803763 : Nat := 118140960795 + 803763 * 2 ^ 59
def prefixEnd_803763 : Nat := 4983230072969 + 3 ^ 40 * 803763 * 2
def baseEnd_803763 : Nat := 412716751299844007266067

theorem tailTrace_803763 : CollatzResearch.WordTrace tailWord_803763 prefixEnd_803763 412716751299844007266067 := by
  unfold tailWord_803763
  simp only [CollatzResearch.WordTrace]
  refine ⟨29315644987111397636743943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19543763324740931757829295 29315644987111397636743943)
  ·
    refine ⟨43973467480667096455115915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29315644987111397636743943 43973467480667096455115915)
    ·
      refine ⟨65960201221000644682673873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43973467480667096455115915 65960201221000644682673873)
      ·
        refine ⟨49470150915750483512005405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65960201221000644682673873 49470150915750483512005405)
        ·
          refine ⟨18551306593406431317002027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49470150915750483512005405 18551306593406431317002027)
          ·
            refine ⟨27826959890109646975503041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18551306593406431317002027 27826959890109646975503041)
            ·
              refine ⟨20870219917582235231627281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27826959890109646975503041 20870219917582235231627281)
              ·
                refine ⟨15652664938186676423720461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20870219917582235231627281 15652664938186676423720461)
                ·
                  refine ⟨5869749351820003658895173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15652664938186676423720461 5869749351820003658895173)
                  ·
                    refine ⟨1100578003466250686042845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5869749351820003658895173 1100578003466250686042845)
                    ·
                      refine ⟨412716751299844007266067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1100578003466250686042845 412716751299844007266067)
                      ·
                        rfl

theorem cell23_803763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_803763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803763 prefixEnd_803763 := by exact prefixLift 803763
  have htrace : WordTrace (prefixWord ++ tailWord_803763) baseStart_803763 baseEnd_803763 := by
    simpa [prefixWord, tailWord_803763, baseEnd_803763] using wordTrace_append hprefix tailTrace_803763
  have hstable : (prefixWord ++ tailWord_803763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803763).length < 2 ^ (prefixWord ++ tailWord_803763).sum := by decide
  have hdescent : baseEnd_803763 < baseStart_803763 := by decide
  rcases family_descends (prefixWord ++ tailWord_803763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803820 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 5, 2]
def baseStart_803820 : Nat := 118140960795 + 803820 * 2 ^ 59
def prefixEnd_803820 : Nat := 4983230072969 + 3 ^ 40 * 803820 * 2
def baseEnd_803820 : Nat := 412746019697150284253305

theorem tailTrace_803820 : CollatzResearch.WordTrace tailWord_803820 prefixEnd_803820 412746019697150284253305 := by
  unfold tailWord_803820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658861973952448185784457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19545149298603264247712609 14658861973952448185784457)
  ·
    refine ⟨10994146480464336139338343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14658861973952448185784457 10994146480464336139338343)
    ·
      refine ⟨16491219720696504209007515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10994146480464336139338343 16491219720696504209007515)
      ·
        refine ⟨24736829581044756313511273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16491219720696504209007515 24736829581044756313511273)
        ·
          refine ⟨18552622185783567235133455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24736829581044756313511273 18552622185783567235133455)
          ·
            refine ⟨27828933278675350852700183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18552622185783567235133455 27828933278675350852700183)
            ·
              refine ⟨41743399918013026279050275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27828933278675350852700183 41743399918013026279050275)
              ·
                refine ⟨62615099877019539418575413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41743399918013026279050275 62615099877019539418575413)
                ·
                  refine ⟨5870165613470581820491445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62615099877019539418575413 5870165613470581820491445)
                  ·
                    refine ⟨550328026262867045671073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5870165613470581820491445 550328026262867045671073)
                    ·
                      refine ⟨412746019697150284253305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550328026262867045671073 412746019697150284253305)
                      ·
                        rfl

theorem cell23_803820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_803820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803820 prefixEnd_803820 := by exact prefixLift 803820
  have htrace : WordTrace (prefixWord ++ tailWord_803820) baseStart_803820 baseEnd_803820 := by
    simpa [prefixWord, tailWord_803820, baseEnd_803820] using wordTrace_append hprefix tailTrace_803820
  have hstable : (prefixWord ++ tailWord_803820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803820).length < 2 ^ (prefixWord ++ tailWord_803820).sum := by decide
  have hdescent : baseEnd_803820 < baseStart_803820 := by decide
  rcases family_descends (prefixWord ++ tailWord_803820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803854 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_803854 : Nat := 118140960795 + 803854 * 2 ^ 59
def prefixEnd_803854 : Nat := 4983230072969 + 3 ^ 40 * 803854 * 2
def baseEnd_803854 : Nat := 412763478039403151228149

theorem tailTrace_803854 : CollatzResearch.WordTrace tailWord_803854 prefixEnd_803854 412763478039403151228149 := by
  unfold tailWord_803854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3664870503722715022288327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19545976019854480118871077 3664870503722715022288327)
  ·
    refine ⟨5497305755584072533432491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3664870503722715022288327 5497305755584072533432491)
    ·
      refine ⟨8245958633376108800148737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497305755584072533432491 8245958633376108800148737)
      ·
        refine ⟨6184468975032081600111553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8245958633376108800148737 6184468975032081600111553)
        ·
          refine ⟨4638351731274061200083665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184468975032081600111553 4638351731274061200083665)
          ·
            refine ⟨3478763798455545900062749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4638351731274061200083665 3478763798455545900062749)
            ·
              refine ⟨1304536424420829712523531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478763798455545900062749 1304536424420829712523531)
              ·
                refine ⟨1956804636631244568785297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304536424420829712523531 1956804636631244568785297)
                ·
                  refine ⟨1467603477473433426588973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1956804636631244568785297 1467603477473433426588973)
                  ·
                    refine ⟨550351304052537534970865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467603477473433426588973 550351304052537534970865)
                    ·
                      refine ⟨412763478039403151228149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550351304052537534970865 412763478039403151228149)
                      ·
                        rfl

theorem cell23_803854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_803854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803854 prefixEnd_803854 := by exact prefixLift 803854
  have htrace : WordTrace (prefixWord ++ tailWord_803854) baseStart_803854 baseEnd_803854 := by
    simpa [prefixWord, tailWord_803854, baseEnd_803854] using wordTrace_append hprefix tailTrace_803854
  have hstable : (prefixWord ++ tailWord_803854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803854).length < 2 ^ (prefixWord ++ tailWord_803854).sum := by decide
  have hdescent : baseEnd_803854 < baseStart_803854 := by decide
  rcases family_descends (prefixWord ++ tailWord_803854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803861 : List Nat := [1, 3, 2, 1, 4, 2, 2, 3, 1, 1, 3]
def baseStart_803861 : Nat := 118140960795 + 803861 * 2 ^ 59
def prefixEnd_803861 : Nat := 4983230072969 + 3 ^ 40 * 803861 * 2
def baseEnd_803861 : Nat := 412767072403984623840617

theorem tailTrace_803861 : CollatzResearch.WordTrace tailWord_803861 prefixEnd_803861 412767072403984623840617 := by
  unfold tailWord_803861
  simp only [CollatzResearch.WordTrace]
  refine ⟨29319219340756360373811437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19546146227170906915874291 29319219340756360373811437)
  ·
    refine ⟨10994707252783635140179289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29319219340756360373811437 10994707252783635140179289)
    ·
      refine ⟨8246030439587726355134467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10994707252783635140179289 8246030439587726355134467)
      ·
        refine ⟨12369045659381589532701701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246030439587726355134467 12369045659381589532701701)
        ·
          refine ⟨2319196061134048037381569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12369045659381589532701701 2319196061134048037381569)
          ·
            refine ⟨1739397045850536028036177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2319196061134048037381569 1739397045850536028036177)
            ·
              refine ⟨1304547784387902021027133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1739397045850536028036177 1304547784387902021027133)
              ·
                refine ⟨489205419145463257885175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1304547784387902021027133 489205419145463257885175)
                ·
                  refine ⟨733808128718194886827763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489205419145463257885175 733808128718194886827763)
                  ·
                    refine ⟨1100712193077292330241645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733808128718194886827763 1100712193077292330241645)
                    ·
                      refine ⟨412767072403984623840617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1100712193077292330241645 412767072403984623840617)
                      ·
                        rfl

theorem cell23_803861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_803861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803861 prefixEnd_803861 := by exact prefixLift 803861
  have htrace : WordTrace (prefixWord ++ tailWord_803861) baseStart_803861 baseEnd_803861 := by
    simpa [prefixWord, tailWord_803861, baseEnd_803861] using wordTrace_append hprefix tailTrace_803861
  have hstable : (prefixWord ++ tailWord_803861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803861).length < 2 ^ (prefixWord ++ tailWord_803861).sum := by decide
  have hdescent : baseEnd_803861 < baseStart_803861 := by decide
  rcases family_descends (prefixWord ++ tailWord_803861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803864 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 1, 5]
def baseStart_803864 : Nat := 118140960795 + 803864 * 2 ^ 59
def prefixEnd_803864 : Nat := 4983230072969 + 3 ^ 40 * 803864 * 2
def baseEnd_803864 : Nat := 137589537615316037367701

theorem tailTrace_803864 : CollatzResearch.WordTrace tailWord_803864 prefixEnd_803864 137589537615316037367701 := by
  unfold tailWord_803864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14659664379872745943085323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19546219173163661257447097 14659664379872745943085323)
  ·
    refine ⟨21989496569809118914627985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14659664379872745943085323 21989496569809118914627985)
    ·
      refine ⟨16492122427356839185970989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21989496569809118914627985 16492122427356839185970989)
      ·
        refine ⟨6184545910258814694739121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16492122427356839185970989 6184545910258814694739121)
        ·
          refine ⟨4638409432694111021054341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6184545910258814694739121 4638409432694111021054341)
          ·
            refine ⟨869701768630145816447689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4638409432694111021054341 869701768630145816447689)
            ·
              refine ⟨652276326472609362335767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 869701768630145816447689 652276326472609362335767)
              ·
                refine ⟨978414489708914043503651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652276326472609362335767 978414489708914043503651)
                ·
                  refine ⟨1467621734563371065255477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 978414489708914043503651 1467621734563371065255477)
                  ·
                    refine ⟨137589537615316037367701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1467621734563371065255477 137589537615316037367701)
                    ·
                      rfl

theorem cell23_803864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 5].length) (baseStart_803864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803864 prefixEnd_803864 := by exact prefixLift 803864
  have htrace : WordTrace (prefixWord ++ tailWord_803864) baseStart_803864 baseEnd_803864 := by
    simpa [prefixWord, tailWord_803864, baseEnd_803864] using wordTrace_append hprefix tailTrace_803864
  have hstable : (prefixWord ++ tailWord_803864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803864).length < 2 ^ (prefixWord ++ tailWord_803864).sum := by decide
  have hdescent : baseEnd_803864 < baseStart_803864 := by decide
  rcases family_descends (prefixWord ++ tailWord_803864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803884 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 3, 2, 2]
def baseStart_803884 : Nat := 118140960795 + 803884 * 2 ^ 59
def prefixEnd_803884 : Nat := 4983230072969 + 3 ^ 40 * 803884 * 2
def baseEnd_803884 : Nat := 412778882459038033853011

theorem tailTrace_803884 : CollatzResearch.WordTrace tailWord_803884 prefixEnd_803884 412778882459038033853011 := by
  unfold tailWord_803884
  simp only [CollatzResearch.WordTrace]
  refine ⟨14660029109836517650949353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19546705479782023534599137 14660029109836517650949353)
  ·
    refine ⟨10995021832377388238212015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14660029109836517650949353 10995021832377388238212015)
    ·
      refine ⟨16492532748566082357318023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995021832377388238212015 16492532748566082357318023)
      ·
        refine ⟨24738799122849123535977035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16492532748566082357318023 24738799122849123535977035)
        ·
          refine ⟨37108198684273685303965553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24738799122849123535977035 37108198684273685303965553)
          ·
            refine ⟨27831149013205263977974165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37108198684273685303965553 27831149013205263977974165)
            ·
              refine ⟨1304585109993996748967539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27831149013205263977974165 1304585109993996748967539)
              ·
                refine ⟨1956877664990995123451309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304585109993996748967539 1956877664990995123451309)
                ·
                  refine ⟨733829124371623171294241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1956877664990995123451309 733829124371623171294241)
                  ·
                    refine ⟨550371843278717378470681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 733829124371623171294241 550371843278717378470681)
                    ·
                      refine ⟨412778882459038033853011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550371843278717378470681 412778882459038033853011)
                      ·
                        rfl

theorem cell23_803884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_803884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803884 prefixEnd_803884 := by exact prefixLift 803884
  have htrace : WordTrace (prefixWord ++ tailWord_803884) baseStart_803884 baseEnd_803884 := by
    simpa [prefixWord, tailWord_803884, baseEnd_803884] using wordTrace_append hprefix tailTrace_803884
  have hstable : (prefixWord ++ tailWord_803884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803884).length < 2 ^ (prefixWord ++ tailWord_803884).sum := by decide
  have hdescent : baseEnd_803884 < baseStart_803884 := by decide
  rcases family_descends (prefixWord ++ tailWord_803884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803894 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_803894 : Nat := 118140960795 + 803894 * 2 ^ 59
def prefixEnd_803894 : Nat := 4983230072969 + 3 ^ 40 * 803894 * 2
def baseEnd_803894 : Nat := 137594672421860998242655

theorem tailTrace_803894 : CollatzResearch.WordTrace tailWord_803894 prefixEnd_803894 137594672421860998242655 := by
  unfold tailWord_803894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1832526434352300438110171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19546948633091204673175157 1832526434352300438110171)
  ·
    refine ⟨2748789651528450657165257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1832526434352300438110171 2748789651528450657165257)
    ·
      refine ⟨2061592238646337992873943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2748789651528450657165257 2061592238646337992873943)
      ·
        refine ⟨3092388357969506989310915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2061592238646337992873943 3092388357969506989310915)
        ·
          refine ⟨4638582536954260483966373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3092388357969506989310915 4638582536954260483966373)
          ·
            refine ⟨869734225678923840743695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4638582536954260483966373 869734225678923840743695)
            ·
              refine ⟨1304601338518385761115543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869734225678923840743695 1304601338518385761115543)
              ·
                refine ⟨1956902007777578641673315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304601338518385761115543 1956902007777578641673315)
                ·
                  refine ⟨2935353011666367962509973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956902007777578641673315 2935353011666367962509973)
                  ·
                    refine ⟨137594672421860998242655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2935353011666367962509973 137594672421860998242655)
                    ·
                      rfl

theorem cell23_803894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_803894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803894 prefixEnd_803894 := by exact prefixLift 803894
  have htrace : WordTrace (prefixWord ++ tailWord_803894) baseStart_803894 baseEnd_803894 := by
    simpa [prefixWord, tailWord_803894, baseEnd_803894] using wordTrace_append hprefix tailTrace_803894
  have hstable : (prefixWord ++ tailWord_803894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803894).length < 2 ^ (prefixWord ++ tailWord_803894).sum := by decide
  have hdescent : baseEnd_803894 < baseStart_803894 := by decide
  rcases family_descends (prefixWord ++ tailWord_803894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803897 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_803897 : Nat := 118140960795 + 803897 * 2 ^ 59
def prefixEnd_803897 : Nat := 4983230072969 + 3 ^ 40 * 803897 * 2
def baseEnd_803897 : Nat := 412785557707546482990451

theorem tailTrace_803897 : CollatzResearch.WordTrace tailWord_803897 prefixEnd_803897 412785557707546482990451 := by
  unfold tailWord_803897
  simp only [CollatzResearch.WordTrace]
  refine ⟨29320532368625938522121945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547021579083959014747963 29320532368625938522121945)
  ·
    refine ⟨21990399276469453891591459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29320532368625938522121945 21990399276469453891591459)
    ·
      refine ⟨32985598914704180837387189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21990399276469453891591459 32985598914704180837387189)
      ·
        refine ⟨3092399898253516953505049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32985598914704180837387189 3092399898253516953505049)
        ·
          refine ⟨2319299923690137715128787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3092399898253516953505049 2319299923690137715128787)
          ·
            refine ⟨3478949885535206572693181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319299923690137715128787 3478949885535206572693181)
            ·
              refine ⟨1304606207075702464759943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3478949885535206572693181 1304606207075702464759943)
              ·
                refine ⟨1956909310613553697139915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1304606207075702464759943 1956909310613553697139915)
                ·
                  refine ⟨2935363965920330545709873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1956909310613553697139915 2935363965920330545709873)
                  ·
                    refine ⟨2201522974440247909282405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2935363965920330545709873 2201522974440247909282405)
                    ·
                      refine ⟨412785557707546482990451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2201522974440247909282405 412785557707546482990451)
                      ·
                        rfl

theorem cell23_803897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_803897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803897 prefixEnd_803897 := by exact prefixLift 803897
  have htrace : WordTrace (prefixWord ++ tailWord_803897) baseStart_803897 baseEnd_803897 := by
    simpa [prefixWord, tailWord_803897, baseEnd_803897] using wordTrace_append hprefix tailTrace_803897
  have hstable : (prefixWord ++ tailWord_803897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803897).length < 2 ^ (prefixWord ++ tailWord_803897).sum := by decide
  have hdescent : baseEnd_803897 < baseStart_803897 := by decide
  rcases family_descends (prefixWord ++ tailWord_803897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803927 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 5, 3, 2]
def baseStart_803927 : Nat := 118140960795 + 803927 * 2 ^ 59
def prefixEnd_803927 : Nat := 4983230072969 + 3 ^ 40 * 803927 * 2
def baseEnd_803927 : Nat := 412800962127181365615313

theorem tailTrace_803927 : CollatzResearch.WordTrace tailWord_803927 prefixEnd_803927 412800962127181365615313 := by
  unfold tailWord_803927
  simp only [CollatzResearch.WordTrace]
  refine ⟨29321626558517253645714035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19547751039011502430476023 29321626558517253645714035)
  ·
    refine ⟨43982439837775880468571053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29321626558517253645714035 43982439837775880468571053)
    ·
      refine ⟨16493414939165955175714145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43982439837775880468571053 16493414939165955175714145)
      ·
        refine ⟨12370061204374466381785609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16493414939165955175714145 12370061204374466381785609)
        ·
          refine ⟨9277545903280849786339207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370061204374466381785609 9277545903280849786339207)
          ·
            refine ⟨13916318854921274679508811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277545903280849786339207 13916318854921274679508811)
            ·
              refine ⟨20874478282381912019263217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916318854921274679508811 20874478282381912019263217)
              ·
                refine ⟨15655858711786434014447413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20874478282381912019263217 15655858711786434014447413)
                ·
                  refine ⟨1467736754229978188854445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15655858711786434014447413 1467736754229978188854445)
                  ·
                    refine ⟨550401282836241820820417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1467736754229978188854445 550401282836241820820417)
                    ·
                      refine ⟨412800962127181365615313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550401282836241820820417 412800962127181365615313)
                      ·
                        rfl

theorem cell23_803927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 3, 2].length) (baseStart_803927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803927 prefixEnd_803927 := by exact prefixLift 803927
  have htrace : WordTrace (prefixWord ++ tailWord_803927) baseStart_803927 baseEnd_803927 := by
    simpa [prefixWord, tailWord_803927, baseEnd_803927] using wordTrace_append hprefix tailTrace_803927
  have hstable : (prefixWord ++ tailWord_803927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803927).length < 2 ^ (prefixWord ++ tailWord_803927).sum := by decide
  have hdescent : baseEnd_803927 < baseStart_803927 := by decide
  rcases family_descends (prefixWord ++ tailWord_803927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803940 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_803940 : Nat := 118140960795 + 803940 * 2 ^ 59
def prefixEnd_803940 : Nat := 4983230072969 + 3 ^ 40 * 803940 * 2
def baseEnd_803940 : Nat := 412807637375689814752753

theorem tailTrace_803940 : CollatzResearch.WordTrace tailWord_803940 prefixEnd_803940 412807637375689814752753 := by
  unfold tailWord_803940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661050353735078432968637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19548067138313437910624849 14661050353735078432968637)
  ·
    refine ⟨5497893882650654412363239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14661050353735078432968637 5497893882650654412363239)
    ·
      refine ⟨8246840823975981618544859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5497893882650654412363239 8246840823975981618544859)
      ·
        refine ⟨12370261235963972427817289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8246840823975981618544859 12370261235963972427817289)
        ·
          refine ⟨9277695926972979320862967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12370261235963972427817289 9277695926972979320862967)
          ·
            refine ⟨13916543890459468981294451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9277695926972979320862967 13916543890459468981294451)
            ·
              refine ⟨20874815835689203471941677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13916543890459468981294451 20874815835689203471941677)
              ·
                refine ⟨7828055938383451301978129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20874815835689203471941677 7828055938383451301978129)
                ·
                  refine ⟨5871041953787588476483597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7828055938383451301978129 5871041953787588476483597)
                  ·
                    refine ⟨2201640732670345678681349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5871041953787588476483597 2201640732670345678681349)
                    ·
                      refine ⟨412807637375689814752753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2201640732670345678681349 412807637375689814752753)
                      ·
                        rfl

theorem cell23_803940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_803940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803940 prefixEnd_803940 := by exact prefixLift 803940
  have htrace : WordTrace (prefixWord ++ tailWord_803940) baseStart_803940 baseEnd_803940 := by
    simpa [prefixWord, tailWord_803940, baseEnd_803940] using wordTrace_append hprefix tailTrace_803940
  have hstable : (prefixWord ++ tailWord_803940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803940).length < 2 ^ (prefixWord ++ tailWord_803940).sum := by decide
  have hdescent : baseEnd_803940 < baseStart_803940 := by decide
  rcases family_descends (prefixWord ++ tailWord_803940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803960 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_803960 : Nat := 118140960795 + 803960 * 2 ^ 59
def prefixEnd_803960 : Nat := 4983230072969 + 3 ^ 40 * 803960 * 2
def baseEnd_803960 : Nat := 412817906988779736502661

theorem tailTrace_803960 : CollatzResearch.WordTrace tailWord_803960 prefixEnd_803960 412817906988779736502661 := by
  unfold tailWord_803960
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661415083698850140832667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19548553444931800187776889 14661415083698850140832667)
  ·
    refine ⟨21992122625548275211249001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14661415083698850140832667 21992122625548275211249001)
    ·
      refine ⟨16494091969161206408436751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21992122625548275211249001 16494091969161206408436751)
      ·
        refine ⟨24741137953741809612655127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16494091969161206408436751 24741137953741809612655127)
        ·
          refine ⟨37111706930612714418982691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24741137953741809612655127 37111706930612714418982691)
          ·
            refine ⟨55667560395919071628474037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37111706930612714418982691 55667560395919071628474037)
            ·
              refine ⟨5218833787117412965169441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55667560395919071628474037 5218833787117412965169441)
              ·
                refine ⟨3914125340338059723877081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5218833787117412965169441 3914125340338059723877081)
                ·
                  refine ⟨2935594005253544792907811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914125340338059723877081 2935594005253544792907811)
                  ·
                    refine ⟨4403391007880317189361717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2935594005253544792907811 4403391007880317189361717)
                    ·
                      refine ⟨412817906988779736502661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4403391007880317189361717 412817906988779736502661)
                      ·
                        rfl

theorem cell23_803960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_803960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803960 prefixEnd_803960 := by exact prefixLift 803960
  have htrace : WordTrace (prefixWord ++ tailWord_803960) baseStart_803960 baseEnd_803960 := by
    simpa [prefixWord, tailWord_803960, baseEnd_803960] using wordTrace_append hprefix tailTrace_803960
  have hstable : (prefixWord ++ tailWord_803960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803960).length < 2 ^ (prefixWord ++ tailWord_803960).sum := by decide
  have hdescent : baseEnd_803960 < baseStart_803960 := by decide
  rcases family_descends (prefixWord ++ tailWord_803960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_803991 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 2, 2, 2]
def baseStart_803991 : Nat := 118140960795 + 803991 * 2 ^ 59
def prefixEnd_803991 : Nat := 4983230072969 + 3 ^ 40 * 803991 * 2
def baseEnd_803991 : Nat := 412833824889069115215019

theorem tailTrace_803991 : CollatzResearch.WordTrace tailWord_803991 prefixEnd_803991 412833824889069115215019 := by
  unfold tailWord_803991
  simp only [CollatzResearch.WordTrace]
  refine ⟨29323960830285392576043827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19549307220190261717362551 29323960830285392576043827)
  ·
    refine ⟨43985941245428088864065741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29323960830285392576043827 43985941245428088864065741)
    ·
      refine ⟨16494727967035533324024653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43985941245428088864065741 16494727967035533324024653)
      ·
        refine ⟨6185522987638324996509245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16494727967035533324024653 6185522987638324996509245)
        ·
          refine ⟨2319571120364371873690967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6185522987638324996509245 2319571120364371873690967)
          ·
            refine ⟨3479356680546557810536451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319571120364371873690967 3479356680546557810536451)
            ·
              refine ⟨5219035020819836715804677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3479356680546557810536451 5219035020819836715804677)
              ·
                refine ⟨978569066403719384213377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5219035020819836715804677 978569066403719384213377)
                ·
                  refine ⟨733926799802789538160033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978569066403719384213377 733926799802789538160033)
                  ·
                    refine ⟨550445099852092153620025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 733926799802789538160033 550445099852092153620025)
                    ·
                      refine ⟨412833824889069115215019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550445099852092153620025 412833824889069115215019)
                      ·
                        rfl

theorem cell23_803991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_803991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_803991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_803991 prefixEnd_803991 := by exact prefixLift 803991
  have htrace : WordTrace (prefixWord ++ tailWord_803991) baseStart_803991 baseEnd_803991 := by
    simpa [prefixWord, tailWord_803991, baseEnd_803991] using wordTrace_append hprefix tailTrace_803991
  have hstable : (prefixWord ++ tailWord_803991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_803991).length < 2 ^ (prefixWord ++ tailWord_803991).sum := by decide
  have hdescent : baseEnd_803991 < baseStart_803991 := by decide
  rcases family_descends (prefixWord ++ tailWord_803991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804064 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2]
def baseStart_804064 : Nat := 118140960795 + 804064 * 2 ^ 59
def prefixEnd_804064 : Nat := 4983230072969 + 3 ^ 40 * 804064 * 2
def baseEnd_804064 : Nat := 412871308976847329602183

theorem tailTrace_804064 : CollatzResearch.WordTrace tailWord_804064 prefixEnd_804064 412871308976847329602183 := by
  unfold tailWord_804064
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663311679510463021725623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19551082239347284028967497 14663311679510463021725623)
  ·
    refine ⟨21994967519265694532588435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14663311679510463021725623 21994967519265694532588435)
    ·
      refine ⟨32992451278898541798882653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21994967519265694532588435 32992451278898541798882653)
      ·
        refine ⟨12372169229586953174580995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32992451278898541798882653 12372169229586953174580995)
        ·
          refine ⟨18558253844380429761871493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12372169229586953174580995 18558253844380429761871493)
          ·
            refine ⟨3479672595821330580350905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18558253844380429761871493 3479672595821330580350905)
            ·
              refine ⟨2609754446865997935263179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479672595821330580350905 2609754446865997935263179)
              ·
                refine ⟨3914631670298996902894769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2609754446865997935263179 3914631670298996902894769)
                ·
                  refine ⟨2935973752724247677171077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3914631670298996902894769 2935973752724247677171077)
                  ·
                    refine ⟨550495078635796439469577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2935973752724247677171077 550495078635796439469577)
                    ·
                      refine ⟨412871308976847329602183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550495078635796439469577 412871308976847329602183)
                      ·
                        rfl

theorem cell23_804064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_804064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804064 prefixEnd_804064 := by exact prefixLift 804064
  have htrace : WordTrace (prefixWord ++ tailWord_804064) baseStart_804064 baseEnd_804064 := by
    simpa [prefixWord, tailWord_804064, baseEnd_804064] using wordTrace_append hprefix tailTrace_804064
  have hstable : (prefixWord ++ tailWord_804064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804064).length < 2 ^ (prefixWord ++ tailWord_804064).sum := by decide
  have hdescent : baseEnd_804064 < baseStart_804064 := by decide
  rcases family_descends (prefixWord ++ tailWord_804064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804074 : List Nat := [3, 1, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_804074 : Nat := 118140960795 + 804074 * 2 ^ 59
def prefixEnd_804074 : Nat := 4983230072969 + 3 ^ 40 * 804074 * 2
def baseEnd_804074 : Nat := 137625481261130763492379

theorem tailTrace_804074 : CollatzResearch.WordTrace tailWord_804074 prefixEnd_804074 137625481261130763492379 := by
  unfold tailWord_804074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331747022246174437828819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19551325392656465167543517 7331747022246174437828819)
  ·
    refine ⟨10997620533369261656743229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7331747022246174437828819 10997620533369261656743229)
    ·
      refine ⟨4124107700013473121278711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10997620533369261656743229 4124107700013473121278711)
      ·
        refine ⟨6186161550020209681918067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124107700013473121278711 6186161550020209681918067)
        ·
          refine ⟨9279242325030314522877101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186161550020209681918067 9279242325030314522877101)
          ·
            refine ⟨3479715871886367946078913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9279242325030314522877101 3479715871886367946078913)
            ·
              refine ⟨2609786903914775959559185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3479715871886367946078913 2609786903914775959559185)
              ·
                refine ⟨1957340177936081969669389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2609786903914775959559185 1957340177936081969669389)
                ·
                  refine ⟨734002566726030738626021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1957340177936081969669389 734002566726030738626021)
                  ·
                    refine ⟨137625481261130763492379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734002566726030738626021 137625481261130763492379)
                    ·
                      rfl

theorem cell23_804074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_804074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804074 prefixEnd_804074 := by exact prefixLift 804074
  have htrace : WordTrace (prefixWord ++ tailWord_804074) baseStart_804074 baseEnd_804074 := by
    simpa [prefixWord, tailWord_804074, baseEnd_804074] using wordTrace_append hprefix tailTrace_804074
  have hstable : (prefixWord ++ tailWord_804074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804074).length < 2 ^ (prefixWord ++ tailWord_804074).sum := by decide
  have hdescent : baseEnd_804074 < baseStart_804074 := by decide
  rcases family_descends (prefixWord ++ tailWord_804074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804080 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_804080 : Nat := 118140960795 + 804080 * 2 ^ 59
def prefixEnd_804080 : Nat := 4983230072969 + 3 ^ 40 * 804080 * 2
def baseEnd_804080 : Nat := 412879524667319267002109

theorem tailTrace_804080 : CollatzResearch.WordTrace tailWord_804080 prefixEnd_804080 412879524667319267002109 := by
  unfold tailWord_804080
  simp only [CollatzResearch.WordTrace]
  refine ⟨14663603463481480388016847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19551471284641973850689129 14663603463481480388016847)
  ·
    refine ⟨21995405195222220582025271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14663603463481480388016847 21995405195222220582025271)
    ·
      refine ⟨32993107792833330873037907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21995405195222220582025271 32993107792833330873037907)
      ·
        refine ⟨49489661689249996309556861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32993107792833330873037907 49489661689249996309556861)
        ·
          refine ⟨18558623133468748616083823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49489661689249996309556861 18558623133468748616083823)
          ·
            refine ⟨27837934700203122924125735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18558623133468748616083823 27837934700203122924125735)
            ·
              refine ⟨41756902050304684386188603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27837934700203122924125735 41756902050304684386188603)
              ·
                refine ⟨62635353075457026579282905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41756902050304684386188603 62635353075457026579282905)
                ·
                  refine ⟨46976514806592769934462179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62635353075457026579282905 46976514806592769934462179)
                  ·
                    refine ⟨70464772209889154901693269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46976514806592769934462179 70464772209889154901693269)
                    ·
                      refine ⟨412879524667319267002109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 70464772209889154901693269 412879524667319267002109)
                      ·
                        rfl

theorem cell23_804080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_804080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804080 prefixEnd_804080 := by exact prefixLift 804080
  have htrace : WordTrace (prefixWord ++ tailWord_804080) baseStart_804080 baseEnd_804080 := by
    simpa [prefixWord, tailWord_804080, baseEnd_804080] using wordTrace_append hprefix tailTrace_804080
  have hstable : (prefixWord ++ tailWord_804080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804080).length < 2 ^ (prefixWord ++ tailWord_804080).sum := by decide
  have hdescent : baseEnd_804080 < baseStart_804080 := by decide
  rcases family_descends (prefixWord ++ tailWord_804080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804108 : List Nat := [2, 2, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_804108 : Nat := 118140960795 + 804108 * 2 ^ 59
def prefixEnd_804108 : Nat := 4983230072969 + 3 ^ 40 * 804108 * 2
def baseEnd_804108 : Nat := 137631300708548385817327

theorem tailTrace_804108 : CollatzResearch.WordTrace tailWord_804108 prefixEnd_804108 137631300708548385817327 := by
  unfold tailWord_804108
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664114085430760779026489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19552152113907681038701985 14664114085430760779026489)
  ·
    refine ⟨10998085564073070584269867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14664114085430760779026489 10998085564073070584269867)
    ·
      refine ⟨16497128346109605876404801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10998085564073070584269867 16497128346109605876404801)
      ·
        refine ⟨12372846259582204407303601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16497128346109605876404801 12372846259582204407303601)
        ·
          refine ⟨9279634694686653305477701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372846259582204407303601 9279634694686653305477701)
          ·
            refine ⟨1739931505253747494777069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9279634694686653305477701 1739931505253747494777069)
            ·
              refine ⟨652474314470155310541401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1739931505253747494777069 652474314470155310541401)
              ·
                refine ⟨489355735852616482906051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 652474314470155310541401 489355735852616482906051)
                ·
                  refine ⟨734033603778924724359077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489355735852616482906051 734033603778924724359077)
                  ·
                    refine ⟨137631300708548385817327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734033603778924724359077 137631300708548385817327)
                    ·
                      rfl

theorem cell23_804108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_804108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804108 prefixEnd_804108 := by exact prefixLift 804108
  have htrace : WordTrace (prefixWord ++ tailWord_804108) baseStart_804108 baseEnd_804108 := by
    simpa [prefixWord, tailWord_804108, baseEnd_804108] using wordTrace_append hprefix tailTrace_804108
  have hstable : (prefixWord ++ tailWord_804108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804108).length < 2 ^ (prefixWord ++ tailWord_804108).sum := by decide
  have hdescent : baseEnd_804108 < baseStart_804108 := by decide
  rcases family_descends (prefixWord ++ tailWord_804108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804117 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 3, 5]
def baseStart_804117 : Nat := 118140960795 + 804117 * 2 ^ 59
def prefixEnd_804117 : Nat := 4983230072969 + 3 ^ 40 * 804117 * 2
def baseEnd_804117 : Nat := 137632841150511874079813

theorem tailTrace_804117 : CollatzResearch.WordTrace tailWord_804117 prefixEnd_804117 137632841150511874079813 := by
  unfold tailWord_804117
  simp only [CollatzResearch.WordTrace]
  refine ⟨29328556427828916095130605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19552370951885944063420403 29328556427828916095130605)
  ·
    refine ⟨10998208660435843535673977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29328556427828916095130605 10998208660435843535673977)
    ·
      refine ⟨8248656495326882651755483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10998208660435843535673977 8248656495326882651755483)
      ·
        refine ⟨12372984742990323977633225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8248656495326882651755483 12372984742990323977633225)
        ·
          refine ⟨9279738557242742983224919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12372984742990323977633225 9279738557242742983224919)
          ·
            refine ⟨13919607835864114474837379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279738557242742983224919 13919607835864114474837379)
            ·
              refine ⟨20879411753796171712256069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13919607835864114474837379 20879411753796171712256069)
              ·
                refine ⟨3914889703836782196048013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20879411753796171712256069 3914889703836782196048013)
                ·
                  refine ⟨1468083638938793323518005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3914889703836782196048013 1468083638938793323518005)
                  ·
                    refine ⟨137632841150511874079813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1468083638938793323518005 137632841150511874079813)
                    ·
                      rfl

theorem cell23_804117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 5].length) (baseStart_804117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804117 prefixEnd_804117 := by exact prefixLift 804117
  have htrace : WordTrace (prefixWord ++ tailWord_804117) baseStart_804117 baseEnd_804117 := by
    simpa [prefixWord, tailWord_804117, baseEnd_804117] using wordTrace_append hprefix tailTrace_804117
  have hstable : (prefixWord ++ tailWord_804117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804117).length < 2 ^ (prefixWord ++ tailWord_804117).sum := by decide
  have hdescent : baseEnd_804117 < baseStart_804117 := by decide
  rcases family_descends (prefixWord ++ tailWord_804117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804124 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 5, 2]
def baseStart_804124 : Nat := 118140960795 + 804124 * 2 ^ 59
def prefixEnd_804124 : Nat := 4983230072969 + 3 ^ 40 * 804124 * 2
def baseEnd_804124 : Nat := 412902117816117094851907

theorem tailTrace_804124 : CollatzResearch.WordTrace tailWord_804124 prefixEnd_804124 412902117816117094851907 := by
  unfold tailWord_804124
  simp only [CollatzResearch.WordTrace]
  refine ⟨14664405869401778145317713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19552541159202370860423617 14664405869401778145317713)
  ·
    refine ⟨10998304402051333608988285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14664405869401778145317713 10998304402051333608988285)
    ·
      refine ⟨4124364150769250103370607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10998304402051333608988285 4124364150769250103370607)
      ·
        refine ⟨6186546226153875155055911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124364150769250103370607 6186546226153875155055911)
        ·
          refine ⟨9279819339230812732583867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6186546226153875155055911 9279819339230812732583867)
          ·
            refine ⟨13919729008846219098875801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9279819339230812732583867 13919729008846219098875801)
            ·
              refine ⟨10439796756634664324156851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13919729008846219098875801 10439796756634664324156851)
              ·
                refine ⟨15659695134951996486235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10439796756634664324156851 15659695134951996486235277)
                ·
                  refine ⟨5872385675606998682338229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15659695134951996486235277 5872385675606998682338229)
                  ·
                    refine ⟨550536157088156126469209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5872385675606998682338229 550536157088156126469209)
                    ·
                      refine ⟨412902117816117094851907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550536157088156126469209 412902117816117094851907)
                      ·
                        rfl

theorem cell23_804124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_804124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804124 prefixEnd_804124 := by exact prefixLift 804124
  have htrace : WordTrace (prefixWord ++ tailWord_804124) baseStart_804124 baseEnd_804124 := by
    simpa [prefixWord, tailWord_804124, baseEnd_804124] using wordTrace_append hprefix tailTrace_804124
  have hstable : (prefixWord ++ tailWord_804124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804124).length < 2 ^ (prefixWord ++ tailWord_804124).sum := by decide
  have hdescent : baseEnd_804124 < baseStart_804124 := by decide
  rcases family_descends (prefixWord ++ tailWord_804124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804147 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 6]
def baseStart_804147 : Nat := 118140960795 + 804147 * 2 ^ 59
def prefixEnd_804147 : Nat := 4983230072969 + 3 ^ 40 * 804147 * 2
def baseEnd_804147 : Nat := 137637975957056834954767

theorem tailTrace_804147 : CollatzResearch.WordTrace tailWord_804147 prefixEnd_804147 137637975957056834954767 := by
  unfold tailWord_804147
  simp only [CollatzResearch.WordTrace]
  refine ⟨29329650617720231218722695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19553100411813487479148463 29329650617720231218722695)
  ·
    refine ⟨43994475926580346828084043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29329650617720231218722695 43994475926580346828084043)
    ·
      refine ⟨65991713889870520242126065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43994475926580346828084043 65991713889870520242126065)
      ·
        refine ⟨49493785417402890181594549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65991713889870520242126065 49493785417402890181594549)
        ·
          refine ⟨4640042382881520954524489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49493785417402890181594549 4640042382881520954524489)
          ·
            refine ⟨3480031787161140715893367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4640042382881520954524489 3480031787161140715893367)
            ·
              refine ⟨5220047680741711073840051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480031787161140715893367 5220047680741711073840051)
              ·
                refine ⟨7830071521112566610760077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5220047680741711073840051 7830071521112566610760077)
                ·
                  refine ⟨2936276820417212479035029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7830071521112566610760077 2936276820417212479035029)
                  ·
                    refine ⟨137637975957056834954767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2936276820417212479035029 137637975957056834954767)
                    ·
                      rfl

theorem cell23_804147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_804147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804147 prefixEnd_804147 := by exact prefixLift 804147
  have htrace : WordTrace (prefixWord ++ tailWord_804147) baseStart_804147 baseEnd_804147 := by
    simpa [prefixWord, tailWord_804147, baseEnd_804147] using wordTrace_append hprefix tailTrace_804147
  have hstable : (prefixWord ++ tailWord_804147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804147).length < 2 ^ (prefixWord ++ tailWord_804147).sum := by decide
  have hdescent : baseEnd_804147 < baseStart_804147 := by decide
  rcases family_descends (prefixWord ++ tailWord_804147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804174 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_804174 : Nat := 118140960795 + 804174 * 2 ^ 59
def prefixEnd_804174 : Nat := 4983230072969 + 3 ^ 40 * 804174 * 2
def baseEnd_804174 : Nat := 412927791848841899226677

theorem tailTrace_804174 : CollatzResearch.WordTrace tailWord_804174 prefixEnd_804174 412927791848841899226677 := by
  unfold tailWord_804174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3666329423577801853744447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19553756925748276553303717 3666329423577801853744447)
  ·
    refine ⟨5499494135366702780616671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3666329423577801853744447 5499494135366702780616671)
    ·
      refine ⟨8249241203050054170925007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499494135366702780616671 8249241203050054170925007)
      ·
        refine ⟨12373861804575081256387511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249241203050054170925007 12373861804575081256387511)
        ·
          refine ⟨18560792706862621884581267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12373861804575081256387511 18560792706862621884581267)
          ·
            refine ⟨27841189060293932826871901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18560792706862621884581267 27841189060293932826871901)
            ·
              refine ⟨10440445897610224810076963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27841189060293932826871901 10440445897610224810076963)
              ·
                refine ⟨15660668846415337215115445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10440445897610224810076963 15660668846415337215115445)
                ·
                  refine ⟨1468187704351437863917073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15660668846415337215115445 1468187704351437863917073)
                  ·
                    refine ⟨1101140778263578397937805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468187704351437863917073 1101140778263578397937805)
                    ·
                      refine ⟨412927791848841899226677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101140778263578397937805 412927791848841899226677)
                      ·
                        rfl

theorem cell23_804174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_804174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804174 prefixEnd_804174 := by exact prefixLift 804174
  have htrace : WordTrace (prefixWord ++ tailWord_804174) baseStart_804174 baseEnd_804174 := by
    simpa [prefixWord, tailWord_804174, baseEnd_804174] using wordTrace_append hprefix tailTrace_804174
  have hstable : (prefixWord ++ tailWord_804174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804174).length < 2 ^ (prefixWord ++ tailWord_804174).sum := by decide
  have hdescent : baseEnd_804174 < baseStart_804174 := by decide
  rcases family_descends (prefixWord ++ tailWord_804174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804181 : List Nat := [1, 3, 2, 2, 3, 1, 2, 3, 2, 4]
def baseStart_804181 : Nat := 118140960795 + 804181 * 2 ^ 59
def prefixEnd_804181 : Nat := 4983230072969 + 3 ^ 40 * 804181 * 2
def baseEnd_804181 : Nat := 137643795404474457279715

theorem tailTrace_804181 : CollatzResearch.WordTrace tailWord_804181 prefixEnd_804181 137643795404474457279715 := by
  unfold tailWord_804181
  simp only [CollatzResearch.WordTrace]
  refine ⟨29330890699597055025460397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19553927133064703350306931 29330890699597055025460397)
  ·
    refine ⟨10999084012348895634547649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29330890699597055025460397 10999084012348895634547649)
    ·
      refine ⟨8249313009261671725910737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10999084012348895634547649 8249313009261671725910737)
      ·
        refine ⟨6186984756946253794433053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8249313009261671725910737 6186984756946253794433053)
        ·
          refine ⟨2320119283854845172912395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6186984756946253794433053 2320119283854845172912395)
          ·
            refine ⟨3480178925782267759368593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320119283854845172912395 3480178925782267759368593)
            ·
              refine ⟨2610134194336700819526445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3480178925782267759368593 2610134194336700819526445)
              ·
                refine ⟨978800322876262807322417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2610134194336700819526445 978800322876262807322417)
                ·
                  refine ⟨734100242157197105491813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 978800322876262807322417 734100242157197105491813)
                  ·
                    refine ⟨137643795404474457279715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734100242157197105491813 137643795404474457279715)
                    ·
                      rfl

theorem cell23_804181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_804181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804181 prefixEnd_804181 := by exact prefixLift 804181
  have htrace : WordTrace (prefixWord ++ tailWord_804181) baseStart_804181 baseEnd_804181 := by
    simpa [prefixWord, tailWord_804181, baseEnd_804181] using wordTrace_append hprefix tailTrace_804181
  have hstable : (prefixWord ++ tailWord_804181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804181).length < 2 ^ (prefixWord ++ tailWord_804181).sum := by decide
  have hdescent : baseEnd_804181 < baseStart_804181 := by decide
  rcases family_descends (prefixWord ++ tailWord_804181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804184 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_804184 : Nat := 118140960795 + 804184 * 2 ^ 59
def prefixEnd_804184 : Nat := 4983230072969 + 3 ^ 40 * 804184 * 2
def baseEnd_804184 : Nat := 412932926655386860101631

theorem tailTrace_804184 : CollatzResearch.WordTrace tailWord_804184 prefixEnd_804184 412932926655386860101631 := by
  unfold tailWord_804184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14665500059293093268909803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19554000079057457691879737 14665500059293093268909803)
  ·
    refine ⟨21998250088939639903364705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14665500059293093268909803 21998250088939639903364705)
    ·
      refine ⟨16498687566704729927523529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21998250088939639903364705 16498687566704729927523529)
      ·
        refine ⟨12374015675028547445642647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16498687566704729927523529 12374015675028547445642647)
        ·
          refine ⟨18561023512542821168463971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12374015675028547445642647 18561023512542821168463971)
          ·
            refine ⟨27841535268814231752695957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18561023512542821168463971 27841535268814231752695957)
            ·
              refine ⟨1305071965725667113407623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27841535268814231752695957 1305071965725667113407623)
              ·
                refine ⟨1957607948588500670111435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305071965725667113407623 1957607948588500670111435)
                ·
                  refine ⟨2936411922882751005167153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1957607948588500670111435 2936411922882751005167153)
                  ·
                    refine ⟨2202308942162063253875365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936411922882751005167153 2202308942162063253875365)
                    ·
                      refine ⟨412932926655386860101631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2202308942162063253875365 412932926655386860101631)
                      ·
                        rfl

theorem cell23_804184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_804184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804184 prefixEnd_804184 := by exact prefixLift 804184
  have htrace : WordTrace (prefixWord ++ tailWord_804184) baseStart_804184 baseEnd_804184 := by
    simpa [prefixWord, tailWord_804184, baseEnd_804184] using wordTrace_append hprefix tailTrace_804184
  have hstable : (prefixWord ++ tailWord_804184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804184).length < 2 ^ (prefixWord ++ tailWord_804184).sum := by decide
  have hdescent : baseEnd_804184 < baseStart_804184 := by decide
  rcases family_descends (prefixWord ++ tailWord_804184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804205 : List Nat := [1, 5, 1, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_804205 : Nat := 118140960795 + 804205 * 2 ^ 59
def prefixEnd_804205 : Nat := 4983230072969 + 3 ^ 40 * 804205 * 2
def baseEnd_804205 : Nat := 412943709749131277939035

theorem tailTrace_804205 : CollatzResearch.WordTrace tailWord_804205 prefixEnd_804205 412943709749131277939035 := by
  unfold tailWord_804205
  simp only [CollatzResearch.WordTrace]
  refine ⟨29331766051510107124334069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19554510701006738082889379 29331766051510107124334069)
  ·
    refine ⟨2749853067329072542906319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29331766051510107124334069 2749853067329072542906319)
    ·
      refine ⟨4124779600993608814359479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749853067329072542906319 4124779600993608814359479)
      ·
        refine ⟨6187169401490413221539219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4124779600993608814359479 6187169401490413221539219)
        ·
          refine ⟨9280754102235619832308829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187169401490413221539219 9280754102235619832308829)
          ·
            refine ⟨3480282788338357437115811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9280754102235619832308829 3480282788338357437115811)
            ·
              refine ⟨5220424182507536155673717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480282788338357437115811 5220424182507536155673717)
              ·
                refine ⟨489414767110081514594411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5220424182507536155673717 489414767110081514594411)
                ·
                  refine ⟨734122150665122271891617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489414767110081514594411 734122150665122271891617)
                  ·
                    refine ⟨550591612998841703918713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 734122150665122271891617 550591612998841703918713)
                    ·
                      refine ⟨412943709749131277939035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550591612998841703918713 412943709749131277939035)
                      ·
                        rfl

theorem cell23_804205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_804205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804205 prefixEnd_804205 := by exact prefixLift 804205
  have htrace : WordTrace (prefixWord ++ tailWord_804205) baseStart_804205 baseEnd_804205 := by
    simpa [prefixWord, tailWord_804205, baseEnd_804205] using wordTrace_append hprefix tailTrace_804205
  have hstable : (prefixWord ++ tailWord_804205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804205).length < 2 ^ (prefixWord ++ tailWord_804205).sum := by decide
  have hdescent : baseEnd_804205 < baseStart_804205 := by decide
  rcases family_descends (prefixWord ++ tailWord_804205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804221 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 3]
def baseStart_804221 : Nat := 118140960795 + 804221 * 2 ^ 59
def prefixEnd_804221 : Nat := 4983230072969 + 3 ^ 40 * 804221 * 2
def baseEnd_804221 : Nat := 412951925439603215338961

theorem tailTrace_804221 : CollatzResearch.WordTrace tailWord_804221 prefixEnd_804221 412951925439603215338961 := by
  unfold tailWord_804221
  simp only [CollatzResearch.WordTrace]
  refine ⟨29332349619452141856916517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19554899746301427904611011 29332349619452141856916517)
  ·
    refine ⟨5499815553647276598171847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29332349619452141856916517 5499815553647276598171847)
    ·
      refine ⟨8249723330470914897257771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5499815553647276598171847 8249723330470914897257771)
      ·
        refine ⟨12374584995706372345886657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8249723330470914897257771 12374584995706372345886657)
        ·
          refine ⟨9280938746779779259414993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12374584995706372345886657 9280938746779779259414993)
          ·
            refine ⟨6960704060084834444561245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9280938746779779259414993 6960704060084834444561245)
            ·
              refine ⟨2610264022531812916710467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6960704060084834444561245 2610264022531812916710467)
              ·
                refine ⟨3915396033797719375065701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610264022531812916710467 3915396033797719375065701)
                ·
                  refine ⟨734136756337072382824819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3915396033797719375065701 734136756337072382824819)
                  ·
                    refine ⟨1101205134505608574237229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734136756337072382824819 1101205134505608574237229)
                    ·
                      refine ⟨412951925439603215338961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101205134505608574237229 412951925439603215338961)
                      ·
                        rfl

theorem cell23_804221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_804221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804221 prefixEnd_804221 := by exact prefixLift 804221
  have htrace : WordTrace (prefixWord ++ tailWord_804221) baseStart_804221 baseEnd_804221 := by
    simpa [prefixWord, tailWord_804221, baseEnd_804221] using wordTrace_append hprefix tailTrace_804221
  have hstable : (prefixWord ++ tailWord_804221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804221).length < 2 ^ (prefixWord ++ tailWord_804221).sum := by decide
  have hdescent : baseEnd_804221 < baseStart_804221 := by decide
  rcases family_descends (prefixWord ++ tailWord_804221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804274 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_804274 : Nat := 118140960795 + 804274 * 2 ^ 59
def prefixEnd_804274 : Nat := 4983230072969 + 3 ^ 40 * 804274 * 2
def baseEnd_804274 : Nat := 412979139914291507976217

theorem tailTrace_804274 : CollatzResearch.WordTrace tailWord_804274 prefixEnd_804274 412979139914291507976217 := by
  unfold tailWord_804274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333570672065032977148969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19556188458840087939063917 7333570672065032977148969)
  ·
    refine ⟨5500178004048774732861727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7333570672065032977148969 5500178004048774732861727)
    ·
      refine ⟨8250267006073162099292591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500178004048774732861727 8250267006073162099292591)
      ·
        refine ⟨12375400509109743148938887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8250267006073162099292591 12375400509109743148938887)
        ·
          refine ⟨18563100763664614723408331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12375400509109743148938887 18563100763664614723408331)
          ·
            refine ⟨27844651145496922085112497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18563100763664614723408331 27844651145496922085112497)
            ·
              refine ⟨20883488359122691563834373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27844651145496922085112497 20883488359122691563834373)
              ·
                refine ⟨3915654067335504668218945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20883488359122691563834373 3915654067335504668218945)
                ·
                  refine ⟨2936740550501628501164209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3915654067335504668218945 2936740550501628501164209)
                  ·
                    refine ⟨2202555412876221375873157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2936740550501628501164209 2202555412876221375873157)
                    ·
                      refine ⟨412979139914291507976217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2202555412876221375873157 412979139914291507976217)
                      ·
                        rfl

theorem cell23_804274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_804274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804274 prefixEnd_804274 := by exact prefixLift 804274
  have htrace : WordTrace (prefixWord ++ tailWord_804274) baseStart_804274 baseEnd_804274 := by
    simpa [prefixWord, tailWord_804274, baseEnd_804274] using wordTrace_append hprefix tailTrace_804274
  have hstable : (prefixWord ++ tailWord_804274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804274).length < 2 ^ (prefixWord ++ tailWord_804274).sum := by decide
  have hdescent : baseEnd_804274 < baseStart_804274 := by decide
  rcases family_descends (prefixWord ++ tailWord_804274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804338 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_804338 : Nat := 118140960795 + 804338 * 2 ^ 59
def prefixEnd_804338 : Nat := 4983230072969 + 3 ^ 40 * 804338 * 2
def baseEnd_804338 : Nat := 413012002676179257575923

theorem tailTrace_804338 : CollatzResearch.WordTrace tailWord_804338 prefixEnd_804338 413012002676179257575923 := by
  unfold tailWord_804338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7334154240007067709731417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19557744640018847225950445 7334154240007067709731417)
  ·
    refine ⟨5500615680005300782298563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7334154240007067709731417 5500615680005300782298563)
    ·
      refine ⟨8250923520007951173447845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5500615680005300782298563 8250923520007951173447845)
      ·
        refine ⟨1547048160001490845021471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8250923520007951173447845 1547048160001490845021471)
        ·
          refine ⟨2320572240002236267532207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547048160001490845021471 2320572240002236267532207)
          ·
            refine ⟨3480858360003354401298311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2320572240002236267532207 3480858360003354401298311)
            ·
              refine ⟨5221287540005031601947467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3480858360003354401298311 5221287540005031601947467)
              ·
                refine ⟨7831931310007547402921201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5221287540005031601947467 7831931310007547402921201)
                ·
                  refine ⟨5873948482505660552190901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7831931310007547402921201 5873948482505660552190901)
                  ·
                    refine ⟨550682670234905676767897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5873948482505660552190901 550682670234905676767897)
                    ·
                      refine ⟨413012002676179257575923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550682670234905676767897 413012002676179257575923)
                      ·
                        rfl

theorem cell23_804338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_804338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804338 prefixEnd_804338 := by exact prefixLift 804338
  have htrace : WordTrace (prefixWord ++ tailWord_804338) baseStart_804338 baseEnd_804338 := by
    simpa [prefixWord, tailWord_804338, baseEnd_804338] using wordTrace_append hprefix tailTrace_804338
  have hstable : (prefixWord ++ tailWord_804338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804338).length < 2 ^ (prefixWord ++ tailWord_804338).sum := by decide
  have hdescent : baseEnd_804338 < baseStart_804338 := by decide
  rcases family_descends (prefixWord ++ tailWord_804338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804361 : List Nat := [1, 2, 1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_804361 : Nat := 118140960795 + 804361 * 2 ^ 59
def prefixEnd_804361 : Nat := 4983230072969 + 3 ^ 40 * 804361 * 2
def baseEnd_804361 : Nat := 137674604243744222529439

theorem tailTrace_804361 : CollatzResearch.WordTrace tailWord_804361 prefixEnd_804361 137674604243744222529439 := by
  unfold tailWord_804361
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337455838944945767012937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19558303892629963844675291 29337455838944945767012937)
  ·
    refine ⟨22003091879208709325259703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29337455838944945767012937 22003091879208709325259703)
    ·
      refine ⟨33004637818813063987889555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22003091879208709325259703 33004637818813063987889555)
      ·
        refine ⟨49506956728219595981834333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33004637818813063987889555 49506956728219595981834333)
        ·
          refine ⟨18565108773082348493187875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49506956728219595981834333 18565108773082348493187875)
          ·
            refine ⟨27847663159623522739781813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18565108773082348493187875 27847663159623522739781813)
            ·
              refine ⟨2610718421214705256854545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27847663159623522739781813 2610718421214705256854545)
              ·
                refine ⟨1958038815911028942640909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2610718421214705256854545 1958038815911028942640909)
                ·
                  refine ⟨734264555966635853490341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1958038815911028942640909 734264555966635853490341)
                  ·
                    refine ⟨137674604243744222529439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734264555966635853490341 137674604243744222529439)
                    ·
                      rfl

theorem cell23_804361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_804361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804361 prefixEnd_804361 := by exact prefixLift 804361
  have htrace : WordTrace (prefixWord ++ tailWord_804361) baseStart_804361 baseEnd_804361 := by
    simpa [prefixWord, tailWord_804361, baseEnd_804361] using wordTrace_append hprefix tailTrace_804361
  have hstable : (prefixWord ++ tailWord_804361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804361).length < 2 ^ (prefixWord ++ tailWord_804361).sum := by decide
  have hdescent : baseEnd_804361 < baseStart_804361 := by decide
  rcases family_descends (prefixWord ++ tailWord_804361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804365 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_804365 : Nat := 118140960795 + 804365 * 2 ^ 59
def prefixEnd_804365 : Nat := 4983230072969 + 3 ^ 40 * 804365 * 2
def baseEnd_804365 : Nat := 137675288884616883979433

theorem tailTrace_804365 : CollatzResearch.WordTrace tailWord_804365 prefixEnd_804365 137675288884616883979433 := by
  unfold tailWord_804365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337601730930454450158549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19558401153953636300105699 29337601730930454450158549)
  ·
    refine ⟨687600040568682526175591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 29337601730930454450158549 687600040568682526175591)
    ·
      refine ⟨1031400060853023789263387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687600040568682526175591 1031400060853023789263387)
      ·
        refine ⟨1547100091279535683895081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031400060853023789263387 1547100091279535683895081)
        ·
          refine ⟨1160325068459651762921311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547100091279535683895081 1160325068459651762921311)
          ·
            refine ⟨1740487602689477644381967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160325068459651762921311 1740487602689477644381967)
            ·
              refine ⟨2610731404034216466572951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740487602689477644381967 2610731404034216466572951)
              ·
                refine ⟨3916097106051324699859427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610731404034216466572951 3916097106051324699859427)
                ·
                  refine ⟨5874145659076987049789141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916097106051324699859427 5874145659076987049789141)
                  ·
                    refine ⟨137675288884616883979433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5874145659076987049789141 137675288884616883979433)
                    ·
                      rfl

theorem cell23_804365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_804365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804365 prefixEnd_804365 := by exact prefixLift 804365
  have htrace : WordTrace (prefixWord ++ tailWord_804365) baseStart_804365 baseEnd_804365 := by
    simpa [prefixWord, tailWord_804365, baseEnd_804365] using wordTrace_append hprefix tailTrace_804365
  have hstable : (prefixWord ++ tailWord_804365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804365).length < 2 ^ (prefixWord ++ tailWord_804365).sum := by decide
  have hdescent : baseEnd_804365 < baseStart_804365 := by decide
  rcases family_descends (prefixWord ++ tailWord_804365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804371 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3]
def baseStart_804371 : Nat := 118140960795 + 804371 * 2 ^ 59
def prefixEnd_804371 : Nat := 4983230072969 + 3 ^ 40 * 804371 * 2
def baseEnd_804371 : Nat := 413028947537777628463271

theorem tailTrace_804371 : CollatzResearch.WordTrace tailWord_804371 prefixEnd_804371 413028947537777628463271 := by
  unfold tailWord_804371
  simp only [CollatzResearch.WordTrace]
  refine ⟨29337820568908717474876967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19558547045939144983251311 29337820568908717474876967)
  ·
    refine ⟨44006730853363076212315451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29337820568908717474876967 44006730853363076212315451)
    ·
      refine ⟨66010096280044614318473177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44006730853363076212315451 66010096280044614318473177)
      ·
        refine ⟨49507572210033460738854883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66010096280044614318473177 49507572210033460738854883)
        ·
          refine ⟨74261358315050191108282325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49507572210033460738854883 74261358315050191108282325)
          ·
            refine ⟨1740500585508988854100367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 74261358315050191108282325 1740500585508988854100367)
            ·
              refine ⟨2610750878263483281150551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740500585508988854100367 2610750878263483281150551)
              ·
                refine ⟨3916126317395224921725827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610750878263483281150551 3916126317395224921725827)
                ·
                  refine ⟨5874189476092837382588741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916126317395224921725827 5874189476092837382588741)
                  ·
                    refine ⟨1101410526767407009235389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5874189476092837382588741 1101410526767407009235389)
                    ·
                      refine ⟨413028947537777628463271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101410526767407009235389 413028947537777628463271)
                      ·
                        rfl

theorem cell23_804371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_804371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804371 prefixEnd_804371 := by exact prefixLift 804371
  have htrace : WordTrace (prefixWord ++ tailWord_804371) baseStart_804371 baseEnd_804371 := by
    simpa [prefixWord, tailWord_804371, baseEnd_804371] using wordTrace_append hprefix tailTrace_804371
  have hstable : (prefixWord ++ tailWord_804371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804371).length < 2 ^ (prefixWord ++ tailWord_804371).sum := by decide
  have hdescent : baseEnd_804371 < baseStart_804371 := by decide
  rcases family_descends (prefixWord ++ tailWord_804371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804408 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 6]
def baseStart_804408 : Nat := 118140960795 + 804408 * 2 ^ 59
def prefixEnd_804408 : Nat := 4983230072969 + 3 ^ 40 * 804408 * 2
def baseEnd_804408 : Nat := 45894216257999331522289

theorem tailTrace_804408 : CollatzResearch.WordTrace tailWord_804408 prefixEnd_804408 45894216257999331522289 := by
  unfold tailWord_804408
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669585034887336396986939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19559446713183115195982585 14669585034887336396986939)
  ·
    refine ⟨22004377552331004595480409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669585034887336396986939 22004377552331004595480409)
    ·
      refine ⟨16503283164248253446610307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22004377552331004595480409 16503283164248253446610307)
      ·
        refine ⟨24754924746372380169915461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16503283164248253446610307 24754924746372380169915461)
        ·
          refine ⟨4641548389944821281859149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24754924746372380169915461 4641548389944821281859149)
          ·
            refine ⟨1740580646229307980697181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4641548389944821281859149 1740580646229307980697181)
            ·
              refine ⟨652717742335990492761443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1740580646229307980697181 652717742335990492761443)
              ·
                refine ⟨979076613503985739142165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 652717742335990492761443 979076613503985739142165)
                ·
                  refine ⟨45894216257999331522289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 979076613503985739142165 45894216257999331522289)
                  ·
                    rfl

theorem cell23_804408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 6].length) (baseStart_804408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804408 prefixEnd_804408 := by exact prefixLift 804408
  have htrace : WordTrace (prefixWord ++ tailWord_804408) baseStart_804408 baseEnd_804408 := by
    simpa [prefixWord, tailWord_804408, baseEnd_804408] using wordTrace_append hprefix tailTrace_804408
  have hstable : (prefixWord ++ tailWord_804408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804408).length < 2 ^ (prefixWord ++ tailWord_804408).sum := by decide
  have hdescent : baseEnd_804408 < baseStart_804408 := by decide
  rcases family_descends (prefixWord ++ tailWord_804408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804428 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 5, 2]
def baseStart_804428 : Nat := 118140960795 + 804428 * 2 ^ 59
def prefixEnd_804428 : Nat := 4983230072969 + 3 ^ 40 * 804428 * 2
def baseEnd_804428 : Nat := 413058215935083905450509

theorem tailTrace_804428 : CollatzResearch.WordTrace tailWord_804428 prefixEnd_804428 413058215935083905450509 := by
  unfold tailWord_804428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669949764851108104850969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19559933019801477473134625 14669949764851108104850969)
  ·
    refine ⟨11002462323638331078638227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14669949764851108104850969 11002462323638331078638227)
    ·
      refine ⟨16503693485457496617957341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11002462323638331078638227 16503693485457496617957341)
      ·
        refine ⟨6188885057046561231734003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16503693485457496617957341 6188885057046561231734003)
        ·
          refine ⟨9283327585569841847601005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6188885057046561231734003 9283327585569841847601005)
          ·
            refine ⟨3481247844588690692850377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9283327585569841847601005 3481247844588690692850377)
            ·
              refine ⟨2610935883441518019637783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481247844588690692850377 2610935883441518019637783)
              ·
                refine ⟨3916403825162277029456675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2610935883441518019637783 3916403825162277029456675)
                ·
                  refine ⟨5874605737743415544185013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3916403825162277029456675 5874605737743415544185013)
                  ·
                    refine ⟨550744287913445207267345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5874605737743415544185013 550744287913445207267345)
                    ·
                      refine ⟨413058215935083905450509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550744287913445207267345 413058215935083905450509)
                      ·
                        rfl

theorem cell23_804428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_804428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804428 prefixEnd_804428 := by exact prefixLift 804428
  have htrace : WordTrace (prefixWord ++ tailWord_804428) baseStart_804428 baseEnd_804428 := by
    simpa [prefixWord, tailWord_804428, baseEnd_804428] using wordTrace_append hprefix tailTrace_804428
  have hstable : (prefixWord ++ tailWord_804428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804428).length < 2 ^ (prefixWord ++ tailWord_804428).sum := by decide
  have hdescent : baseEnd_804428 < baseStart_804428 := by decide
  rcases family_descends (prefixWord ++ tailWord_804428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804429 : List Nat := [1, 6, 1, 1, 3, 2, 1, 3, 1, 4]
def baseStart_804429 : Nat := 118140960795 + 804429 * 2 ^ 59
def prefixEnd_804429 : Nat := 4983230072969 + 3 ^ 40 * 804429 * 2
def baseEnd_804429 : Nat := 137686243138579467179335

theorem tailTrace_804429 : CollatzResearch.WordTrace tailWord_804429 prefixEnd_804429 137686243138579467179335 := by
  unfold tailWord_804429
  simp only [CollatzResearch.WordTrace]
  refine ⟨29339936002698593380488341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19559957335132395586992227 29339936002698593380488341)
  ·
    refine ⟨1375309500126496564710391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29339936002698593380488341 1375309500126496564710391)
    ·
      refine ⟨2062964250189744847065587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375309500126496564710391 2062964250189744847065587)
      ·
        refine ⟨3094446375284617270598381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2062964250189744847065587 3094446375284617270598381)
        ·
          refine ⟨1160417390731731476474393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3094446375284617270598381 1160417390731731476474393)
          ·
            refine ⟨870313043048798607355795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1160417390731731476474393 870313043048798607355795)
            ·
              refine ⟨1305469564573197911033693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870313043048798607355795 1305469564573197911033693)
              ·
                refine ⟨489551086714949216637635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1305469564573197911033693 489551086714949216637635)
                ·
                  refine ⟨734326630072423824956453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489551086714949216637635 734326630072423824956453)
                  ·
                    refine ⟨137686243138579467179335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734326630072423824956453 137686243138579467179335)
                    ·
                      rfl

theorem cell23_804429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_804429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804429 prefixEnd_804429 := by exact prefixLift 804429
  have htrace : WordTrace (prefixWord ++ tailWord_804429) baseStart_804429 baseEnd_804429 := by
    simpa [prefixWord, tailWord_804429, baseEnd_804429] using wordTrace_append hprefix tailTrace_804429
  have hstable : (prefixWord ++ tailWord_804429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804429).length < 2 ^ (prefixWord ++ tailWord_804429).sum := by decide
  have hdescent : baseEnd_804429 < baseStart_804429 := by decide
  rcases family_descends (prefixWord ++ tailWord_804429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804471 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4]
def baseStart_804471 : Nat := 118140960795 + 804471 * 2 ^ 59
def prefixEnd_804471 : Nat := 4983230072969 + 3 ^ 40 * 804471 * 2
def baseEnd_804471 : Nat := 413080295603227237212811

theorem tailTrace_804471 : CollatzResearch.WordTrace tailWord_804471 prefixEnd_804471 413080295603227237212811 := by
  unfold tailWord_804471
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341467868546434553517267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19560978579030956369011511 29341467868546434553517267)
  ·
    refine ⟨44012201802819651830275901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29341467868546434553517267 44012201802819651830275901)
    ·
      refine ⟨16504575676057369436353463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44012201802819651830275901 16504575676057369436353463)
      ·
        refine ⟨24756863514086054154530195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16504575676057369436353463 24756863514086054154530195)
        ·
          refine ⟨37135295271129081231795293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24756863514086054154530195 37135295271129081231795293)
          ·
            refine ⟨13925735726673405461923235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37135295271129081231795293 13925735726673405461923235)
            ·
              refine ⟨20888603590010108192884853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13925735726673405461923235 20888603590010108192884853)
              ·
                refine ⟨1958306586563447643082955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20888603590010108192884853 1958306586563447643082955)
                ·
                  refine ⟨2937459879845171464624433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958306586563447643082955 2937459879845171464624433)
                  ·
                    refine ⟨2203094909883878598468325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2937459879845171464624433 2203094909883878598468325)
                    ·
                      refine ⟨413080295603227237212811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2203094909883878598468325 413080295603227237212811)
                      ·
                        rfl

theorem cell23_804471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_804471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804471 prefixEnd_804471 := by exact prefixLift 804471
  have htrace : WordTrace (prefixWord ++ tailWord_804471) baseStart_804471 baseEnd_804471 := by
    simpa [prefixWord, tailWord_804471, baseEnd_804471] using wordTrace_append hprefix tailTrace_804471
  have hstable : (prefixWord ++ tailWord_804471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804471).length < 2 ^ (prefixWord ++ tailWord_804471).sum := by decide
  have hdescent : baseEnd_804471 < baseStart_804471 := by decide
  rcases family_descends (prefixWord ++ tailWord_804471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804481 : List Nat := [1, 2, 4, 2, 1, 2, 2, 9]
def baseStart_804481 : Nat := 118140960795 + 804481 * 2 ^ 59
def prefixEnd_804481 : Nat := 4983230072969 + 3 ^ 40 * 804481 * 2
def baseEnd_804481 : Nat := 15299460385547118447695

theorem tailTrace_804481 : CollatzResearch.WordTrace tailWord_804481 prefixEnd_804481 15299460385547118447695 := by
  unfold tailWord_804481
  simp only [CollatzResearch.WordTrace]
  refine ⟨29341832598510206261381297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19561221732340137507587531 29341832598510206261381297)
  ·
    refine ⟨22006374448882654696035973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29341832598510206261381297 22006374448882654696035973)
    ·
      refine ⟨4126195209165497755506745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22006374448882654696035973 4126195209165497755506745)
      ·
        refine ⟨3094646406874123316630059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4126195209165497755506745 3094646406874123316630059)
        ·
          refine ⟨4641969610311184974945089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094646406874123316630059 4641969610311184974945089)
          ·
            refine ⟨3481477207733388731208817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4641969610311184974945089 3481477207733388731208817)
            ·
              refine ⟨2611107905800041548406613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481477207733388731208817 2611107905800041548406613)
              ·
                refine ⟨15299460385547118447695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2611107905800041548406613 15299460385547118447695)
                ·
                  rfl

theorem cell23_804481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 9].length) (baseStart_804481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804481 prefixEnd_804481 := by exact prefixLift 804481
  have htrace : WordTrace (prefixWord ++ tailWord_804481) baseStart_804481 baseEnd_804481 := by
    simpa [prefixWord, tailWord_804481, baseEnd_804481] using wordTrace_append hprefix tailTrace_804481
  have hstable : (prefixWord ++ tailWord_804481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804481).length < 2 ^ (prefixWord ++ tailWord_804481).sum := by decide
  have hdescent : baseEnd_804481 < baseStart_804481 := by decide
  rcases family_descends (prefixWord ++ tailWord_804481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804492 : List Nat := [2, 2, 1, 2, 1, 1, 4, 5, 1, 2, 2]
def baseStart_804492 : Nat := 118140960795 + 804492 * 2 ^ 59
def prefixEnd_804492 : Nat := 4983230072969 + 3 ^ 40 * 804492 * 2
def baseEnd_804492 : Nat := 413091078696971655050215

theorem tailTrace_804492 : CollatzResearch.WordTrace tailWord_804492 prefixEnd_804492 413091078696971655050215 := by
  unfold tailWord_804492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14671116900735177570015865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19561489200980236760021153 14671116900735177570015865)
  ·
    refine ⟨11003337675551383177511899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14671116900735177570015865 11003337675551383177511899)
    ·
      refine ⟨16505006513327074766267849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11003337675551383177511899 16505006513327074766267849)
      ·
        refine ⟨12378754884995306074700887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16505006513327074766267849 12378754884995306074700887)
        ·
          refine ⟨18568132327492959112051331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12378754884995306074700887 18568132327492959112051331)
          ·
            refine ⟨27852198491239438668076997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18568132327492959112051331 27852198491239438668076997)
            ·
              refine ⟨5222287217107394750264437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27852198491239438668076997 5222287217107394750264437)
              ·
                refine ⟨489589426603818257837291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5222287217107394750264437 489589426603818257837291)
                ·
                  refine ⟨734384139905727386755937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489589426603818257837291 734384139905727386755937)
                  ·
                    refine ⟨550788104929295540066953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 734384139905727386755937 550788104929295540066953)
                    ·
                      refine ⟨413091078696971655050215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550788104929295540066953 413091078696971655050215)
                      ·
                        rfl

theorem cell23_804492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_804492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804492 prefixEnd_804492 := by exact prefixLift 804492
  have htrace : WordTrace (prefixWord ++ tailWord_804492) baseStart_804492 baseEnd_804492 := by
    simpa [prefixWord, tailWord_804492, baseEnd_804492] using wordTrace_append hprefix tailTrace_804492
  have hstable : (prefixWord ++ tailWord_804492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804492).length < 2 ^ (prefixWord ++ tailWord_804492).sum := by decide
  have hdescent : baseEnd_804492 < baseStart_804492 := by decide
  rcases family_descends (prefixWord ++ tailWord_804492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804498 : List Nat := [3, 2, 3, 1, 4, 10]
def baseStart_804498 : Nat := 118140960795 + 804498 * 2 ^ 59
def prefixEnd_804498 : Nat := 4983230072969 + 3 ^ 40 * 804498 * 2
def baseEnd_804498 : Nat := 1699975965353492311009

theorem tailTrace_804498 : CollatzResearch.WordTrace tailWord_804498 prefixEnd_804498 1699975965353492311009 := by
  unfold tailWord_804498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7335613159862154541187537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19561635092965745443166765 7335613159862154541187537)
  ·
    refine ⟨5501709869896615905890653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7335613159862154541187537 5501709869896615905890653)
    ·
      refine ⟨2063141201211230964708995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5501709869896615905890653 2063141201211230964708995)
      ·
        refine ⟨3094711801816846447063493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063141201211230964708995 3094711801816846447063493)
        ·
          refine ⟨580258462840658708824405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3094711801816846447063493 580258462840658708824405)
          ·
            refine ⟨1699975965353492311009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 580258462840658708824405 1699975965353492311009)
            ·
              rfl

theorem cell23_804498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 10].length) (baseStart_804498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804498 prefixEnd_804498 := by exact prefixLift 804498
  have htrace : WordTrace (prefixWord ++ tailWord_804498) baseStart_804498 baseEnd_804498 := by
    simpa [prefixWord, tailWord_804498, baseEnd_804498] using wordTrace_append hprefix tailTrace_804498
  have hstable : (prefixWord ++ tailWord_804498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804498).length < 2 ^ (prefixWord ++ tailWord_804498).sum := by decide
  have hdescent : baseEnd_804498 < baseStart_804498 := by decide
  rcases family_descends (prefixWord ++ tailWord_804498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804525 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_804525 : Nat := 118140960795 + 804525 * 2 ^ 59
def prefixEnd_804525 : Nat := 4983230072969 + 3 ^ 40 * 804525 * 2
def baseEnd_804525 : Nat := 413108023558570025937563

theorem tailTrace_804525 : CollatzResearch.WordTrace tailWord_804525 prefixEnd_804525 413108023558570025937563 := by
  unfold tailWord_804525
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343437410350801775983029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562291606900534517322019 29343437410350801775983029)
  ·
    refine ⟨2750947257220387666498409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29343437410350801775983029 2750947257220387666498409)
    ·
      refine ⟨2063210442915290749873807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2750947257220387666498409 2063210442915290749873807)
      ·
        refine ⟨3094815664372936124810711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063210442915290749873807 3094815664372936124810711)
        ·
          refine ⟨4642223496559404187216067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3094815664372936124810711 4642223496559404187216067)
          ·
            refine ⟨6963335244839106280824101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4642223496559404187216067 6963335244839106280824101)
            ·
              refine ⟨1305625358407332427654519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6963335244839106280824101 1305625358407332427654519)
              ·
                refine ⟨1958438037610998641481779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1305625358407332427654519 1958438037610998641481779)
                ·
                  refine ⟨2937657056416497962222669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1958438037610998641481779 2937657056416497962222669)
                  ·
                    refine ⟨1101621396156186735833501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2937657056416497962222669 1101621396156186735833501)
                    ·
                      refine ⟨413108023558570025937563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101621396156186735833501 413108023558570025937563)
                      ·
                        rfl

theorem cell23_804525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_804525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804525 prefixEnd_804525 := by exact prefixLift 804525
  have htrace : WordTrace (prefixWord ++ tailWord_804525) baseStart_804525 baseEnd_804525 := by
    simpa [prefixWord, tailWord_804525, baseEnd_804525] using wordTrace_append hprefix tailTrace_804525
  have hstable : (prefixWord ++ tailWord_804525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804525).length < 2 ^ (prefixWord ++ tailWord_804525).sum := by decide
  have hdescent : baseEnd_804525 < baseStart_804525 := by decide
  rcases family_descends (prefixWord ++ tailWord_804525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804531 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_804531 : Nat := 118140960795 + 804531 * 2 ^ 59
def prefixEnd_804531 : Nat := 4983230072969 + 3 ^ 40 * 804531 * 2
def baseEnd_804531 : Nat := 413111104442497002462535

theorem tailTrace_804531 : CollatzResearch.WordTrace tailWord_804531 prefixEnd_804531 413111104442497002462535 := by
  unfold tailWord_804531
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343656248329064800701447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562437498886043200467631 29343656248329064800701447)
  ·
    refine ⟨44015484372493597201052171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29343656248329064800701447 44015484372493597201052171)
    ·
      refine ⟨66023226558740395801578257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44015484372493597201052171 66023226558740395801578257)
      ·
        refine ⟨49517419919055296851183693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66023226558740395801578257 49517419919055296851183693)
        ·
          refine ⟨18569032469645736319193885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49517419919055296851183693 18569032469645736319193885)
          ·
            refine ⟨6963387176117151119697707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18569032469645736319193885 6963387176117151119697707)
            ·
              refine ⟨10445080764175726679546561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963387176117151119697707 10445080764175726679546561)
              ·
                refine ⟨7833810573131795009659921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445080764175726679546561 7833810573131795009659921)
                ·
                  refine ⟨5875357929848846257244941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7833810573131795009659921 5875357929848846257244941)
                  ·
                    refine ⟨2203259223693317346466853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5875357929848846257244941 2203259223693317346466853)
                    ·
                      refine ⟨413111104442497002462535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2203259223693317346466853 413111104442497002462535)
                      ·
                        rfl

theorem cell23_804531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_804531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804531 prefixEnd_804531 := by exact prefixLift 804531
  have htrace : WordTrace (prefixWord ++ tailWord_804531) baseStart_804531 baseEnd_804531 := by
    simpa [prefixWord, tailWord_804531, baseEnd_804531] using wordTrace_append hprefix tailTrace_804531
  have hstable : (prefixWord ++ tailWord_804531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804531).length < 2 ^ (prefixWord ++ tailWord_804531).sum := by decide
  have hdescent : baseEnd_804531 < baseStart_804531 := by decide
  rcases family_descends (prefixWord ++ tailWord_804531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804535 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 3, 3, 2]
def baseStart_804535 : Nat := 118140960795 + 804535 * 2 ^ 59
def prefixEnd_804535 : Nat := 4983230072969 + 3 ^ 40 * 804535 * 2
def baseEnd_804535 : Nat := 413113158365114986812517

theorem tailTrace_804535 : CollatzResearch.WordTrace tailWord_804535 prefixEnd_804535 413113158365114986812517 := by
  unfold tailWord_804535
  simp only [CollatzResearch.WordTrace]
  refine ⟨29343802140314573483847059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562534760209715655898039 29343802140314573483847059)
  ·
    refine ⟨44015703210471860225770589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29343802140314573483847059 44015703210471860225770589)
    ·
      refine ⟨16505888703926947584663971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44015703210471860225770589 16505888703926947584663971)
      ·
        refine ⟨24758833055890421376995957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16505888703926947584663971 24758833055890421376995957)
        ·
          refine ⟨2321140598989727004093371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24758833055890421376995957 2321140598989727004093371)
          ·
            refine ⟨3481710898484590506140057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321140598989727004093371 3481710898484590506140057)
            ·
              refine ⟨2611283173863442879605043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3481710898484590506140057 2611283173863442879605043)
              ·
                refine ⟨3916924760795164319407565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2611283173863442879605043 3916924760795164319407565)
                ·
                  refine ⟨1468846785298186619777837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3916924760795164319407565 1468846785298186619777837)
                  ·
                    refine ⟨550817544486819982416689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1468846785298186619777837 550817544486819982416689)
                    ·
                      refine ⟨413113158365114986812517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 550817544486819982416689 413113158365114986812517)
                      ·
                        rfl

theorem cell23_804535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 3, 2].length) (baseStart_804535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804535 prefixEnd_804535 := by exact prefixLift 804535
  have htrace : WordTrace (prefixWord ++ tailWord_804535) baseStart_804535 baseEnd_804535 := by
    simpa [prefixWord, tailWord_804535, baseEnd_804535] using wordTrace_append hprefix tailTrace_804535
  have hstable : (prefixWord ++ tailWord_804535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804535).length < 2 ^ (prefixWord ++ tailWord_804535).sum := by decide
  have hdescent : baseEnd_804535 < baseStart_804535 := by decide
  rcases family_descends (prefixWord ++ tailWord_804535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804541 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_804541 : Nat := 118140960795 + 804541 * 2 ^ 59
def prefixEnd_804541 : Nat := 4983230072969 + 3 ^ 40 * 804541 * 2
def baseEnd_804541 : Nat := 137705413083013987779163

theorem tailTrace_804541 : CollatzResearch.WordTrace tailWord_804541 prefixEnd_804541 137705413083013987779163 := by
  unfold tailWord_804541
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344020978292836508565477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562680652195224339043651 29344020978292836508565477)
  ·
    refine ⟨5502003933429906845356027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29344020978292836508565477 5502003933429906845356027)
    ·
      refine ⟨8253005900144860268034041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5502003933429906845356027 8253005900144860268034041)
      ·
        refine ⟨6189754425108645201025531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253005900144860268034041 6189754425108645201025531)
        ·
          refine ⟨9284631637662967801538297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6189754425108645201025531 9284631637662967801538297)
          ·
            refine ⟨6963473728247225851153723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9284631637662967801538297 6963473728247225851153723)
            ·
              refine ⟨10445210592370838776730585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6963473728247225851153723 10445210592370838776730585)
              ·
                refine ⟨7833907944278129082547939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10445210592370838776730585 7833907944278129082547939)
                ·
                  refine ⟨11750861916417193623821909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7833907944278129082547939 11750861916417193623821909)
                  ·
                    refine ⟨137705413083013987779163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11750861916417193623821909 137705413083013987779163)
                    ·
                      rfl

theorem cell23_804541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_804541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804541 prefixEnd_804541 := by exact prefixLift 804541
  have htrace : WordTrace (prefixWord ++ tailWord_804541) baseStart_804541 baseEnd_804541 := by
    simpa [prefixWord, tailWord_804541, baseEnd_804541] using wordTrace_append hprefix tailTrace_804541
  have hstable : (prefixWord ++ tailWord_804541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804541).length < 2 ^ (prefixWord ++ tailWord_804541).sum := by decide
  have hdescent : baseEnd_804541 < baseStart_804541 := by decide
  rcases family_descends (prefixWord ++ tailWord_804541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804546 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_804546 : Nat := 118140960795 + 804546 * 2 ^ 59
def prefixEnd_804546 : Nat := 4983230072969 + 3 ^ 40 * 804546 * 2
def baseEnd_804546 : Nat := 413118806652314443774967

theorem tailTrace_804546 : CollatzResearch.WordTrace tailWord_804546 prefixEnd_804546 413118806652314443774967 := by
  unfold tailWord_804546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336050835818680590624373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19562802228849814908331661 7336050835818680590624373)
  ·
    refine ⟨687754765858001305371035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7336050835818680590624373 687754765858001305371035)
    ·
      refine ⟨1031632148787001958056553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687754765858001305371035 1031632148787001958056553)
      ·
        refine ⟨773724111590251468542415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1031632148787001958056553 773724111590251468542415)
        ·
          refine ⟨1160586167385377202813623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773724111590251468542415 1160586167385377202813623)
          ·
            refine ⟨1740879251078065804220435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160586167385377202813623 1740879251078065804220435)
            ·
              refine ⟨2611318876617098706330653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1740879251078065804220435 2611318876617098706330653)
              ·
                refine ⟨979244578731412014873995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2611318876617098706330653 979244578731412014873995)
                ·
                  refine ⟨1468866868097118022310993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979244578731412014873995 1468866868097118022310993)
                  ·
                    refine ⟨1101650151072838516733245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1468866868097118022310993 1101650151072838516733245)
                    ·
                      refine ⟨413118806652314443774967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101650151072838516733245 413118806652314443774967)
                      ·
                        rfl

theorem cell23_804546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_804546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804546 prefixEnd_804546 := by exact prefixLift 804546
  have htrace : WordTrace (prefixWord ++ tailWord_804546) baseStart_804546 baseEnd_804546 := by
    simpa [prefixWord, tailWord_804546, baseEnd_804546] using wordTrace_append hprefix tailTrace_804546
  have hstable : (prefixWord ++ tailWord_804546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804546).length < 2 ^ (prefixWord ++ tailWord_804546).sum := by decide
  have hdescent : baseEnd_804546 < baseStart_804546 := by decide
  rcases family_descends (prefixWord ++ tailWord_804546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804551 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_804551 : Nat := 118140960795 + 804551 * 2 ^ 59
def prefixEnd_804551 : Nat := 4983230072969 + 3 ^ 40 * 804551 * 2
def baseEnd_804551 : Nat := 413121374055586924212443

theorem tailTrace_804551 : CollatzResearch.WordTrace tailWord_804551 prefixEnd_804551 413121374055586924212443 := by
  unfold tailWord_804551
  simp only [CollatzResearch.WordTrace]
  refine ⟨29344385708256608216429507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19562923805504405477619671 29344385708256608216429507)
  ·
    refine ⟨44016578562384912324644261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29344385708256608216429507 44016578562384912324644261)
    ·
      refine ⟨8253108480447171060870799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44016578562384912324644261 8253108480447171060870799)
      ·
        refine ⟨12379662720670756591306199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8253108480447171060870799 12379662720670756591306199)
        ·
          refine ⟨18569494081006134886959299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12379662720670756591306199 18569494081006134886959299)
          ·
            refine ⟨27854241121509202330438949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18569494081006134886959299 27854241121509202330438949)
            ·
              refine ⟨5222670210282975436957303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27854241121509202330438949 5222670210282975436957303)
              ·
                refine ⟨7834005315424463155435955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5222670210282975436957303 7834005315424463155435955)
                ·
                  refine ⟨11751007973136694733153933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7834005315424463155435955 11751007973136694733153933)
                  ·
                    refine ⟨4406627989926260524932725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11751007973136694733153933 4406627989926260524932725)
                    ·
                      refine ⟨413121374055586924212443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4406627989926260524932725 413121374055586924212443)
                      ·
                        rfl

theorem cell23_804551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_804551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804551 prefixEnd_804551 := by exact prefixLift 804551
  have htrace : WordTrace (prefixWord ++ tailWord_804551) baseStart_804551 baseEnd_804551 := by
    simpa [prefixWord, tailWord_804551, baseEnd_804551] using wordTrace_append hprefix tailTrace_804551
  have hstable : (prefixWord ++ tailWord_804551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804551).length < 2 ^ (prefixWord ++ tailWord_804551).sum := by decide
  have hdescent : baseEnd_804551 < baseStart_804551 := by decide
  rcases family_descends (prefixWord ++ tailWord_804551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804618 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 4, 5]
def baseStart_804618 : Nat := 118140960795 + 804618 * 2 ^ 59
def prefixEnd_804618 : Nat := 4983230072969 + 3 ^ 40 * 804618 * 2
def baseEnd_804618 : Nat := 137718592419812720691545

theorem tailTrace_804618 : CollatzResearch.WordTrace tailWord_804618 prefixEnd_804618 137718592419812720691545 := by
  unfold tailWord_804618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336707349753469664779627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19564552932675919106079005 7336707349753469664779627)
  ·
    refine ⟨11005061024630204497169441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7336707349753469664779627 11005061024630204497169441)
    ·
      refine ⟨8253795768472653372877081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11005061024630204497169441 8253795768472653372877081)
      ·
        refine ⟨6190346826354490029657811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8253795768472653372877081 6190346826354490029657811)
        ·
          refine ⟨9285520239531735044486717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6190346826354490029657811 9285520239531735044486717)
          ·
            refine ⟨3482070089824400641682519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9285520239531735044486717 3482070089824400641682519)
            ·
              refine ⟨5223105134736600962523779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482070089824400641682519 5223105134736600962523779)
              ·
                refine ⟨7834657702104901443785669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5223105134736600962523779 7834657702104901443785669)
                ·
                  refine ⟨1468998319144669020709813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7834657702104901443785669 1468998319144669020709813)
                  ·
                    refine ⟨137718592419812720691545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1468998319144669020709813 137718592419812720691545)
                    ·
                      rfl

theorem cell23_804618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_804618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804618 prefixEnd_804618 := by exact prefixLift 804618
  have htrace : WordTrace (prefixWord ++ tailWord_804618) baseStart_804618 baseEnd_804618 := by
    simpa [prefixWord, tailWord_804618, baseEnd_804618] using wordTrace_append hprefix tailTrace_804618
  have hstable : (prefixWord ++ tailWord_804618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804618).length < 2 ^ (prefixWord ++ tailWord_804618).sum := by decide
  have hdescent : baseEnd_804618 < baseStart_804618 := by decide
  rcases family_descends (prefixWord ++ tailWord_804618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804675 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3]
def baseStart_804675 : Nat := 118140960795 + 804675 * 2 ^ 59
def prefixEnd_804675 : Nat := 4983230072969 + 3 ^ 40 * 804675 * 2
def baseEnd_804675 : Nat := 413185045656744439061873

theorem tailTrace_804675 : CollatzResearch.WordTrace tailWord_804675 prefixEnd_804675 413185045656744439061873 := by
  unfold tailWord_804675
  simp only [CollatzResearch.WordTrace]
  refine ⟨29348908359807377393943479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19565938906538251595962319 29348908359807377393943479)
  ·
    refine ⟨44023362539711066090915219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29348908359807377393943479 44023362539711066090915219)
    ·
      refine ⟨66035043809566599136372829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44023362539711066090915219 66035043809566599136372829)
      ·
        refine ⟨24763141428587474676139811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66035043809566599136372829 24763141428587474676139811)
        ·
          refine ⟨37144712142881212014209717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24763141428587474676139811 37144712142881212014209717)
          ·
            refine ⟨3482316763395113626332161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37144712142881212014209717 3482316763395113626332161)
            ·
              refine ⟨2611737572546335219749121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482316763395113626332161 2611737572546335219749121)
              ·
                refine ⟨1958803179409751414811841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2611737572546335219749121 1958803179409751414811841)
                ·
                  refine ⟨1469102384557313561108881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1958803179409751414811841 1469102384557313561108881)
                  ·
                    refine ⟨1101826788417985170831661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1469102384557313561108881 1101826788417985170831661)
                    ·
                      refine ⟨413185045656744439061873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101826788417985170831661 413185045656744439061873)
                      ·
                        rfl

theorem cell23_804675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 3].length) (baseStart_804675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804675 prefixEnd_804675 := by exact prefixLift 804675
  have htrace : WordTrace (prefixWord ++ tailWord_804675) baseStart_804675 baseEnd_804675 := by
    simpa [prefixWord, tailWord_804675, baseEnd_804675] using wordTrace_append hprefix tailTrace_804675
  have hstable : (prefixWord ++ tailWord_804675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804675).length < 2 ^ (prefixWord ++ tailWord_804675).sum := by decide
  have hdescent : baseEnd_804675 < baseStart_804675 := by decide
  rcases family_descends (prefixWord ++ tailWord_804675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804682 : List Nat := [3, 1, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_804682 : Nat := 118140960795 + 804682 * 2 ^ 59
def prefixEnd_804682 : Nat := 4983230072969 + 3 ^ 40 * 804682 * 2
def baseEnd_804682 : Nat := 137729546673775303891447

theorem tailTrace_804682 : CollatzResearch.WordTrace tailWord_804682 prefixEnd_804682 137729546673775303891447 := by
  unfold tailWord_804682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337290917695504397362075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19566109113854678392965533 7337290917695504397362075)
  ·
    refine ⟨11005936376543256596043113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7337290917695504397362075 11005936376543256596043113)
    ·
      refine ⟨8254452282407442447032335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11005936376543256596043113 8254452282407442447032335)
      ·
        refine ⟨12381678423611163670548503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8254452282407442447032335 12381678423611163670548503)
        ·
          refine ⟨18572517635416745505822755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12381678423611163670548503 18572517635416745505822755)
          ·
            refine ⟨27858776453125118258734133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18572517635416745505822755 27858776453125118258734133)
            ·
              refine ⟨2611760292480479836756325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27858776453125118258734133 2611760292480479836756325)
              ·
                refine ⟨489705054840089969391811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611760292480479836756325 489705054840089969391811)
                ·
                  refine ⟨734557582260134954087717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489705054840089969391811 734557582260134954087717)
                  ·
                    refine ⟨137729546673775303891447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734557582260134954087717 137729546673775303891447)
                    ·
                      rfl

theorem cell23_804682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_804682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804682 prefixEnd_804682 := by exact prefixLift 804682
  have htrace : WordTrace (prefixWord ++ tailWord_804682) baseStart_804682 baseEnd_804682 := by
    simpa [prefixWord, tailWord_804682, baseEnd_804682] using wordTrace_append hprefix tailTrace_804682
  have hstable : (prefixWord ++ tailWord_804682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804682).length < 2 ^ (prefixWord ++ tailWord_804682).sum := by decide
  have hdescent : baseEnd_804682 < baseStart_804682 := by decide
  rcases family_descends (prefixWord ++ tailWord_804682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804688 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_804688 : Nat := 118140960795 + 804688 * 2 ^ 59
def prefixEnd_804688 : Nat := 4983230072969 + 3 ^ 40 * 804688 * 2
def baseEnd_804688 : Nat := 413191720905252888199313

theorem tailTrace_804688 : CollatzResearch.WordTrace tailWord_804688 prefixEnd_804688 413191720905252888199313 := by
  unfold tailWord_804688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14674691254380140307083359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19566255005840187076111145 14674691254380140307083359)
  ·
    refine ⟨22012036881570210460625039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14674691254380140307083359 22012036881570210460625039)
    ·
      refine ⟨33018055322355315690937559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22012036881570210460625039 33018055322355315690937559)
      ·
        refine ⟨49527082983532973536406339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33018055322355315690937559 49527082983532973536406339)
        ·
          refine ⟨74290624475299460304609509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49527082983532973536406339 74290624475299460304609509)
          ·
            refine ⟨13929492089118648807114283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74290624475299460304609509 13929492089118648807114283)
            ·
              refine ⟨20894238133677973210671425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13929492089118648807114283 20894238133677973210671425)
              ·
                refine ⟨15670678600258479908003569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20894238133677973210671425 15670678600258479908003569)
                ·
                  refine ⟨11753008950193859931002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15670678600258479908003569 11753008950193859931002677)
                  ·
                    refine ⟨1101844589080674368531501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11753008950193859931002677 1101844589080674368531501)
                    ·
                      refine ⟨413191720905252888199313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101844589080674368531501 413191720905252888199313)
                      ·
                        rfl

theorem cell23_804688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_804688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804688 prefixEnd_804688 := by exact prefixLift 804688
  have htrace : WordTrace (prefixWord ++ tailWord_804688) baseStart_804688 baseEnd_804688 := by
    simpa [prefixWord, tailWord_804688, baseEnd_804688] using wordTrace_append hprefix tailTrace_804688
  have hstable : (prefixWord ++ tailWord_804688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804688).length < 2 ^ (prefixWord ++ tailWord_804688).sum := by decide
  have hdescent : baseEnd_804688 < baseStart_804688 := by decide
  rcases family_descends (prefixWord ++ tailWord_804688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804739 : List Nat := [1, 1, 1, 3, 4, 2, 2, 4, 1, 1, 3]
def baseStart_804739 : Nat := 118140960795 + 804739 * 2 ^ 59
def prefixEnd_804739 : Nat := 4983230072969 + 3 ^ 40 * 804739 * 2
def baseEnd_804739 : Nat := 413217908418632188661579

theorem tailTrace_804739 : CollatzResearch.WordTrace tailWord_804739 prefixEnd_804739 413217908418632188661579 := by
  unfold tailWord_804739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29351242631575516324273271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19567495087717010882848847 29351242631575516324273271)
  ·
    refine ⟨44026863947363274486409907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29351242631575516324273271 44026863947363274486409907)
    ·
      refine ⟨66040295921044911729614861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44026863947363274486409907 66040295921044911729614861)
      ·
        refine ⟨24765110970391841898605573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66040295921044911729614861 24765110970391841898605573)
        ·
          refine ⟨4643458306948470355988545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24765110970391841898605573 4643458306948470355988545)
          ·
            refine ⟨3482593730211352766991409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4643458306948470355988545 3482593730211352766991409)
            ·
              refine ⟨2611945297658514575243557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3482593730211352766991409 2611945297658514575243557)
              ·
                refine ⟨489739743310971482858167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611945297658514575243557 489739743310971482858167)
                ·
                  refine ⟨734609614966457224287251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489739743310971482858167 734609614966457224287251)
                  ·
                    refine ⟨1101914422449685836430877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734609614966457224287251 1101914422449685836430877)
                    ·
                      refine ⟨413217908418632188661579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1101914422449685836430877 413217908418632188661579)
                      ·
                        rfl

theorem cell23_804739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 1, 1, 3].length) (baseStart_804739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804739 prefixEnd_804739 := by exact prefixLift 804739
  have htrace : WordTrace (prefixWord ++ tailWord_804739) baseStart_804739 baseEnd_804739 := by
    simpa [prefixWord, tailWord_804739, baseEnd_804739] using wordTrace_append hprefix tailTrace_804739
  have hstable : (prefixWord ++ tailWord_804739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804739).length < 2 ^ (prefixWord ++ tailWord_804739).sum := by decide
  have hdescent : baseEnd_804739 < baseStart_804739 := by decide
  rcases family_descends (prefixWord ++ tailWord_804739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804762 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_804762 : Nat := 118140960795 + 804762 * 2 ^ 59
def prefixEnd_804762 : Nat := 4983230072969 + 3 ^ 40 * 804762 * 2
def baseEnd_804762 : Nat := 413229718473685598673973

theorem tailTrace_804762 : CollatzResearch.WordTrace tailWord_804762 prefixEnd_804762 413229718473685598673973 := by
  unfold tailWord_804762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7338020377623047813090135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19568054340328127501573693 7338020377623047813090135)
  ·
    refine ⟨11007030566434571719635203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7338020377623047813090135 11007030566434571719635203)
    ·
      refine ⟨16510545849651857579452805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11007030566434571719635203 16510545849651857579452805)
      ·
        refine ⟨3095727346809723296147401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16510545849651857579452805 3095727346809723296147401)
        ·
          refine ⟨2321795510107292472110551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095727346809723296147401 2321795510107292472110551)
          ·
            refine ⟨3482693265160938708165827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2321795510107292472110551 3482693265160938708165827)
            ·
              refine ⟨5224039897741408062248741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3482693265160938708165827 5224039897741408062248741)
              ·
                refine ⟨979507480826514011671639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5224039897741408062248741 979507480826514011671639)
                ·
                  refine ⟨1469261221239771017507459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979507480826514011671639 1469261221239771017507459)
                  ·
                    refine ⟨2203891831859656526261189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469261221239771017507459 2203891831859656526261189)
                    ·
                      refine ⟨413229718473685598673973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2203891831859656526261189 413229718473685598673973)
                      ·
                        rfl

theorem cell23_804762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_804762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804762 prefixEnd_804762 := by exact prefixLift 804762
  have htrace : WordTrace (prefixWord ++ tailWord_804762) baseStart_804762 baseEnd_804762 := by
    simpa [prefixWord, tailWord_804762, baseEnd_804762] using wordTrace_append hprefix tailTrace_804762
  have hstable : (prefixWord ++ tailWord_804762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804762).length < 2 ^ (prefixWord ++ tailWord_804762).sum := by decide
  have hdescent : baseEnd_804762 < baseStart_804762 := by decide
  rcases family_descends (prefixWord ++ tailWord_804762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804785 : List Nat := [1, 2, 2, 4, 2, 3, 9]
def baseStart_804785 : Nat := 118140960795 + 804785 * 2 ^ 59
def prefixEnd_804785 : Nat := 4983230072969 + 3 ^ 40 * 804785 * 2
def baseEnd_804785 : Nat := 5101747265786901341807

theorem tailTrace_804785 : CollatzResearch.WordTrace tailWord_804785 prefixEnd_804785 5101747265786901341807 := by
  unfold tailWord_804785
  simp only [CollatzResearch.WordTrace]
  refine ⟨29352920389408866180447809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19568613592939244120298539 29352920389408866180447809)
  ·
    refine ⟨22014690292056649635335857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29352920389408866180447809 22014690292056649635335857)
    ·
      refine ⟨16511017719042487226501893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22014690292056649635335857 16511017719042487226501893)
      ·
        refine ⟨3095815822320466354969105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16511017719042487226501893 3095815822320466354969105)
        ·
          refine ⟨2321861866740349766226829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3095815822320466354969105 2321861866740349766226829)
          ·
            refine ⟨870698200027631162335061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2321861866740349766226829 870698200027631162335061)
            ·
              refine ⟨5101747265786901341807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 870698200027631162335061 5101747265786901341807)
              ·
                rfl

theorem cell23_804785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 9].length) (baseStart_804785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804785 prefixEnd_804785 := by exact prefixLift 804785
  have htrace : WordTrace (prefixWord ++ tailWord_804785) baseStart_804785 baseEnd_804785 := by
    simpa [prefixWord, tailWord_804785, baseEnd_804785] using wordTrace_append hprefix tailTrace_804785
  have hstable : (prefixWord ++ tailWord_804785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804785).length < 2 ^ (prefixWord ++ tailWord_804785).sum := by decide
  have hdescent : baseEnd_804785 < baseStart_804785 := by decide
  rcases family_descends (prefixWord ++ tailWord_804785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804829 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_804829 : Nat := 118140960795 + 804829 * 2 ^ 59
def prefixEnd_804829 : Nat := 4983230072969 + 3 ^ 40 * 804829 * 2
def baseEnd_804829 : Nat := 413264121677536836536165

theorem tailTrace_804829 : CollatzResearch.WordTrace tailWord_804829 prefixEnd_804829 413264121677536836536165 := by
  unfold tailWord_804829
  simp only [CollatzResearch.WordTrace]
  refine ⟨29354525201249461695049541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19569683467499641130033027 29354525201249461695049541)
  ·
    refine ⟨5503973475234274067821789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29354525201249461695049541 5503973475234274067821789)
    ·
      refine ⟨2063990053212852775433171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5503973475234274067821789 2063990053212852775433171)
      ·
        refine ⟨3095985079819279163149757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063990053212852775433171 3095985079819279163149757)
        ·
          refine ⟨1160994404932229686181159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3095985079819279163149757 1160994404932229686181159)
          ·
            refine ⟨1741491607398344529271739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160994404932229686181159 1741491607398344529271739)
            ·
              refine ⟨2612237411097516793907609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741491607398344529271739 2612237411097516793907609)
              ·
                refine ⟨1959178058323137595430707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612237411097516793907609 1959178058323137595430707)
                ·
                  refine ⟨2938767087484706393146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959178058323137595430707 2938767087484706393146061)
                  ·
                    refine ⟨1102037657806764897429773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2938767087484706393146061 1102037657806764897429773)
                    ·
                      refine ⟨413264121677536836536165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1102037657806764897429773 413264121677536836536165)
                      ·
                        rfl

theorem cell23_804829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_804829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804829 prefixEnd_804829 := by exact prefixLift 804829
  have htrace : WordTrace (prefixWord ++ tailWord_804829) baseStart_804829 baseEnd_804829 := by
    simpa [prefixWord, tailWord_804829, baseEnd_804829] using wordTrace_append hprefix tailTrace_804829
  have hstable : (prefixWord ++ tailWord_804829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804829).length < 2 ^ (prefixWord ++ tailWord_804829).sum := by decide
  have hdescent : baseEnd_804829 < baseStart_804829 := by decide
  rcases family_descends (prefixWord ++ tailWord_804829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804846 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_804846 : Nat := 118140960795 + 804846 * 2 ^ 59
def prefixEnd_804846 : Nat := 4983230072969 + 3 ^ 40 * 804846 * 2
def baseEnd_804846 : Nat := 413272850848663270023587

theorem tailTrace_804846 : CollatzResearch.WordTrace tailWord_804846 prefixEnd_804846 413272850848663270023587 := by
  unfold tailWord_804846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669393155273484199802299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19570096828125249065612261 3669393155273484199802299)
  ·
    refine ⟨5504089732910226299703449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669393155273484199802299 5504089732910226299703449)
    ·
      refine ⟨4128067299682669724777587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5504089732910226299703449 4128067299682669724777587)
      ·
        refine ⟨6192100949524004587166381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128067299682669724777587 6192100949524004587166381)
        ·
          refine ⟨2322037856071501720187393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6192100949524004587166381 2322037856071501720187393)
          ·
            refine ⟨1741528392053626290140545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322037856071501720187393 1741528392053626290140545)
            ·
              refine ⟨1306146294040219717605409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741528392053626290140545 1306146294040219717605409)
              ·
                refine ⟨979609720530164788204057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1306146294040219717605409 979609720530164788204057)
                ·
                  refine ⟨734707290397623591153043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979609720530164788204057 734707290397623591153043)
                  ·
                    refine ⟨1102060935596435386729565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734707290397623591153043 1102060935596435386729565)
                    ·
                      refine ⟨413272850848663270023587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1102060935596435386729565 413272850848663270023587)
                      ·
                        rfl

theorem cell23_804846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_804846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804846 prefixEnd_804846 := by exact prefixLift 804846
  have htrace : WordTrace (prefixWord ++ tailWord_804846) baseStart_804846 baseEnd_804846 := by
    simpa [prefixWord, tailWord_804846, baseEnd_804846] using wordTrace_append hprefix tailTrace_804846
  have hstable : (prefixWord ++ tailWord_804846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804846).length < 2 ^ (prefixWord ++ tailWord_804846).sum := by decide
  have hdescent : baseEnd_804846 < baseStart_804846 := by decide
  rcases family_descends (prefixWord ++ tailWord_804846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804862 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_804862 : Nat := 118140960795 + 804862 * 2 ^ 59
def prefixEnd_804862 : Nat := 4983230072969 + 3 ^ 40 * 804862 * 2
def baseEnd_804862 : Nat := 137760355513045069141171

theorem tailTrace_804862 : CollatzResearch.WordTrace tailWord_804862 prefixEnd_804862 137760355513045069141171 := by
  unfold tailWord_804862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669466101266238541375105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19570485873419938887333893 3669466101266238541375105)
  ·
    refine ⟨2752099575949678906031329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3669466101266238541375105 2752099575949678906031329)
    ·
      refine ⟨2064074681962259179523497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2752099575949678906031329 2064074681962259179523497)
      ·
        refine ⟨1548056011471694384642623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2064074681962259179523497 1548056011471694384642623)
        ·
          refine ⟨2322084017207541576963935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1548056011471694384642623 2322084017207541576963935)
          ·
            refine ⟨3483126025811312365445903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2322084017207541576963935 3483126025811312365445903)
            ·
              refine ⟨5224689038716968548168855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483126025811312365445903 5224689038716968548168855)
              ·
                refine ⟨7837033558075452822253283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5224689038716968548168855 7837033558075452822253283)
                ·
                  refine ⟨11755550337113179233379925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7837033558075452822253283 11755550337113179233379925)
                  ·
                    refine ⟨137760355513045069141171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11755550337113179233379925 137760355513045069141171)
                    ·
                      rfl

theorem cell23_804862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_804862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804862 prefixEnd_804862 := by exact prefixLift 804862
  have htrace : WordTrace (prefixWord ++ tailWord_804862) baseStart_804862 baseEnd_804862 := by
    simpa [prefixWord, tailWord_804862, baseEnd_804862] using wordTrace_append hprefix tailTrace_804862
  have hstable : (prefixWord ++ tailWord_804862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804862).length < 2 ^ (prefixWord ++ tailWord_804862).sum := by decide
  have hdescent : baseEnd_804862 < baseStart_804862 := by decide
  rcases family_descends (prefixWord ++ tailWord_804862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804869 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 4, 2]
def baseStart_804869 : Nat := 118140960795 + 804869 * 2 ^ 59
def prefixEnd_804869 : Nat := 4983230072969 + 3 ^ 40 * 804869 * 2
def baseEnd_804869 : Nat := 413284660903716680035981

theorem tailTrace_804869 : CollatzResearch.WordTrace tailWord_804869 prefixEnd_804869 413284660903716680035981 := by
  unfold tailWord_804869
  simp only [CollatzResearch.WordTrace]
  refine ⟨29355984121104548526505661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19570656080736365684337107 29355984121104548526505661)
  ·
    refine ⟨11008494045414205697439623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29355984121104548526505661 11008494045414205697439623)
    ·
      refine ⟨16512741068121308546159435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11008494045414205697439623 16512741068121308546159435)
      ·
        refine ⟨24769111602181962819239153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16512741068121308546159435 24769111602181962819239153)
        ·
          refine ⟨18576833701636472114429365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24769111602181962819239153 18576833701636472114429365)
          ·
            refine ⟨1741578159528419260727753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18576833701636472114429365 1741578159528419260727753)
            ·
              refine ⟨1306183619646314445545815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741578159528419260727753 1306183619646314445545815)
              ·
                refine ⟨1959275429469471668318723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1306183619646314445545815 1959275429469471668318723)
                ·
                  refine ⟨2938913144204207502478085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1959275429469471668318723 2938913144204207502478085)
                  ·
                    refine ⟨551046214538288906714641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2938913144204207502478085 551046214538288906714641)
                    ·
                      refine ⟨413284660903716680035981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551046214538288906714641 413284660903716680035981)
                      ·
                        rfl

theorem cell23_804869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 4, 2].length) (baseStart_804869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804869 prefixEnd_804869 := by exact prefixLift 804869
  have htrace : WordTrace (prefixWord ++ tailWord_804869) baseStart_804869 baseEnd_804869 := by
    simpa [prefixWord, tailWord_804869, baseEnd_804869] using wordTrace_append hprefix tailTrace_804869
  have hstable : (prefixWord ++ tailWord_804869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804869).length < 2 ^ (prefixWord ++ tailWord_804869).sum := by decide
  have hdescent : baseEnd_804869 < baseStart_804869 := by decide
  rcases family_descends (prefixWord ++ tailWord_804869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804875 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 7]
def baseStart_804875 : Nat := 118140960795 + 804875 * 2 ^ 59
def prefixEnd_804875 : Nat := 4983230072969 + 3 ^ 40 * 804875 * 2
def baseEnd_804875 : Nat := 45920860198627072951217

theorem tailTrace_804875 : CollatzResearch.WordTrace tailWord_804875 prefixEnd_804875 45920860198627072951217 := by
  unfold tailWord_804875
  simp only [CollatzResearch.WordTrace]
  refine ⟨29356202959082811551224079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19570801972721874367482719 29356202959082811551224079)
  ·
    refine ⟨44034304438624217326836119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29356202959082811551224079 44034304438624217326836119)
    ·
      refine ⟨66051456657936325990254179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44034304438624217326836119 66051456657936325990254179)
      ·
        refine ⟨99077184986904488985381269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66051456657936325990254179 99077184986904488985381269)
        ·
          refine ⟨4644243046261147921189747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 99077184986904488985381269 4644243046261147921189747)
          ·
            refine ⟨6966364569391721881784621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644243046261147921189747 6966364569391721881784621)
            ·
              refine ⟨2612386713521895705669233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6966364569391721881784621 2612386713521895705669233)
              ·
                refine ⟨1959290035141421779251925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2612386713521895705669233 1959290035141421779251925)
                ·
                  refine ⟨45920860198627072951217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1959290035141421779251925 45920860198627072951217)
                  ·
                    rfl

theorem cell23_804875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 7].length) (baseStart_804875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804875 prefixEnd_804875 := by exact prefixLift 804875
  have htrace : WordTrace (prefixWord ++ tailWord_804875) baseStart_804875 baseEnd_804875 := by
    simpa [prefixWord, tailWord_804875, baseEnd_804875] using wordTrace_append hprefix tailTrace_804875
  have hstable : (prefixWord ++ tailWord_804875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804875).length < 2 ^ (prefixWord ++ tailWord_804875).sum := by decide
  have hdescent : baseEnd_804875 < baseStart_804875 := by decide
  rcases family_descends (prefixWord ++ tailWord_804875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804903 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_804903 : Nat := 118140960795 + 804903 * 2 ^ 59
def prefixEnd_804903 : Nat := 4983230072969 + 3 ^ 40 * 804903 * 2
def baseEnd_804903 : Nat := 413302119245969547010825

theorem tailTrace_804903 : CollatzResearch.WordTrace tailWord_804903 prefixEnd_804903 413302119245969547010825 := by
  unfold tailWord_804903
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357224202981372333243363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571482801987581555495575 29357224202981372333243363)
  ·
    refine ⟨44035836304472058499865045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357224202981372333243363 44035836304472058499865045)
    ·
      refine ⟨1032089913386063871090587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 44035836304472058499865045 1032089913386063871090587)
      ·
        refine ⟨1548134870079095806635881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1032089913386063871090587 1548134870079095806635881)
        ·
          refine ⟨1161101152559321854976911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1548134870079095806635881 1161101152559321854976911)
          ·
            refine ⟨1741651728838982782465367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161101152559321854976911 1741651728838982782465367)
            ·
              refine ⟨2612477593258474173698051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741651728838982782465367 2612477593258474173698051)
              ·
                refine ⟨3918716389887711260547077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612477593258474173698051 3918716389887711260547077)
                ·
                  refine ⟨734759323103945861352577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3918716389887711260547077 734759323103945861352577)
                  ·
                    refine ⟨551069492327959396014433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 734759323103945861352577 551069492327959396014433)
                    ·
                      refine ⟨413302119245969547010825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551069492327959396014433 413302119245969547010825)
                      ·
                        rfl

theorem cell23_804903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_804903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804903 prefixEnd_804903 := by exact prefixLift 804903
  have htrace : WordTrace (prefixWord ++ tailWord_804903) baseStart_804903 baseEnd_804903 := by
    simpa [prefixWord, tailWord_804903, baseEnd_804903] using wordTrace_append hprefix tailTrace_804903
  have hstable : (prefixWord ++ tailWord_804903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804903).length < 2 ^ (prefixWord ++ tailWord_804903).sum := by decide
  have hdescent : baseEnd_804903 < baseStart_804903 := by decide
  rcases family_descends (prefixWord ++ tailWord_804903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804915 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5]
def baseStart_804915 : Nat := 118140960795 + 804915 * 2 ^ 59
def prefixEnd_804915 : Nat := 4983230072969 + 3 ^ 40 * 804915 * 2
def baseEnd_804915 : Nat := 413308281013823500060769

theorem tailTrace_804915 : CollatzResearch.WordTrace tailWord_804915 prefixEnd_804915 413308281013823500060769 := by
  unfold tailWord_804915
  simp only [CollatzResearch.WordTrace]
  refine ⟨29357661878937898382680199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19571774585958598921786799 29357661878937898382680199)
  ·
    refine ⟨44036492818406847574020299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29357661878937898382680199 44036492818406847574020299)
    ·
      refine ⟨66054739227610271361030449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44036492818406847574020299 66054739227610271361030449)
      ·
        refine ⟨49541054420707703520772837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66054739227610271361030449 49541054420707703520772837)
        ·
          refine ⟨9288947703882694410144907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49541054420707703520772837 9288947703882694410144907)
          ·
            refine ⟨13933421555824041615217361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9288947703882694410144907 13933421555824041615217361)
            ·
              refine ⟨10450066166868031211413021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13933421555824041615217361 10450066166868031211413021)
              ·
                refine ⟨3918774812575511704279883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10450066166868031211413021 3918774812575511704279883)
                ·
                  refine ⟨5878162218863267556419825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918774812575511704279883 5878162218863267556419825)
                  ·
                    refine ⟨4408621664147450667314869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5878162218863267556419825 4408621664147450667314869)
                    ·
                      refine ⟨413308281013823500060769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4408621664147450667314869 413308281013823500060769)
                      ·
                        rfl

theorem cell23_804915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_804915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804915 prefixEnd_804915 := by exact prefixLift 804915
  have htrace : WordTrace (prefixWord ++ tailWord_804915) baseStart_804915 baseEnd_804915 := by
    simpa [prefixWord, tailWord_804915, baseEnd_804915] using wordTrace_append hprefix tailTrace_804915
  have hstable : (prefixWord ++ tailWord_804915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804915).length < 2 ^ (prefixWord ++ tailWord_804915).sum := by decide
  have hdescent : baseEnd_804915 < baseStart_804915 := by decide
  rcases family_descends (prefixWord ++ tailWord_804915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804935 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 8]
def baseStart_804935 : Nat := 118140960795 + 804935 * 2 ^ 59
def prefixEnd_804935 : Nat := 4983230072969 + 3 ^ 40 * 804935 * 2
def baseEnd_804935 : Nat := 137772850208971140603559

theorem tailTrace_804935 : CollatzResearch.WordTrace tailWord_804935 prefixEnd_804935 137772850208971140603559 := by
  unfold tailWord_804935
  simp only [CollatzResearch.WordTrace]
  refine ⟨29358391338865441798408259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19572260892576961198938839 29358391338865441798408259)
  ·
    refine ⟨44037587008298162697612389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29358391338865441798408259 44037587008298162697612389)
    ·
      refine ⟨8257047564055905505802323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44037587008298162697612389 8257047564055905505802323)
      ·
        refine ⟨12385571346083858258703485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257047564055905505802323 12385571346083858258703485)
        ·
          refine ⟨4644589254781446847013807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12385571346083858258703485 4644589254781446847013807)
          ·
            refine ⟨6966883882172170270520711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4644589254781446847013807 6966883882172170270520711)
            ·
              refine ⟨10450325823258255405781067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6966883882172170270520711 10450325823258255405781067)
              ·
                refine ⟨15675488734887383108671601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10450325823258255405781067 15675488734887383108671601)
                ·
                  refine ⟨11756616551165537331503701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15675488734887383108671601 11756616551165537331503701)
                  ·
                    refine ⟨137772850208971140603559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 11756616551165537331503701 137772850208971140603559)
                    ·
                      rfl

theorem cell23_804935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_804935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804935 prefixEnd_804935 := by exact prefixLift 804935
  have htrace : WordTrace (prefixWord ++ tailWord_804935) baseStart_804935 baseEnd_804935 := by
    simpa [prefixWord, tailWord_804935, baseEnd_804935] using wordTrace_append hprefix tailTrace_804935
  have hstable : (prefixWord ++ tailWord_804935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804935).length < 2 ^ (prefixWord ++ tailWord_804935).sum := by decide
  have hdescent : baseEnd_804935 < baseStart_804935 := by decide
  rcases family_descends (prefixWord ++ tailWord_804935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804942 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_804942 : Nat := 118140960795 + 804942 * 2 ^ 59
def prefixEnd_804942 : Nat := 4983230072969 + 3 ^ 40 * 804942 * 2
def baseEnd_804942 : Nat := 413322144991494894423145

theorem tailTrace_804942 : CollatzResearch.WordTrace tailWord_804942 prefixEnd_804942 413322144991494894423145 := by
  unfold tailWord_804942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669830831230010249239135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19572431099893387995942053 3669830831230010249239135)
  ·
    refine ⟨5504746246845015373858703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3669830831230010249239135 5504746246845015373858703)
    ·
      refine ⟨8257119370267523060788055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504746246845015373858703 8257119370267523060788055)
      ·
        refine ⟨12385679055401284591182083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8257119370267523060788055 12385679055401284591182083)
        ·
          refine ⟨18578518583101926886773125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12385679055401284591182083 18578518583101926886773125)
          ·
            refine ⟨3483472234331611291269961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18578518583101926886773125 3483472234331611291269961)
            ·
              refine ⟨2612604175748708468452471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3483472234331611291269961 2612604175748708468452471)
              ·
                refine ⟨3918906263623062702678707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2612604175748708468452471 3918906263623062702678707)
                ·
                  refine ⟨5878359395434594054018061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3918906263623062702678707 5878359395434594054018061)
                  ·
                    refine ⟨2204384773287972770256773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5878359395434594054018061 2204384773287972770256773)
                    ·
                      refine ⟨413322144991494894423145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2204384773287972770256773 413322144991494894423145)
                      ·
                        rfl

theorem cell23_804942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_804942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804942 prefixEnd_804942 := by exact prefixLift 804942
  have htrace : WordTrace (prefixWord ++ tailWord_804942) baseStart_804942 baseEnd_804942 := by
    simpa [prefixWord, tailWord_804942, baseEnd_804942] using wordTrace_append hprefix tailTrace_804942
  have hstable : (prefixWord ++ tailWord_804942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804942).length < 2 ^ (prefixWord ++ tailWord_804942).sum := by decide
  have hdescent : baseEnd_804942 < baseStart_804942 := by decide
  rcases family_descends (prefixWord ++ tailWord_804942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_804945 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_804945 : Nat := 118140960795 + 804945 * 2 ^ 59
def prefixEnd_804945 : Nat := 4983230072969 + 3 ^ 40 * 804945 * 2
def baseEnd_804945 : Nat := 413323685433458382685631

theorem tailTrace_804945 : CollatzResearch.WordTrace tailWord_804945 prefixEnd_804945 413323685433458382685631 := by
  unfold tailWord_804945
  simp only [CollatzResearch.WordTrace]
  refine ⟨29358756068829213506272289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19572504045886142337514859 29358756068829213506272289)
  ·
    refine ⟨22019067051621910129704217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29358756068829213506272289 22019067051621910129704217)
    ·
      refine ⟨16514300288716432597278163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22019067051621910129704217 16514300288716432597278163)
      ·
        refine ⟨24771450433074648895917245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16514300288716432597278163 24771450433074648895917245)
        ·
          refine ⟨9289293912402993335968967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24771450433074648895917245 9289293912402993335968967)
          ·
            refine ⟨13933940868604490003953451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289293912402993335968967 13933940868604490003953451)
            ·
              refine ⟨20900911302906735005930177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13933940868604490003953451 20900911302906735005930177)
              ·
                refine ⟨15675683477180051254447633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20900911302906735005930177 15675683477180051254447633)
                ·
                  refine ⟨11756762607885038440835725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15675683477180051254447633 11756762607885038440835725)
                  ·
                    refine ⟨4408785977956889415313397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11756762607885038440835725 4408785977956889415313397)
                    ·
                      refine ⟨413323685433458382685631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 4408785977956889415313397 413323685433458382685631)
                      ·
                        rfl

theorem cell23_804945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_804945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_804945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_804945 prefixEnd_804945 := by exact prefixLift 804945
  have htrace : WordTrace (prefixWord ++ tailWord_804945) baseStart_804945 baseEnd_804945 := by
    simpa [prefixWord, tailWord_804945, baseEnd_804945] using wordTrace_append hprefix tailTrace_804945
  have hstable : (prefixWord ++ tailWord_804945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_804945).length < 2 ^ (prefixWord ++ tailWord_804945).sum := by decide
  have hdescent : baseEnd_804945 < baseStart_804945 := by decide
  rcases family_descends (prefixWord ++ tailWord_804945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 2, 3, 2]
def baseStart_805019 : Nat := 118140960795 + 805019 * 2 ^ 59
def prefixEnd_805019 : Nat := 4983230072969 + 3 ^ 40 * 805019 * 2
def baseEnd_805019 : Nat := 413361683001891093160291

theorem tailTrace_805019 : CollatzResearch.WordTrace tailWord_805019 prefixEnd_805019 413361683001891093160291 := by
  unfold tailWord_805019
  simp only [CollatzResearch.WordTrace]
  refine ⟨29361455070561124144466111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19574303380374082762977407 29361455070561124144466111)
  ·
    refine ⟨44042182605841686216699167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29361455070561124144466111 44042182605841686216699167)
    ·
      refine ⟨66063273908762529325048751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44042182605841686216699167 66063273908762529325048751)
      ·
        refine ⟨99094910863143793987573127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66063273908762529325048751 99094910863143793987573127)
        ·
          refine ⟨148642366294715690981359691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99094910863143793987573127 148642366294715690981359691)
          ·
            refine ⟨222963549442073536472039537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148642366294715690981359691 222963549442073536472039537)
            ·
              refine ⟨167222662081555152354029653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222963549442073536472039537 167222662081555152354029653)
              ·
                refine ⟨1959640571268224441648785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 167222662081555152354029653 1959640571268224441648785)
                ·
                  refine ⟨1469730428451168331236589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1959640571268224441648785 1469730428451168331236589)
                  ·
                    refine ⟨551148910669188124213721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1469730428451168331236589 551148910669188124213721)
                    ·
                      refine ⟨413361683001891093160291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551148910669188124213721 413361683001891093160291)
                      ·
                        rfl

theorem cell23_805019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 3, 2].length) (baseStart_805019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805019 prefixEnd_805019 := by exact prefixLift 805019
  have htrace : WordTrace (prefixWord ++ tailWord_805019) baseStart_805019 baseEnd_805019 := by
    simpa [prefixWord, tailWord_805019, baseEnd_805019] using wordTrace_append hprefix tailTrace_805019
  have hstable : (prefixWord ++ tailWord_805019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805019).length < 2 ^ (prefixWord ++ tailWord_805019).sum := by decide
  have hdescent : baseEnd_805019 < baseStart_805019 := by decide
  rcases family_descends (prefixWord ++ tailWord_805019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805049 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_805049 : Nat := 118140960795 + 805049 * 2 ^ 59
def prefixEnd_805049 : Nat := 4983230072969 + 3 ^ 40 * 805049 * 2
def baseEnd_805049 : Nat := 413377087421525975785153

theorem tailTrace_805049 : CollatzResearch.WordTrace tailWord_805049 prefixEnd_805049 413377087421525975785153 := by
  unfold tailWord_805049
  simp only [CollatzResearch.WordTrace]
  refine ⟨29362549260452439268058201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19575032840301626178705467 29362549260452439268058201)
  ·
    refine ⟨22021911945339329451043651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29362549260452439268058201 22021911945339329451043651)
    ·
      refine ⟨33032867918008994176565477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22021911945339329451043651 33032867918008994176565477)
      ·
        refine ⟨6193662734626686408106027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33032867918008994176565477 6193662734626686408106027)
        ·
          refine ⟨9290494101940029612159041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193662734626686408106027 9290494101940029612159041)
          ·
            refine ⟨6967870576455022209119281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9290494101940029612159041 6967870576455022209119281)
            ·
              refine ⟨5225902932341266656839461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6967870576455022209119281 5225902932341266656839461)
              ·
                refine ⟨979856799813987498157399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5225902932341266656839461 979856799813987498157399)
                ·
                  refine ⟨1469785199720981247236099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 979856799813987498157399 1469785199720981247236099)
                  ·
                    refine ⟨2204677799581471870854149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1469785199720981247236099 2204677799581471870854149)
                    ·
                      refine ⟨413377087421525975785153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2204677799581471870854149 413377087421525975785153)
                      ·
                        rfl

theorem cell23_805049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_805049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805049 prefixEnd_805049 := by exact prefixLift 805049
  have htrace : WordTrace (prefixWord ++ tailWord_805049) baseStart_805049 baseEnd_805049 := by
    simpa [prefixWord, tailWord_805049, baseEnd_805049] using wordTrace_append hprefix tailTrace_805049
  have hstable : (prefixWord ++ tailWord_805049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805049).length < 2 ^ (prefixWord ++ tailWord_805049).sum := by decide
  have hdescent : baseEnd_805049 < baseStart_805049 := by decide
  rcases family_descends (prefixWord ++ tailWord_805049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805060 : List Nat := [2, 3, 3, 1, 2, 2, 2, 3, 1, 1, 3]
def baseStart_805060 : Nat := 118140960795 + 805060 * 2 ^ 59
def prefixEnd_805060 : Nat := 4983230072969 + 3 ^ 40 * 805060 * 2
def baseEnd_805060 : Nat := 413382735708725432747603

theorem tailTrace_805060 : CollatzResearch.WordTrace tailWord_805060 prefixEnd_805060 413382735708725432747603 := by
  unfold tailWord_805060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14681475231706294073354317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19575300308941725431139089 14681475231706294073354317)
  ·
    refine ⟨5505553211889860277507869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14681475231706294073354317 5505553211889860277507869)
    ·
      refine ⟨2064582454458697604065451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5505553211889860277507869 2064582454458697604065451)
      ·
        refine ⟨3096873681688046406098177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2064582454458697604065451 3096873681688046406098177)
        ·
          refine ⟨2322655261266034804573633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096873681688046406098177 2322655261266034804573633)
          ·
            refine ⟨1741991445949526103430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322655261266034804573633 1741991445949526103430225)
            ·
              refine ⟨1306493584462144577572669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1741991445949526103430225 1306493584462144577572669)
              ·
                refine ⟨489935094173304216589751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1306493584462144577572669 489935094173304216589751)
                ·
                  refine ⟨734902641259956324884627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 489935094173304216589751 734902641259956324884627)
                  ·
                    refine ⟨1102353961889934487326941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 734902641259956324884627 1102353961889934487326941)
                    ·
                      refine ⟨413382735708725432747603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1102353961889934487326941 413382735708725432747603)
                      ·
                        rfl

theorem cell23_805060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_805060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805060 prefixEnd_805060 := by exact prefixLift 805060
  have htrace : WordTrace (prefixWord ++ tailWord_805060) baseStart_805060 baseEnd_805060 := by
    simpa [prefixWord, tailWord_805060, baseEnd_805060] using wordTrace_append hprefix tailTrace_805060
  have hstable : (prefixWord ++ tailWord_805060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805060).length < 2 ^ (prefixWord ++ tailWord_805060).sum := by decide
  have hdescent : baseEnd_805060 < baseStart_805060 := by decide
  rcases family_descends (prefixWord ++ tailWord_805060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805066 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_805066 : Nat := 118140960795 + 805066 * 2 ^ 59
def prefixEnd_805066 : Nat := 4983230072969 + 3 ^ 40 * 805066 * 2
def baseEnd_805066 : Nat := 413385816592652409272575

theorem tailTrace_805066 : CollatzResearch.WordTrace tailWord_805066 prefixEnd_805066 413385816592652409272575 := by
  unfold tailWord_805066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340792325347712792856763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19575446200927234114284701 7340792325347712792856763)
  ·
    refine ⟨11011188488021569189285145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7340792325347712792856763 11011188488021569189285145)
    ·
      refine ⟨8258391366016176891963859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11011188488021569189285145 8258391366016176891963859)
      ·
        refine ⟨12387587049024265337945789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258391366016176891963859 12387587049024265337945789)
        ·
          refine ⟨4645345143384099501729671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12387587049024265337945789 4645345143384099501729671)
          ·
            refine ⟨6968017715076149252594507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645345143384099501729671 6968017715076149252594507)
            ·
              refine ⟨10452026572614223878891761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968017715076149252594507 10452026572614223878891761)
              ·
                refine ⟨7839019929460667909168821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10452026572614223878891761 7839019929460667909168821)
                ·
                  refine ⟨734908118386937616484577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7839019929460667909168821 734908118386937616484577)
                  ·
                    refine ⟨551181088790203212363433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 734908118386937616484577 551181088790203212363433)
                    ·
                      refine ⟨413385816592652409272575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 551181088790203212363433 413385816592652409272575)
                      ·
                        rfl

theorem cell23_805066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_805066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805066 prefixEnd_805066 := by exact prefixLift 805066
  have htrace : WordTrace (prefixWord ++ tailWord_805066) baseStart_805066 baseEnd_805066 := by
    simpa [prefixWord, tailWord_805066, baseEnd_805066] using wordTrace_append hprefix tailTrace_805066
  have hstable : (prefixWord ++ tailWord_805066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805066).length < 2 ^ (prefixWord ++ tailWord_805066).sum := by decide
  have hdescent : baseEnd_805066 < baseStart_805066 := by decide
  rcases family_descends (prefixWord ++ tailWord_805066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_805093 : List Nat := [1, 3, 1, 4, 2, 2, 3, 1, 2, 4]
def baseStart_805093 : Nat := 118140960795 + 805093 * 2 ^ 59
def prefixEnd_805093 : Nat := 4983230072969 + 3 ^ 40 * 805093 * 2
def baseEnd_805093 : Nat := 137799893523441267878317

theorem tailTrace_805093 : CollatzResearch.WordTrace tailWord_805093 prefixEnd_805093 137799893523441267878317 := by
  unfold tailWord_805093
  simp only [CollatzResearch.WordTrace]
  refine ⟨29364154072293034782659933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19576102714862023188439955 29364154072293034782659933)
  ·
    refine ⟨11011557777109888043497475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29364154072293034782659933 11011557777109888043497475)
    ·
      refine ⟨16517336665664832065246213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11011557777109888043497475 16517336665664832065246213)
      ·
        refine ⟨3097000624812156012233665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16517336665664832065246213 3097000624812156012233665)
        ·
          refine ⟨2322750468609117009175249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3097000624812156012233665 2322750468609117009175249)
          ·
            refine ⟨1742062851456837756881437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2322750468609117009175249 1742062851456837756881437)
            ·
              refine ⟨653273569296314158830539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742062851456837756881437 653273569296314158830539)
              ·
                refine ⟨979910353944471238245809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653273569296314158830539 979910353944471238245809)
                ·
                  refine ⟨734932765458353428684357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979910353944471238245809 734932765458353428684357)
                  ·
                    refine ⟨137799893523441267878317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734932765458353428684357 137799893523441267878317)
                    ·
                      rfl

theorem cell23_805093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 1, 2, 4].length) (baseStart_805093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_805093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_805093 prefixEnd_805093 := by exact prefixLift 805093
  have htrace : WordTrace (prefixWord ++ tailWord_805093) baseStart_805093 baseEnd_805093 := by
    simpa [prefixWord, tailWord_805093, baseEnd_805093] using wordTrace_append hprefix tailTrace_805093
  have hstable : (prefixWord ++ tailWord_805093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_805093).length < 2 ^ (prefixWord ++ tailWord_805093).sum := by decide
  have hdescent : baseEnd_805093 < baseStart_805093 := by decide
  rcases family_descends (prefixWord ++ tailWord_805093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
