import V185TrunkScan23Chunk1072

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6352109 : List Nat := [1, 5, 1, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6352109 : Nat := 118140960795 + 6352109 * 2 ^ 59
def prefixEnd_6352109 : Nat := 4983230072969 + 3 ^ 40 * 6352109 * 2
def baseEnd_6352109 : Nat := 3261685086750593078024689

theorem tailTrace_6352109 : CollatzResearch.WordTrace tailWord_6352109 prefixEnd_6352109 3261685086750593078024689 := by
  unfold tailWord_6352109
  simp only [CollatzResearch.WordTrace]
  refine ⟨231680448544401421692683381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154453632362934281128455587 231680448544401421692683381)
  ·
    refine ⟨21720042051037633283689067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231680448544401421692683381 21720042051037633283689067)
    ·
      refine ⟨32580063076556449925533601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21720042051037633283689067 32580063076556449925533601)
      ·
        refine ⟨24435047307417337444150201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32580063076556449925533601 24435047307417337444150201)
        ·
          refine ⟨18326285480563003083112651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24435047307417337444150201 18326285480563003083112651)
          ·
            refine ⟨27489428220844504624668977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18326285480563003083112651 27489428220844504624668977)
            ·
              refine ⟨20617071165633378468501733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27489428220844504624668977 20617071165633378468501733)
              ·
                refine ⟨3865700843556258462844075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20617071165633378468501733 3865700843556258462844075)
                ·
                  refine ⟨5798551265334387694266113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865700843556258462844075 5798551265334387694266113)
                  ·
                    refine ⟨4348913449000790770699585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5798551265334387694266113 4348913449000790770699585)
                    ·
                      refine ⟨3261685086750593078024689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4348913449000790770699585 3261685086750593078024689)
                      ·
                        rfl

theorem cell23_6352109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6352109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352109 prefixEnd_6352109 := by exact prefixLift 6352109
  have htrace : WordTrace (prefixWord ++ tailWord_6352109) baseStart_6352109 baseEnd_6352109 := by
    simpa [prefixWord, tailWord_6352109, baseEnd_6352109] using wordTrace_append hprefix tailTrace_6352109
  have hstable : (prefixWord ++ tailWord_6352109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352109).length < 2 ^ (prefixWord ++ tailWord_6352109).sum := by decide
  have hdescent : baseEnd_6352109 < baseStart_6352109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352201 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 7]
def baseStart_6352201 : Nat := 118140960795 + 6352201 * 2 ^ 59
def prefixEnd_6352201 : Nat := 4983230072969 + 3 ^ 40 * 6352201 * 2
def baseEnd_6352201 : Nat := 1087244108990268906024755

theorem tailTrace_6352201 : CollatzResearch.WordTrace tailWord_6352201 prefixEnd_6352201 1087244108990268906024755 := by
  unfold tailWord_6352201
  simp only [CollatzResearch.WordTrace]
  refine ⟨231683804060068121405032457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154455869373378747603354971 231683804060068121405032457)
  ·
    refine ⟨173762853045051091053774343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231683804060068121405032457 173762853045051091053774343)
    ·
      refine ⟨260644279567576636580661515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173762853045051091053774343 260644279567576636580661515)
      ·
        refine ⟨390966419351364954870992273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260644279567576636580661515 390966419351364954870992273)
        ·
          refine ⟨293224814513523716153244205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390966419351364954870992273 293224814513523716153244205)
          ·
            refine ⟨109959305442571393557466577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293224814513523716153244205 109959305442571393557466577)
            ·
              refine ⟨82469479081928545168099933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109959305442571393557466577 82469479081928545168099933)
              ·
                refine ⟨30926054655723204438037475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82469479081928545168099933 30926054655723204438037475)
                ·
                  refine ⟨46389081983584806657056213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30926054655723204438037475 46389081983584806657056213)
                  ·
                    refine ⟨1087244108990268906024755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46389081983584806657056213 1087244108990268906024755)
                    ·
                      rfl

theorem cell23_6352201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_6352201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352201 prefixEnd_6352201 := by exact prefixLift 6352201
  have htrace : WordTrace (prefixWord ++ tailWord_6352201) baseStart_6352201 baseEnd_6352201 := by
    simpa [prefixWord, tailWord_6352201, baseEnd_6352201] using wordTrace_append hprefix tailTrace_6352201
  have hstable : (prefixWord ++ tailWord_6352201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352201).length < 2 ^ (prefixWord ++ tailWord_6352201).sum := by decide
  have hdescent : baseEnd_6352201 < baseStart_6352201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352211 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5]
def baseStart_6352211 : Nat := 118140960795 + 6352211 * 2 ^ 59
def prefixEnd_6352211 : Nat := 4983230072969 + 3 ^ 40 * 6352211 * 2
def baseEnd_6352211 : Nat := 3261737461777351678949219

theorem tailTrace_6352211 : CollatzResearch.WordTrace tailWord_6352211 prefixEnd_6352211 3261737461777351678949219 := by
  unfold tailWord_6352211
  simp only [CollatzResearch.WordTrace]
  refine ⟨231684168790031893112896487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154456112526687928741930991 231684168790031893112896487)
  ·
    refine ⟨347526253185047839669344731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231684168790031893112896487 347526253185047839669344731)
    ·
      refine ⟨521289379777571759504017097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347526253185047839669344731 521289379777571759504017097)
      ·
        refine ⟨390967034833178819628012823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521289379777571759504017097 390967034833178819628012823)
        ·
          refine ⟨586450552249768229442019235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390967034833178819628012823 586450552249768229442019235)
          ·
            refine ⟨879675828374652344163028853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586450552249768229442019235 879675828374652344163028853)
            ·
              refine ⟨82469608910123657265283955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 879675828374652344163028853 82469608910123657265283955)
              ·
                refine ⟨123704413365185485897925933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82469608910123657265283955 123704413365185485897925933)
                ·
                  refine ⟨46389155011944557211722225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123704413365185485897925933 46389155011944557211722225)
                  ·
                    refine ⟨34791866258958417908791669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46389155011944557211722225 34791866258958417908791669)
                    ·
                      refine ⟨3261737461777351678949219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34791866258958417908791669 3261737461777351678949219)
                      ·
                        rfl

theorem cell23_6352211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_6352211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352211 prefixEnd_6352211 := by exact prefixLift 6352211
  have htrace : WordTrace (prefixWord ++ tailWord_6352211) baseStart_6352211 baseEnd_6352211 := by
    simpa [prefixWord, tailWord_6352211, baseEnd_6352211] using wordTrace_append hprefix tailTrace_6352211
  have hstable : (prefixWord ++ tailWord_6352211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352211).length < 2 ^ (prefixWord ++ tailWord_6352211).sum := by decide
  have hdescent : baseEnd_6352211 < baseStart_6352211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352218 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 2, 5]
def baseStart_6352218 : Nat := 118140960795 + 6352218 * 2 ^ 59
def prefixEnd_6352218 : Nat := 4983230072969 + 3 ^ 40 * 6352218 * 2
def baseEnd_6352218 : Nat := 1087247018713977717187229

theorem tailTrace_6352218 : CollatzResearch.WordTrace tailWord_6352218 prefixEnd_6352218 1087247018713977717187229 := by
  unfold tailWord_6352218
  simp only [CollatzResearch.WordTrace]
  refine ⟨57921106025251633327100327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154456282734004355538934205 57921106025251633327100327)
  ·
    refine ⟨86881659037877449990650491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57921106025251633327100327 86881659037877449990650491)
    ·
      refine ⟨130322488556816174985975737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86881659037877449990650491 130322488556816174985975737)
      ·
        refine ⟨97741866417612131239481803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130322488556816174985975737 97741866417612131239481803)
        ·
          refine ⟨146612799626418196859222705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97741866417612131239481803 146612799626418196859222705)
          ·
            refine ⟨109959599719813647644417029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146612799626418196859222705 109959599719813647644417029)
            ·
              refine ⟨20617424947465058933328193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109959599719813647644417029 20617424947465058933328193)
              ·
                refine ⟨15463068710598794199996145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20617424947465058933328193 15463068710598794199996145)
                ·
                  refine ⟨11597301532949095649997109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15463068710598794199996145 11597301532949095649997109)
                  ·
                    refine ⟨1087247018713977717187229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11597301532949095649997109 1087247018713977717187229)
                    ·
                      rfl

theorem cell23_6352218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 5].length) (baseStart_6352218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352218 prefixEnd_6352218 := by exact prefixLift 6352218
  have htrace : WordTrace (prefixWord ++ tailWord_6352218) baseStart_6352218 baseEnd_6352218 := by
    simpa [prefixWord, tailWord_6352218, baseEnd_6352218] using wordTrace_append hprefix tailTrace_6352218
  have hstable : (prefixWord ++ tailWord_6352218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352218).length < 2 ^ (prefixWord ++ tailWord_6352218).sum := by decide
  have hdescent : baseEnd_6352218 < baseStart_6352218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352228 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_6352228 : Nat := 118140960795 + 6352228 * 2 ^ 59
def prefixEnd_6352228 : Nat := 4983230072969 + 3 ^ 40 * 6352228 * 2
def baseEnd_6352228 : Nat := 3261746190948478112436641

theorem tailTrace_6352228 : CollatzResearch.WordTrace tailWord_6352228 prefixEnd_6352228 3261746190948478112436641 := by
  unfold tailWord_6352228
  simp only [CollatzResearch.WordTrace]
  refine ⟨115842394415485152508132669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154456525887313536677510225 115842394415485152508132669)
  ·
    refine ⟨43440897905806932190549751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115842394415485152508132669 43440897905806932190549751)
    ·
      refine ⟨65161346858710398285824627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43440897905806932190549751 65161346858710398285824627)
      ·
        refine ⟨97742020288065597428736941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65161346858710398285824627 97742020288065597428736941)
        ·
          refine ⟨36653257608024599035776353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97742020288065597428736941 36653257608024599035776353)
          ·
            refine ⟨27489943206018449276832265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36653257608024599035776353 27489943206018449276832265)
            ·
              refine ⟨20617457404513836957624199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27489943206018449276832265 20617457404513836957624199)
              ·
                refine ⟨30926186106770755436436299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20617457404513836957624199 30926186106770755436436299)
                ·
                  refine ⟨46389279160156133154654449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30926186106770755436436299 46389279160156133154654449)
                  ·
                    refine ⟨34791959370117099865990837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46389279160156133154654449 34791959370117099865990837)
                    ·
                      refine ⟨3261746190948478112436641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34791959370117099865990837 3261746190948478112436641)
                      ·
                        rfl

theorem cell23_6352228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_6352228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352228 prefixEnd_6352228 := by exact prefixLift 6352228
  have htrace : WordTrace (prefixWord ++ tailWord_6352228) baseStart_6352228 baseEnd_6352228 := by
    simpa [prefixWord, tailWord_6352228, baseEnd_6352228] using wordTrace_append hprefix tailTrace_6352228
  have hstable : (prefixWord ++ tailWord_6352228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352228).length < 2 ^ (prefixWord ++ tailWord_6352228).sum := by decide
  have hdescent : baseEnd_6352228 < baseStart_6352228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352271 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_6352271 : Nat := 118140960795 + 6352271 * 2 ^ 59
def prefixEnd_6352271 : Nat := 4983230072969 + 3 ^ 40 * 6352271 * 2
def baseEnd_6352271 : Nat := 3261768270616621444198943

theorem tailTrace_6352271 : CollatzResearch.WordTrace tailWord_6352271 prefixEnd_6352271 3261768270616621444198943 := by
  unfold tailWord_6352271
  simp only [CollatzResearch.WordTrace]
  refine ⟨231686357169814523360080667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154457571446543015573387111 231686357169814523360080667)
  ·
    refine ⟨347529535754721785040121001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231686357169814523360080667 347529535754721785040121001)
    ·
      refine ⟨260647151816041338780090751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347529535754721785040121001 260647151816041338780090751)
      ·
        refine ⟨390970727724062008170136127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260647151816041338780090751 390970727724062008170136127)
        ·
          refine ⟨586456091586093012255204191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390970727724062008170136127 586456091586093012255204191)
          ·
            refine ⟨879684137379139518382806287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586456091586093012255204191 879684137379139518382806287)
            ·
              refine ⟨1319526206068709277574209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879684137379139518382806287 1319526206068709277574209431)
              ·
                refine ⟨1979289309103063916361314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319526206068709277574209431 1979289309103063916361314147)
                ·
                  refine ⟨2968933963654595874541971221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1979289309103063916361314147 2968933963654595874541971221)
                  ·
                    refine ⟨139168779546309181619154901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2968933963654595874541971221 139168779546309181619154901)
                    ·
                      refine ⟨3261768270616621444198943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139168779546309181619154901 3261768270616621444198943)
                      ·
                        rfl

theorem cell23_6352271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_6352271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352271 prefixEnd_6352271 := by exact prefixLift 6352271
  have htrace : WordTrace (prefixWord ++ tailWord_6352271) baseStart_6352271 baseEnd_6352271 := by
    simpa [prefixWord, tailWord_6352271, baseEnd_6352271] using wordTrace_append hprefix tailTrace_6352271
  have hstable : (prefixWord ++ tailWord_6352271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352271).length < 2 ^ (prefixWord ++ tailWord_6352271).sum := by decide
  have hdescent : baseEnd_6352271 < baseStart_6352271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352282 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 1, 4]
def baseStart_6352282 : Nat := 118140960795 + 6352282 * 2 ^ 59
def prefixEnd_6352282 : Nat := 4983230072969 + 3 ^ 40 * 6352282 * 2
def baseEnd_6352282 : Nat := 1087257972967940300387131

theorem tailTrace_6352282 : CollatzResearch.WordTrace tailWord_6352282 prefixEnd_6352282 1087257972967940300387131 := by
  unfold tailWord_6352282
  simp only [CollatzResearch.WordTrace]
  refine ⟨57921689593193668059682775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154457838915183114825820733 57921689593193668059682775)
  ·
    refine ⟨86882534389790502089524163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57921689593193668059682775 86882534389790502089524163)
    ·
      refine ⟨130323801584685753134286245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86882534389790502089524163 130323801584685753134286245)
      ·
        refine ⟨24435712797128578712678671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130323801584685753134286245 24435712797128578712678671)
        ·
          refine ⟨36653569195692868069018007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24435712797128578712678671 36653569195692868069018007)
          ·
            refine ⟨54980353793539302103527011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36653569195692868069018007 54980353793539302103527011)
            ·
              refine ⟨82470530690308953155290517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54980353793539302103527011 82470530690308953155290517)
              ·
                refine ⟨3865806126108232179154243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82470530690308953155290517 3865806126108232179154243)
                ·
                  refine ⟨5798709189162348268731365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865806126108232179154243 5798709189162348268731365)
                  ·
                    refine ⟨1087257972967940300387131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798709189162348268731365 1087257972967940300387131)
                    ·
                      rfl

theorem cell23_6352282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 4].length) (baseStart_6352282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352282 prefixEnd_6352282 := by exact prefixLift 6352282
  have htrace : WordTrace (prefixWord ++ tailWord_6352282) baseStart_6352282 baseEnd_6352282 := by
    simpa [prefixWord, tailWord_6352282, baseEnd_6352282] using wordTrace_append hprefix tailTrace_6352282
  have hstable : (prefixWord ++ tailWord_6352282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352282).length < 2 ^ (prefixWord ++ tailWord_6352282).sum := by decide
  have hdescent : baseEnd_6352282 < baseStart_6352282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352316 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_6352316 : Nat := 118140960795 + 6352316 * 2 ^ 59
def prefixEnd_6352316 : Nat := 4983230072969 + 3 ^ 40 * 6352316 * 2
def baseEnd_6352316 : Nat := 1087263792415357922712079

theorem tailTrace_6352316 : CollatzResearch.WordTrace tailWord_6352316 prefixEnd_6352316 1087263792415357922712079 := by
  unfold tailWord_6352316
  simp only [CollatzResearch.WordTrace]
  refine ⟨115843999227325748022734401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154458665636434330696979201 115843999227325748022734401)
  ·
    refine ⟨86882999420494311017050801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115843999227325748022734401 86882999420494311017050801)
    ·
      refine ⟨65162249565370733262788101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86882999420494311017050801 65162249565370733262788101)
      ·
        refine ⟨12217921793507012486772769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65162249565370733262788101 12217921793507012486772769)
        ·
          refine ⟨9163441345130259365079577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12217921793507012486772769 9163441345130259365079577)
          ·
            refine ⟨6872581008847694523809683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9163441345130259365079577 6872581008847694523809683)
            ·
              refine ⟨10308871513271541785714525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6872581008847694523809683 10308871513271541785714525)
              ·
                refine ⟨3865826817476828169642947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10308871513271541785714525 3865826817476828169642947)
                ·
                  refine ⟨5798740226215242254464421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3865826817476828169642947 5798740226215242254464421)
                  ·
                    refine ⟨1087263792415357922712079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5798740226215242254464421 1087263792415357922712079)
                    ·
                      rfl

theorem cell23_6352316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_6352316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352316 prefixEnd_6352316 := by exact prefixLift 6352316
  have htrace : WordTrace (prefixWord ++ tailWord_6352316) baseStart_6352316 baseEnd_6352316 := by
    simpa [prefixWord, tailWord_6352316, baseEnd_6352316] using wordTrace_append hprefix tailTrace_6352316
  have hstable : (prefixWord ++ tailWord_6352316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352316).length < 2 ^ (prefixWord ++ tailWord_6352316).sum := by decide
  have hdescent : baseEnd_6352316 < baseStart_6352316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352332 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6352332 : Nat := 118140960795 + 6352332 * 2 ^ 59
def prefixEnd_6352332 : Nat := 4983230072969 + 3 ^ 40 * 6352332 * 2
def baseEnd_6352332 : Nat := 3261799592936545705536163

theorem tailTrace_6352332 : CollatzResearch.WordTrace tailWord_6352332 prefixEnd_6352332 3261799592936545705536163 := by
  unfold tailWord_6352332
  simp only [CollatzResearch.WordTrace]
  refine ⟨115844291011296765389025625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154459054681729020518700833 115844291011296765389025625)
  ·
    refine ⟨86883218258472574041769219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115844291011296765389025625 86883218258472574041769219)
    ·
      refine ⟨130324827387708861062653829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86883218258472574041769219 130324827387708861062653829)
      ·
        refine ⟨24435905135195411449247593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130324827387708861062653829 24435905135195411449247593)
        ·
          refine ⟨18326928851396558586935695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24435905135195411449247593 18326928851396558586935695)
          ·
            refine ⟨27490393277094837880403543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18326928851396558586935695 27490393277094837880403543)
            ·
              refine ⟨41235589915642256820605315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27490393277094837880403543 41235589915642256820605315)
              ·
                refine ⟨61853384873463385230907973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41235589915642256820605315 61853384873463385230907973)
                ·
                  refine ⟨11597509663774384730795245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61853384873463385230907973 11597509663774384730795245)
                  ·
                    refine ⟨4349066123915394274048217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11597509663774384730795245 4349066123915394274048217)
                    ·
                      refine ⟨3261799592936545705536163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349066123915394274048217 3261799592936545705536163)
                      ·
                        rfl

theorem cell23_6352332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6352332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352332 prefixEnd_6352332 := by exact prefixLift 6352332
  have htrace : WordTrace (prefixWord ++ tailWord_6352332) baseStart_6352332 baseEnd_6352332 := by
    simpa [prefixWord, tailWord_6352332, baseEnd_6352332] using wordTrace_append hprefix tailTrace_6352332
  have hstable : (prefixWord ++ tailWord_6352332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352332).length < 2 ^ (prefixWord ++ tailWord_6352332).sum := by decide
  have hdescent : baseEnd_6352332 < baseStart_6352332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352362 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_6352362 : Nat := 118140960795 + 6352362 * 2 ^ 59
def prefixEnd_6352362 : Nat := 4983230072969 + 3 ^ 40 * 6352362 * 2
def baseEnd_6352362 : Nat := 3261814997356180588161025

theorem tailTrace_6352362 : CollatzResearch.WordTrace tailWord_6352362 prefixEnd_6352362 3261814997356180588161025 := by
  unfold tailWord_6352362
  simp only [CollatzResearch.WordTrace]
  refine ⟨57922419053121211475410835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154459784141656563934428893 57922419053121211475410835)
  ·
    refine ⟨86883628579681817213116253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57922419053121211475410835 86883628579681817213116253)
    ·
      refine ⟨32581360717380681454918595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86883628579681817213116253 32581360717380681454918595)
      ·
        refine ⟨48872041076071022182377893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32581360717380681454918595 48872041076071022182377893)
        ·
          refine ⟨9163507701763316659195855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48872041076071022182377893 9163507701763316659195855)
          ·
            refine ⟨13745261552644974988793783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9163507701763316659195855 13745261552644974988793783)
            ·
              refine ⟨20617892328967462483190675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745261552644974988793783 20617892328967462483190675)
              ·
                refine ⟨30926838493451193724786013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20617892328967462483190675 30926838493451193724786013)
                ·
                  refine ⟨11597564435044197646794755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30926838493451193724786013 11597564435044197646794755)
                  ·
                    refine ⟨17396346652566296470192133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11597564435044197646794755 17396346652566296470192133)
                    ·
                      refine ⟨3261814997356180588161025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17396346652566296470192133 3261814997356180588161025)
                      ·
                        rfl

theorem cell23_6352362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_6352362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352362 prefixEnd_6352362 := by exact prefixLift 6352362
  have htrace : WordTrace (prefixWord ++ tailWord_6352362) baseStart_6352362 baseEnd_6352362 := by
    simpa [prefixWord, tailWord_6352362, baseEnd_6352362] using wordTrace_append hprefix tailTrace_6352362
  have hstable : (prefixWord ++ tailWord_6352362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352362).length < 2 ^ (prefixWord ++ tailWord_6352362).sum := by decide
  have hdescent : baseEnd_6352362 < baseStart_6352362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352368 : List Nat := [2, 1, 1, 1, 3, 4, 2, 9]
def baseStart_6352368 : Nat := 118140960795 + 6352368 * 2 ^ 59
def prefixEnd_6352368 : Nat := 4983230072969 + 3 ^ 40 * 6352368 * 2
def baseEnd_6352368 : Nat := 120808076971855835729111

theorem tailTrace_6352368 : CollatzResearch.WordTrace tailWord_6352368 prefixEnd_6352368 120808076971855835729111 := by
  unfold tailWord_6352368
  simp only [CollatzResearch.WordTrace]
  refine ⟨115844947525231554463180879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154459930033642072617574505 115844947525231554463180879)
  ·
    refine ⟨173767421287847331694771319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115844947525231554463180879 173767421287847331694771319)
    ·
      refine ⟨260651131931770997542156979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173767421287847331694771319 260651131931770997542156979)
      ·
        refine ⟨390976697897656496313235469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260651131931770997542156979 390976697897656496313235469)
        ·
          refine ⟨146616261711621186117463301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390976697897656496313235469 146616261711621186117463301)
          ·
            refine ⟨27490549070928972397024369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146616261711621186117463301 27490549070928972397024369)
            ·
              refine ⟨20617911803196729297768277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27490549070928972397024369 20617911803196729297768277)
              ·
                refine ⟨120808076971855835729111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20617911803196729297768277 120808076971855835729111)
                ·
                  rfl

theorem cell23_6352368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 9].length) (baseStart_6352368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352368 prefixEnd_6352368 := by exact prefixLift 6352368
  have htrace : WordTrace (prefixWord ++ tailWord_6352368) baseStart_6352368 baseEnd_6352368 := by
    simpa [prefixWord, tailWord_6352368, baseEnd_6352368] using wordTrace_append hprefix tailTrace_6352368
  have hstable : (prefixWord ++ tailWord_6352368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352368).length < 2 ^ (prefixWord ++ tailWord_6352368).sum := by decide
  have hdescent : baseEnd_6352368 < baseStart_6352368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352385 : List Nat := [1, 2, 4, 1, 5, 10]
def baseStart_6352385 : Nat := 118140960795 + 6352385 * 2 ^ 59
def prefixEnd_6352385 : Nat := 4983230072969 + 3 ^ 40 * 6352385 * 2
def baseEnd_6352385 : Nat := 13423155586054460897833

theorem tailTrace_6352385 : CollatzResearch.WordTrace tailWord_6352385 prefixEnd_6352385 13423155586054460897833 := by
  unfold tailWord_6352385
  simp only [CollatzResearch.WordTrace]
  refine ⟨231690515091401520829730609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154460343394267680553153739 231690515091401520829730609)
  ·
    refine ⟨173767886318551140622297957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231690515091401520829730609 173767886318551140622297957)
    ·
      refine ⟨32581478684728338866680867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173767886318551140622297957 32581478684728338866680867)
      ·
        refine ⟨48872218027092508300021301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32581478684728338866680867 48872218027092508300021301)
        ·
          refine ⟨4581770440039922653126997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48872218027092508300021301 4581770440039922653126997)
          ·
            refine ⟨13423155586054460897833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4581770440039922653126997 13423155586054460897833)
            ·
              rfl

theorem cell23_6352385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 10].length) (baseStart_6352385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352385 prefixEnd_6352385 := by exact prefixLift 6352385
  have htrace : WordTrace (prefixWord ++ tailWord_6352385) baseStart_6352385 baseEnd_6352385 := by
    simpa [prefixWord, tailWord_6352385, baseEnd_6352385] using wordTrace_append hprefix tailTrace_6352385
  have hstable : (prefixWord ++ tailWord_6352385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352385).length < 2 ^ (prefixWord ++ tailWord_6352385).sum := by decide
  have hdescent : baseEnd_6352385 < baseStart_6352385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352412 : List Nat := [2, 2, 3, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6352412 : Nat := 118140960795 + 6352412 * 2 ^ 59
def prefixEnd_6352412 : Nat := 4983230072969 + 3 ^ 40 * 6352412 * 2
def baseEnd_6352412 : Nat := 3261840671388905392535795

theorem tailTrace_6352412 : CollatzResearch.WordTrace tailWord_6352412 prefixEnd_6352412 3261840671388905392535795 := by
  unfold tailWord_6352412
  simp only [CollatzResearch.WordTrace]
  refine ⟨115845749931151852220481745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154460999908202469627308993 115845749931151852220481745)
  ·
    refine ⟨86884312448363889165361309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115845749931151852220481745 86884312448363889165361309)
    ·
      refine ⟨32581617168136458437010491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86884312448363889165361309 32581617168136458437010491)
      ·
        refine ⟨48872425752204687655515737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32581617168136458437010491 48872425752204687655515737)
        ·
          refine ⟨36654319314153515741636803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48872425752204687655515737 36654319314153515741636803)
          ·
            refine ⟨54981478971230273612455205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36654319314153515741636803 54981478971230273612455205)
            ·
              refine ⟨10309027307105676302335351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54981478971230273612455205 10309027307105676302335351)
              ·
                refine ⟨15463540960658514453503027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309027307105676302335351 15463540960658514453503027)
                ·
                  refine ⟨23195311440987771680254541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15463540960658514453503027 23195311440987771680254541)
                  ·
                    refine ⟨8698241790370414380095453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23195311440987771680254541 8698241790370414380095453)
                    ·
                      refine ⟨3261840671388905392535795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698241790370414380095453 3261840671388905392535795)
                      ·
                        rfl

theorem cell23_6352412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6352412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352412 prefixEnd_6352412 := by exact prefixLift 6352412
  have htrace : WordTrace (prefixWord ++ tailWord_6352412) baseStart_6352412 baseEnd_6352412 := by
    simpa [prefixWord, tailWord_6352412, baseEnd_6352412] using wordTrace_append hprefix tailTrace_6352412
  have hstable : (prefixWord ++ tailWord_6352412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352412).length < 2 ^ (prefixWord ++ tailWord_6352412).sum := by decide
  have hdescent : baseEnd_6352412 < baseStart_6352412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352439 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_6352439 : Nat := 118140960795 + 6352439 * 2 ^ 59
def prefixEnd_6352439 : Nat := 4983230072969 + 3 ^ 40 * 6352439 * 2
def baseEnd_6352439 : Nat := 3261854535366576786898171

theorem tailTrace_6352439 : CollatzResearch.WordTrace tailWord_6352439 prefixEnd_6352439 3261854535366576786898171 := by
  unfold tailWord_6352439
  simp only [CollatzResearch.WordTrace]
  refine ⟨231692484633205888052196371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154461656422137258701464247 231692484633205888052196371)
  ·
    refine ⟨347538726949808832078294557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231692484633205888052196371 347538726949808832078294557)
    ·
      refine ⟨130327022606178312029360459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347538726949808832078294557 130327022606178312029360459)
      ·
        refine ⟨195490533909267468044040689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130327022606178312029360459 195490533909267468044040689)
        ·
          refine ⟨146617900431950601033030517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195490533909267468044040689 146617900431950601033030517)
          ·
            refine ⟨13745428165495368846846611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146617900431950601033030517 13745428165495368846846611)
            ·
              refine ⟨20618142248243053270269917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13745428165495368846846611 20618142248243053270269917)
              ·
                refine ⟨7731803343091144976351219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20618142248243053270269917 7731803343091144976351219)
                ·
                  refine ⟨11597705014636717464526829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7731803343091144976351219 11597705014636717464526829)
                  ·
                    refine ⟨4349139380488769049197561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11597705014636717464526829 4349139380488769049197561)
                    ·
                      refine ⟨3261854535366576786898171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349139380488769049197561 3261854535366576786898171)
                      ·
                        rfl

theorem cell23_6352439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_6352439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352439 prefixEnd_6352439 := by exact prefixLift 6352439
  have htrace : WordTrace (prefixWord ++ tailWord_6352439) baseStart_6352439 baseEnd_6352439 := by
    simpa [prefixWord, tailWord_6352439, baseEnd_6352439] using wordTrace_append hprefix tailTrace_6352439
  have hstable : (prefixWord ++ tailWord_6352439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352439).length < 2 ^ (prefixWord ++ tailWord_6352439).sum := by decide
  have hdescent : baseEnd_6352439 < baseStart_6352439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352465 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_6352465 : Nat := 118140960795 + 6352465 * 2 ^ 59
def prefixEnd_6352465 : Nat := 4983230072969 + 3 ^ 40 * 6352465 * 2
def baseEnd_6352465 : Nat := 3261867885863593685173051

theorem tailTrace_6352465 : CollatzResearch.WordTrace tailWord_6352465 prefixEnd_6352465 3261867885863593685173051 := by
  unfold tailWord_6352465
  simp only [CollatzResearch.WordTrace]
  refine ⟨231693432931111694492642849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154462288620741129661761899 231693432931111694492642849)
  ·
    refine ⟨173770074698333770869482137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231693432931111694492642849 173770074698333770869482137)
    ·
      refine ⟨130327556023750328152111603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173770074698333770869482137 130327556023750328152111603)
      ·
        refine ⟨195491334035625492228167405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130327556023750328152111603 195491334035625492228167405)
        ·
          refine ⟨73309250263359559585562777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195491334035625492228167405 73309250263359559585562777)
          ·
            refine ⟨54981937697519669689172083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73309250263359559585562777 54981937697519669689172083)
            ·
              refine ⟨82472906546279504533758125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54981937697519669689172083 82472906546279504533758125)
              ·
                refine ⟨30927339954854814200159297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82472906546279504533758125 30927339954854814200159297)
                ·
                  refine ⟨23195504966141110650119473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30927339954854814200159297 23195504966141110650119473)
                  ·
                    refine ⟨17396628724605832987589605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23195504966141110650119473 17396628724605832987589605)
                    ·
                      refine ⟨3261867885863593685173051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17396628724605832987589605 3261867885863593685173051)
                      ·
                        rfl

theorem cell23_6352465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_6352465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352465 prefixEnd_6352465 := by exact prefixLift 6352465
  have htrace : WordTrace (prefixWord ++ tailWord_6352465) baseStart_6352465 baseEnd_6352465 := by
    simpa [prefixWord, tailWord_6352465, baseEnd_6352465] using wordTrace_append hprefix tailTrace_6352465
  have hstable : (prefixWord ++ tailWord_6352465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352465).length < 2 ^ (prefixWord ++ tailWord_6352465).sum := by decide
  have hdescent : baseEnd_6352465 < baseStart_6352465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352512 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2]
def baseStart_6352512 : Nat := 118140960795 + 6352512 * 2 ^ 59
def prefixEnd_6352512 : Nat := 4983230072969 + 3 ^ 40 * 6352512 * 2
def baseEnd_6352512 : Nat := 3261892019454355001285335

theorem tailTrace_6352512 : CollatzResearch.WordTrace tailWord_6352512 prefixEnd_6352512 3261892019454355001285335 := by
  unfold tailWord_6352512
  simp only [CollatzResearch.WordTrace]
  refine ⟨115847573580970710759801895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154463431441294281013069193 115847573580970710759801895)
  ·
    refine ⟨173771360371456066139702843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115847573580970710759801895 173771360371456066139702843)
    ·
      refine ⟨260657040557184099209554265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173771360371456066139702843 260657040557184099209554265)
      ·
        refine ⟨195492780417888074407165699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260657040557184099209554265 195492780417888074407165699)
        ·
          refine ⟨293239170626832111610748549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195492780417888074407165699 293239170626832111610748549)
          ·
            refine ⟨54982344492531020927015353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293239170626832111610748549 54982344492531020927015353)
            ·
              refine ⟨41236758369398265695261515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54982344492531020927015353 41236758369398265695261515)
              ·
                refine ⟨61855137554097398542892273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41236758369398265695261515 61855137554097398542892273)
                ·
                  refine ⟨46391353165573048907169205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61855137554097398542892273 46391353165573048907169205)
                  ·
                    refine ⟨4349189359272473335047113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46391353165573048907169205 4349189359272473335047113)
                    ·
                      refine ⟨3261892019454355001285335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349189359272473335047113 3261892019454355001285335)
                      ·
                        rfl

theorem cell23_6352512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 2, 5, 2].length) (baseStart_6352512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352512 prefixEnd_6352512 := by exact prefixLift 6352512
  have htrace : WordTrace (prefixWord ++ tailWord_6352512) baseStart_6352512 baseEnd_6352512 := by
    simpa [prefixWord, tailWord_6352512, baseEnd_6352512] using wordTrace_append hprefix tailTrace_6352512
  have hstable : (prefixWord ++ tailWord_6352512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352512).length < 2 ^ (prefixWord ++ tailWord_6352512).sum := by decide
  have hdescent : baseEnd_6352512 < baseStart_6352512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352596 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6352596 : Nat := 118140960795 + 6352596 * 2 ^ 59
def prefixEnd_6352596 : Nat := 4983230072969 + 3 ^ 40 * 6352596 * 2
def baseEnd_6352596 : Nat := 3261935151829332672634949

theorem tailTrace_6352596 : CollatzResearch.WordTrace tailWord_6352596 prefixEnd_6352596 3261935151829332672634949 := by
  unfold tailWord_6352596
  simp only [CollatzResearch.WordTrace]
  refine ⟨115849105446818551932830821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154465473929091402577107761 115849105446818551932830821)
  ·
    refine ⟨21721707271278478487405779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115849105446818551932830821 21721707271278478487405779)
    ·
      refine ⟨32582560906917717731108669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21721707271278478487405779 32582560906917717731108669)
      ·
        refine ⟨12218460340094144149165751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32582560906917717731108669 12218460340094144149165751)
        ·
          refine ⟨18327690510141216223748627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218460340094144149165751 18327690510141216223748627)
          ·
            refine ⟨27491535765211824335622941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18327690510141216223748627 27491535765211824335622941)
            ·
              refine ⟨10309325911954434125858603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27491535765211824335622941 10309325911954434125858603)
              ·
                refine ⟨15463988867931651188787905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309325911954434125858603 15463988867931651188787905)
                ·
                  refine ⟨11597991650948738391590929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15463988867931651188787905 11597991650948738391590929)
                  ·
                    refine ⟨8698493738211553793693197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11597991650948738391590929 8698493738211553793693197)
                    ·
                      refine ⟨3261935151829332672634949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698493738211553793693197 3261935151829332672634949)
                      ·
                        rfl

theorem cell23_6352596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6352596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352596 prefixEnd_6352596 := by exact prefixLift 6352596
  have htrace : WordTrace (prefixWord ++ tailWord_6352596) baseStart_6352596 baseEnd_6352596 := by
    simpa [prefixWord, tailWord_6352596, baseEnd_6352596] using wordTrace_append hprefix tailTrace_6352596
  have hstable : (prefixWord ++ tailWord_6352596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352596).length < 2 ^ (prefixWord ++ tailWord_6352596).sum := by decide
  have hdescent : baseEnd_6352596 < baseStart_6352596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352619 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 2, 3, 2]
def baseStart_6352619 : Nat := 118140960795 + 6352619 * 2 ^ 59
def prefixEnd_6352619 : Nat := 4983230072969 + 3 ^ 40 * 6352619 * 2
def baseEnd_6352619 : Nat := 3261946961884386082647343

theorem tailTrace_6352619 : CollatzResearch.WordTrace tailWord_6352619 prefixEnd_6352619 3261946961884386082647343 := by
  unfold tailWord_6352619
  simp only [CollatzResearch.WordTrace]
  refine ⟨231699049772553778793748911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154466033181702519195832607 231699049772553778793748911)
  ·
    refine ⟨347548574658830668190623367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231699049772553778793748911 347548574658830668190623367)
    ·
      refine ⟨521322861988246002285935051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347548574658830668190623367 521322861988246002285935051)
      ·
        refine ⟨781984292982369003428902577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521322861988246002285935051 781984292982369003428902577)
        ·
          refine ⟨586488219736776752571676933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 781984292982369003428902577 586488219736776752571676933)
          ·
            refine ⟨109966541200645641107189425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586488219736776752571676933 109966541200645641107189425)
            ·
              refine ⟨82474905900484230830392069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109966541200645641107189425 82474905900484230830392069)
              ·
                refine ⟨15464044856340793280698513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82474905900484230830392069 15464044856340793280698513)
                ·
                  refine ⟨11598033642255594960523885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464044856340793280698513 11598033642255594960523885)
                  ·
                    refine ⟨4349262615845848110196457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11598033642255594960523885 4349262615845848110196457)
                    ·
                      refine ⟨3261946961884386082647343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349262615845848110196457 3261946961884386082647343)
                      ·
                        rfl

theorem cell23_6352619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 3, 2].length) (baseStart_6352619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352619 prefixEnd_6352619 := by exact prefixLift 6352619
  have htrace : WordTrace (prefixWord ++ tailWord_6352619) baseStart_6352619 baseEnd_6352619 := by
    simpa [prefixWord, tailWord_6352619, baseEnd_6352619] using wordTrace_append hprefix tailTrace_6352619
  have hstable : (prefixWord ++ tailWord_6352619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352619).length < 2 ^ (prefixWord ++ tailWord_6352619).sum := by decide
  have hdescent : baseEnd_6352619 < baseStart_6352619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352626 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6352626 : Nat := 118140960795 + 6352626 * 2 ^ 59
def prefixEnd_6352626 : Nat := 4983230072969 + 3 ^ 40 * 6352626 * 2
def baseEnd_6352626 : Nat := 3261950556248967555259811

theorem tailTrace_6352626 : CollatzResearch.WordTrace tailWord_6352626 prefixEnd_6352626 3261950556248967555259811 := by
  unfold tailWord_6352626
  simp only [CollatzResearch.WordTrace]
  refine ⟨57924826270882104747313433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154466203389018945992835821 57924826270882104747313433)
  ·
    refine ⟨43443619703161578560485075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57924826270882104747313433 43443619703161578560485075)
    ·
      refine ⟨65165429554742367840727613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43443619703161578560485075 65165429554742367840727613)
      ·
        refine ⟨24437036083028387940272855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65165429554742367840727613 24437036083028387940272855)
        ·
          refine ⟨36655554124542581910409283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24437036083028387940272855 36655554124542581910409283)
          ·
            refine ⟨54983331186813872865613925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36655554124542581910409283 54983331186813872865613925)
            ·
              refine ⟨10309374597527601162302611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54983331186813872865613925 10309374597527601162302611)
              ·
                refine ⟨15464061896291401743453917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309374597527601162302611 15464061896291401743453917)
                ·
                  refine ⟨5799023211109275653795219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15464061896291401743453917 5799023211109275653795219)
                  ·
                    refine ⟨8698534816663913480692829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799023211109275653795219 8698534816663913480692829)
                    ·
                      refine ⟨3261950556248967555259811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698534816663913480692829 3261950556248967555259811)
                      ·
                        rfl

theorem cell23_6352626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6352626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352626 prefixEnd_6352626 := by exact prefixLift 6352626
  have htrace : WordTrace (prefixWord ++ tailWord_6352626) baseStart_6352626 baseEnd_6352626 := by
    simpa [prefixWord, tailWord_6352626, baseEnd_6352626] using wordTrace_append hprefix tailTrace_6352626
  have hstable : (prefixWord ++ tailWord_6352626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352626).length < 2 ^ (prefixWord ++ tailWord_6352626).sum := by decide
  have hdescent : baseEnd_6352626 < baseStart_6352626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352632 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_6352632 : Nat := 118140960795 + 6352632 * 2 ^ 59
def prefixEnd_6352632 : Nat := 4983230072969 + 3 ^ 40 * 6352632 * 2
def baseEnd_6352632 : Nat := 3261953637132894531784783

theorem tailTrace_6352632 : CollatzResearch.WordTrace tailWord_6352632 prefixEnd_6352632 3261953637132894531784783 := by
  unfold tailWord_6352632
  simp only [CollatzResearch.WordTrace]
  refine ⟨115849761960753341006986075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154466349281004454675981433 115849761960753341006986075)
  ·
    refine ⟨173774642941130011510479113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115849761960753341006986075 173774642941130011510479113)
    ·
      refine ⟨130330982205847508632859335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173774642941130011510479113 130330982205847508632859335)
      ·
        refine ⟨195496473308771262949289003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130330982205847508632859335 195496473308771262949289003)
        ·
          refine ⟨293244709963156894423933505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195496473308771262949289003 293244709963156894423933505)
          ·
            refine ⟨219933532472367670817950129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293244709963156894423933505 219933532472367670817950129)
            ·
              refine ⟨164950149354275753113462597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219933532472367670817950129 164950149354275753113462597)
              ·
                refine ⟨30928153003926703708774237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164950149354275753113462597 30928153003926703708774237)
                ·
                  refine ⟨11598057376472513890790339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30928153003926703708774237 11598057376472513890790339)
                  ·
                    refine ⟨17397086064708770836185509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11598057376472513890790339 17397086064708770836185509)
                    ·
                      refine ⟨3261953637132894531784783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17397086064708770836185509 3261953637132894531784783)
                      ·
                        rfl

theorem cell23_6352632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_6352632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352632 prefixEnd_6352632 := by exact prefixLift 6352632
  have htrace : WordTrace (prefixWord ++ tailWord_6352632) baseStart_6352632 baseEnd_6352632 := by
    simpa [prefixWord, tailWord_6352632, baseEnd_6352632] using wordTrace_append hprefix tailTrace_6352632
  have hstable : (prefixWord ++ tailWord_6352632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352632).length < 2 ^ (prefixWord ++ tailWord_6352632).sum := by decide
  have hdescent : baseEnd_6352632 < baseStart_6352632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352703 : List Nat := [1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_6352703 : Nat := 118140960795 + 6352703 * 2 ^ 59
def prefixEnd_6352703 : Nat := 4983230072969 + 3 ^ 40 * 6352703 * 2
def baseEnd_6352703 : Nat := 3261990094259363753996957

theorem tailTrace_6352703 : CollatzResearch.WordTrace tailWord_6352703 prefixEnd_6352703 3261990094259363753996957 := by
  unfold tailWord_6352703
  simp only [CollatzResearch.WordTrace]
  refine ⟨231702113504249461139806763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154468075669499640759871175 231702113504249461139806763)
  ·
    refine ⟨347553170256374191709710145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231702113504249461139806763 347553170256374191709710145)
    ·
      refine ⟨260664877692280643782282609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347553170256374191709710145 260664877692280643782282609)
      ·
        refine ⟨195498658269210482836711957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260664877692280643782282609 195498658269210482836711957)
        ·
          refine ⟨9163999606369241382970873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 195498658269210482836711957 9163999606369241382970873)
          ·
            refine ⟨6872999704776931037228155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9163999606369241382970873 6872999704776931037228155)
            ·
              refine ⟨10309499557165396555842233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6872999704776931037228155 10309499557165396555842233)
              ·
                refine ⟨7732124667874047416881675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10309499557165396555842233 7732124667874047416881675)
                ·
                  refine ⟨11598187001811071125322513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732124667874047416881675 11598187001811071125322513)
                  ·
                    refine ⟨8698640251358303343991885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11598187001811071125322513 8698640251358303343991885)
                    ·
                      refine ⟨3261990094259363753996957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698640251358303343991885 3261990094259363753996957)
                      ·
                        rfl

theorem cell23_6352703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_6352703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352703 prefixEnd_6352703 := by exact prefixLift 6352703
  have htrace : WordTrace (prefixWord ++ tailWord_6352703) baseStart_6352703 baseEnd_6352703 := by
    simpa [prefixWord, tailWord_6352703, baseEnd_6352703] using wordTrace_append hprefix tailTrace_6352703
  have hstable : (prefixWord ++ tailWord_6352703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352703).length < 2 ^ (prefixWord ++ tailWord_6352703).sum := by decide
  have hdescent : baseEnd_6352703 < baseStart_6352703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352716 : List Nat := [2, 2, 1, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6352716 : Nat := 118140960795 + 6352716 * 2 ^ 59
def prefixEnd_6352716 : Nat := 4983230072969 + 3 ^ 40 * 6352716 * 2
def baseEnd_6352716 : Nat := 3261996769507872203134397

theorem tailTrace_6352716 : CollatzResearch.WordTrace tailWord_6352716 prefixEnd_6352716 3261996769507872203134397 := by
  unfold tailWord_6352716
  simp only [CollatzResearch.WordTrace]
  refine ⟨115851293826601182180015001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154468391768801576240020001 115851293826601182180015001)
  ·
    refine ⟨86888470369950886635011251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115851293826601182180015001 86888470369950886635011251)
    ·
      refine ⟨130332705554926329952516877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86888470369950886635011251 130332705554926329952516877)
      ·
        refine ⟨48874764583097373732193829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130332705554926329952516877 48874764583097373732193829)
        ·
          refine ⟨9164018359330757574786343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48874764583097373732193829 9164018359330757574786343)
          ·
            refine ⟨13746027538996136362179515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164018359330757574786343 13746027538996136362179515)
            ·
              refine ⟨20619041308494204543269273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13746027538996136362179515 20619041308494204543269273)
              ·
                refine ⟨15464280981370653407451955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619041308494204543269273 15464280981370653407451955)
                ·
                  refine ⟨23196421472055980111177933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464280981370653407451955 23196421472055980111177933)
                  ·
                    refine ⟨8698658052020992541691725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23196421472055980111177933 8698658052020992541691725)
                    ·
                      refine ⟨3261996769507872203134397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698658052020992541691725 3261996769507872203134397)
                      ·
                        rfl

theorem cell23_6352716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6352716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352716 prefixEnd_6352716 := by exact prefixLift 6352716
  have htrace : WordTrace (prefixWord ++ tailWord_6352716) baseStart_6352716 baseEnd_6352716 := by
    simpa [prefixWord, tailWord_6352716, baseEnd_6352716] using wordTrace_append hprefix tailTrace_6352716
  have hstable : (prefixWord ++ tailWord_6352716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352716).length < 2 ^ (prefixWord ++ tailWord_6352716).sum := by decide
  have hdescent : baseEnd_6352716 < baseStart_6352716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352762 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_6352762 : Nat := 118140960795 + 6352762 * 2 ^ 59
def prefixEnd_6352762 : Nat := 4983230072969 + 3 ^ 40 * 6352762 * 2
def baseEnd_6352762 : Nat := 362446709957553224795465

theorem tailTrace_6352762 : CollatzResearch.WordTrace tailWord_6352762 prefixEnd_6352762 362446709957553224795465 := by
  unfold tailWord_6352762
  simp only [CollatzResearch.WordTrace]
  refine ⟨57926066352758928554051135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154469510274023809477469693 57926066352758928554051135)
  ·
    refine ⟨86889099529138392831076703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57926066352758928554051135 86889099529138392831076703)
    ·
      refine ⟨130333649293707589246615055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86889099529138392831076703 130333649293707589246615055)
      ·
        refine ⟨195500473940561383869922583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130333649293707589246615055 195500473940561383869922583)
        ·
          refine ⟨293250710910842075804883875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195500473940561383869922583 293250710910842075804883875)
          ·
            refine ⟨439876066366263113707325813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293250710910842075804883875 439876066366263113707325813)
            ·
              refine ⟨41238381221837166910061795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439876066366263113707325813 41238381221837166910061795)
              ·
                refine ⟨61857571832755750365092693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41238381221837166910061795 61857571832755750365092693)
                ·
                  refine ⟨362446709957553224795465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61857571832755750365092693 362446709957553224795465)
                  ·
                    rfl

theorem cell23_6352762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_6352762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352762 prefixEnd_6352762 := by exact prefixLift 6352762
  have htrace : WordTrace (prefixWord ++ tailWord_6352762) baseStart_6352762 baseEnd_6352762 := by
    simpa [prefixWord, tailWord_6352762, baseEnd_6352762] using wordTrace_append hprefix tailTrace_6352762
  have hstable : (prefixWord ++ tailWord_6352762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352762).length < 2 ^ (prefixWord ++ tailWord_6352762).sum := by decide
  have hdescent : baseEnd_6352762 < baseStart_6352762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352786 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6352786 : Nat := 118140960795 + 6352786 * 2 ^ 59
def prefixEnd_6352786 : Nat := 4983230072969 + 3 ^ 40 * 6352786 * 2
def baseEnd_6352786 : Nat := 3262032713153686929259075

theorem tailTrace_6352786 : CollatzResearch.WordTrace tailWord_6352786 prefixEnd_6352786 3262032713153686929259075 := by
  unfold tailWord_6352786
  simp only [CollatzResearch.WordTrace]
  refine ⟨57926285190737191578769553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154470093841965844210052141 57926285190737191578769553)
  ·
    refine ⟨43444713893052893684077165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57926285190737191578769553 43444713893052893684077165)
    ·
      refine ⟨16291767709894835131528937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43444713893052893684077165 16291767709894835131528937)
      ·
        refine ⟨12218825782421126348646703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16291767709894835131528937 12218825782421126348646703)
        ·
          refine ⟨18328238673631689522970055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218825782421126348646703 18328238673631689522970055)
          ·
            refine ⟨27492358010447534284455083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18328238673631689522970055 27492358010447534284455083)
            ·
              refine ⟨41238537015671301426682625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27492358010447534284455083 41238537015671301426682625)
              ·
                refine ⟨30928902761753476070011969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41238537015671301426682625 30928902761753476070011969)
                ·
                  refine ⟨23196677071315107052508977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30928902761753476070011969 23196677071315107052508977)
                  ·
                    refine ⟨17397507803486330289381733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23196677071315107052508977 17397507803486330289381733)
                    ·
                      refine ⟨3262032713153686929259075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17397507803486330289381733 3262032713153686929259075)
                      ·
                        rfl

theorem cell23_6352786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6352786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352786 prefixEnd_6352786 := by exact prefixLift 6352786
  have htrace : WordTrace (prefixWord ++ tailWord_6352786) baseStart_6352786 baseEnd_6352786 := by
    simpa [prefixWord, tailWord_6352786, baseEnd_6352786] using wordTrace_append hprefix tailTrace_6352786
  have hstable : (prefixWord ++ tailWord_6352786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352786).length < 2 ^ (prefixWord ++ tailWord_6352786).sum := by decide
  have hdescent : baseEnd_6352786 < baseStart_6352786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352789 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_6352789 : Nat := 118140960795 + 6352789 * 2 ^ 59
def prefixEnd_6352789 : Nat := 4983230072969 + 3 ^ 40 * 6352789 * 2
def baseEnd_6352789 : Nat := 3262034253595650417521561

theorem tailTrace_6352789 : CollatzResearch.WordTrace tailWord_6352789 prefixEnd_6352789 3262034253595650417521561 := by
  unfold tailWord_6352789
  simp only [CollatzResearch.WordTrace]
  refine ⟨231705250181937897827437421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154470166787958598551624947 231705250181937897827437421)
  ·
    refine ⟨86889468818226711685289033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231705250181937897827437421 86889468818226711685289033)
    ·
      refine ⟨65167101613670033763966775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86889468818226711685289033 65167101613670033763966775)
      ·
        refine ⟨97750652420505050645950163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65167101613670033763966775 97750652420505050645950163)
        ·
          refine ⟨146625978630757575968925245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97750652420505050645950163 146625978630757575968925245)
          ·
            refine ⟨54984741986534090988346967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146625978630757575968925245 54984741986534090988346967)
            ·
              refine ⟨82477112979801136482520451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54984741986534090988346967 82477112979801136482520451)
              ·
                refine ⟨123715669469701704723780677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82477112979801136482520451 123715669469701704723780677)
                ·
                  refine ⟨23196688025569069635708877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123715669469701704723780677 23196688025569069635708877)
                  ·
                    refine ⟨8698758009588401113390829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23196688025569069635708877 8698758009588401113390829)
                    ·
                      refine ⟨3262034253595650417521561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698758009588401113390829 3262034253595650417521561)
                      ·
                        rfl

theorem cell23_6352789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_6352789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352789 prefixEnd_6352789 := by exact prefixLift 6352789
  have htrace : WordTrace (prefixWord ++ tailWord_6352789) baseStart_6352789 baseEnd_6352789 := by
    simpa [prefixWord, tailWord_6352789, baseEnd_6352789] using wordTrace_append hprefix tailTrace_6352789
  have hstable : (prefixWord ++ tailWord_6352789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352789).length < 2 ^ (prefixWord ++ tailWord_6352789).sum := by decide
  have hdescent : baseEnd_6352789 < baseStart_6352789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352796 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 7]
def baseStart_6352796 : Nat := 118140960795 + 6352796 * 2 ^ 59
def prefixEnd_6352796 : Nat := 4983230072969 + 3 ^ 40 * 6352796 * 2
def baseEnd_6352796 : Nat := 362448649773359098903781

theorem tailTrace_6352796 : CollatzResearch.WordTrace tailWord_6352796 prefixEnd_6352796 362448649773359098903781 := by
  unfold tailWord_6352796
  simp only [CollatzResearch.WordTrace]
  refine ⟨115852752746456269011471121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154470336995275025348628161 115852752746456269011471121)
  ·
    refine ⟨86889564559842201758603341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115852752746456269011471121 86889564559842201758603341)
    ·
      refine ⟨32583586709940825659476253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86889564559842201758603341 32583586709940825659476253)
      ·
        refine ⟨12218845016227809622303595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32583586709940825659476253 12218845016227809622303595)
        ·
          refine ⟨18328267524341714433455393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218845016227809622303595 18328267524341714433455393)
          ·
            refine ⟨13746200643256285825091545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18328267524341714433455393 13746200643256285825091545)
            ·
              refine ⟨10309650482442214368818659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13746200643256285825091545 10309650482442214368818659)
              ·
                refine ⟨15464475723663321553227989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10309650482442214368818659 15464475723663321553227989)
                ·
                  refine ⟨362448649773359098903781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15464475723663321553227989 362448649773359098903781)
                  ·
                    rfl

theorem cell23_6352796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_6352796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352796 prefixEnd_6352796 := by exact prefixLift 6352796
  have htrace : WordTrace (prefixWord ++ tailWord_6352796) baseStart_6352796 baseEnd_6352796 := by
    simpa [prefixWord, tailWord_6352796, baseEnd_6352796] using wordTrace_append hprefix tailTrace_6352796
  have hstable : (prefixWord ++ tailWord_6352796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352796).length < 2 ^ (prefixWord ++ tailWord_6352796).sum := by decide
  have hdescent : baseEnd_6352796 < baseStart_6352796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352807 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6352807 : Nat := 118140960795 + 6352807 * 2 ^ 59
def prefixEnd_6352807 : Nat := 4983230072969 + 3 ^ 40 * 6352807 * 2
def baseEnd_6352807 : Nat := 3262043496247431347096479

theorem tailTrace_6352807 : CollatzResearch.WordTrace tailWord_6352807 prefixEnd_6352807 3262043496247431347096479 := by
  unfold tailWord_6352807
  simp only [CollatzResearch.WordTrace]
  refine ⟨231705906695872686901592675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154470604463915124601061783 231705906695872686901592675)
  ·
    refine ⟨347558860043809030352389013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231705906695872686901592675 347558860043809030352389013)
    ·
      refine ⟨16291821564553548297768235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 347558860043809030352389013 16291821564553548297768235)
      ·
        refine ⟨24437732346830322446652353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16291821564553548297768235 24437732346830322446652353)
        ·
          refine ⟨18328299260122741834989265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24437732346830322446652353 18328299260122741834989265)
          ·
            refine ⟨13746224445092056376241949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18328299260122741834989265 13746224445092056376241949)
            ·
              refine ⟨5154834166909521141090731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13746224445092056376241949 5154834166909521141090731)
              ·
                refine ⟨7732251250364281711636097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154834166909521141090731 7732251250364281711636097)
                ·
                  refine ⟨5799188437773211283727073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7732251250364281711636097 5799188437773211283727073)
                  ·
                    refine ⟨4349391328329908462795305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799188437773211283727073 4349391328329908462795305)
                    ·
                      refine ⟨3262043496247431347096479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349391328329908462795305 3262043496247431347096479)
                      ·
                        rfl

theorem cell23_6352807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6352807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352807 prefixEnd_6352807 := by exact prefixLift 6352807
  have htrace : WordTrace (prefixWord ++ tailWord_6352807) baseStart_6352807 baseEnd_6352807 := by
    simpa [prefixWord, tailWord_6352807, baseEnd_6352807] using wordTrace_append hprefix tailTrace_6352807
  have hstable : (prefixWord ++ tailWord_6352807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352807).length < 2 ^ (prefixWord ++ tailWord_6352807).sum := by decide
  have hdescent : baseEnd_6352807 < baseStart_6352807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352846 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6352846 : Nat := 118140960795 + 6352846 * 2 ^ 59
def prefixEnd_6352846 : Nat := 4983230072969 + 3 ^ 40 * 6352846 * 2
def baseEnd_6352846 : Nat := 3262063521992956694508799

theorem tailTrace_6352846 : CollatzResearch.WordTrace tailWord_6352846 prefixEnd_6352846 3262063521992956694508799 := by
  unfold tailWord_6352846
  simp only [CollatzResearch.WordTrace]
  refine ⟨28963416142841424570282799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154471552761820931041508261 28963416142841424570282799)
  ·
    refine ⟨43445124214262136855424199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28963416142841424570282799 43445124214262136855424199)
    ·
      refine ⟨65167686321393205283136299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43445124214262136855424199 65167686321393205283136299)
      ·
        refine ⟨97751529482089807924704449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65167686321393205283136299 97751529482089807924704449)
        ·
          refine ⟨73313647111567355943528337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97751529482089807924704449 73313647111567355943528337)
          ·
            refine ⟨54985235333675516957646253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73313647111567355943528337 54985235333675516957646253)
            ·
              refine ⟨20619463250128318859117345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54985235333675516957646253 20619463250128318859117345)
              ·
                refine ⟨15464597437596239144338009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619463250128318859117345 15464597437596239144338009)
                ·
                  refine ⟨11598448078197179358253507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15464597437596239144338009 11598448078197179358253507)
                  ·
                    refine ⟨17397672117295769037380261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11598448078197179358253507 17397672117295769037380261)
                    ·
                      refine ⟨3262063521992956694508799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17397672117295769037380261 3262063521992956694508799)
                      ·
                        rfl

theorem cell23_6352846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6352846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352846 prefixEnd_6352846 := by exact prefixLift 6352846
  have htrace : WordTrace (prefixWord ++ tailWord_6352846) baseStart_6352846 baseEnd_6352846 := by
    simpa [prefixWord, tailWord_6352846, baseEnd_6352846] using wordTrace_append hprefix tailTrace_6352846
  have hstable : (prefixWord ++ tailWord_6352846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352846).length < 2 ^ (prefixWord ++ tailWord_6352846).sum := by decide
  have hdescent : baseEnd_6352846 < baseStart_6352846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352849 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_6352849 : Nat := 118140960795 + 6352849 * 2 ^ 59
def prefixEnd_6352849 : Nat := 4983230072969 + 3 ^ 40 * 6352849 * 2
def baseEnd_6352849 : Nat := 3262065062434920182771285

theorem tailTrace_6352849 : CollatzResearch.WordTrace tailWord_6352849 prefixEnd_6352849 3262065062434920182771285 := by
  unfold tailWord_6352849
  simp only [CollatzResearch.WordTrace]
  refine ⟨231707438561720528074621601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154471625707813685383081067 231707438561720528074621601)
  ·
    refine ⟨173780578921290396055966201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231707438561720528074621601 173780578921290396055966201)
    ·
      refine ⟨130335434190967797041974651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173780578921290396055966201 130335434190967797041974651)
      ·
        refine ⟨195503151286451695562961977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130335434190967797041974651 195503151286451695562961977)
        ·
          refine ⟨146627363464838771672221483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195503151286451695562961977 146627363464838771672221483)
          ·
            refine ⟨219941045197258157508332225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146627363464838771672221483 219941045197258157508332225)
            ·
              refine ⟨164955783897943618131249169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219941045197258157508332225 164955783897943618131249169)
              ·
                refine ⟨123716837923457713598436877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164955783897943618131249169 123716837923457713598436877)
                ·
                  refine ⟨46393814221296642599413829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123716837923457713598436877 46393814221296642599413829)
                  ·
                    refine ⟨8698840166493120487390093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46393814221296642599413829 8698840166493120487390093)
                    ·
                      refine ⟨3262065062434920182771285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698840166493120487390093 3262065062434920182771285)
                      ·
                        rfl

theorem cell23_6352849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_6352849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352849 prefixEnd_6352849 := by exact prefixLift 6352849
  have htrace : WordTrace (prefixWord ++ tailWord_6352849) baseStart_6352849 baseEnd_6352849 := by
    simpa [prefixWord, tailWord_6352849, baseEnd_6352849] using wordTrace_append hprefix tailTrace_6352849
  have hstable : (prefixWord ++ tailWord_6352849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352849).length < 2 ^ (prefixWord ++ tailWord_6352849).sum := by decide
  have hdescent : baseEnd_6352849 < baseStart_6352849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352896 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3]
def baseStart_6352896 : Nat := 118140960795 + 6352896 * 2 ^ 59
def prefixEnd_6352896 : Nat := 4983230072969 + 3 ^ 40 * 6352896 * 2
def baseEnd_6352896 : Nat := 3262089196025681498883569

theorem tailTrace_6352896 : CollatzResearch.WordTrace tailWord_6352896 prefixEnd_6352896 3262089196025681498883569 := by
  unfold tailWord_6352896
  simp only [CollatzResearch.WordTrace]
  refine ⟨115854576396275127550791271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154472768528366836734388361 115854576396275127550791271)
  ·
    refine ⟨173781864594412691326186907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115854576396275127550791271 173781864594412691326186907)
    ·
      refine ⟨260672796891619036989280361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173781864594412691326186907 260672796891619036989280361)
      ·
        refine ⟨195504597668714277741960271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260672796891619036989280361 195504597668714277741960271)
        ·
          refine ⟨293256896503071416612940407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195504597668714277741960271 293256896503071416612940407)
          ·
            refine ⟨439885344754607124919410611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293256896503071416612940407 439885344754607124919410611)
            ·
              refine ⟨659828017131910687379115917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439885344754607124919410611 659828017131910687379115917)
              ·
                refine ⟨247435506424466507767168469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 659828017131910687379115917 247435506424466507767168469)
                ·
                  refine ⟨5799269681823433775793011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 247435506424466507767168469 5799269681823433775793011)
                  ·
                    refine ⟨8698904522735150663689517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799269681823433775793011 8698904522735150663689517)
                    ·
                      refine ⟨3262089196025681498883569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8698904522735150663689517 3262089196025681498883569)
                      ·
                        rfl

theorem cell23_6352896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 7, 1, 3].length) (baseStart_6352896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352896 prefixEnd_6352896 := by exact prefixLift 6352896
  have htrace : WordTrace (prefixWord ++ tailWord_6352896) baseStart_6352896 baseEnd_6352896 := by
    simpa [prefixWord, tailWord_6352896, baseEnd_6352896] using wordTrace_append hprefix tailTrace_6352896
  have hstable : (prefixWord ++ tailWord_6352896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352896).length < 2 ^ (prefixWord ++ tailWord_6352896).sum := by decide
  have hdescent : baseEnd_6352896 < baseStart_6352896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352939 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5]
def baseStart_6352939 : Nat := 118140960795 + 6352939 * 2 ^ 59
def prefixEnd_6352939 : Nat := 4983230072969 + 3 ^ 40 * 6352939 * 2
def baseEnd_6352939 : Nat := 3262111275693824830645871

theorem tailTrace_6352939 : CollatzResearch.WordTrace tailWord_6352939 prefixEnd_6352939 3262111275693824830645871 := by
  unfold tailWord_6352939
  simp only [CollatzResearch.WordTrace]
  refine ⟨231710721131394473445397871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154473814087596315630265247 231710721131394473445397871)
  ·
    refine ⟨347566081697091710168096807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231710721131394473445397871 347566081697091710168096807)
    ·
      refine ⟨521349122545637565252145211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347566081697091710168096807 521349122545637565252145211)
      ·
        refine ⟨782023683818456347878217817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521349122545637565252145211 782023683818456347878217817)
        ·
          refine ⟨586517762863842260908663363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782023683818456347878217817 586517762863842260908663363)
          ·
            refine ⟨879776644295763391362995045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586517762863842260908663363 879776644295763391362995045)
            ·
              refine ⟨164958120805455635880561571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 879776644295763391362995045 164958120805455635880561571)
              ·
                refine ⟨247437181208183453820842357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164958120805455635880561571 247437181208183453820842357)
                ·
                  refine ⟨23197235738267198795703971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 247437181208183453820842357 23197235738267198795703971)
                  ·
                    refine ⟨34795853607400798193555957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23197235738267198795703971 34795853607400798193555957)
                    ·
                      refine ⟨3262111275693824830645871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34795853607400798193555957 3262111275693824830645871)
                      ·
                        rfl

theorem cell23_6352939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 5].length) (baseStart_6352939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352939 prefixEnd_6352939 := by exact prefixLift 6352939
  have htrace : WordTrace (prefixWord ++ tailWord_6352939) baseStart_6352939 baseEnd_6352939 := by
    simpa [prefixWord, tailWord_6352939, baseEnd_6352939] using wordTrace_append hprefix tailTrace_6352939
  have hstable : (prefixWord ++ tailWord_6352939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352939).length < 2 ^ (prefixWord ++ tailWord_6352939).sum := by decide
  have hdescent : baseEnd_6352939 < baseStart_6352939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352946 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_6352946 : Nat := 118140960795 + 6352946 * 2 ^ 59
def prefixEnd_6352946 : Nat := 4983230072969 + 3 ^ 40 * 6352946 * 2
def baseEnd_6352946 : Nat := 1087371623352802101086113

theorem tailTrace_6352946 : CollatzResearch.WordTrace tailWord_6352946 prefixEnd_6352946 1087371623352802101086113 := by
  unfold tailWord_6352946
  simp only [CollatzResearch.WordTrace]
  refine ⟨57927744110592278410225673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154473984294912742427268461 57927744110592278410225673)
  ·
    refine ⟨43445808082944208807669255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57927744110592278410225673 43445808082944208807669255)
    ·
      refine ⟨65168712124416313211503883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43445808082944208807669255 65168712124416313211503883)
      ·
        refine ⟨97753068186624469817255825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65168712124416313211503883 97753068186624469817255825)
        ·
          refine ⟨73314801139968352362941869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97753068186624469817255825 73314801139968352362941869)
          ·
            refine ⟨27493050427488132136103201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73314801139968352362941869 27493050427488132136103201)
            ·
              refine ⟨20619787820616099102077401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27493050427488132136103201 20619787820616099102077401)
              ·
                refine ⟨15464840865462074326558051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619787820616099102077401 15464840865462074326558051)
                ·
                  refine ⟨23197261298193111489837077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464840865462074326558051 23197261298193111489837077)
                  ·
                    refine ⟨1087371623352802101086113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23197261298193111489837077 1087371623352802101086113)
                    ·
                      rfl

theorem cell23_6352946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_6352946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352946 prefixEnd_6352946 := by exact prefixLift 6352946
  have htrace : WordTrace (prefixWord ++ tailWord_6352946) baseStart_6352946 baseEnd_6352946 := by
    simpa [prefixWord, tailWord_6352946, baseEnd_6352946] using wordTrace_append hprefix tailTrace_6352946
  have hstable : (prefixWord ++ tailWord_6352946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352946).length < 2 ^ (prefixWord ++ tailWord_6352946).sum := by decide
  have hdescent : baseEnd_6352946 < baseStart_6352946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352956 : List Nat := [2, 2, 2, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_6352956 : Nat := 118140960795 + 6352956 * 2 ^ 59
def prefixEnd_6352956 : Nat := 4983230072969 + 3 ^ 40 * 6352956 * 2
def baseEnd_6352956 : Nat := 3262120004864951264133293

theorem tailTrace_6352956 : CollatzResearch.WordTrace tailWord_6352956 prefixEnd_6352956 3262120004864951264133293 := by
  unfold tailWord_6352956
  simp only [CollatzResearch.WordTrace]
  refine ⟨115855670586166442674383361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154474227448221923565844481 115855670586166442674383361)
  ·
    refine ⟨86891752939624832005787521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115855670586166442674383361 86891752939624832005787521)
    ·
      refine ⟨65168814704718624004340641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86891752939624832005787521 65168814704718624004340641)
      ·
        refine ⟨48876611028538968003255481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65168814704718624004340641 48876611028538968003255481)
        ·
          refine ⟨36657458271404226002441611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48876611028538968003255481 36657458271404226002441611)
          ·
            refine ⟨54986187407106339003662417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36657458271404226002441611 54986187407106339003662417)
            ·
              refine ⟨41239640555329754252746813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54986187407106339003662417 41239640555329754252746813)
              ·
                refine ⟨15464865208248657844780055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41239640555329754252746813 15464865208248657844780055)
                ·
                  refine ⟨23197297812372986767170083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464865208248657844780055 23197297812372986767170083)
                  ·
                    refine ⟨34795946718559480150755125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23197297812372986767170083 34795946718559480150755125)
                    ·
                      refine ⟨3262120004864951264133293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34795946718559480150755125 3262120004864951264133293)
                      ·
                        rfl

theorem cell23_6352956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_6352956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352956 prefixEnd_6352956 := by exact prefixLift 6352956
  have htrace : WordTrace (prefixWord ++ tailWord_6352956) baseStart_6352956 baseEnd_6352956 := by
    simpa [prefixWord, tailWord_6352956, baseEnd_6352956] using wordTrace_append hprefix tailTrace_6352956
  have hstable : (prefixWord ++ tailWord_6352956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352956).length < 2 ^ (prefixWord ++ tailWord_6352956).sum := by decide
  have hdescent : baseEnd_6352956 < baseStart_6352956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6352973 : List Nat := [1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_6352973 : Nat := 118140960795 + 6352973 * 2 ^ 59
def prefixEnd_6352973 : Nat := 4983230072969 + 3 ^ 40 * 6352973 * 2
def baseEnd_6352973 : Nat := 3262128734036077697620715

theorem tailTrace_6352973 : CollatzResearch.WordTrace tailWord_6352973 prefixEnd_6352973 3262128734036077697620715 := by
  unfold tailWord_6352973
  simp only [CollatzResearch.WordTrace]
  refine ⟨231711961213271297252135573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154474640808847531501423715 231711961213271297252135573)
  ·
    refine ⟨10861498181872092058693855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231711961213271297252135573 10861498181872092058693855)
    ·
      refine ⟨16292247272808138088040783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10861498181872092058693855 16292247272808138088040783)
      ·
        refine ⟨24438370909212207132061175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16292247272808138088040783 24438370909212207132061175)
        ·
          refine ⟨36657556363818310698091763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24438370909212207132061175 36657556363818310698091763)
          ·
            refine ⟨54986334545727466047137645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36657556363818310698091763 54986334545727466047137645)
            ·
              refine ⟨20619875454647799767676617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54986334545727466047137645 20619875454647799767676617)
              ·
                refine ⟨15464906590985849825757463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20619875454647799767676617 15464906590985849825757463)
                ·
                  refine ⟨23197359886478774738636195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15464906590985849825757463 23197359886478774738636195)
                  ·
                    refine ⟨34796039829718162107954293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23197359886478774738636195 34796039829718162107954293)
                    ·
                      refine ⟨3262128734036077697620715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34796039829718162107954293 3262128734036077697620715)
                      ·
                        rfl

theorem cell23_6352973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_6352973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6352973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6352973 prefixEnd_6352973 := by exact prefixLift 6352973
  have htrace : WordTrace (prefixWord ++ tailWord_6352973) baseStart_6352973 baseEnd_6352973 := by
    simpa [prefixWord, tailWord_6352973, baseEnd_6352973] using wordTrace_append hprefix tailTrace_6352973
  have hstable : (prefixWord ++ tailWord_6352973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6352973).length < 2 ^ (prefixWord ++ tailWord_6352973).sum := by decide
  have hdescent : baseEnd_6352973 < baseStart_6352973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6352973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353004 : List Nat := [2, 2, 1, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_6353004 : Nat := 118140960795 + 6353004 * 2 ^ 59
def prefixEnd_6353004 : Nat := 4983230072969 + 3 ^ 40 * 6353004 * 2
def baseEnd_6353004 : Nat := 3262144651936367076333073

theorem tailTrace_6353004 : CollatzResearch.WordTrace tailWord_6353004 prefixEnd_6353004 3262144651936367076333073 := by
  unfold tailWord_6353004
  simp only [CollatzResearch.WordTrace]
  refine ⟨115856545938079494773257033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154475394584105993031009377 115856545938079494773257033)
  ·
    refine ⟨86892409453559621079942775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115856545938079494773257033 86892409453559621079942775)
    ·
      refine ⟨130338614180339431619914163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86892409453559621079942775 130338614180339431619914163)
      ·
        refine ⟨195507921270509147429871245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130338614180339431619914163 195507921270509147429871245)
        ·
          refine ⟨73315470476440930286201717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195507921270509147429871245 73315470476440930286201717)
          ·
            refine ⟨6873325357166337214331411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73315470476440930286201717 6873325357166337214331411)
            ·
              refine ⟨10309988035749505821497117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873325357166337214331411 10309988035749505821497117)
              ·
                refine ⟨3866245513406064683061419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10309988035749505821497117 3866245513406064683061419)
                ·
                  refine ⟨5799368270109097024592129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866245513406064683061419 5799368270109097024592129)
                  ·
                    refine ⟨4349526202581822768444097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799368270109097024592129 4349526202581822768444097)
                    ·
                      refine ⟨3262144651936367076333073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349526202581822768444097 3262144651936367076333073)
                      ·
                        rfl

theorem cell23_6353004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_6353004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353004 prefixEnd_6353004 := by exact prefixLift 6353004
  have htrace : WordTrace (prefixWord ++ tailWord_6353004) baseStart_6353004 baseEnd_6353004 := by
    simpa [prefixWord, tailWord_6353004, baseEnd_6353004] using wordTrace_append hprefix tailTrace_6353004
  have hstable : (prefixWord ++ tailWord_6353004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353004).length < 2 ^ (prefixWord ++ tailWord_6353004).sum := by decide
  have hdescent : baseEnd_6353004 < baseStart_6353004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353043 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 1, 4, 2]
def baseStart_6353043 : Nat := 118140960795 + 6353043 * 2 ^ 59
def prefixEnd_6353043 : Nat := 4983230072969 + 3 ^ 40 * 6353043 * 2
def baseEnd_6353043 : Nat := 3262164677681892423745393

theorem tailTrace_6353043 : CollatzResearch.WordTrace tailWord_6353043 prefixEnd_6353043 3262164677681892423745393 := by
  unfold tailWord_6353043
  simp only [CollatzResearch.WordTrace]
  refine ⟨231714514323017699207183783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154476342882011799471455855 231714514323017699207183783)
  ·
    refine ⟨347571771484526548810775675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231714514323017699207183783 347571771484526548810775675)
    ·
      refine ⟨521357657226789823216163513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347571771484526548810775675 521357657226789823216163513)
      ·
        refine ⟨391018242920092367412122635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521357657226789823216163513 391018242920092367412122635)
        ·
          refine ⟨586527364380138551118183953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391018242920092367412122635 586527364380138551118183953)
          ·
            refine ⟨439895523285103913338637965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586527364380138551118183953 439895523285103913338637965)
            ·
              refine ⟨164960821231913967501989237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 439895523285103913338637965 164960821231913967501989237)
              ·
                refine ⟨15465076990491934453311491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164960821231913967501989237 15465076990491934453311491)
                ·
                  refine ⟨23197615485737901679967237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15465076990491934453311491 23197615485737901679967237)
                  ·
                    refine ⟨4349552903575856564993857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23197615485737901679967237 4349552903575856564993857)
                    ·
                      refine ⟨3262164677681892423745393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349552903575856564993857 3262164677681892423745393)
                      ·
                        rfl

theorem cell23_6353043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 4, 2].length) (baseStart_6353043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353043 prefixEnd_6353043 := by exact prefixLift 6353043
  have htrace : WordTrace (prefixWord ++ tailWord_6353043) baseStart_6353043 baseEnd_6353043 := by
    simpa [prefixWord, tailWord_6353043, baseEnd_6353043] using wordTrace_append hprefix tailTrace_6353043
  have hstable : (prefixWord ++ tailWord_6353043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353043).length < 2 ^ (prefixWord ++ tailWord_6353043).sum := by decide
  have hdescent : baseEnd_6353043 < baseStart_6353043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353083 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 5]
def baseStart_6353083 : Nat := 118140960795 + 6353083 * 2 ^ 59
def prefixEnd_6353083 : Nat := 4983230072969 + 3 ^ 40 * 6353083 * 2
def baseEnd_6353083 : Nat := 362465024100896918582801

theorem tailTrace_6353083 : CollatzResearch.WordTrace tailWord_6353083 prefixEnd_6353083 362465024100896918582801 := by
  unfold tailWord_6353083
  simp only [CollatzResearch.WordTrace]
  refine ⟨231715973242872786038639903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154477315495248524025759935 231715973242872786038639903)
  ·
    refine ⟨347573959864309179057959855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231715973242872786038639903 347573959864309179057959855)
    ·
      refine ⟨521360939796463768586939783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347573959864309179057959855 521360939796463768586939783)
      ·
        refine ⟨782041409694695652880409675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521360939796463768586939783 782041409694695652880409675)
        ·
          refine ⟨1173062114542043479320614513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782041409694695652880409675 1173062114542043479320614513)
          ·
            refine ⟨879796585906532609490460885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173062114542043479320614513 879796585906532609490460885)
            ·
              refine ⟨20620232482184358034932677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 879796585906532609490460885 20620232482184358034932677)
              ·
                refine ⟨3866293590409567131549877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20620232482184358034932677 3866293590409567131549877)
                ·
                  refine ⟨362465024100896918582801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866293590409567131549877 362465024100896918582801)
                  ·
                    rfl

theorem cell23_6353083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 5].length) (baseStart_6353083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353083 prefixEnd_6353083 := by exact prefixLift 6353083
  have htrace : WordTrace (prefixWord ++ tailWord_6353083) baseStart_6353083 baseEnd_6353083 := by
    simpa [prefixWord, tailWord_6353083, baseEnd_6353083] using wordTrace_append hprefix tailTrace_6353083
  have hstable : (prefixWord ++ tailWord_6353083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353083).length < 2 ^ (prefixWord ++ tailWord_6353083).sum := by decide
  have hdescent : baseEnd_6353083 < baseStart_6353083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353096 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6353096 : Nat := 118140960795 + 6353096 * 2 ^ 59
def prefixEnd_6353096 : Nat := 4983230072969 + 3 ^ 40 * 6353096 * 2
def baseEnd_6353096 : Nat := 1087397297385526905460883

theorem tailTrace_6353096 : CollatzResearch.WordTrace tailWord_6353096 prefixEnd_6353096 1087397297385526905460883 := by
  unfold tailWord_6353096
  simp only [CollatzResearch.WordTrace]
  refine ⟨115858223695912844629431571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154477631594550459505908761 115858223695912844629431571)
  ·
    refine ⟨173787335543869266944147357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115858223695912844629431571 173787335543869266944147357)
    ·
      refine ⟨65170250828950975104055259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173787335543869266944147357 65170250828950975104055259)
      ·
        refine ⟨97755376243426462656082889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65170250828950975104055259 97755376243426462656082889)
        ·
          refine ⟨73316532182569846992062167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97755376243426462656082889 73316532182569846992062167)
          ·
            refine ⟨109974798273854770488093251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73316532182569846992062167 109974798273854770488093251)
            ·
              refine ⟨164962197410782155732139877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109974798273854770488093251 164962197410782155732139877)
              ·
                refine ⟨30930412014521654199776227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164962197410782155732139877 30930412014521654199776227)
                ·
                  refine ⟨46395618021782481299664341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30930412014521654199776227 46395618021782481299664341)
                  ·
                    refine ⟨1087397297385526905460883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46395618021782481299664341 1087397297385526905460883)
                    ·
                      rfl

theorem cell23_6353096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6353096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353096 prefixEnd_6353096 := by exact prefixLift 6353096
  have htrace : WordTrace (prefixWord ++ tailWord_6353096) baseStart_6353096 baseEnd_6353096 := by
    simpa [prefixWord, tailWord_6353096, baseEnd_6353096] using wordTrace_append hprefix tailTrace_6353096
  have hstable : (prefixWord ++ tailWord_6353096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353096).length < 2 ^ (prefixWord ++ tailWord_6353096).sum := by decide
  have hdescent : baseEnd_6353096 < baseStart_6353096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353100 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 7]
def baseStart_6353100 : Nat := 118140960795 + 6353100 * 2 ^ 59
def prefixEnd_6353100 : Nat := 4983230072969 + 3 ^ 40 * 6353100 * 2
def baseEnd_6353100 : Nat := 362465994008799855636959

theorem tailTrace_6353100 : CollatzResearch.WordTrace tailWord_6353100 prefixEnd_6353100 362465994008799855636959 := by
  unfold tailWord_6353100
  simp only [CollatzResearch.WordTrace]
  refine ⟨115858296641905598971004377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154477728855874131961339169 115858296641905598971004377)
  ·
    refine ⟨86893722481429199228253283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115858296641905598971004377 86893722481429199228253283)
    ·
      refine ⟨130340583722143798842379925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86893722481429199228253283 130340583722143798842379925)
      ·
        refine ⟨6109714861975490570736559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130340583722143798842379925 6109714861975490570736559)
        ·
          refine ⟨9164572292963235856104839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6109714861975490570736559 9164572292963235856104839)
          ·
            refine ⟨13746858439444853784157259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164572292963235856104839 13746858439444853784157259)
            ·
              refine ⟨20620287659167280676235889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13746858439444853784157259 20620287659167280676235889)
              ·
                refine ⟨15465215744375460507176917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20620287659167280676235889 15465215744375460507176917)
                ·
                  refine ⟨362465994008799855636959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15465215744375460507176917 362465994008799855636959)
                  ·
                    rfl

theorem cell23_6353100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_6353100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353100 prefixEnd_6353100 := by exact prefixLift 6353100
  have htrace : WordTrace (prefixWord ++ tailWord_6353100) baseStart_6353100 baseEnd_6353100 := by
    simpa [prefixWord, tailWord_6353100, baseEnd_6353100] using wordTrace_append hprefix tailTrace_6353100
  have hstable : (prefixWord ++ tailWord_6353100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353100).length < 2 ^ (prefixWord ++ tailWord_6353100).sum := by decide
  have hdescent : baseEnd_6353100 < baseStart_6353100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353103 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 2, 5, 2]
def baseStart_6353103 : Nat := 118140960795 + 6353103 * 2 ^ 59
def prefixEnd_6353103 : Nat := 4983230072969 + 3 ^ 40 * 6353103 * 2
def baseEnd_6353103 : Nat := 3262195486521162188995117

theorem tailTrace_6353103 : CollatzResearch.WordTrace tailWord_6353103 prefixEnd_6353103 3262195486521162188995117 := by
  unfold tailWord_6353103
  simp only [CollatzResearch.WordTrace]
  refine ⟨231716702702800329454367963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154477801801866886302911975 231716702702800329454367963)
  ·
    refine ⟨347575054054200494181551945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231716702702800329454367963 347575054054200494181551945)
    ·
      refine ⟨260681290540650370636163959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347575054054200494181551945 260681290540650370636163959)
      ·
        refine ⟨391021935810975555954245939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260681290540650370636163959 391021935810975555954245939)
        ·
          refine ⟨586532903716463333931368909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391021935810975555954245939 586532903716463333931368909)
          ·
            refine ⟨219949838893673750224263341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586532903716463333931368909 219949838893673750224263341)
            ·
              refine ⟨82481189585127656334098753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219949838893673750224263341 82481189585127656334098753)
              ·
                refine ⟨61860892188845742250574065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82481189585127656334098753 61860892188845742250574065)
                ·
                  refine ⟨46395669141634306687930549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61860892188845742250574065 46395669141634306687930549)
                  ·
                    refine ⟨4349593982028216251993489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46395669141634306687930549 4349593982028216251993489)
                    ·
                      refine ⟨3262195486521162188995117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349593982028216251993489 3262195486521162188995117)
                      ·
                        rfl

theorem cell23_6353103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 5, 2].length) (baseStart_6353103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353103 prefixEnd_6353103 := by exact prefixLift 6353103
  have htrace : WordTrace (prefixWord ++ tailWord_6353103) baseStart_6353103 baseEnd_6353103 := by
    simpa [prefixWord, tailWord_6353103, baseEnd_6353103] using wordTrace_append hprefix tailTrace_6353103
  have hstable : (prefixWord ++ tailWord_6353103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353103).length < 2 ^ (prefixWord ++ tailWord_6353103).sum := by decide
  have hdescent : baseEnd_6353103 < baseStart_6353103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353113 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 2, 5]
def baseStart_6353113 : Nat := 118140960795 + 6353113 * 2 ^ 59
def prefixEnd_6353113 : Nat := 4983230072969 + 3 ^ 40 * 6353113 * 2
def baseEnd_6353113 : Nat := 1087400207109235716623357

theorem tailTrace_6353113 : CollatzResearch.WordTrace tailWord_6353113 prefixEnd_6353113 1087400207109235716623357 := by
  unfold tailWord_6353113
  simp only [CollatzResearch.WordTrace]
  refine ⟨231717067432764101162231993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154478044955176067441487995 231717067432764101162231993)
  ·
    refine ⟨173787800574573075871673995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231717067432764101162231993 173787800574573075871673995)
    ·
      refine ⟨260681700861859613807510993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173787800574573075871673995 260681700861859613807510993)
      ·
        refine ⟨195511275646394710355633245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260681700861859613807510993 195511275646394710355633245)
        ·
          refine ⟨73316728367398016383362467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195511275646394710355633245 73316728367398016383362467)
          ·
            refine ⟨109975092551097024575043701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73316728367398016383362467 109975092551097024575043701)
            ·
              refine ⟨10310164926665346053910347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109975092551097024575043701 10310164926665346053910347)
              ·
                refine ⟨15465247389998019080865521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10310164926665346053910347 15465247389998019080865521)
                ·
                  refine ⟨11598935542498514310649141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15465247389998019080865521 11598935542498514310649141)
                  ·
                    refine ⟨1087400207109235716623357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11598935542498514310649141 1087400207109235716623357)
                    ·
                      rfl

theorem cell23_6353113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_6353113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353113 prefixEnd_6353113 := by exact prefixLift 6353113
  have htrace : WordTrace (prefixWord ++ tailWord_6353113) baseStart_6353113 baseEnd_6353113 := by
    simpa [prefixWord, tailWord_6353113, baseEnd_6353113] using wordTrace_append hprefix tailTrace_6353113
  have hstable : (prefixWord ++ tailWord_6353113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353113).length < 2 ^ (prefixWord ++ tailWord_6353113).sum := by decide
  have hdescent : baseEnd_6353113 < baseStart_6353113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353117 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 5]
def baseStart_6353117 : Nat := 118140960795 + 6353117 * 2 ^ 59
def prefixEnd_6353117 : Nat := 4983230072969 + 3 ^ 40 * 6353117 * 2
def baseEnd_6353117 : Nat := 362466963916702792691117

theorem tailTrace_6353117 : CollatzResearch.WordTrace tailWord_6353117 prefixEnd_6353117 362466963916702792691117 := by
  unfold tailWord_6353117
  simp only [CollatzResearch.WordTrace]
  refine ⟨231717213324749609845377605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154478142216499739896918403 231717213324749609845377605)
  ·
    refine ⟨43446977498390551846008301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231717213324749609845377605 43446977498390551846008301)
    ·
      refine ⟨16292616561896456942253113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43446977498390551846008301 16292616561896456942253113)
      ·
        refine ⟨12219462421422342706689835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16292616561896456942253113 12219462421422342706689835)
        ·
          refine ⟨18329193632133514060034753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219462421422342706689835 18329193632133514060034753)
          ·
            refine ⟨13746895224100135545026065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18329193632133514060034753 13746895224100135545026065)
            ·
              refine ⟨10310171418075101658769549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13746895224100135545026065 10310171418075101658769549)
              ·
                refine ⟨3866314281778163122038581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10310171418075101658769549 3866314281778163122038581)
                ·
                  refine ⟨362466963916702792691117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866314281778163122038581 362466963916702792691117)
                  ·
                    rfl

theorem cell23_6353117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_6353117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353117 prefixEnd_6353117 := by exact prefixLift 6353117
  have htrace : WordTrace (prefixWord ++ tailWord_6353117) baseStart_6353117 baseEnd_6353117 := by
    simpa [prefixWord, tailWord_6353117, baseEnd_6353117] using wordTrace_append hprefix tailTrace_6353117
  have hstable : (prefixWord ++ tailWord_6353117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353117).length < 2 ^ (prefixWord ++ tailWord_6353117).sum := by decide
  have hdescent : baseEnd_6353117 < baseStart_6353117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353136 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5]
def baseStart_6353136 : Nat := 118140960795 + 6353136 * 2 ^ 59
def prefixEnd_6353136 : Nat := 4983230072969 + 3 ^ 40 * 6353136 * 2
def baseEnd_6353136 : Nat := 3262212431382760559882465

theorem tailTrace_6353136 : CollatzResearch.WordTrace tailWord_6353136 prefixEnd_6353136 3262212431382760559882465 := by
  unfold tailWord_6353136
  simp only [CollatzResearch.WordTrace]
  refine ⟨115858953155840388045159631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154478604207787184060212841 115858953155840388045159631)
  ·
    refine ⟨173788429733760582067739447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115858953155840388045159631 173788429733760582067739447)
    ·
      refine ⟨260682644600640873101609171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173788429733760582067739447 260682644600640873101609171)
      ·
        refine ⟨391023966900961309652413757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260682644600640873101609171 391023966900961309652413757)
        ·
          refine ⟨146633987587860491119655159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391023966900961309652413757 146633987587860491119655159)
          ·
            refine ⟨219950981381790736679482739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146633987587860491119655159 219950981381790736679482739)
            ·
              refine ⟨329926472072686105019224109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219950981381790736679482739 329926472072686105019224109)
              ·
                refine ⟨123722427027257289382209041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329926472072686105019224109 123722427027257289382209041)
                ·
                  refine ⟨92791820270442967036656781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123722427027257289382209041 92791820270442967036656781)
                  ·
                    refine ⟨34796932601416112638746293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92791820270442967036656781 34796932601416112638746293)
                    ·
                      refine ⟨3262212431382760559882465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34796932601416112638746293 3262212431382760559882465)
                      ·
                        rfl

theorem cell23_6353136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_6353136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353136 prefixEnd_6353136 := by exact prefixLift 6353136
  have htrace : WordTrace (prefixWord ++ tailWord_6353136) baseStart_6353136 baseEnd_6353136 := by
    simpa [prefixWord, tailWord_6353136, baseEnd_6353136] using wordTrace_append hprefix tailTrace_6353136
  have hstable : (prefixWord ++ tailWord_6353136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353136).length < 2 ^ (prefixWord ++ tailWord_6353136).sum := by decide
  have hdescent : baseEnd_6353136 < baseStart_6353136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353153 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_6353153 : Nat := 118140960795 + 6353153 * 2 ^ 59
def prefixEnd_6353153 : Nat := 4983230072969 + 3 ^ 40 * 6353153 * 2
def baseEnd_6353153 : Nat := 3262221160553886993369887

theorem tailTrace_6353153 : CollatzResearch.WordTrace tailWord_6353153 prefixEnd_6353153 3262221160553886993369887 := by
  unfold tailWord_6353153
  simp only [CollatzResearch.WordTrace]
  refine ⟨231718526352619187993688113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154479017568412791995792075 231718526352619187993688113)
  ·
    refine ⟨173788894764464390995266085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231718526352619187993688113 173788894764464390995266085)
    ·
      refine ⟨32585417768337073311612391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173788894764464390995266085 32585417768337073311612391)
      ·
        refine ⟨48878126652505609967418587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32585417768337073311612391 48878126652505609967418587)
        ·
          refine ⟨73317189978758414951127881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48878126652505609967418587 73317189978758414951127881)
          ·
            refine ⟨54987892484068811213345911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73317189978758414951127881 54987892484068811213345911)
            ·
              refine ⟨82481838726103216820018867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54987892484068811213345911 82481838726103216820018867)
              ·
                refine ⟨123722758089154825230028301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82481838726103216820018867 123722758089154825230028301)
                ·
                  refine ⟨46396034283433059461260613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123722758089154825230028301 46396034283433059461260613)
                  ·
                    refine ⟨8699256428143698648986365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46396034283433059461260613 8699256428143698648986365)
                    ·
                      refine ⟨3262221160553886993369887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8699256428143698648986365 3262221160553886993369887)
                      ·
                        rfl

theorem cell23_6353153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_6353153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353153 prefixEnd_6353153 := by exact prefixLift 6353153
  have htrace : WordTrace (prefixWord ++ tailWord_6353153) baseStart_6353153 baseEnd_6353153 := by
    simpa [prefixWord, tailWord_6353153, baseEnd_6353153] using wordTrace_append hprefix tailTrace_6353153
  have hstable : (prefixWord ++ tailWord_6353153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353153).length < 2 ^ (prefixWord ++ tailWord_6353153).sum := by decide
  have hdescent : baseEnd_6353153 < baseStart_6353153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353160 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 3, 4]
def baseStart_6353160 : Nat := 118140960795 + 6353160 * 2 ^ 59
def prefixEnd_6353160 : Nat := 4983230072969 + 3 ^ 40 * 6353160 * 2
def baseEnd_6353160 : Nat := 1087408251639489488660785

theorem tailTrace_6353160 : CollatzResearch.WordTrace tailWord_6353160 prefixEnd_6353160 1087408251639489488660785 := by
  unfold tailWord_6353160
  simp only [CollatzResearch.WordTrace]
  refine ⟨115859390831796914094596467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154479187775729218792795289 115859390831796914094596467)
  ·
    refine ⟨173789086247695371141894701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115859390831796914094596467 173789086247695371141894701)
    ·
      refine ⟨65170907342885764178210513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173789086247695371141894701 65170907342885764178210513)
      ·
        refine ⟨48878180507164323133657885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65170907342885764178210513 48878180507164323133657885)
        ·
          refine ⟨18329317690186621175121707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48878180507164323133657885 18329317690186621175121707)
          ·
            refine ⟨27493976535279931762682561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18329317690186621175121707 27493976535279931762682561)
            ·
              refine ⟨20620482401459948822011921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27493976535279931762682561 20620482401459948822011921)
              ·
                refine ⟨15465361801094961616508941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20620482401459948822011921 15465361801094961616508941)
                ·
                  refine ⟨5799510675410610606190853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15465361801094961616508941 5799510675410610606190853)
                  ·
                    refine ⟨1087408251639489488660785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5799510675410610606190853 1087408251639489488660785)
                    ·
                      rfl

theorem cell23_6353160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_6353160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353160 prefixEnd_6353160 := by exact prefixLift 6353160
  have htrace : WordTrace (prefixWord ++ tailWord_6353160) baseStart_6353160 baseEnd_6353160 := by
    simpa [prefixWord, tailWord_6353160, baseEnd_6353160] using wordTrace_append hprefix tailTrace_6353160
  have hstable : (prefixWord ++ tailWord_6353160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353160).length < 2 ^ (prefixWord ++ tailWord_6353160).sum := by decide
  have hdescent : baseEnd_6353160 < baseStart_6353160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353194 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 3, 4]
def baseStart_6353194 : Nat := 118140960795 + 6353194 * 2 ^ 59
def prefixEnd_6353194 : Nat := 4983230072969 + 3 ^ 40 * 6353194 * 2
def baseEnd_6353194 : Nat := 1087414071086907110985733

theorem tailTrace_6353194 : CollatzResearch.WordTrace tailWord_6353194 prefixEnd_6353194 1087414071086907110985733 := by
  unfold tailWord_6353194
  simp only [CollatzResearch.WordTrace]
  refine ⟨57930005436367662998982659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154480014496980434663953757 57930005436367662998982659)
  ·
    refine ⟨86895008154551494498473989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57930005436367662998982659 86895008154551494498473989)
    ·
      refine ⟨16292814028978405218463873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86895008154551494498473989 16292814028978405218463873)
      ·
        refine ⟨12219610521733803913847905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16292814028978405218463873 12219610521733803913847905)
        ·
          refine ⟨9164707891300352935385929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12219610521733803913847905 9164707891300352935385929)
          ·
            refine ⟨6873530918475264701539447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9164707891300352935385929 6873530918475264701539447)
            ·
              refine ⟨10310296377712897052309171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873530918475264701539447 10310296377712897052309171)
              ·
                refine ⟨15465444566569345578463757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10310296377712897052309171 15465444566569345578463757)
                ·
                  refine ⟨5799541712463504591923909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15465444566569345578463757 5799541712463504591923909)
                  ·
                    refine ⟨1087414071086907110985733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5799541712463504591923909 1087414071086907110985733)
                    ·
                      rfl

theorem cell23_6353194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_6353194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353194 prefixEnd_6353194 := by exact prefixLift 6353194
  have htrace : WordTrace (prefixWord ++ tailWord_6353194) baseStart_6353194 baseEnd_6353194 := by
    simpa [prefixWord, tailWord_6353194, baseEnd_6353194] using wordTrace_append hprefix tailTrace_6353194
  have hstable : (prefixWord ++ tailWord_6353194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353194).length < 2 ^ (prefixWord ++ tailWord_6353194).sum := by decide
  have hdescent : baseEnd_6353194 < baseStart_6353194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353200 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3]
def baseStart_6353200 : Nat := 118140960795 + 6353200 * 2 ^ 59
def prefixEnd_6353200 : Nat := 4983230072969 + 3 ^ 40 * 6353200 * 2
def baseEnd_6353200 : Nat := 3262245294144648309482171

theorem tailTrace_6353200 : CollatzResearch.WordTrace tailWord_6353200 prefixEnd_6353200 3262245294144648309482171 := by
  unfold tailWord_6353200
  simp only [CollatzResearch.WordTrace]
  refine ⟨115860120291724457510324527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154480160388965943347099369 115860120291724457510324527)
  ·
    refine ⟨173790180437586686265486791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115860120291724457510324527 173790180437586686265486791)
    ·
      refine ⟨260685270656380029398230187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173790180437586686265486791 260685270656380029398230187)
      ·
        refine ⟨391027905984570044097345281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260685270656380029398230187 391027905984570044097345281)
        ·
          refine ⟨293270929488427533073008961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391027905984570044097345281 293270929488427533073008961)
          ·
            refine ⟨219953197116320649804756721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293270929488427533073008961 219953197116320649804756721)
            ·
              refine ⟨164964897837240487353567541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219953197116320649804756721 164964897837240487353567541)
              ·
                refine ⟨15465459172241295689396957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164964897837240487353567541 15465459172241295689396957)
                ·
                  refine ⟨5799547189590485883523859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15465459172241295689396957 5799547189590485883523859)
                  ·
                    refine ⟨8699320784385728825285789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799547189590485883523859 8699320784385728825285789)
                    ·
                      refine ⟨3262245294144648309482171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8699320784385728825285789 3262245294144648309482171)
                      ·
                        rfl

theorem cell23_6353200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_6353200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353200 prefixEnd_6353200 := by exact prefixLift 6353200
  have htrace : WordTrace (prefixWord ++ tailWord_6353200) baseStart_6353200 baseEnd_6353200 := by
    simpa [prefixWord, tailWord_6353200, baseEnd_6353200] using wordTrace_append hprefix tailTrace_6353200
  have hstable : (prefixWord ++ tailWord_6353200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353200).length < 2 ^ (prefixWord ++ tailWord_6353200).sum := by decide
  have hdescent : baseEnd_6353200 < baseStart_6353200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353203 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 3, 5]
def baseStart_6353203 : Nat := 118140960795 + 6353203 * 2 ^ 59
def prefixEnd_6353203 : Nat := 4983230072969 + 3 ^ 40 * 6353203 * 2
def baseEnd_6353203 : Nat := 1087415611528870599248219

theorem tailTrace_6353203 : CollatzResearch.WordTrace tailWord_6353203 prefixEnd_6353203 1087415611528870599248219 := by
  unfold tailWord_6353203
  simp only [CollatzResearch.WordTrace]
  refine ⟨231720350002438046533008263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154480233334958697688672175 231720350002438046533008263)
  ·
    refine ⟨347580525003657069799512395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231720350002438046533008263 347580525003657069799512395)
    ·
      refine ⟨521370787505485604699268593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347580525003657069799512395 521370787505485604699268593)
      ·
        refine ⟨391028090629114203524451445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521370787505485604699268593 391028090629114203524451445)
        ·
          refine ⟨36658883496479456580417323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 391028090629114203524451445 36658883496479456580417323)
          ·
            refine ⟨54988325244719184870625985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36658883496479456580417323 54988325244719184870625985)
            ·
              refine ⟨41241243933539388652969489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54988325244719184870625985 41241243933539388652969489)
              ·
                refine ⟨30930932950154541489727117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41241243933539388652969489 30930932950154541489727117)
                ·
                  refine ⟨11599099856307953058647669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30930932950154541489727117 11599099856307953058647669)
                  ·
                    refine ⟨1087415611528870599248219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11599099856307953058647669 1087415611528870599248219)
                    ·
                      rfl

theorem cell23_6353203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 5].length) (baseStart_6353203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353203 prefixEnd_6353203 := by exact prefixLift 6353203
  have htrace : WordTrace (prefixWord ++ tailWord_6353203) baseStart_6353203 baseEnd_6353203 := by
    simpa [prefixWord, tailWord_6353203, baseEnd_6353203] using wordTrace_append hprefix tailTrace_6353203
  have hstable : (prefixWord ++ tailWord_6353203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353203).length < 2 ^ (prefixWord ++ tailWord_6353203).sum := by decide
  have hdescent : baseEnd_6353203 < baseStart_6353203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353233 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 6]
def baseStart_6353233 : Nat := 118140960795 + 6353233 * 2 ^ 59
def prefixEnd_6353233 : Nat := 4983230072969 + 3 ^ 40 * 6353233 * 2
def baseEnd_6353233 : Nat := 1087420746335415560123173

theorem tailTrace_6353233 : CollatzResearch.WordTrace tailWord_6353233 prefixEnd_6353233 1087420746335415560123173 := by
  unfold tailWord_6353233
  simp only [CollatzResearch.WordTrace]
  refine ⟨231721444192329361656600353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154480962794886241104400235 231721444192329361656600353)
  ·
    refine ⟨173791083144247021242450265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231721444192329361656600353 173791083144247021242450265)
    ·
      refine ⟨130343312358185265931837699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173791083144247021242450265 130343312358185265931837699)
      ·
        refine ⟨195514968537277898897756549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130343312358185265931837699 195514968537277898897756549)
        ·
          refine ⟨36659056600739606043329353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195514968537277898897756549 36659056600739606043329353)
          ·
            refine ⟨27494292450554704532497015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36659056600739606043329353 27494292450554704532497015)
            ·
              refine ⟨41241438675832056798745523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27494292450554704532497015 41241438675832056798745523)
              ·
                refine ⟨61862158013748085198118285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41241438675832056798745523 61862158013748085198118285)
                ·
                  refine ⟨23198309255155531949294357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61862158013748085198118285 23198309255155531949294357)
                  ·
                    refine ⟨1087420746335415560123173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23198309255155531949294357 1087420746335415560123173)
                    ·
                      rfl

theorem cell23_6353233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_6353233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353233 prefixEnd_6353233 := by exact prefixLift 6353233
  have htrace : WordTrace (prefixWord ++ tailWord_6353233) baseStart_6353233 baseEnd_6353233 := by
    simpa [prefixWord, tailWord_6353233, baseEnd_6353233] using wordTrace_append hprefix tailTrace_6353233
  have hstable : (prefixWord ++ tailWord_6353233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353233).length < 2 ^ (prefixWord ++ tailWord_6353233).sum := by decide
  have hdescent : baseEnd_6353233 < baseStart_6353233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353257 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 3, 2, 2]
def baseStart_6353257 : Nat := 118140960795 + 6353257 * 2 ^ 59
def prefixEnd_6353257 : Nat := 4983230072969 + 3 ^ 40 * 6353257 * 2
def baseEnd_6353257 : Nat := 3262274562541954586469409

theorem tailTrace_6353257 : CollatzResearch.WordTrace tailWord_6353257 prefixEnd_6353257 3262274562541954586469409 := by
  unfold tailWord_6353257
  simp only [CollatzResearch.WordTrace]
  refine ⟨231722319544242413755474025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154481546362828275836982683 231722319544242413755474025)
  ·
    refine ⟨173791739658181810316605519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231722319544242413755474025 173791739658181810316605519)
    ·
      refine ⟨260687609487272715474908279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173791739658181810316605519 260687609487272715474908279)
      ·
        refine ⟨391031414230909073212362419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260687609487272715474908279 391031414230909073212362419)
        ·
          refine ⟨586547121346363609818543629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391031414230909073212362419 586547121346363609818543629)
          ·
            refine ⟨219955170504886353681953861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586547121346363609818543629 219955170504886353681953861)
            ·
              refine ⟨41241594469666191315366349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 219955170504886353681953861 41241594469666191315366349)
              ·
                refine ⟨15465597926124821743262381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41241594469666191315366349 15465597926124821743262381)
                ·
                  refine ⟨5799599222296808153723393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15465597926124821743262381 5799599222296808153723393)
                  ·
                    refine ⟨4349699416722606115292545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799599222296808153723393 4349699416722606115292545)
                    ·
                      refine ⟨3262274562541954586469409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349699416722606115292545 3262274562541954586469409)
                      ·
                        rfl

theorem cell23_6353257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 3, 2, 2].length) (baseStart_6353257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353257 prefixEnd_6353257 := by exact prefixLift 6353257
  have htrace : WordTrace (prefixWord ++ tailWord_6353257) baseStart_6353257 baseEnd_6353257 := by
    simpa [prefixWord, tailWord_6353257, baseEnd_6353257] using wordTrace_append hprefix tailTrace_6353257
  have hstable : (prefixWord ++ tailWord_6353257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353257).length < 2 ^ (prefixWord ++ tailWord_6353257).sum := by decide
  have hdescent : baseEnd_6353257 < baseStart_6353257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353291 : List Nat := [1, 1, 1, 1, 4, 5, 2, 3, 1, 2, 2]
def baseStart_6353291 : Nat := 118140960795 + 6353291 * 2 ^ 59
def prefixEnd_6353291 : Nat := 4983230072969 + 3 ^ 40 * 6353291 * 2
def baseEnd_6353291 : Nat := 3262292020884207453444253

theorem tailTrace_6353291 : CollatzResearch.WordTrace tailWord_6353291 prefixEnd_6353291 3262292020884207453444253 := by
  unfold tailWord_6353291
  simp only [CollatzResearch.WordTrace]
  refine ⟨231723559626119237562211727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154482373084079491708141151 231723559626119237562211727)
  ·
    refine ⟨347585339439178856343317591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231723559626119237562211727 347585339439178856343317591)
    ·
      refine ⟨521378009158768284514976387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347585339439178856343317591 521378009158768284514976387)
      ·
        refine ⟨782067013738152426772464581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521378009158768284514976387 782067013738152426772464581)
        ·
          refine ⟨146637565075903580019837109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 782067013738152426772464581 146637565075903580019837109)
          ·
            refine ⟨13747271725865960626859729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146637565075903580019837109 13747271725865960626859729)
            ·
              refine ⟨10310453794399470470144797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13747271725865960626859729 10310453794399470470144797)
              ·
                refine ⟨3866420172899801426304299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10310453794399470470144797 3866420172899801426304299)
                ·
                  refine ⟨5799630259349702139456449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866420172899801426304299 5799630259349702139456449)
                  ·
                    refine ⟨4349722694512276604592337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5799630259349702139456449 4349722694512276604592337)
                    ·
                      refine ⟨3262292020884207453444253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349722694512276604592337 3262292020884207453444253)
                      ·
                        rfl

theorem cell23_6353291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 1, 2, 2].length) (baseStart_6353291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353291 prefixEnd_6353291 := by exact prefixLift 6353291
  have htrace : WordTrace (prefixWord ++ tailWord_6353291) baseStart_6353291 baseEnd_6353291 := by
    simpa [prefixWord, tailWord_6353291, baseEnd_6353291] using wordTrace_append hprefix tailTrace_6353291
  have hstable : (prefixWord ++ tailWord_6353291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353291).length < 2 ^ (prefixWord ++ tailWord_6353291).sum := by decide
  have hdescent : baseEnd_6353291 < baseStart_6353291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353294 : List Nat := [4, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3]
def baseStart_6353294 : Nat := 118140960795 + 6353294 * 2 ^ 59
def prefixEnd_6353294 : Nat := 4983230072969 + 3 ^ 40 * 6353294 * 2
def baseEnd_6353294 : Nat := 3262293561326170941706739

theorem tailTrace_6353294 : CollatzResearch.WordTrace tailWord_6353294 prefixEnd_6353294 3262293561326170941706739 := by
  unfold tailWord_6353294
  simp only [CollatzResearch.WordTrace]
  refine ⟨28965458630638546134321367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154482446030072246049713957 28965458630638546134321367)
  ·
    refine ⟨43448187945957819201482051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28965458630638546134321367 43448187945957819201482051)
    ·
      refine ⟨65172281918936728802223077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43448187945957819201482051 65172281918936728802223077)
      ·
        refine ⟨12219802859800636650416827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65172281918936728802223077 12219802859800636650416827)
        ·
          refine ⟨18329704289700954975625241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12219802859800636650416827 18329704289700954975625241)
          ·
            refine ⟨13747278217275716231718931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18329704289700954975625241 13747278217275716231718931)
            ·
              refine ⟨20620917325913574347578397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747278217275716231718931 20620917325913574347578397)
              ·
                refine ⟨7732843997217590380341899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20620917325913574347578397 7732843997217590380341899)
                ·
                  refine ⟨11599265995826385570512849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7732843997217590380341899 11599265995826385570512849)
                  ·
                    refine ⟨8699449496869789177884637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11599265995826385570512849 8699449496869789177884637)
                    ·
                      refine ⟨3262293561326170941706739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8699449496869789177884637 3262293561326170941706739)
                      ·
                        rfl

theorem cell23_6353294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_6353294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353294 prefixEnd_6353294 := by exact prefixLift 6353294
  have htrace : WordTrace (prefixWord ++ tailWord_6353294) baseStart_6353294 baseEnd_6353294 := by
    simpa [prefixWord, tailWord_6353294, baseEnd_6353294] using wordTrace_append hprefix tailTrace_6353294
  have hstable : (prefixWord ++ tailWord_6353294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353294).length < 2 ^ (prefixWord ++ tailWord_6353294).sum := by decide
  have hdescent : baseEnd_6353294 < baseStart_6353294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353353 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 9]
def baseStart_6353353 : Nat := 118140960795 + 6353353 * 2 ^ 59
def prefixEnd_6353353 : Nat := 4983230072969 + 3 ^ 40 * 6353353 * 2
def baseEnd_6353353 : Nat := 362480428520531801207663

theorem tailTrace_6353353 : CollatzResearch.WordTrace tailWord_6353353 prefixEnd_6353353 362480428520531801207663 := by
  unfold tailWord_6353353
  simp only [CollatzResearch.WordTrace]
  refine ⟨231725820951894622150968713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154483880634596414767312475 231725820951894622150968713)
  ·
    refine ⟨173794365713920966613226535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231725820951894622150968713 173794365713920966613226535)
    ·
      refine ⟨260691548570881449919839803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173794365713920966613226535 260691548570881449919839803)
      ·
        refine ⟨391037322856322174879759705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260691548570881449919839803 391037322856322174879759705)
        ·
          refine ⟨293277992142241631159819779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391037322856322174879759705 293277992142241631159819779)
          ·
            refine ⟨439916988213362446739729669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293277992142241631159819779 439916988213362446739729669)
            ·
              refine ⟨82484435290005458763699313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 439916988213362446739729669 82484435290005458763699313)
              ·
                refine ⟨61863326467504094072774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82484435290005458763699313 61863326467504094072774485)
                ·
                  refine ⟨362480428520531801207663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61863326467504094072774485 362480428520531801207663)
                  ·
                    rfl

theorem cell23_6353353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 9].length) (baseStart_6353353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353353 prefixEnd_6353353 := by exact prefixLift 6353353
  have htrace : WordTrace (prefixWord ++ tailWord_6353353) baseStart_6353353 baseEnd_6353353 := by
    simpa [prefixWord, tailWord_6353353, baseEnd_6353353] using wordTrace_append hprefix tailTrace_6353353
  have hstable : (prefixWord ++ tailWord_6353353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353353).length < 2 ^ (prefixWord ++ tailWord_6353353).sum := by decide
  have hdescent : baseEnd_6353353 < baseStart_6353353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353454 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_6353454 : Nat := 118140960795 + 6353454 * 2 ^ 59
def prefixEnd_6353454 : Nat := 4983230072969 + 3 ^ 40 * 6353454 * 2
def baseEnd_6353454 : Nat := 3262375718230890315706003

theorem tailTrace_6353454 : CollatzResearch.WordTrace tailWord_6353454 prefixEnd_6353454 3262375718230890315706003 := by
  unfold tailWord_6353454
  simp only [CollatzResearch.WordTrace]
  refine ⟨28966188090566089550049427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154486336483019144266930277 28966188090566089550049427)
  ·
    refine ⟨43449282135849134325074141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28966188090566089550049427 43449282135849134325074141)
    ·
      refine ⟨16293480800943425371902803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43449282135849134325074141 16293480800943425371902803)
      ·
        refine ⟨24440221201415138057854205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16293480800943425371902803 24440221201415138057854205)
        ·
          refine ⟨9165082950530676771695327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24440221201415138057854205 9165082950530676771695327)
          ·
            refine ⟨13747624425796015157542991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165082950530676771695327 13747624425796015157542991)
            ·
              refine ⟨20621436638694022736314487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747624425796015157542991 20621436638694022736314487)
              ·
                refine ⟨30932154958041034104471731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20621436638694022736314487 30932154958041034104471731)
                ·
                  refine ⟨46398232437061551156707597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30932154958041034104471731 46398232437061551156707597)
                  ·
                    refine ⟨17399337163898081683765349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46398232437061551156707597 17399337163898081683765349)
                    ·
                      refine ⟨3262375718230890315706003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17399337163898081683765349 3262375718230890315706003)
                      ·
                        rfl

theorem cell23_6353454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_6353454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353454 prefixEnd_6353454 := by exact prefixLift 6353454
  have htrace : WordTrace (prefixWord ++ tailWord_6353454) baseStart_6353454 baseEnd_6353454 := by
    simpa [prefixWord, tailWord_6353454, baseEnd_6353454] using wordTrace_append hprefix tailTrace_6353454
  have hstable : (prefixWord ++ tailWord_6353454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353454).length < 2 ^ (prefixWord ++ tailWord_6353454).sum := by decide
  have hdescent : baseEnd_6353454 < baseStart_6353454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353477 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 6]
def baseStart_6353477 : Nat := 118140960795 + 6353477 * 2 ^ 59
def prefixEnd_6353477 : Nat := 4983230072969 + 3 ^ 40 * 6353477 * 2
def baseEnd_6353477 : Nat := 362487503142882636190933

theorem tailTrace_6353477 : CollatzResearch.WordTrace tailWord_6353477 prefixEnd_6353477 362487503142882636190933 := by
  unfold tailWord_6353477
  simp only [CollatzResearch.WordTrace]
  refine ⟨231730343603445391328482685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154486895735630260885655123 231730343603445391328482685)
  ·
    refine ⟨86898878851292021748181007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231730343603445391328482685 86898878851292021748181007)
    ·
      refine ⟨130348318276938032622271511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86898878851292021748181007 130348318276938032622271511)
      ·
        refine ⟨195522477415407048933407267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130348318276938032622271511 195522477415407048933407267)
        ·
          refine ⟨293283716123110573400110901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195522477415407048933407267 293283716123110573400110901)
          ·
            refine ⟨27495348386541616256260397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293283716123110573400110901 27495348386541616256260397)
            ·
              refine ⟨10310755644953106096097649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27495348386541616256260397 10310755644953106096097649)
              ·
                refine ⟨7733066733714829572073237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10310755644953106096097649 7733066733714829572073237)
                ·
                  refine ⟨362487503142882636190933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7733066733714829572073237 362487503142882636190933)
                  ·
                    rfl

theorem cell23_6353477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 6].length) (baseStart_6353477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353477 prefixEnd_6353477 := by exact prefixLift 6353477
  have htrace : WordTrace (prefixWord ++ tailWord_6353477) baseStart_6353477 baseEnd_6353477 := by
    simpa [prefixWord, tailWord_6353477, baseEnd_6353477] using wordTrace_append hprefix tailTrace_6353477
  have hstable : (prefixWord ++ tailWord_6353477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353477).length < 2 ^ (prefixWord ++ tailWord_6353477).sum := by decide
  have hdescent : baseEnd_6353477 < baseStart_6353477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353504 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3]
def baseStart_6353504 : Nat := 118140960795 + 6353504 * 2 ^ 59
def prefixEnd_6353504 : Nat := 4983230072969 + 3 ^ 40 * 6353504 * 2
def baseEnd_6353504 : Nat := 3262401392263615120080773

theorem tailTrace_6353504 : CollatzResearch.WordTrace tailWord_6353504 prefixEnd_6353504 3262401392263615120080773 := by
  unfold tailWord_6353504
  simp only [CollatzResearch.WordTrace]
  refine ⟨115865664187173787469857783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154487552249565049959810377 115865664187173787469857783)
  ·
    refine ⟨173798496280760681204786675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115865664187173787469857783 173798496280760681204786675)
    ·
      refine ⟨260697744421141021807180013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173798496280760681204786675 260697744421141021807180013)
      ·
        refine ⟨97761654157927883177692505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260697744421141021807180013 97761654157927883177692505)
        ·
          refine ⟨73321240618445912383269379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97761654157927883177692505 73321240618445912383269379)
          ·
            refine ⟨109981860927668868574904069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73321240618445912383269379 109981860927668868574904069)
            ·
              refine ⟨20621598923937912857794513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109981860927668868574904069 20621598923937912857794513)
              ·
                refine ⟨15466199192953434643345885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20621598923937912857794513 15466199192953434643345885)
                ·
                  refine ⟨5799824697357537991254707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15466199192953434643345885 5799824697357537991254707)
                  ·
                    refine ⟨8699737046036306986882061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5799824697357537991254707 8699737046036306986882061)
                    ·
                      refine ⟨3262401392263615120080773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8699737046036306986882061 3262401392263615120080773)
                      ·
                        rfl

theorem cell23_6353504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_6353504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353504 prefixEnd_6353504 := by exact prefixLift 6353504
  have htrace : WordTrace (prefixWord ++ tailWord_6353504) baseStart_6353504 baseEnd_6353504 := by
    simpa [prefixWord, tailWord_6353504, baseEnd_6353504] using wordTrace_append hprefix tailTrace_6353504
  have hstable : (prefixWord ++ tailWord_6353504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353504).length < 2 ^ (prefixWord ++ tailWord_6353504).sum := by decide
  have hdescent : baseEnd_6353504 < baseStart_6353504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353514 : List Nat := [3, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_6353514 : Nat := 118140960795 + 6353514 * 2 ^ 59
def prefixEnd_6353514 : Nat := 4983230072969 + 3 ^ 40 * 6353514 * 2
def baseEnd_6353514 : Nat := 3262406527070160080955727

theorem tailTrace_6353514 : CollatzResearch.WordTrace tailWord_6353514 prefixEnd_6353514 3262406527070160080955727 := by
  unfold tailWord_6353514
  simp only [CollatzResearch.WordTrace]
  refine ⟨57932923276077836661894899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154487795402874231098386397 57932923276077836661894899)
  ·
    refine ⟨86899384914116754992842349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57932923276077836661894899 86899384914116754992842349)
    ·
      refine ⟨32587269342793783122315881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86899384914116754992842349 32587269342793783122315881)
      ·
        refine ⟨24440452007095337341736911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32587269342793783122315881 24440452007095337341736911)
        ·
          refine ⟨36660678010643006012605367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24440452007095337341736911 36660678010643006012605367)
          ·
            refine ⟨54991017015964509018908051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36660678010643006012605367 54991017015964509018908051)
            ·
              refine ⟨82486525523946763528362077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54991017015964509018908051 82486525523946763528362077)
              ·
                refine ⟨30932447071480036323135779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82486525523946763528362077 30932447071480036323135779)
                ·
                  refine ⟨46398670607220054484703669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30932447071480036323135779 46398670607220054484703669)
                  ·
                    refine ⟨4349875369426880107940969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46398670607220054484703669 4349875369426880107940969)
                    ·
                      refine ⟨3262406527070160080955727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4349875369426880107940969 3262406527070160080955727)
                      ·
                        rfl

theorem cell23_6353514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_6353514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353514 prefixEnd_6353514 := by exact prefixLift 6353514
  have htrace : WordTrace (prefixWord ++ tailWord_6353514) baseStart_6353514 baseEnd_6353514 := by
    simpa [prefixWord, tailWord_6353514, baseEnd_6353514] using wordTrace_append hprefix tailTrace_6353514
  have hstable : (prefixWord ++ tailWord_6353514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353514).length < 2 ^ (prefixWord ++ tailWord_6353514).sum := by decide
  have hdescent : baseEnd_6353514 < baseStart_6353514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353577 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_6353577 : Nat := 118140960795 + 6353577 * 2 ^ 59
def prefixEnd_6353577 : Nat := 4983230072969 + 3 ^ 40 * 6353577 * 2
def baseEnd_6353577 : Nat := 3262438876351393334467937

theorem tailTrace_6353577 : CollatzResearch.WordTrace tailWord_6353577 prefixEnd_6353577 3262438876351393334467937 := by
  unfold tailWord_6353577
  simp only [CollatzResearch.WordTrace]
  refine ⟨231733990903083108407122985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154489327268722072271415323 231733990903083108407122985)
  ·
    refine ⟨173800493177312331305342239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231733990903083108407122985 173800493177312331305342239)
    ·
      refine ⟨260700739765968496958013359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173800493177312331305342239 260700739765968496958013359)
      ·
        refine ⟨391051109648952745437020039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260700739765968496958013359 391051109648952745437020039)
        ·
          refine ⟨586576664473429118155530059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391051109648952745437020039 586576664473429118155530059)
          ·
            refine ⟨879864996710143677233295089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586576664473429118155530059 879864996710143677233295089)
            ·
              refine ⟨659898747532607757924971317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879864996710143677233295089 659898747532607757924971317)
              ·
                refine ⟨61865507581181977305466061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 659898747532607757924971317 61865507581181977305466061)
                ·
                  refine ⟨23199565342943241489549773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61865507581181977305466061 23199565342943241489549773)
                  ·
                    refine ⟨8699837003603715558581165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23199565342943241489549773 8699837003603715558581165)
                    ·
                      refine ⟨3262438876351393334467937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8699837003603715558581165 3262438876351393334467937)
                      ·
                        rfl

theorem cell23_6353577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_6353577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353577 prefixEnd_6353577 := by exact prefixLift 6353577
  have htrace : WordTrace (prefixWord ++ tailWord_6353577) baseStart_6353577 baseEnd_6353577 := by
    simpa [prefixWord, tailWord_6353577, baseEnd_6353577] using wordTrace_append hprefix tailTrace_6353577
  have hstable : (prefixWord ++ tailWord_6353577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353577).length < 2 ^ (prefixWord ++ tailWord_6353577).sum := by decide
  have hdescent : baseEnd_6353577 < baseStart_6353577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353581 : List Nat := [1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_6353581 : Nat := 118140960795 + 6353581 * 2 ^ 59
def prefixEnd_6353581 : Nat := 4983230072969 + 3 ^ 40 * 6353581 * 2
def baseEnd_6353581 : Nat := 3262440930274011318817919

theorem tailTrace_6353581 : CollatzResearch.WordTrace tailWord_6353581 prefixEnd_6353581 3262440930274011318817919 := by
  unfold tailWord_6353581
  simp only [CollatzResearch.WordTrace]
  refine ⟨231734136795068617090268597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154489424530045744726845731 231734136795068617090268597)
  ·
    refine ⟨21725075324537682852212681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231734136795068617090268597 21725075324537682852212681)
    ·
      refine ⟨16293806493403262139159511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21725075324537682852212681 16293806493403262139159511)
      ·
        refine ⟨24440709740104893208739267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16293806493403262139159511 24440709740104893208739267)
        ·
          refine ⟨36661064610157339813108901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24440709740104893208739267 36661064610157339813108901)
          ·
            refine ⟨6873949614404501214957919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36661064610157339813108901 6873949614404501214957919)
            ·
              refine ⟨10310924421606751822436879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6873949614404501214957919 10310924421606751822436879)
              ·
                refine ⟨15466386632410127733655319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10310924421606751822436879 15466386632410127733655319)
                ·
                  refine ⟨23199579948615191600482979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15466386632410127733655319 23199579948615191600482979)
                  ·
                    refine ⟨34799369922922787400724469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23199579948615191600482979 34799369922922787400724469)
                    ·
                      refine ⟨3262440930274011318817919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34799369922922787400724469 3262440930274011318817919)
                      ·
                        rfl

theorem cell23_6353581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_6353581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353581 prefixEnd_6353581 := by exact prefixLift 6353581
  have htrace : WordTrace (prefixWord ++ tailWord_6353581) baseStart_6353581 baseEnd_6353581 := by
    simpa [prefixWord, tailWord_6353581, baseEnd_6353581] using wordTrace_append hprefix tailTrace_6353581
  have hstable : (prefixWord ++ tailWord_6353581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353581).length < 2 ^ (prefixWord ++ tailWord_6353581).sum := by decide
  have hdescent : baseEnd_6353581 < baseStart_6353581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353597 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_6353597 : Nat := 118140960795 + 6353597 * 2 ^ 59
def prefixEnd_6353597 : Nat := 4983230072969 + 3 ^ 40 * 6353597 * 2
def baseEnd_6353597 : Nat := 1087483048654827752072615

theorem tailTrace_6353597 : CollatzResearch.WordTrace tailWord_6353597 prefixEnd_6353597 1087483048654827752072615 := by
  unfold tailWord_6353597
  simp only [CollatzResearch.WordTrace]
  refine ⟨231734720363010651822851045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154489813575340434548567363 231734720363010651822851045)
  ·
    refine ⟨43450260068064497216784571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231734720363010651822851045 43450260068064497216784571)
    ·
      refine ⟨65175390102096745825176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43450260068064497216784571 65175390102096745825176857)
      ·
        refine ⟨48881542576572559368882643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65175390102096745825176857 48881542576572559368882643)
        ·
          refine ⟨73322313864858839053323965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48881542576572559368882643 73322313864858839053323965)
          ·
            refine ⟨27495867699322064644996487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73322313864858839053323965 27495867699322064644996487)
            ·
              refine ⟨41243801548983096967494731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27495867699322064644996487 41243801548983096967494731)
              ·
                refine ⟨61865702323474645451242097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41243801548983096967494731 61865702323474645451242097)
                ·
                  refine ⟨46399276742605984088431573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61865702323474645451242097 46399276742605984088431573)
                  ·
                    refine ⟨1087483048654827752072615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46399276742605984088431573 1087483048654827752072615)
                    ·
                      rfl

theorem cell23_6353597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_6353597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353597 prefixEnd_6353597 := by exact prefixLift 6353597
  have htrace : WordTrace (prefixWord ++ tailWord_6353597) baseStart_6353597 baseEnd_6353597 := by
    simpa [prefixWord, tailWord_6353597, baseEnd_6353597] using wordTrace_append hprefix tailTrace_6353597
  have hstable : (prefixWord ++ tailWord_6353597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353597).length < 2 ^ (prefixWord ++ tailWord_6353597).sum := by decide
  have hdescent : baseEnd_6353597 < baseStart_6353597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353617 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_6353617 : Nat := 118140960795 + 6353617 * 2 ^ 59
def prefixEnd_6353617 : Nat := 4983230072969 + 3 ^ 40 * 6353617 * 2
def baseEnd_6353617 : Nat := 3262459415577573177967753

theorem tailTrace_6353617 : CollatzResearch.WordTrace tailWord_6353617 prefixEnd_6353617 3262459415577573177967753 := by
  unfold tailWord_6353617
  simp only [CollatzResearch.WordTrace]
  refine ⟨231735449822938195238579105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154490299881958796825719403 231735449822938195238579105)
  ·
    refine ⟨173801587367203646428934329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231735449822938195238579105 173801587367203646428934329)
    ·
      refine ⟨130351190525402734821700747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173801587367203646428934329 130351190525402734821700747)
      ·
        refine ⟨195526785788104102232551121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130351190525402734821700747 195526785788104102232551121)
        ·
          refine ⟨146645089341078076674413341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195526785788104102232551121 146645089341078076674413341)
          ·
            refine ⟨54991908502904278752905003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146645089341078076674413341 54991908502904278752905003)
            ·
              refine ⟨82487862754356418129357505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54991908502904278752905003 82487862754356418129357505)
              ·
                refine ⟨61865897065767313597018129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82487862754356418129357505 61865897065767313597018129)
                ·
                  refine ⟨46399422799325485197763597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61865897065767313597018129 46399422799325485197763597)
                  ·
                    refine ⟨17399783549747056949161349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46399422799325485197763597 17399783549747056949161349)
                    ·
                      refine ⟨3262459415577573177967753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17399783549747056949161349 3262459415577573177967753)
                      ·
                        rfl

theorem cell23_6353617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_6353617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353617 prefixEnd_6353617 := by exact prefixLift 6353617
  have htrace : WordTrace (prefixWord ++ tailWord_6353617) baseStart_6353617 baseEnd_6353617 := by
    simpa [prefixWord, tailWord_6353617, baseEnd_6353617] using wordTrace_append hprefix tailTrace_6353617
  have hstable : (prefixWord ++ tailWord_6353617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353617).length < 2 ^ (prefixWord ++ tailWord_6353617).sum := by decide
  have hdescent : baseEnd_6353617 < baseStart_6353617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353714 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6353714 : Nat := 118140960795 + 6353714 * 2 ^ 59
def prefixEnd_6353714 : Nat := 4983230072969 + 3 ^ 40 * 6353714 * 2
def baseEnd_6353714 : Nat := 3262509223201059298454807

theorem tailTrace_6353714 : CollatzResearch.WordTrace tailWord_6353714 prefixEnd_6353714 3262509223201059298454807 := by
  unfold tailWord_6353714
  simp only [CollatzResearch.WordTrace]
  refine ⟨57934746925896695201215049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154492658469057853869906797 57934746925896695201215049)
  ·
    refine ⟨43451060194422521400911287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57934746925896695201215049 43451060194422521400911287)
    ·
      refine ⟨65176590291633782101366931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43451060194422521400911287 65176590291633782101366931)
      ·
        refine ⟨97764885437450673152050397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65176590291633782101366931 97764885437450673152050397)
        ·
          refine ⟨36661832039044002432018899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97764885437450673152050397 36661832039044002432018899)
          ·
            refine ⟨54992748058566003648028349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36661832039044002432018899 54992748058566003648028349)
            ·
              refine ⟨20622280521962251368010631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54992748058566003648028349 20622280521962251368010631)
              ·
                refine ⟨30933420782943377052015947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20622280521962251368010631 30933420782943377052015947)
                ·
                  refine ⟨46400131174415065578023921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30933420782943377052015947 46400131174415065578023921)
                  ·
                    refine ⟨34800098380811299183517941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46400131174415065578023921 34800098380811299183517941)
                    ·
                      refine ⟨3262509223201059298454807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34800098380811299183517941 3262509223201059298454807)
                      ·
                        rfl

theorem cell23_6353714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6353714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353714 prefixEnd_6353714 := by exact prefixLift 6353714
  have htrace : WordTrace (prefixWord ++ tailWord_6353714) baseStart_6353714 baseEnd_6353714 := by
    simpa [prefixWord, tailWord_6353714, baseEnd_6353714] using wordTrace_append hprefix tailTrace_6353714
  have hstable : (prefixWord ++ tailWord_6353714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353714).length < 2 ^ (prefixWord ++ tailWord_6353714).sum := by decide
  have hdescent : baseEnd_6353714 < baseStart_6353714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353724 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_6353724 : Nat := 118140960795 + 6353724 * 2 ^ 59
def prefixEnd_6353724 : Nat := 4983230072969 + 3 ^ 40 * 6353724 * 2
def baseEnd_6353724 : Nat := 3262514358007604259329761

theorem tailTrace_6353724 : CollatzResearch.WordTrace tailWord_6353724 prefixEnd_6353724 3262514358007604259329761 := by
  unfold tailWord_6353724
  simp only [CollatzResearch.WordTrace]
  refine ⟨115869676216775276256362113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154492901622367035008482817 115869676216775276256362113)
  ·
    refine ⟨86902257162581457192271585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115869676216775276256362113 86902257162581457192271585)
    ·
      refine ⟨65176692871936092894203689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86902257162581457192271585 65176692871936092894203689)
      ·
        refine ⟨48882519653952069670652767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65176692871936092894203689 48882519653952069670652767)
        ·
          refine ⟨73323779480928104505979151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48882519653952069670652767 73323779480928104505979151)
          ·
            refine ⟨109985669221392156758968727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73323779480928104505979151 109985669221392156758968727)
            ·
              refine ⟨164978503832088235138453091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109985669221392156758968727 164978503832088235138453091)
              ·
                refine ⟨247467755748132352707679637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164978503832088235138453091 247467755748132352707679637)
                ·
                  refine ⟨11600051050693704033172483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247467755748132352707679637 11600051050693704033172483)
                  ·
                    refine ⟨17400076576040556049758725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11600051050693704033172483 17400076576040556049758725)
                    ·
                      refine ⟨3262514358007604259329761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17400076576040556049758725 3262514358007604259329761)
                      ·
                        rfl

theorem cell23_6353724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_6353724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353724 prefixEnd_6353724 := by exact prefixLift 6353724
  have htrace : WordTrace (prefixWord ++ tailWord_6353724) baseStart_6353724 baseEnd_6353724 := by
    simpa [prefixWord, tailWord_6353724, baseEnd_6353724] using wordTrace_append hprefix tailTrace_6353724
  have hstable : (prefixWord ++ tailWord_6353724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353724).length < 2 ^ (prefixWord ++ tailWord_6353724).sum := by decide
  have hdescent : baseEnd_6353724 < baseStart_6353724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353744 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3]
def baseStart_6353744 : Nat := 118140960795 + 6353744 * 2 ^ 59
def prefixEnd_6353744 : Nat := 4983230072969 + 3 ^ 40 * 6353744 * 2
def baseEnd_6353744 : Nat := 3262524627620694181079669

theorem tailTrace_6353744 : CollatzResearch.WordTrace tailWord_6353744 prefixEnd_6353744 3262524627620694181079669 := by
  unfold tailWord_6353744
  simp only [CollatzResearch.WordTrace]
  refine ⟨115870040946739047964226143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154493387928985397285634857 115870040946739047964226143)
  ·
    refine ⟨173805061420108571946339215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115870040946739047964226143 173805061420108571946339215)
    ·
      refine ⟨260707592130162857919508823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173805061420108571946339215 260707592130162857919508823)
      ·
        refine ⟨391061388195244286879263235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260707592130162857919508823 391061388195244286879263235)
        ·
          refine ⟨586592082292866430318894853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391061388195244286879263235 586592082292866430318894853)
          ·
            refine ⟨109986015429912455684792785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 586592082292866430318894853 109986015429912455684792785)
            ·
              refine ⟨82489511572434341763594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109986015429912455684792785 82489511572434341763594589)
              ·
                refine ⟨30933566839662878161347971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82489511572434341763594589 30933566839662878161347971)
                ·
                  refine ⟨46400350259494317242021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30933566839662878161347971 46400350259494317242021957)
                  ·
                    refine ⟨8700065673655184482879117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46400350259494317242021957 8700065673655184482879117)
                    ·
                      refine ⟨3262524627620694181079669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700065673655184482879117 3262524627620694181079669)
                      ·
                        rfl

theorem cell23_6353744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_6353744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353744 prefixEnd_6353744 := by exact prefixLift 6353744
  have htrace : WordTrace (prefixWord ++ tailWord_6353744) baseStart_6353744 baseEnd_6353744 := by
    simpa [prefixWord, tailWord_6353744, baseEnd_6353744] using wordTrace_append hprefix tailTrace_6353744
  have hstable : (prefixWord ++ tailWord_6353744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353744).length < 2 ^ (prefixWord ++ tailWord_6353744).sum := by decide
  have hdescent : baseEnd_6353744 < baseStart_6353744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353747 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 10]
def baseStart_6353747 : Nat := 118140960795 + 6353747 * 2 ^ 59
def prefixEnd_6353747 : Nat := 4983230072969 + 3 ^ 40 * 6353747 * 2
def baseEnd_6353747 : Nat := 362502907562517518815795

theorem tailTrace_6353747 : CollatzResearch.WordTrace tailWord_6353747 prefixEnd_6353747 362502907562517518815795 := by
  unfold tailWord_6353747
  simp only [CollatzResearch.WordTrace]
  refine ⟨231740191312467227440811495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154493460874978151627207663 231740191312467227440811495)
  ·
    refine ⟨347610286968700841161217243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231740191312467227440811495 347610286968700841161217243)
    ·
      refine ⟨521415430453051261741825865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347610286968700841161217243 521415430453051261741825865)
      ·
        refine ⟨391061572839788446306369399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521415430453051261741825865 391061572839788446306369399)
        ·
          refine ⟨586592359259682669459554099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391061572839788446306369399 586592359259682669459554099)
          ·
            refine ⟨879888538889524004189331149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586592359259682669459554099 879888538889524004189331149)
            ·
              refine ⟨329958202083571501570999181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879888538889524004189331149 329958202083571501570999181)
              ·
                refine ⟨123734325781339313089124693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329958202083571501570999181 123734325781339313089124693)
                ·
                  refine ⟨362502907562517518815795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 123734325781339313089124693 362502907562517518815795)
                  ·
                    rfl

theorem cell23_6353747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 10].length) (baseStart_6353747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353747 prefixEnd_6353747 := by exact prefixLift 6353747
  have htrace : WordTrace (prefixWord ++ tailWord_6353747) baseStart_6353747 baseEnd_6353747 := by
    simpa [prefixWord, tailWord_6353747, baseEnd_6353747] using wordTrace_append hprefix tailTrace_6353747
  have hstable : (prefixWord ++ tailWord_6353747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353747).length < 2 ^ (prefixWord ++ tailWord_6353747).sum := by decide
  have hdescent : baseEnd_6353747 < baseStart_6353747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353781 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 6]
def baseStart_6353781 : Nat := 118140960795 + 6353781 * 2 ^ 59
def prefixEnd_6353781 : Nat := 4983230072969 + 3 ^ 40 * 6353781 * 2
def baseEnd_6353781 : Nat := 362504847378323392924111

theorem tailTrace_6353781 : CollatzResearch.WordTrace tailWord_6353781 prefixEnd_6353781 362504847378323392924111 := by
  unfold tailWord_6353781
  simp only [CollatzResearch.WordTrace]
  refine ⟨231741431394344051247549197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154494287596229367498366131 231741431394344051247549197)
  ·
    refine ⟨86903036772879019217830949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231741431394344051247549197 86903036772879019217830949)
    ·
      refine ⟨16294319394914816103343303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86903036772879019217830949 16294319394914816103343303)
      ·
        refine ⟨24441479092372224155014955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16294319394914816103343303 24441479092372224155014955)
        ·
          refine ⟨36662218638558336232522433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24441479092372224155014955 36662218638558336232522433)
          ·
            refine ⟨27496663978918752174391825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36662218638558336232522433 27496663978918752174391825)
            ·
              refine ⟨20622497984189064130793869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27496663978918752174391825 20622497984189064130793869)
              ·
                refine ⟨7733436744070899049047701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20622497984189064130793869 7733436744070899049047701)
                ·
                  refine ⟨362504847378323392924111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7733436744070899049047701 362504847378323392924111)
                  ·
                    rfl

theorem cell23_6353781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_6353781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353781 prefixEnd_6353781 := by exact prefixLift 6353781
  have htrace : WordTrace (prefixWord ++ tailWord_6353781) baseStart_6353781 baseEnd_6353781 := by
    simpa [prefixWord, tailWord_6353781, baseEnd_6353781] using wordTrace_append hprefix tailTrace_6353781
  have hstable : (prefixWord ++ tailWord_6353781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353781).length < 2 ^ (prefixWord ++ tailWord_6353781).sum := by decide
  have hdescent : baseEnd_6353781 < baseStart_6353781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353791 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_6353791 : Nat := 118140960795 + 6353791 * 2 ^ 59
def prefixEnd_6353791 : Nat := 4983230072969 + 3 ^ 40 * 6353791 * 2
def baseEnd_6353791 : Nat := 3262548761211455497191953

theorem tailTrace_6353791 : CollatzResearch.WordTrace tailWord_6353791 prefixEnd_6353791 3262548761211455497191953 := by
  unfold tailWord_6353791
  simp only [CollatzResearch.WordTrace]
  refine ⟨231741796124307822955413227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154494530749538548636942151 231741796124307822955413227)
  ·
    refine ⟨347612694186461734433119841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231741796124307822955413227 347612694186461734433119841)
    ·
      refine ⟨260709520639846300824839881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347612694186461734433119841 260709520639846300824839881)
      ·
        refine ⟨195532140479884725618629911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260709520639846300824839881 195532140479884725618629911)
        ·
          refine ⟨293298210719827088427944867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195532140479884725618629911 293298210719827088427944867)
          ·
            refine ⟨439947316079740632641917301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293298210719827088427944867 439947316079740632641917301)
            ·
              refine ⟨41245060882475684310179747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439947316079740632641917301 41245060882475684310179747)
              ·
                refine ⟨61867591323713526465269621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41245060882475684310179747 61867591323713526465269621)
                ·
                  refine ⟨5800086686598143106119027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61867591323713526465269621 5800086686598143106119027)
                  ·
                    refine ⟨8700130029897214659178541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5800086686598143106119027 8700130029897214659178541)
                    ·
                      refine ⟨3262548761211455497191953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700130029897214659178541 3262548761211455497191953)
                      ·
                        rfl

theorem cell23_6353791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_6353791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353791 prefixEnd_6353791 := by exact prefixLift 6353791
  have htrace : WordTrace (prefixWord ++ tailWord_6353791) baseStart_6353791 baseEnd_6353791 := by
    simpa [prefixWord, tailWord_6353791, baseEnd_6353791] using wordTrace_append hprefix tailTrace_6353791
  have hstable : (prefixWord ++ tailWord_6353791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353791).length < 2 ^ (prefixWord ++ tailWord_6353791).sum := by decide
  have hdescent : baseEnd_6353791 < baseStart_6353791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353824 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 6]
def baseStart_6353824 : Nat := 118140960795 + 6353824 * 2 ^ 59
def prefixEnd_6353824 : Nat := 4983230072969 + 3 ^ 40 * 6353824 * 2
def baseEnd_6353824 : Nat := 1087521902024351289359767

theorem tailTrace_6353824 : CollatzResearch.WordTrace tailWord_6353824 prefixEnd_6353824 1087521902024351289359767 := by
  unfold tailWord_6353824
  simp only [CollatzResearch.WordTrace]
  refine ⟨115871499866594134795682263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154495333155458846394243017 115871499866594134795682263)
  ·
    refine ⟨173807249799891202193523395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115871499866594134795682263 173807249799891202193523395)
    ·
      refine ⟨260710874699836803290285093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173807249799891202193523395 260710874699836803290285093)
      ·
        refine ⟨48883289006219400616928455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260710874699836803290285093 48883289006219400616928455)
        ·
          refine ⟨73324933509329100925392683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48883289006219400616928455 73324933509329100925392683)
          ·
            refine ⟨109987400263993651388089025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73324933509329100925392683 109987400263993651388089025)
            ·
              refine ⟨82490550197995238541066769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109987400263993651388089025 82490550197995238541066769)
              ·
                refine ⟨61867912648496428905800077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82490550197995238541066769 61867912648496428905800077)
                ·
                  refine ⟨23200467243186160839675029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61867912648496428905800077 23200467243186160839675029)
                  ·
                    refine ⟨1087521902024351289359767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23200467243186160839675029 1087521902024351289359767)
                    ·
                      rfl

theorem cell23_6353824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 6].length) (baseStart_6353824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353824 prefixEnd_6353824 := by exact prefixLift 6353824
  have htrace : WordTrace (prefixWord ++ tailWord_6353824) baseStart_6353824 baseEnd_6353824 := by
    simpa [prefixWord, tailWord_6353824, baseEnd_6353824] using wordTrace_append hprefix tailTrace_6353824
  have hstable : (prefixWord ++ tailWord_6353824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353824).length < 2 ^ (prefixWord ++ tailWord_6353824).sum := by decide
  have hdescent : baseEnd_6353824 < baseStart_6353824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353825 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6353825 : Nat := 118140960795 + 6353825 * 2 ^ 59
def prefixEnd_6353825 : Nat := 4983230072969 + 3 ^ 40 * 6353825 * 2
def baseEnd_6353825 : Nat := 3262566219553708364166797

theorem tailTrace_6353825 : CollatzResearch.WordTrace tailWord_6353825 prefixEnd_6353825 3262566219553708364166797 := by
  unfold tailWord_6353825
  simp only [CollatzResearch.WordTrace]
  refine ⟨231743036206184646762150929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154495357470789764508100619 231743036206184646762150929)
  ·
    refine ⟨173807277154638485071613197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231743036206184646762150929 173807277154638485071613197)
    ·
      refine ⟨65177728932989431901854949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173807277154638485071613197 65177728932989431901854949)
      ·
        refine ⟨12220824174935518481597803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65177728932989431901854949 12220824174935518481597803)
        ·
          refine ⟨18331236262403277722396705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12220824174935518481597803 18331236262403277722396705)
          ·
            refine ⟨13748427196802458291797529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18331236262403277722396705 13748427196802458291797529)
            ·
              refine ⟨10311320397601843718848147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13748427196802458291797529 10311320397601843718848147)
              ·
                refine ⟨15466980596402765578272221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311320397601843718848147 15466980596402765578272221)
                ·
                  refine ⟨5800117723651037091852083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15466980596402765578272221 5800117723651037091852083)
                  ·
                    refine ⟨8700176585476555637778125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5800117723651037091852083 8700176585476555637778125)
                    ·
                      refine ⟨3262566219553708364166797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700176585476555637778125 3262566219553708364166797)
                      ·
                        rfl

theorem cell23_6353825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6353825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353825 prefixEnd_6353825 := by exact prefixLift 6353825
  have htrace : WordTrace (prefixWord ++ tailWord_6353825) baseStart_6353825 baseEnd_6353825 := by
    simpa [prefixWord, tailWord_6353825, baseEnd_6353825] using wordTrace_append hprefix tailTrace_6353825
  have hstable : (prefixWord ++ tailWord_6353825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353825).length < 2 ^ (prefixWord ++ tailWord_6353825).sum := by decide
  have hdescent : baseEnd_6353825 < baseStart_6353825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353848 : List Nat := [2, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_6353848 : Nat := 118140960795 + 6353848 * 2 ^ 59
def prefixEnd_6353848 : Nat := 4983230072969 + 3 ^ 40 * 6353848 * 2
def baseEnd_6353848 : Nat := 3262578029608761774179191

theorem tailTrace_6353848 : CollatzResearch.WordTrace tailWord_6353848 prefixEnd_6353848 3262578029608761774179191 := by
  unfold tailWord_6353848
  simp only [CollatzResearch.WordTrace]
  refine ⟨115871937542550660845119099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154495916723400881126825465 115871937542550660845119099)
  ·
    refine ⟨173807906313825991267678649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115871937542550660845119099 173807906313825991267678649)
    ·
      refine ⟨130355929735369493450758987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173807906313825991267678649 130355929735369493450758987)
      ·
        refine ⟨195533894603054240176138481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130355929735369493450758987 195533894603054240176138481)
        ·
          refine ⟨146650420952290680132103861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195533894603054240176138481 146650420952290680132103861)
          ·
            refine ⟨13748476964277251262384737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146650420952290680132103861 13748476964277251262384737)
            ·
              refine ⟨10311357723207938446788553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13748476964277251262384737 10311357723207938446788553)
              ·
                refine ⟨7733518292405953835091415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10311357723207938446788553 7733518292405953835091415)
                ·
                  refine ⟨11600277438608930752637123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733518292405953835091415 11600277438608930752637123)
                  ·
                    refine ⟨17400416157913396128955685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11600277438608930752637123 17400416157913396128955685)
                    ·
                      refine ⟨3262578029608761774179191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17400416157913396128955685 3262578029608761774179191)
                      ·
                        rfl

theorem cell23_6353848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_6353848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353848 prefixEnd_6353848 := by exact prefixLift 6353848
  have htrace : WordTrace (prefixWord ++ tailWord_6353848) baseStart_6353848 baseEnd_6353848 := by
    simpa [prefixWord, tailWord_6353848, baseEnd_6353848] using wordTrace_append hprefix tailTrace_6353848
  have hstable : (prefixWord ++ tailWord_6353848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353848).length < 2 ^ (prefixWord ++ tailWord_6353848).sum := by decide
  have hdescent : baseEnd_6353848 < baseStart_6353848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353868 : List Nat := [2, 2, 1, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6353868 : Nat := 118140960795 + 6353868 * 2 ^ 59
def prefixEnd_6353868 : Nat := 4983230072969 + 3 ^ 40 * 6353868 * 2
def baseEnd_6353868 : Nat := 3262588299221851695929099

theorem tailTrace_6353868 : CollatzResearch.WordTrace tailWord_6353868 prefixEnd_6353868 3262588299221851695929099 := by
  unfold tailWord_6353868
  simp only [CollatzResearch.WordTrace]
  refine ⟨115872302272514432552983129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154496403030019243403977505 115872302272514432552983129)
  ·
    refine ⟨86904226704385824414737347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115872302272514432552983129 86904226704385824414737347)
    ·
      refine ⟨130356340056578736622106021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86904226704385824414737347 130356340056578736622106021)
      ·
        refine ⟨24441813760608513116644879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130356340056578736622106021 24441813760608513116644879)
        ·
          refine ⟨36662720640912769674967319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24441813760608513116644879 36662720640912769674967319)
          ·
            refine ⟨54994080961369154512450979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36662720640912769674967319 54994080961369154512450979)
            ·
              refine ⟨82491121442053731768676469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54994080961369154512450979 82491121442053731768676469)
              ·
                refine ⟨7733542635192537353313419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82491121442053731768676469 7733542635192537353313419)
                ·
                  refine ⟨11600313952788806029970129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733542635192537353313419 11600313952788806029970129)
                  ·
                    refine ⟨8700235464591604522477597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11600313952788806029970129 8700235464591604522477597)
                    ·
                      refine ⟨3262588299221851695929099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700235464591604522477597 3262588299221851695929099)
                      ·
                        rfl

theorem cell23_6353868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6353868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353868 prefixEnd_6353868 := by exact prefixLift 6353868
  have htrace : WordTrace (prefixWord ++ tailWord_6353868) baseStart_6353868 baseEnd_6353868 := by
    simpa [prefixWord, tailWord_6353868, baseEnd_6353868] using wordTrace_append hprefix tailTrace_6353868
  have hstable : (prefixWord ++ tailWord_6353868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353868).length < 2 ^ (prefixWord ++ tailWord_6353868).sum := by decide
  have hdescent : baseEnd_6353868 < baseStart_6353868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353878 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6353878 : Nat := 118140960795 + 6353878 * 2 ^ 59
def prefixEnd_6353878 : Nat := 4983230072969 + 3 ^ 40 * 6353878 * 2
def baseEnd_6353878 : Nat := 3262593434028396656804053

theorem tailTrace_6353878 : CollatzResearch.WordTrace tailWord_6353878 prefixEnd_6353878 3262593434028396656804053 := by
  unfold tailWord_6353878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484060579687039800864393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154496646183328424542553525 14484060579687039800864393)
  ·
    refine ⟨10863045434765279850648295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14484060579687039800864393 10863045434765279850648295)
    ·
      refine ⟨16294568152147919775972443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863045434765279850648295 16294568152147919775972443)
      ·
        refine ⟨24441852228221879663958665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16294568152147919775972443 24441852228221879663958665)
        ·
          refine ⟨18331389171166409747968999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24441852228221879663958665 18331389171166409747968999)
          ·
            refine ⟨27497083756749614621953499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18331389171166409747968999 27497083756749614621953499)
            ·
              refine ⟨41245625635124421932930249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27497083756749614621953499 41245625635124421932930249)
              ·
                refine ⟨30934219226343316449697687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41245625635124421932930249 30934219226343316449697687)
                ·
                  refine ⟨46401328839514974674546531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30934219226343316449697687 46401328839514974674546531)
                  ·
                    refine ⟨69601993259272462011819797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46401328839514974674546531 69601993259272462011819797)
                    ·
                      refine ⟨3262593434028396656804053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69601993259272462011819797 3262593434028396656804053)
                      ·
                        rfl

theorem cell23_6353878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6353878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353878 prefixEnd_6353878 := by exact prefixLift 6353878
  have htrace : WordTrace (prefixWord ++ tailWord_6353878) baseStart_6353878 baseEnd_6353878 := by
    simpa [prefixWord, tailWord_6353878, baseEnd_6353878] using wordTrace_append hprefix tailTrace_6353878
  have hstable : (prefixWord ++ tailWord_6353878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353878).length < 2 ^ (prefixWord ++ tailWord_6353878).sum := by decide
  have hdescent : baseEnd_6353878 < baseStart_6353878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353882 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2]
def baseStart_6353882 : Nat := 118140960795 + 6353882 * 2 ^ 59
def prefixEnd_6353882 : Nat := 4983230072969 + 3 ^ 40 * 6353882 * 2
def baseEnd_6353882 : Nat := 3262595487951014641154035

theorem tailTrace_6353882 : CollatzResearch.WordTrace tailWord_6353882 prefixEnd_6353882 3262595487951014641154035 := by
  unfold tailWord_6353882
  simp only [CollatzResearch.WordTrace]
  refine ⟨57936278791744536374243975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154496743444652096997983933 57936278791744536374243975)
  ·
    refine ⟨86904418187616804561365963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57936278791744536374243975 86904418187616804561365963)
    ·
      refine ⟨130356627281425206842048945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86904418187616804561365963 130356627281425206842048945)
      ·
        refine ⟨97767470461068905131536709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130356627281425206842048945 97767470461068905131536709)
        ·
          refine ⟨18331400711450419712163133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97767470461068905131536709 18331400711450419712163133)
          ·
            refine ⟨6874275266793907392061175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18331400711450419712163133 6874275266793907392061175)
            ·
              refine ⟨10311412900190861088091763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874275266793907392061175 10311412900190861088091763)
              ·
                refine ⟨15467119350286291632137645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311412900190861088091763 15467119350286291632137645)
                ·
                  refine ⟨5800169756357359362051617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15467119350286291632137645 5800169756357359362051617)
                  ·
                    refine ⟨4350127317268019521538713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800169756357359362051617 4350127317268019521538713)
                    ·
                      refine ⟨3262595487951014641154035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350127317268019521538713 3262595487951014641154035)
                      ·
                        rfl

theorem cell23_6353882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3, 2, 2].length) (baseStart_6353882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353882 prefixEnd_6353882 := by exact prefixLift 6353882
  have htrace : WordTrace (prefixWord ++ tailWord_6353882) baseStart_6353882 baseEnd_6353882 := by
    simpa [prefixWord, tailWord_6353882, baseEnd_6353882] using wordTrace_append hprefix tailTrace_6353882
  have hstable : (prefixWord ++ tailWord_6353882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353882).length < 2 ^ (prefixWord ++ tailWord_6353882).sum := by decide
  have hdescent : baseEnd_6353882 < baseStart_6353882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353902 : List Nat := [4, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_6353902 : Nat := 118140960795 + 6353902 * 2 ^ 59
def prefixEnd_6353902 : Nat := 4983230072969 + 3 ^ 40 * 6353902 * 2
def baseEnd_6353902 : Nat := 3262605757564104562903943

theorem tailTrace_6353902 : CollatzResearch.WordTrace tailWord_6353902 prefixEnd_6353902 3262605757564104562903943 := by
  unfold tailWord_6353902
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968230578363211114087995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154497229751270459275135973 28968230578363211114087995)
  ·
    refine ⟨43452345867544816671131993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28968230578363211114087995 43452345867544816671131993)
    ·
      refine ⟨32589259400658612503348995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43452345867544816671131993 32589259400658612503348995)
      ·
        refine ⟨48883889100987918755023493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32589259400658612503348995 48883889100987918755023493)
        ·
          refine ⟨9165729206435234766566905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48883889100987918755023493 9165729206435234766566905)
          ·
            refine ⟨6874296904826426074925179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9165729206435234766566905 6874296904826426074925179)
            ·
              refine ⟨10311445357239639112387769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874296904826426074925179 10311445357239639112387769)
              ·
                refine ⟨7733584017929729334290827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10311445357239639112387769 7733584017929729334290827)
                ·
                  refine ⟨11600376026894594001436241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733584017929729334290827 11600376026894594001436241)
                  ·
                    refine ⟨8700282020170945501077181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11600376026894594001436241 8700282020170945501077181)
                    ·
                      refine ⟨3262605757564104562903943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700282020170945501077181 3262605757564104562903943)
                      ·
                        rfl

theorem cell23_6353902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_6353902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353902 prefixEnd_6353902 := by exact prefixLift 6353902
  have htrace : WordTrace (prefixWord ++ tailWord_6353902) baseStart_6353902 baseEnd_6353902 := by
    simpa [prefixWord, tailWord_6353902, baseEnd_6353902] using wordTrace_append hprefix tailTrace_6353902
  have hstable : (prefixWord ++ tailWord_6353902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353902).length < 2 ^ (prefixWord ++ tailWord_6353902).sum := by decide
  have hdescent : baseEnd_6353902 < baseStart_6353902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353904 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_6353904 : Nat := 118140960795 + 6353904 * 2 ^ 59
def prefixEnd_6353904 : Nat := 4983230072969 + 3 ^ 40 * 6353904 * 2
def baseEnd_6353904 : Nat := 3262606784525413555078933

theorem tailTrace_6353904 : CollatzResearch.WordTrace tailWord_6353904 prefixEnd_6353904 3262606784525413555078933 := by
  unfold tailWord_6353904
  simp only [CollatzResearch.WordTrace]
  refine ⟨115872958786449221627138383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154497278381932295502851177 115872958786449221627138383)
  ·
    refine ⟨173809438179673832440707575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115872958786449221627138383 173809438179673832440707575)
    ·
      refine ⟨260714157269510748661061363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173809438179673832440707575 260714157269510748661061363)
      ·
        refine ⟨391071235904266122991592045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260714157269510748661061363 391071235904266122991592045)
        ·
          refine ⟨146651713464099796121847017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391071235904266122991592045 146651713464099796121847017)
          ·
            refine ⟨109988785098074847091385263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146651713464099796121847017 109988785098074847091385263)
            ·
              refine ⟨164983177647112270637077895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109988785098074847091385263 164983177647112270637077895)
              ·
                refine ⟨247474766470668405955616843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164983177647112270637077895 247474766470668405955616843)
                ·
                  refine ⟨371212149706002608933425265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247474766470668405955616843 371212149706002608933425265)
                  ·
                    refine ⟨278409112279501956700068949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371212149706002608933425265 278409112279501956700068949)
                    ·
                      refine ⟨3262606784525413555078933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278409112279501956700068949 3262606784525413555078933)
                      ·
                        rfl

theorem cell23_6353904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_6353904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353904 prefixEnd_6353904 := by exact prefixLift 6353904
  have htrace : WordTrace (prefixWord ++ tailWord_6353904) baseStart_6353904 baseEnd_6353904 := by
    simpa [prefixWord, tailWord_6353904, baseEnd_6353904] using wordTrace_append hprefix tailTrace_6353904
  have hstable : (prefixWord ++ tailWord_6353904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353904).length < 2 ^ (prefixWord ++ tailWord_6353904).sum := by decide
  have hdescent : baseEnd_6353904 < baseStart_6353904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353948 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_6353948 : Nat := 118140960795 + 6353948 * 2 ^ 59
def prefixEnd_6353948 : Nat := 4983230072969 + 3 ^ 40 * 6353948 * 2
def baseEnd_6353948 : Nat := 1087543125891403794309577

theorem tailTrace_6353948 : CollatzResearch.WordTrace tailWord_6353948 prefixEnd_6353948 1087543125891403794309577 := by
  unfold tailWord_6353948
  simp only [CollatzResearch.WordTrace]
  refine ⟨115873761192369519384439249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154498348256492692512585665 115873761192369519384439249)
  ·
    refine ⟨86905320894277139538329437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115873761192369519384439249 86905320894277139538329437)
    ·
      refine ⟨32589495335353927326873539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86905320894277139538329437 32589495335353927326873539)
      ·
        refine ⟨48884243003030890990310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32589495335353927326873539 48884243003030890990310309)
        ·
          refine ⟨9165795563068292060683183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48884243003030890990310309 9165795563068292060683183)
          ·
            refine ⟨13748693344602438091024775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9165795563068292060683183 13748693344602438091024775)
            ·
              refine ⟨20623040016903657136537163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13748693344602438091024775 20623040016903657136537163)
              ·
                refine ⟨30934560025355485704805745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20623040016903657136537163 30934560025355485704805745)
                ·
                  refine ⟨23200920019016614278604309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30934560025355485704805745 23200920019016614278604309)
                  ·
                    refine ⟨1087543125891403794309577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23200920019016614278604309 1087543125891403794309577)
                    ·
                      rfl

theorem cell23_6353948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_6353948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353948 prefixEnd_6353948 := by exact prefixLift 6353948
  have htrace : WordTrace (prefixWord ++ tailWord_6353948) baseStart_6353948 baseEnd_6353948 := by
    simpa [prefixWord, tailWord_6353948, baseEnd_6353948] using wordTrace_append hprefix tailTrace_6353948
  have hstable : (prefixWord ++ tailWord_6353948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353948).length < 2 ^ (prefixWord ++ tailWord_6353948).sum := by decide
  have hdescent : baseEnd_6353948 < baseStart_6353948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353951 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_6353951 : Nat := 118140960795 + 6353951 * 2 ^ 59
def prefixEnd_6353951 : Nat := 4983230072969 + 3 ^ 40 * 6353951 * 2
def baseEnd_6353951 : Nat := 3262630918116174871191217

theorem tailTrace_6353951 : CollatzResearch.WordTrace tailWord_6353951 prefixEnd_6353951 3262630918116174871191217 := by
  unfold tailWord_6353951
  simp only [CollatzResearch.WordTrace]
  refine ⟨231747631803728170281237707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154498421202485446854158471 231747631803728170281237707)
  ·
    refine ⟨347621447705592255421856561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231747631803728170281237707 347621447705592255421856561)
    ·
      refine ⟨260716085779194191566392421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347621447705592255421856561 260716085779194191566392421)
      ·
        refine ⟨48884266083598910918698579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260716085779194191566392421 48884266083598910918698579)
        ·
          refine ⟨73326399125398366378047869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48884266083598910918698579 73326399125398366378047869)
          ·
            refine ⟨27497399672024387391767951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73326399125398366378047869 27497399672024387391767951)
            ·
              refine ⟨41246099508036581087651927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27497399672024387391767951 41246099508036581087651927)
              ·
                refine ⟨61869149262054871631477891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41246099508036581087651927 61869149262054871631477891)
                ·
                  refine ⟨92803723893082307447216837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61869149262054871631477891 92803723893082307447216837)
                  ·
                    refine ⟨17400698229952932646353157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92803723893082307447216837 17400698229952932646353157)
                    ·
                      refine ⟨3262630918116174871191217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17400698229952932646353157 3262630918116174871191217)
                      ·
                        rfl

theorem cell23_6353951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_6353951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353951 prefixEnd_6353951 := by exact prefixLift 6353951
  have htrace : WordTrace (prefixWord ++ tailWord_6353951) baseStart_6353951 baseEnd_6353951 := by
    simpa [prefixWord, tailWord_6353951, baseEnd_6353951] using wordTrace_append hprefix tailTrace_6353951
  have hstable : (prefixWord ++ tailWord_6353951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353951).length < 2 ^ (prefixWord ++ tailWord_6353951).sum := by decide
  have hdescent : baseEnd_6353951 < baseStart_6353951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353955 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 1, 4, 2]
def baseStart_6353955 : Nat := 118140960795 + 6353955 * 2 ^ 59
def prefixEnd_6353955 : Nat := 4983230072969 + 3 ^ 40 * 6353955 * 2
def baseEnd_6353955 : Nat := 3262632972038792855541199

theorem tailTrace_6353955 : CollatzResearch.WordTrace tailWord_6353955 prefixEnd_6353955 3262632972038792855541199 := by
  unfold tailWord_6353955
  simp only [CollatzResearch.WordTrace]
  refine ⟨231747777695713678964383319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154498518463809119309588879 231747777695713678964383319)
  ·
    refine ⟨347621666543570518446574979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231747777695713678964383319 347621666543570518446574979)
    ·
      refine ⟨521432499815355777669862469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347621666543570518446574979 521432499815355777669862469)
      ·
        refine ⟨97768593715379208313099213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 521432499815355777669862469 97768593715379208313099213)
        ·
          refine ⟨36663222643267203117412205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97768593715379208313099213 36663222643267203117412205)
          ·
            refine ⟨13748708491225201169029577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36663222643267203117412205 13748708491225201169029577)
            ·
              refine ⟨10311531368418900876772183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13748708491225201169029577 10311531368418900876772183)
              ·
                refine ⟨15467297052628351315158275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311531368418900876772183 15467297052628351315158275)
                ·
                  refine ⟨23200945578942526972737413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15467297052628351315158275 23200945578942526972737413)
                  ·
                    refine ⟨4350177296051723807388265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23200945578942526972737413 4350177296051723807388265)
                    ·
                      refine ⟨3262632972038792855541199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350177296051723807388265 3262632972038792855541199)
                      ·
                        rfl

theorem cell23_6353955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_6353955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353955 prefixEnd_6353955 := by exact prefixLift 6353955
  have htrace : WordTrace (prefixWord ++ tailWord_6353955) baseStart_6353955 baseEnd_6353955 := by
    simpa [prefixWord, tailWord_6353955, baseEnd_6353955] using wordTrace_append hprefix tailTrace_6353955
  have hstable : (prefixWord ++ tailWord_6353955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353955).length < 2 ^ (prefixWord ++ tailWord_6353955).sum := by decide
  have hdescent : baseEnd_6353955 < baseStart_6353955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353971 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3]
def baseStart_6353971 : Nat := 118140960795 + 6353971 * 2 ^ 59
def prefixEnd_6353971 : Nat := 4983230072969 + 3 ^ 40 * 6353971 * 2
def baseEnd_6353971 : Nat := 3262641187729264792941125

theorem tailTrace_6353971 : CollatzResearch.WordTrace tailWord_6353971 prefixEnd_6353971 3262641187729264792941125 := by
  unfold tailWord_6353971
  simp only [CollatzResearch.WordTrace]
  refine ⟨231748361263655713696965767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154498907509103809131310511 231748361263655713696965767)
  ·
    refine ⟨347622541895483570545448651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231748361263655713696965767 347622541895483570545448651)
    ·
      refine ⟨521433812843225355818172977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347622541895483570545448651 521433812843225355818172977)
      ·
        refine ⟨391075359632419016863629733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521433812843225355818172977 391075359632419016863629733)
        ·
          refine ⟨73326629931078565661930575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391075359632419016863629733 73326629931078565661930575)
          ·
            refine ⟨109989944896617848492895863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73326629931078565661930575 109989944896617848492895863)
            ·
              refine ⟨164984917344926772739343795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109989944896617848492895863 164984917344926772739343795)
              ·
                refine ⟨247477376017390159109015693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164984917344926772739343795 247477376017390159109015693)
                ·
                  refine ⟨92804016006521309665880885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247477376017390159109015693 92804016006521309665880885)
                  ·
                    refine ⟨8700376500611372781176333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92804016006521309665880885 8700376500611372781176333)
                    ·
                      refine ⟨3262641187729264792941125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700376500611372781176333 3262641187729264792941125)
                      ·
                        rfl

theorem cell23_6353971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_6353971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353971 prefixEnd_6353971 := by exact prefixLift 6353971
  have htrace : WordTrace (prefixWord ++ tailWord_6353971) baseStart_6353971 baseEnd_6353971 := by
    simpa [prefixWord, tailWord_6353971, baseEnd_6353971] using wordTrace_append hprefix tailTrace_6353971
  have hstable : (prefixWord ++ tailWord_6353971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353971).length < 2 ^ (prefixWord ++ tailWord_6353971).sum := by decide
  have hdescent : baseEnd_6353971 < baseStart_6353971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353972 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_6353972 : Nat := 118140960795 + 6353972 * 2 ^ 59
def prefixEnd_6353972 : Nat := 4983230072969 + 3 ^ 40 * 6353972 * 2
def baseEnd_6353972 : Nat := 3262641701209919289028621

theorem tailTrace_6353972 : CollatzResearch.WordTrace tailWord_6353972 prefixEnd_6353972 3262641701209919289028621 := by
  unfold tailWord_6353972
  simp only [CollatzResearch.WordTrace]
  refine ⟨115874198868326045433876085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154498931824434727245168113 115874198868326045433876085)
  ·
    refine ⟨10863206143905566759425883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115874198868326045433876085 10863206143905566759425883)
    ·
      refine ⟨16294809215858350139138825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863206143905566759425883 16294809215858350139138825)
      ·
        refine ⟨12221106911893762604354119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16294809215858350139138825 12221106911893762604354119)
        ·
          refine ⟨18331660367840643906531179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221106911893762604354119 18331660367840643906531179)
          ·
            refine ⟨27497490551760965859796769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18331660367840643906531179 27497490551760965859796769)
            ·
              refine ⟨20623117913820724394847577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27497490551760965859796769 20623117913820724394847577)
              ·
                refine ⟨15467338435365543296135683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20623117913820724394847577 15467338435365543296135683)
                ·
                  refine ⟨23201007653048314944203525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15467338435365543296135683 23201007653048314944203525)
                  ·
                    refine ⟨4350188934946559052038161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23201007653048314944203525 4350188934946559052038161)
                    ·
                      refine ⟨3262641701209919289028621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350188934946559052038161 3262641701209919289028621)
                      ·
                        rfl

theorem cell23_6353972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_6353972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353972 prefixEnd_6353972 := by exact prefixLift 6353972
  have htrace : WordTrace (prefixWord ++ tailWord_6353972) baseStart_6353972 baseEnd_6353972 := by
    simpa [prefixWord, tailWord_6353972, baseEnd_6353972] using wordTrace_append hprefix tailTrace_6353972
  have hstable : (prefixWord ++ tailWord_6353972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353972).length < 2 ^ (prefixWord ++ tailWord_6353972).sum := by decide
  have hdescent : baseEnd_6353972 < baseStart_6353972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6353978 : List Nat := [3, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_6353978 : Nat := 118140960795 + 6353978 * 2 ^ 59
def prefixEnd_6353978 : Nat := 4983230072969 + 3 ^ 40 * 6353978 * 2
def baseEnd_6353978 : Nat := 362516086899316251728177

theorem tailTrace_6353978 : CollatzResearch.WordTrace tailWord_6353978 prefixEnd_6353978 362516086899316251728177 := by
  unfold tailWord_6353978
  simp only [CollatzResearch.WordTrace]
  refine ⟨57937154143657588473117647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154499077716420235928313725 57937154143657588473117647)
  ·
    refine ⟨86905731215486382709676471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57937154143657588473117647 86905731215486382709676471)
    ·
      refine ⟨130358596823229574064514707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86905731215486382709676471 130358596823229574064514707)
      ·
        refine ⟨195537895234844361096772061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130358596823229574064514707 195537895234844361096772061)
        ·
          refine ⟨73326710713066635411289523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195537895234844361096772061 73326710713066635411289523)
          ·
            refine ⟨109990066069599953116934285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73326710713066635411289523 109990066069599953116934285)
            ·
              refine ⟨41246274776099982418850357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109990066069599953116934285 41246274776099982418850357)
              ·
                refine ⟨3866838260259373351767221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41246274776099982418850357 3866838260259373351767221)
                ·
                  refine ⟨362516086899316251728177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3866838260259373351767221 362516086899316251728177)
                  ·
                    rfl

theorem cell23_6353978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_6353978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6353978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6353978 prefixEnd_6353978 := by exact prefixLift 6353978
  have htrace : WordTrace (prefixWord ++ tailWord_6353978) baseStart_6353978 baseEnd_6353978 := by
    simpa [prefixWord, tailWord_6353978, baseEnd_6353978] using wordTrace_append hprefix tailTrace_6353978
  have hstable : (prefixWord ++ tailWord_6353978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6353978).length < 2 ^ (prefixWord ++ tailWord_6353978).sum := by decide
  have hdescent : baseEnd_6353978 < baseStart_6353978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6353978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354001 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 5]
def baseStart_6354001 : Nat := 118140960795 + 6354001 * 2 ^ 59
def prefixEnd_6354001 : Nat := 4983230072969 + 3 ^ 40 * 6354001 * 2
def baseEnd_6354001 : Nat := 3262656592148899675565987

theorem tailTrace_6354001 : CollatzResearch.WordTrace tailWord_6354001 prefixEnd_6354001 3262656592148899675565987 := by
  unfold tailWord_6354001
  simp only [CollatzResearch.WordTrace]
  refine ⟨231749455453547028820557857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154499636969031352547038571 231749455453547028820557857)
  ·
    refine ⟨173812091590160271615418393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231749455453547028820557857 173812091590160271615418393)
    ·
      refine ⟨130359068692620203711563795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173812091590160271615418393 130359068692620203711563795)
      ·
        refine ⟨195538603038930305567345693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130359068692620203711563795 195538603038930305567345693)
        ·
          refine ⟨73326976139598864587754635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195538603038930305567345693 73326976139598864587754635)
          ·
            refine ⟨109990464209398296881631953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73326976139598864587754635 109990464209398296881631953)
            ·
              refine ⟨82492848157048722661223965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109990464209398296881631953 82492848157048722661223965)
              ·
                refine ⟨30934818058893270997958987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82492848157048722661223965 30934818058893270997958987)
                ·
                  refine ⟨46402227088339906496938481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30934818058893270997958987 46402227088339906496938481)
                  ·
                    refine ⟨34801670316254929872703861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46402227088339906496938481 34801670316254929872703861)
                    ·
                      refine ⟨3262656592148899675565987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34801670316254929872703861 3262656592148899675565987)
                      ·
                        rfl

theorem cell23_6354001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_6354001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354001 prefixEnd_6354001 := by exact prefixLift 6354001
  have htrace : WordTrace (prefixWord ++ tailWord_6354001) baseStart_6354001 baseEnd_6354001 := by
    simpa [prefixWord, tailWord_6354001, baseEnd_6354001] using wordTrace_append hprefix tailTrace_6354001
  have hstable : (prefixWord ++ tailWord_6354001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354001).length < 2 ^ (prefixWord ++ tailWord_6354001).sum := by decide
  have hdescent : baseEnd_6354001 < baseStart_6354001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354006 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6354006 : Nat := 118140960795 + 6354006 * 2 ^ 59
def prefixEnd_6354006 : Nat := 4983230072969 + 3 ^ 40 * 6354006 * 2
def baseEnd_6354006 : Nat := 3262659159552172156003465

theorem tailTrace_6354006 : CollatzResearch.WordTrace tailWord_6354006 prefixEnd_6354006 3262659159552172156003465 := by
  unfold tailWord_6354006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484352363658057167155617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154499758545685943116326581 14484352363658057167155617)
  ·
    refine ⟨10863264272743542875366713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14484352363658057167155617 10863264272743542875366713)
    ·
      refine ⟨8147448204557657156525035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10863264272743542875366713 8147448204557657156525035)
      ·
        refine ⟨12221172306836485734787553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8147448204557657156525035 12221172306836485734787553)
        ·
          refine ⟨9165879230127364301090665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12221172306836485734787553 9165879230127364301090665)
          ·
            refine ⟨6874409422595523225817999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9165879230127364301090665 6874409422595523225817999)
            ·
              refine ⟨10311614133893284838726999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874409422595523225817999 10311614133893284838726999)
              ·
                refine ⟨15467421200839927258090499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311614133893284838726999 15467421200839927258090499)
                ·
                  refine ⟨23201131801259890887135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15467421200839927258090499 23201131801259890887135749)
                  ·
                    refine ⟨4350212212736229541337953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23201131801259890887135749 4350212212736229541337953)
                    ·
                      refine ⟨3262659159552172156003465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350212212736229541337953 3262659159552172156003465)
                      ·
                        rfl

theorem cell23_6354006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6354006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354006 prefixEnd_6354006 := by exact prefixLift 6354006
  have htrace : WordTrace (prefixWord ++ tailWord_6354006) baseStart_6354006 baseEnd_6354006 := by
    simpa [prefixWord, tailWord_6354006, baseEnd_6354006] using wordTrace_append hprefix tailTrace_6354006
  have hstable : (prefixWord ++ tailWord_6354006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354006).length < 2 ^ (prefixWord ++ tailWord_6354006).sum := by decide
  have hdescent : baseEnd_6354006 < baseStart_6354006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354021 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 8]
def baseStart_6354021 : Nat := 118140960795 + 6354021 * 2 ^ 59
def prefixEnd_6354021 : Nat := 4983230072969 + 3 ^ 40 * 6354021 * 2
def baseEnd_6354021 : Nat := 1087555620587329865771965

theorem tailTrace_6354021 : CollatzResearch.WordTrace tailWord_6354021 prefixEnd_6354021 1087555620587329865771965 := by
  unfold tailWord_6354021
  simp only [CollatzResearch.WordTrace]
  refine ⟨231750184913474572236285917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154500123275649714824190611 231750184913474572236285917)
  ·
    refine ⟨86906319342552964588607219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231750184913474572236285917 86906319342552964588607219)
    ·
      refine ⟨130359479013829446882910829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86906319342552964588607219 130359479013829446882910829)
      ·
        refine ⟨48884804630186042581091561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130359479013829446882910829 48884804630186042581091561)
        ·
          refine ⟨36663603472639531935818671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48884804630186042581091561 36663603472639531935818671)
          ·
            refine ⟨54995405208959297903728007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36663603472639531935818671 54995405208959297903728007)
            ·
              refine ⟨82493107813438946855592011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54995405208959297903728007 82493107813438946855592011)
              ·
                refine ⟨123739661720158420283388017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82493107813438946855592011 123739661720158420283388017)
                ·
                  refine ⟨92804746290118815212541013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123739661720158420283388017 92804746290118815212541013)
                  ·
                    refine ⟨1087555620587329865771965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 92804746290118815212541013 1087555620587329865771965)
                    ·
                      rfl

theorem cell23_6354021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_6354021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354021 prefixEnd_6354021 := by exact prefixLift 6354021
  have htrace : WordTrace (prefixWord ++ tailWord_6354021) baseStart_6354021 baseEnd_6354021 := by
    simpa [prefixWord, tailWord_6354021, baseEnd_6354021] using wordTrace_append hprefix tailTrace_6354021
  have hstable : (prefixWord ++ tailWord_6354021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354021).length < 2 ^ (prefixWord ++ tailWord_6354021).sum := by decide
  have hdescent : baseEnd_6354021 < baseStart_6354021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354028 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_6354028 : Nat := 118140960795 + 6354028 * 2 ^ 59
def prefixEnd_6354028 : Nat := 4983230072969 + 3 ^ 40 * 6354028 * 2
def baseEnd_6354028 : Nat := 3262670456126571069928363

theorem tailTrace_6354028 : CollatzResearch.WordTrace tailWord_6354028 prefixEnd_6354028 3262670456126571069928363 := by
  unfold tailWord_6354028
  simp only [CollatzResearch.WordTrace]
  refine ⟨115875220112224606215895369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154500293482966141621193825 115875220112224606215895369)
  ·
    refine ⟨86906415084168454661921527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115875220112224606215895369 86906415084168454661921527)
    ·
      refine ⟨130359622626252681992882291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86906415084168454661921527 130359622626252681992882291)
      ·
        refine ⟨195539433939379022989323437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130359622626252681992882291 195539433939379022989323437)
        ·
          refine ⟨73327287727267133620996289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195539433939379022989323437 73327287727267133620996289)
          ·
            refine ⟨54995465795450350215747217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73327287727267133620996289 54995465795450350215747217)
            ·
              refine ⟨41246599346587762661810413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54995465795450350215747217 41246599346587762661810413)
              ·
                refine ⟨15467474754970410998178905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41246599346587762661810413 15467474754970410998178905)
                ·
                  refine ⟨11600606066227808248634179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15467474754970410998178905 11600606066227808248634179)
                  ·
                    refine ⟨17400909099341712372951269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11600606066227808248634179 17400909099341712372951269)
                    ·
                      refine ⟨3262670456126571069928363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17400909099341712372951269 3262670456126571069928363)
                      ·
                        rfl

theorem cell23_6354028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_6354028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354028 prefixEnd_6354028 := by exact prefixLift 6354028
  have htrace : WordTrace (prefixWord ++ tailWord_6354028) baseStart_6354028 baseEnd_6354028 := by
    simpa [prefixWord, tailWord_6354028, baseEnd_6354028] using wordTrace_append hprefix tailTrace_6354028
  have hstable : (prefixWord ++ tailWord_6354028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354028).length < 2 ^ (prefixWord ++ tailWord_6354028).sum := by decide
  have hdescent : baseEnd_6354028 < baseStart_6354028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354046 : List Nat := [4, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_6354046 : Nat := 118140960795 + 6354046 * 2 ^ 59
def prefixEnd_6354046 : Nat := 4983230072969 + 3 ^ 40 * 6354046 * 2
def baseEnd_6354046 : Nat := 362519966530927999944809

theorem tailTrace_6354046 : CollatzResearch.WordTrace tailWord_6354046 prefixEnd_6354046 362519966530927999944809 := by
  unfold tailWord_6354046
  simp only [CollatzResearch.WordTrace]
  refine ⟨28968887092298000188243249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154500731158922667670630661 28968887092298000188243249)
  ·
    refine ⟨21726665319223500141182437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28968887092298000188243249 21726665319223500141182437)
    ·
      refine ⟨4073749747354406276471707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21726665319223500141182437 4073749747354406276471707)
      ·
        refine ⟨6110624621031609414707561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073749747354406276471707 6110624621031609414707561)
        ·
          refine ⟨4582968465773707061030671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110624621031609414707561 4582968465773707061030671)
          ·
            refine ⟨6874452698660560591546007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4582968465773707061030671 6874452698660560591546007)
            ·
              refine ⟨10311679047990840887319011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6874452698660560591546007 10311679047990840887319011)
              ·
                refine ⟨15467518571986261330978517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10311679047990840887319011 15467518571986261330978517)
                ·
                  refine ⟨362519966530927999944809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15467518571986261330978517 362519966530927999944809)
                  ·
                    rfl

theorem cell23_6354046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_6354046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354046 prefixEnd_6354046 := by exact prefixLift 6354046
  have htrace : WordTrace (prefixWord ++ tailWord_6354046) baseStart_6354046 baseEnd_6354046 := by
    simpa [prefixWord, tailWord_6354046, baseEnd_6354046] using wordTrace_append hprefix tailTrace_6354046
  have hstable : (prefixWord ++ tailWord_6354046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354046).length < 2 ^ (prefixWord ++ tailWord_6354046).sum := by decide
  have hdescent : baseEnd_6354046 < baseStart_6354046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354048 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3]
def baseStart_6354048 : Nat := 118140960795 + 6354048 * 2 ^ 59
def prefixEnd_6354048 : Nat := 4983230072969 + 3 ^ 40 * 6354048 * 2
def baseEnd_6354048 : Nat := 3262680725739660991678271

theorem tailTrace_6354048 : CollatzResearch.WordTrace tailWord_6354048 prefixEnd_6354048 3262680725739660991678271 := by
  unfold tailWord_6354048
  simp only [CollatzResearch.WordTrace]
  refine ⟨115875584842188377923759399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154500779789584503898345865 115875584842188377923759399)
  ·
    refine ⟨173813377263282566885639099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115875584842188377923759399 173813377263282566885639099)
    ·
      refine ⟨260720065894923850328458649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173813377263282566885639099 260720065894923850328458649)
      ·
        refine ⟨195540049421192887746343987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260720065894923850328458649 195540049421192887746343987)
        ·
          refine ⟨293310074131789331619515981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195540049421192887746343987 293310074131789331619515981)
          ·
            refine ⟨109991277799420999357318493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293310074131789331619515981 109991277799420999357318493)
            ·
              refine ⟨41246729174782874758994435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109991277799420999357318493 41246729174782874758994435)
              ·
                refine ⟨61870093762174312138491653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41246729174782874758994435 61870093762174312138491653)
                ·
                  refine ⟨11600642580407683525967185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61870093762174312138491653 11600642580407683525967185)
                  ·
                    refine ⟨8700481935305762644475389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11600642580407683525967185 8700481935305762644475389)
                    ·
                      refine ⟨3262680725739660991678271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700481935305762644475389 3262680725739660991678271)
                      ·
                        rfl

theorem cell23_6354048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_6354048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354048 prefixEnd_6354048 := by exact prefixLift 6354048
  have htrace : WordTrace (prefixWord ++ tailWord_6354048) baseStart_6354048 baseEnd_6354048 := by
    simpa [prefixWord, tailWord_6354048, baseEnd_6354048] using wordTrace_append hprefix tailTrace_6354048
  have hstable : (prefixWord ++ tailWord_6354048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354048).length < 2 ^ (prefixWord ++ tailWord_6354048).sum := by decide
  have hdescent : baseEnd_6354048 < baseStart_6354048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354051 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 8]
def baseStart_6354051 : Nat := 118140960795 + 6354051 * 2 ^ 59
def prefixEnd_6354051 : Nat := 4983230072969 + 3 ^ 40 * 6354051 * 2
def baseEnd_6354051 : Nat := 362520251797958275548973

theorem tailTrace_6354051 : CollatzResearch.WordTrace tailWord_6354051 prefixEnd_6354051 362520251797958275548973 := by
  unfold tailWord_6354051
  simp only [CollatzResearch.WordTrace]
  refine ⟨231751279103365887359878007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154500852735577258239918671 231751279103365887359878007)
  ·
    refine ⟨347626918655048831039817011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231751279103365887359878007 347626918655048831039817011)
    ·
      refine ⟨521440377982573246559725517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347626918655048831039817011 521440377982573246559725517)
      ·
        refine ⟨195540141743464967459897069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521440377982573246559725517 195540141743464967459897069)
        ·
          refine ⟨73327553153799362797461401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195540141743464967459897069 73327553153799362797461401)
          ·
            refine ⟨54995664865349522098096051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73327553153799362797461401 54995664865349522098096051)
            ·
              refine ⟨82493497298024283147144077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54995664865349522098096051 82493497298024283147144077)
              ·
                refine ⟨30935061486759106180179029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82493497298024283147144077 30935061486759106180179029)
                ·
                  refine ⟨362520251797958275548973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30935061486759106180179029 362520251797958275548973)
                  ·
                    rfl

theorem cell23_6354051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 8].length) (baseStart_6354051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354051 prefixEnd_6354051 := by exact prefixLift 6354051
  have htrace : WordTrace (prefixWord ++ tailWord_6354051) baseStart_6354051 baseEnd_6354051 := by
    simpa [prefixWord, tailWord_6354051, baseEnd_6354051] using wordTrace_append hprefix tailTrace_6354051
  have hstable : (prefixWord ++ tailWord_6354051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354051).length < 2 ^ (prefixWord ++ tailWord_6354051).sum := by decide
  have hdescent : baseEnd_6354051 < baseStart_6354051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354149 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 1, 5]
def baseStart_6354149 : Nat := 118140960795 + 6354149 * 2 ^ 59
def prefixEnd_6354149 : Nat := 4983230072969 + 3 ^ 40 * 6354149 * 2
def baseEnd_6354149 : Nat := 1087577529095255032171769

theorem tailTrace_6354149 : CollatzResearch.WordTrace tailWord_6354149 prefixEnd_6354149 1087577529095255032171769 := by
  unfold tailWord_6354149
  simp only [CollatzResearch.WordTrace]
  refine ⟨231754853457010850096945501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154503235638007233397963667 231754853457010850096945501)
  ·
    refine ⟨86908070046379068786354563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231754853457010850096945501 86908070046379068786354563)
    ·
      refine ⟨130362105069568603179531845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86908070046379068786354563 130362105069568603179531845)
      ·
        refine ⟨24442894700544113096162221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130362105069568603179531845 24442894700544113096162221)
        ·
          refine ⟨9166085512704042411060833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24442894700544113096162221 9166085512704042411060833)
          ·
            refine ⟨6874564134528031808295625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9166085512704042411060833 6874564134528031808295625)
            ·
              refine ⟨5155923100896023856221719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874564134528031808295625 5155923100896023856221719)
              ·
                refine ⟨7733884651344035784332579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155923100896023856221719 7733884651344035784332579)
                ·
                  refine ⟨11600826977016053676498869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7733884651344035784332579 11600826977016053676498869)
                  ·
                    refine ⟨1087577529095255032171769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11600826977016053676498869 1087577529095255032171769)
                    ·
                      rfl

theorem cell23_6354149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 5].length) (baseStart_6354149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354149 prefixEnd_6354149 := by exact prefixLift 6354149
  have htrace : WordTrace (prefixWord ++ tailWord_6354149) baseStart_6354149 baseEnd_6354149 := by
    simpa [prefixWord, tailWord_6354149, baseEnd_6354149] using wordTrace_append hprefix tailTrace_6354149
  have hstable : (prefixWord ++ tailWord_6354149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354149).length < 2 ^ (prefixWord ++ tailWord_6354149).sum := by decide
  have hdescent : baseEnd_6354149 < baseStart_6354149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354152 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_6354152 : Nat := 118140960795 + 6354152 * 2 ^ 59
def prefixEnd_6354152 : Nat := 4983230072969 + 3 ^ 40 * 6354152 * 2
def baseEnd_6354152 : Nat := 3262734127727728584777793

theorem tailTrace_6354152 : CollatzResearch.WordTrace tailWord_6354152 prefixEnd_6354152 3262734127727728584777793 := by
  unfold tailWord_6354152
  simp only [CollatzResearch.WordTrace]
  refine ⟨115877481437999990804652355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154503308583999987739536473 115877481437999990804652355)
  ·
    refine ⟨173816222156999986206978533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115877481437999990804652355 173816222156999986206978533)
    ·
      refine ⟨32590541654437497413808475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173816222156999986206978533 32590541654437497413808475)
      ·
        refine ⟨48885812481656246120712713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32590541654437497413808475 48885812481656246120712713)
        ·
          refine ⟨36664359361242184590534535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48885812481656246120712713 36664359361242184590534535)
          ·
            refine ⟨54996539041863276885801803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36664359361242184590534535 54996539041863276885801803)
            ·
              refine ⟨82494808562794915328702705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54996539041863276885801803 82494808562794915328702705)
              ·
                refine ⟨61871106422096186496527029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82494808562794915328702705 61871106422096186496527029)
                ·
                  refine ⟨5800416227071517484049409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61871106422096186496527029 5800416227071517484049409)
                  ·
                    refine ⟨4350312170303638113037057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800416227071517484049409 4350312170303638113037057)
                    ·
                      refine ⟨3262734127727728584777793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350312170303638113037057 3262734127727728584777793)
                      ·
                        rfl

theorem cell23_6354152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_6354152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354152 prefixEnd_6354152 := by exact prefixLift 6354152
  have htrace : WordTrace (prefixWord ++ tailWord_6354152) baseStart_6354152 baseEnd_6354152 := by
    simpa [prefixWord, tailWord_6354152, baseEnd_6354152] using wordTrace_append hprefix tailTrace_6354152
  have hstable : (prefixWord ++ tailWord_6354152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354152).length < 2 ^ (prefixWord ++ tailWord_6354152).sum := by decide
  have hdescent : baseEnd_6354152 < baseStart_6354152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354162 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_6354162 : Nat := 118140960795 + 6354162 * 2 ^ 59
def prefixEnd_6354162 : Nat := 4983230072969 + 3 ^ 40 * 6354162 * 2
def baseEnd_6354162 : Nat := 1087579754178091181884249

theorem tailTrace_6354162 : CollatzResearch.WordTrace tailWord_6354162 prefixEnd_6354162 1087579754178091181884249 := by
  unfold tailWord_6354162
  simp only [CollatzResearch.WordTrace]
  refine ⟨57938831901490938329292185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154503551737309168878112493 57938831901490938329292185)
  ·
    refine ⟨43454123926118203746969139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57938831901490938329292185 43454123926118203746969139)
    ·
      refine ⟨65181185889177305620453709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454123926118203746969139 65181185889177305620453709)
      ·
        refine ⟨24442944708441489607670141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65181185889177305620453709 24442944708441489607670141)
        ·
          refine ⟨9166104265665558602876303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24442944708441489607670141 9166104265665558602876303)
          ·
            refine ⟨13749156398498337904314455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9166104265665558602876303 13749156398498337904314455)
            ·
              refine ⟨20623734597747506856471683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13749156398498337904314455 20623734597747506856471683)
              ·
                refine ⟨30935601896621260284707525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20623734597747506856471683 30935601896621260284707525)
                ·
                  refine ⟨5800425355616486303382661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30935601896621260284707525 5800425355616486303382661)
                  ·
                    refine ⟨1087579754178091181884249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800425355616486303382661 1087579754178091181884249)
                    ·
                      rfl

theorem cell23_6354162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_6354162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354162 prefixEnd_6354162 := by exact prefixLift 6354162
  have htrace : WordTrace (prefixWord ++ tailWord_6354162) baseStart_6354162 baseEnd_6354162 := by
    simpa [prefixWord, tailWord_6354162, baseEnd_6354162] using wordTrace_append hprefix tailTrace_6354162
  have hstable : (prefixWord ++ tailWord_6354162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354162).length < 2 ^ (prefixWord ++ tailWord_6354162).sum := by decide
  have hdescent : baseEnd_6354162 < baseStart_6354162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354168 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_6354168 : Nat := 118140960795 + 6354168 * 2 ^ 59
def prefixEnd_6354168 : Nat := 4983230072969 + 3 ^ 40 * 6354168 * 2
def baseEnd_6354168 : Nat := 3262742343418200522177719

theorem tailTrace_6354168 : CollatzResearch.WordTrace tailWord_6354168 prefixEnd_6354168 3262742343418200522177719 := by
  unfold tailWord_6354168
  simp only [CollatzResearch.WordTrace]
  refine ⟨115877773221971008170943579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154503697629294677561258105 115877773221971008170943579)
  ·
    refine ⟨173816659832956512256415369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115877773221971008170943579 173816659832956512256415369)
    ·
      refine ⟨130362494874717384192311527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173816659832956512256415369 130362494874717384192311527)
      ·
        refine ⟨195543742312076076288467291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130362494874717384192311527 195543742312076076288467291)
        ·
          refine ⟨293315613468114114432700937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195543742312076076288467291 293315613468114114432700937)
          ·
            refine ⟨219986710101085585824525703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293315613468114114432700937 219986710101085585824525703)
            ·
              refine ⟨329980065151628378736788555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219986710101085585824525703 329980065151628378736788555)
              ·
                refine ⟨494970097727442568105182833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329980065151628378736788555 494970097727442568105182833)
                ·
                  refine ⟨371227573295581926078887125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494970097727442568105182833 371227573295581926078887125)
                  ·
                    refine ⟨8700646249115201392473917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 371227573295581926078887125 8700646249115201392473917)
                    ·
                      refine ⟨3262742343418200522177719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700646249115201392473917 3262742343418200522177719)
                      ·
                        rfl

theorem cell23_6354168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_6354168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354168 prefixEnd_6354168 := by exact prefixLift 6354168
  have htrace : WordTrace (prefixWord ++ tailWord_6354168) baseStart_6354168 baseEnd_6354168 := by
    simpa [prefixWord, tailWord_6354168, baseEnd_6354168] using wordTrace_append hprefix tailTrace_6354168
  have hstable : (prefixWord ++ tailWord_6354168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354168).length < 2 ^ (prefixWord ++ tailWord_6354168).sum := by decide
  have hdescent : baseEnd_6354168 < baseStart_6354168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354169 : List Nat := [1, 2, 1, 3, 1, 1, 3, 6, 1, 2, 2]
def baseStart_6354169 : Nat := 118140960795 + 6354169 * 2 ^ 59
def prefixEnd_6354169 : Nat := 4983230072969 + 3 ^ 40 * 6354169 * 2
def baseEnd_6354169 : Nat := 3262742856898855018265215

theorem tailTrace_6354169 : CollatzResearch.WordTrace tailWord_6354169 prefixEnd_6354169 3262742856898855018265215 := by
  unfold tailWord_6354169
  simp only [CollatzResearch.WordTrace]
  refine ⟨231755582916938393512673561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154503721944625595675115707 231755582916938393512673561)
  ·
    refine ⟨173816687187703795134505171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231755582916938393512673561 173816687187703795134505171)
    ·
      refine ⟨260725030781555692701757757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173816687187703795134505171 260725030781555692701757757)
      ·
        refine ⟨97771886543083384763159159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260725030781555692701757757 97771886543083384763159159)
        ·
          refine ⟨146657829814625077144738739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97771886543083384763159159 146657829814625077144738739)
          ·
            refine ⟨219986744721937615717108109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146657829814625077144738739 219986744721937615717108109)
            ·
              refine ⟨82495029270726605893915541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 219986744721937615717108109 82495029270726605893915541)
              ·
                refine ⟨3866954497065309651277291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82495029270726605893915541 3866954497065309651277291)
                ·
                  refine ⟨5800431745597964476915937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3866954497065309651277291 5800431745597964476915937)
                  ·
                    refine ⟨4350323809198473357686953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800431745597964476915937 4350323809198473357686953)
                    ·
                      refine ⟨3262742856898855018265215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350323809198473357686953 3262742856898855018265215)
                      ·
                        rfl

theorem cell23_6354169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_6354169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354169 prefixEnd_6354169 := by exact prefixLift 6354169
  have htrace : WordTrace (prefixWord ++ tailWord_6354169) baseStart_6354169 baseEnd_6354169 := by
    simpa [prefixWord, tailWord_6354169, baseEnd_6354169] using wordTrace_append hprefix tailTrace_6354169
  have hstable : (prefixWord ++ tailWord_6354169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354169).length < 2 ^ (prefixWord ++ tailWord_6354169).sum := by decide
  have hdescent : baseEnd_6354169 < baseStart_6354169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354202 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3]
def baseStart_6354202 : Nat := 118140960795 + 6354202 * 2 ^ 59
def prefixEnd_6354202 : Nat := 4983230072969 + 3 ^ 40 * 6354202 * 2
def baseEnd_6354202 : Nat := 3262759801760453389152563

theorem tailTrace_6354202 : CollatzResearch.WordTrace tailWord_6354202 prefixEnd_6354202 3262759801760453389152563 := by
  unfold tailWord_6354202
  simp only [CollatzResearch.WordTrace]
  refine ⟨57939196631454710037156215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154504524350545893432416573 57939196631454710037156215)
  ·
    refine ⟨86908794947182065055734323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57939196631454710037156215 86908794947182065055734323)
    ·
      refine ⟨130363192420773097583601485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86908794947182065055734323 130363192420773097583601485)
      ·
        refine ⟨48886197157789911593850557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130363192420773097583601485 48886197157789911593850557)
        ·
          refine ⟨18332323934171216847693959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48886197157789911593850557 18332323934171216847693959)
          ·
            refine ⟨27498485901256825271540939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18332323934171216847693959 27498485901256825271540939)
            ·
              refine ⟨41247728851885237907311409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27498485901256825271540939 41247728851885237907311409)
              ·
                refine ⟨30935796638913928430483557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41247728851885237907311409 30935796638913928430483557)
                ·
                  refine ⟨5800461869796361580715667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30935796638913928430483557 5800461869796361580715667)
                  ·
                    refine ⟨8700692804694542371073501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5800461869796361580715667 8700692804694542371073501)
                    ·
                      refine ⟨3262759801760453389152563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700692804694542371073501 3262759801760453389152563)
                      ·
                        rfl

theorem cell23_6354202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_6354202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354202 prefixEnd_6354202 := by exact prefixLift 6354202
  have htrace : WordTrace (prefixWord ++ tailWord_6354202) baseStart_6354202 baseEnd_6354202 := by
    simpa [prefixWord, tailWord_6354202, baseEnd_6354202] using wordTrace_append hprefix tailTrace_6354202
  have hstable : (prefixWord ++ tailWord_6354202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354202).length < 2 ^ (prefixWord ++ tailWord_6354202).sum := by decide
  have hdescent : baseEnd_6354202 < baseStart_6354202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354230 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_6354230 : Nat := 118140960795 + 6354230 * 2 ^ 59
def prefixEnd_6354230 : Nat := 4983230072969 + 3 ^ 40 * 6354230 * 2
def baseEnd_6354230 : Nat := 1087591393072926426534145

theorem tailTrace_6354230 : CollatzResearch.WordTrace tailWord_6354230 prefixEnd_6354230 1087591393072926426534145 := by
  unfold tailWord_6354230
  simp only [CollatzResearch.WordTrace]
  refine ⟨14484862985607337558165259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154505205179811600620429429 14484862985607337558165259)
  ·
    refine ⟨21727294478411006337247889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14484862985607337558165259 21727294478411006337247889)
    ·
      refine ⟨16295470858808254752935917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21727294478411006337247889 16295470858808254752935917)
      ·
        refine ⟨6110801572053095532350969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16295470858808254752935917 6110801572053095532350969)
        ·
          refine ⟨4583101179039821649263227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6110801572053095532350969 4583101179039821649263227)
          ·
            refine ⟨6874651768559732473894841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583101179039821649263227 6874651768559732473894841)
            ·
              refine ⟨5155988826419799355421131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874651768559732473894841 5155988826419799355421131)
              ·
                refine ⟨7733983239629699033131697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155988826419799355421131 7733983239629699033131697)
                ·
                  refine ⟨5800487429722274274848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7733983239629699033131697 5800487429722274274848773)
                  ·
                    refine ⟨1087591393072926426534145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800487429722274274848773 1087591393072926426534145)
                    ·
                      rfl

theorem cell23_6354230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_6354230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354230 prefixEnd_6354230 := by exact prefixLift 6354230
  have htrace : WordTrace (prefixWord ++ tailWord_6354230) baseStart_6354230 baseEnd_6354230 := by
    simpa [prefixWord, tailWord_6354230, baseEnd_6354230] using wordTrace_append hprefix tailTrace_6354230
  have hstable : (prefixWord ++ tailWord_6354230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354230).length < 2 ^ (prefixWord ++ tailWord_6354230).sum := by decide
  have hdescent : baseEnd_6354230 < baseStart_6354230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354236 : List Nat := [2, 2, 2, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_6354236 : Nat := 118140960795 + 6354236 * 2 ^ 59
def prefixEnd_6354236 : Nat := 4983230072969 + 3 ^ 40 * 6354236 * 2
def baseEnd_6354236 : Nat := 3262777260102706256127407

theorem tailTrace_6354236 : CollatzResearch.WordTrace tailWord_6354236 prefixEnd_6354236 3262777260102706256127407 := by
  unfold tailWord_6354236
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879013303847831977681281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154505351071797109303575041 115879013303847831977681281)
  ·
    refine ⟨86909259977885873983260961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115879013303847831977681281 86909259977885873983260961)
    ·
      refine ⟨65181944983414405487445721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86909259977885873983260961 65181944983414405487445721)
      ·
        refine ⟨48886458737560804115584291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65181944983414405487445721 48886458737560804115584291)
        ·
          refine ⟨73329688106341206173376437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48886458737560804115584291 73329688106341206173376437)
          ·
            refine ⟨6874658259969488078754041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73329688106341206173376437 6874658259969488078754041)
            ·
              refine ⟨5155993694977116059065531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6874658259969488078754041 5155993694977116059065531)
              ·
                refine ⟨7733990542465674088598297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5155993694977116059065531 7733990542465674088598297)
                ·
                  refine ⟨5800492906849255566448723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7733990542465674088598297 5800492906849255566448723)
                  ·
                    refine ⟨8700739360273883349673085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5800492906849255566448723 8700739360273883349673085)
                    ·
                      refine ⟨3262777260102706256127407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8700739360273883349673085 3262777260102706256127407)
                      ·
                        rfl

theorem cell23_6354236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_6354236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354236 prefixEnd_6354236 := by exact prefixLift 6354236
  have htrace : WordTrace (prefixWord ++ tailWord_6354236) baseStart_6354236 baseEnd_6354236 := by
    simpa [prefixWord, tailWord_6354236, baseEnd_6354236] using wordTrace_append hprefix tailTrace_6354236
  have hstable : (prefixWord ++ tailWord_6354236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354236).length < 2 ^ (prefixWord ++ tailWord_6354236).sum := by decide
  have hdescent : baseEnd_6354236 < baseStart_6354236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354248 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 9]
def baseStart_6354248 : Nat := 118140960795 + 6354248 * 2 ^ 59
def prefixEnd_6354248 : Nat := 4983230072969 + 3 ^ 40 * 6354248 * 2
def baseEnd_6354248 : Nat := 362531491318951134353039

theorem tailTrace_6354248 : CollatzResearch.WordTrace tailWord_6354248 prefixEnd_6354248 362531491318951134353039 := by
  unfold tailWord_6354248
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879232141826095002399699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154505642855768126669866265 115879232141826095002399699)
  ·
    refine ⟨173818848212739142503599549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115879232141826095002399699 173818848212739142503599549)
    ·
      refine ⟨65182068079777178438849831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173818848212739142503599549 65182068079777178438849831)
      ·
        refine ⟨97773102119665767658274747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65182068079777178438849831 97773102119665767658274747)
        ·
          refine ⟨146659653179498651487412121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97773102119665767658274747 146659653179498651487412121)
          ·
            refine ⟨109994739884623988615559091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146659653179498651487412121 109994739884623988615559091)
            ·
              refine ⟨164992109826935982923338637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109994739884623988615559091 164992109826935982923338637)
              ·
                refine ⟨61872041185100993596251989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164992109826935982923338637 61872041185100993596251989)
                ·
                  refine ⟨362531491318951134353039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61872041185100993596251989 362531491318951134353039)
                  ·
                    rfl

theorem cell23_6354248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_6354248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354248 prefixEnd_6354248 := by exact prefixLift 6354248
  have htrace : WordTrace (prefixWord ++ tailWord_6354248) baseStart_6354248 baseEnd_6354248 := by
    simpa [prefixWord, tailWord_6354248, baseEnd_6354248] using wordTrace_append hprefix tailTrace_6354248
  have hstable : (prefixWord ++ tailWord_6354248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354248).length < 2 ^ (prefixWord ++ tailWord_6354248).sum := by decide
  have hdescent : baseEnd_6354248 < baseStart_6354248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354276 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_6354276 : Nat := 118140960795 + 6354276 * 2 ^ 59
def prefixEnd_6354276 : Nat := 4983230072969 + 3 ^ 40 * 6354276 * 2
def baseEnd_6354276 : Nat := 3262797799328886099627223

theorem tailTrace_6354276 : CollatzResearch.WordTrace tailWord_6354276 prefixEnd_6354276 3262797799328886099627223 := by
  unfold tailWord_6354276
  simp only [CollatzResearch.WordTrace]
  refine ⟨115879742763775375393409341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154506323685033833857879121 115879742763775375393409341)
  ·
    refine ⟨43454903536415765772528503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115879742763775375393409341 43454903536415765772528503)
    ·
      refine ⟨65182355304623648658792755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43454903536415765772528503 65182355304623648658792755)
      ·
        refine ⟨97773532956935472988189133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65182355304623648658792755 97773532956935472988189133)
        ·
          refine ⟨36665074858850802370570925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97773532956935472988189133 36665074858850802370570925)
          ·
            refine ⟨13749403072069050888964097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36665074858850802370570925 13749403072069050888964097)
            ·
              refine ⟨10312052304051788166723073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13749403072069050888964097 10312052304051788166723073)
              ·
                refine ⟨7734039228038841125042305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312052304051788166723073 7734039228038841125042305)
                ·
                  refine ⟨5800529421029130843781729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7734039228038841125042305 5800529421029130843781729)
                  ·
                    refine ⟨4350397065771848132836297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800529421029130843781729 4350397065771848132836297)
                    ·
                      refine ⟨3262797799328886099627223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350397065771848132836297 3262797799328886099627223)
                      ·
                        rfl

theorem cell23_6354276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_6354276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354276 prefixEnd_6354276 := by exact prefixLift 6354276
  have htrace : WordTrace (prefixWord ++ tailWord_6354276) baseStart_6354276 baseEnd_6354276 := by
    simpa [prefixWord, tailWord_6354276, baseEnd_6354276] using wordTrace_append hprefix tailTrace_6354276
  have hstable : (prefixWord ++ tailWord_6354276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354276).length < 2 ^ (prefixWord ++ tailWord_6354276).sum := by decide
  have hdescent : baseEnd_6354276 < baseStart_6354276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354312 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 2, 5]
def baseStart_6354312 : Nat := 118140960795 + 6354312 * 2 ^ 59
def prefixEnd_6354312 : Nat := 4983230072969 + 3 ^ 40 * 6354312 * 2
def baseEnd_6354312 : Nat := 1087605428210815986259019

theorem tailTrace_6354312 : CollatzResearch.WordTrace tailWord_6354312 prefixEnd_6354312 1087605428210815986259019 := by
  unfold tailWord_6354312
  simp only [CollatzResearch.WordTrace]
  refine ⟨115880399277710164467564595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154507199036946885956752793 115880399277710164467564595)
  ·
    refine ⟨173820598916565246701346893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115880399277710164467564595 173820598916565246701346893)
    ·
      refine ⟨65182724593711967513005085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173820598916565246701346893 65182724593711967513005085)
      ·
        refine ⟨24443521722641987817376907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65182724593711967513005085 24443521722641987817376907)
        ·
          refine ⟨36665282583962981726065361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24443521722641987817376907 36665282583962981726065361)
          ·
            refine ⟨27498961937972236294549021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36665282583962981726065361 27498961937972236294549021)
            ·
              refine ⟨10312110726739588610455883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27498961937972236294549021 10312110726739588610455883)
              ·
                refine ⟨15468166090109382915683825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10312110726739588610455883 15468166090109382915683825)
                ·
                  refine ⟨11601124567582037186762869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15468166090109382915683825 11601124567582037186762869)
                  ·
                    refine ⟨1087605428210815986259019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11601124567582037186762869 1087605428210815986259019)
                    ·
                      rfl

theorem cell23_6354312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_6354312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354312 prefixEnd_6354312 := by exact prefixLift 6354312
  have htrace : WordTrace (prefixWord ++ tailWord_6354312) baseStart_6354312 baseEnd_6354312 := by
    simpa [prefixWord, tailWord_6354312, baseEnd_6354312] using wordTrace_append hprefix tailTrace_6354312
  have hstable : (prefixWord ++ tailWord_6354312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354312).length < 2 ^ (prefixWord ++ tailWord_6354312).sum := by decide
  have hdescent : baseEnd_6354312 < baseStart_6354312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354315 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4]
def baseStart_6354315 : Nat := 118140960795 + 6354315 * 2 ^ 59
def prefixEnd_6354315 : Nat := 4983230072969 + 3 ^ 40 * 6354315 * 2
def baseEnd_6354315 : Nat := 3262817825074411447039543

theorem tailTrace_6354315 : CollatzResearch.WordTrace tailWord_6354315 prefixEnd_6354315 3262817825074411447039543 := by
  unfold tailWord_6354315
  simp only [CollatzResearch.WordTrace]
  refine ⟨231760907974409460447488399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154507271982939640298325599 231760907974409460447488399)
  ·
    refine ⟨347641361961614190671232599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231760907974409460447488399 347641361961614190671232599)
    ·
      refine ⟨521462042942421286006848899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347641361961614190671232599 521462042942421286006848899)
      ·
        refine ⟨782193064413631929010273349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521462042942421286006848899 782193064413631929010273349)
        ·
          refine ⟨146661199577555986689426253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 782193064413631929010273349 146661199577555986689426253)
          ·
            refine ⟨54997949841583495008534845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146661199577555986689426253 54997949841583495008534845)
            ·
              refine ⟨20624231190593810628200567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54997949841583495008534845 20624231190593810628200567)
              ·
                refine ⟨30936346785890715942300851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20624231190593810628200567 30936346785890715942300851)
                ·
                  refine ⟨46404520178836073913451277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30936346785890715942300851 46404520178836073913451277)
                  ·
                    refine ⟨17401695067063527717544229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46404520178836073913451277 17401695067063527717544229)
                    ·
                      refine ⟨3262817825074411447039543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17401695067063527717544229 3262817825074411447039543)
                      ·
                        rfl

theorem cell23_6354315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 4].length) (baseStart_6354315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354315 prefixEnd_6354315 := by exact prefixLift 6354315
  have htrace : WordTrace (prefixWord ++ tailWord_6354315) baseStart_6354315 baseEnd_6354315 := by
    simpa [prefixWord, tailWord_6354315, baseEnd_6354315] using wordTrace_append hprefix tailTrace_6354315
  have hstable : (prefixWord ++ tailWord_6354315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354315).length < 2 ^ (prefixWord ++ tailWord_6354315).sum := by decide
  have hdescent : baseEnd_6354315 < baseStart_6354315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354355 : List Nat := [1, 1, 1, 2, 3, 1, 1, 7, 6]
def baseStart_6354355 : Nat := 118140960795 + 6354355 * 2 ^ 59
def prefixEnd_6354355 : Nat := 4983230072969 + 3 ^ 40 * 6354355 * 2
def baseEnd_6354355 : Nat := 362537596033399032282151

theorem tailTrace_6354355 : CollatzResearch.WordTrace tailWord_6354355 prefixEnd_6354355 362537596033399032282151 := by
  unfold tailWord_6354355
  simp only [CollatzResearch.WordTrace]
  refine ⟨231762366894264547278944519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154508244596176364852629679 231762366894264547278944519)
  ·
    refine ⟨347643550341396820918416779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231762366894264547278944519 347643550341396820918416779)
    ·
      refine ⟨521465325512095231377625169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347643550341396820918416779 521465325512095231377625169)
      ·
        refine ⟨391098994134071423533218877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521465325512095231377625169 391098994134071423533218877)
        ·
          refine ⟨146662122800276783824957079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391098994134071423533218877 146662122800276783824957079)
          ·
            refine ⟨219993184200415175737435619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146662122800276783824957079 219993184200415175737435619)
            ·
              refine ⟨329989776300622763606153429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219993184200415175737435619 329989776300622763606153429)
              ·
                refine ⟨7734135382045846022019221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329989776300622763606153429 7734135382045846022019221)
                ·
                  refine ⟨362537596033399032282151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7734135382045846022019221 362537596033399032282151)
                  ·
                    rfl

theorem cell23_6354355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 7, 6].length) (baseStart_6354355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354355 prefixEnd_6354355 := by exact prefixLift 6354355
  have htrace : WordTrace (prefixWord ++ tailWord_6354355) baseStart_6354355 baseEnd_6354355 := by
    simpa [prefixWord, tailWord_6354355, baseEnd_6354355] using wordTrace_append hprefix tailTrace_6354355
  have hstable : (prefixWord ++ tailWord_6354355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354355).length < 2 ^ (prefixWord ++ tailWord_6354355).sum := by decide
  have hdescent : baseEnd_6354355 < baseStart_6354355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354372 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 8]
def baseStart_6354372 : Nat := 118140960795 + 6354372 * 2 ^ 59
def prefixEnd_6354372 : Nat := 4983230072969 + 3 ^ 40 * 6354372 * 2
def baseEnd_6354372 : Nat := 362538565941301969336309

theorem tailTrace_6354372 : CollatzResearch.WordTrace tailWord_6354372 prefixEnd_6354372 362538565941301969336309 := by
  unfold tailWord_6354372
  simp only [CollatzResearch.WordTrace]
  refine ⟨115881493467601479591156685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154508657956801972788208913 115881493467601479591156685)
  ·
    refine ⟨43455560050350554846683757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115881493467601479591156685 43455560050350554846683757)
    ·
      refine ⟨16295835018881458067506409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43455560050350554846683757 16295835018881458067506409)
      ·
        refine ⟨12221876264161093550629807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16295835018881458067506409 12221876264161093550629807)
        ·
          refine ⟨18332814396241640325944711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12221876264161093550629807 18332814396241640325944711)
          ·
            refine ⟨27499221594362460488917067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18332814396241640325944711 27499221594362460488917067)
            ·
              refine ⟨41248832391543690733375601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27499221594362460488917067 41248832391543690733375601)
              ·
                refine ⟨30936624293657768050031701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41248832391543690733375601 30936624293657768050031701)
                ·
                  refine ⟨362538565941301969336309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30936624293657768050031701 362538565941301969336309)
                  ·
                    rfl

theorem cell23_6354372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_6354372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354372 prefixEnd_6354372 := by exact prefixLift 6354372
  have htrace : WordTrace (prefixWord ++ tailWord_6354372) baseStart_6354372 baseEnd_6354372 := by
    simpa [prefixWord, tailWord_6354372, baseEnd_6354372] using wordTrace_append hprefix tailTrace_6354372
  have hstable : (prefixWord ++ tailWord_6354372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354372).length < 2 ^ (prefixWord ++ tailWord_6354372).sum := by decide
  have hdescent : baseEnd_6354372 < baseStart_6354372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354385 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 7, 5]
def baseStart_6354385 : Nat := 118140960795 + 6354385 * 2 ^ 59
def prefixEnd_6354385 : Nat := 4983230072969 + 3 ^ 40 * 6354385 * 2
def baseEnd_6354385 : Nat := 1087617922906742057721407

theorem tailTrace_6354385 : CollatzResearch.WordTrace tailWord_6354385 prefixEnd_6354385 1087617922906742057721407 := by
  unfold tailWord_6354385
  simp only [CollatzResearch.WordTrace]
  refine ⟨231763461084155862402536609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154508974056103908268357739 231763461084155862402536609)
  ·
    refine ⟨173822595813116896801902457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231763461084155862402536609 173822595813116896801902457)
    ·
      refine ⟨130366946859837672601426843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173822595813116896801902457 130366946859837672601426843)
      ·
        refine ⟨195550420289756508902140265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130366946859837672601426843 195550420289756508902140265)
        ·
          refine ⟨146662815217317381676605199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195550420289756508902140265 146662815217317381676605199)
          ·
            refine ⟨219994222825976072514907799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146662815217317381676605199 219994222825976072514907799)
            ·
              refine ⟨329991334238964108772361699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219994222825976072514907799 329991334238964108772361699)
              ·
                refine ⟨494987001358446163158542549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329991334238964108772361699 494987001358446163158542549)
                ·
                  refine ⟨11601257844338581949028341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 494987001358446163158542549 11601257844338581949028341)
                  ·
                    refine ⟨1087617922906742057721407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11601257844338581949028341 1087617922906742057721407)
                    ·
                      rfl

theorem cell23_6354385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 5].length) (baseStart_6354385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354385 prefixEnd_6354385 := by exact prefixLift 6354385
  have htrace : WordTrace (prefixWord ++ tailWord_6354385) baseStart_6354385 baseEnd_6354385 := by
    simpa [prefixWord, tailWord_6354385, baseEnd_6354385] using wordTrace_append hprefix tailTrace_6354385
  have hstable : (prefixWord ++ tailWord_6354385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354385).length < 2 ^ (prefixWord ++ tailWord_6354385).sum := by decide
  have hdescent : baseEnd_6354385 < baseStart_6354385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354435 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6]
def baseStart_6354435 : Nat := 118140960795 + 6354435 * 2 ^ 59
def prefixEnd_6354435 : Nat := 4983230072969 + 3 ^ 40 * 6354435 * 2
def baseEnd_6354435 : Nat := 3262879442752950977538991

theorem tailTrace_6354435 : CollatzResearch.WordTrace tailWord_6354435 prefixEnd_6354435 3262879442752950977538991 := by
  unfold tailWord_6354435
  simp only [CollatzResearch.WordTrace]
  refine ⟨231765284733974720941856759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154510189822649813961237839 231765284733974720941856759)
  ·
    refine ⟨347647927100962081412785139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231765284733974720941856759 347647927100962081412785139)
    ·
      refine ⟨521471890651443122119177709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347647927100962081412785139 521471890651443122119177709)
      ·
        refine ⟨195551958994291170794691641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521471890651443122119177709 195551958994291170794691641)
        ·
          refine ⟨146663969245718378096018731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195551958994291170794691641 146663969245718378096018731)
          ·
            refine ⟨219995953868577567144028097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146663969245718378096018731 219995953868577567144028097)
            ·
              refine ⟨164996965401433175358021073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219995953868577567144028097 164996965401433175358021073)
              ·
                refine ⟨123747724051074881518515805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164996965401433175358021073 123747724051074881518515805)
                ·
                  refine ⟨46405396519153080569443427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123747724051074881518515805 46405396519153080569443427)
                  ·
                    refine ⟨69608094778729620854165141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46405396519153080569443427 69608094778729620854165141)
                    ·
                      refine ⟨3262879442752950977538991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69608094778729620854165141 3262879442752950977538991)
                      ·
                        rfl

theorem cell23_6354435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_6354435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354435 prefixEnd_6354435 := by exact prefixLift 6354435
  have htrace : WordTrace (prefixWord ++ tailWord_6354435) baseStart_6354435 baseEnd_6354435 := by
    simpa [prefixWord, tailWord_6354435, baseEnd_6354435] using wordTrace_append hprefix tailTrace_6354435
  have hstable : (prefixWord ++ tailWord_6354435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354435).length < 2 ^ (prefixWord ++ tailWord_6354435).sum := by decide
  have hdescent : baseEnd_6354435 < baseStart_6354435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354449 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 2, 4]
def baseStart_6354449 : Nat := 118140960795 + 6354449 * 2 ^ 59
def prefixEnd_6354449 : Nat := 4983230072969 + 3 ^ 40 * 6354449 * 2
def baseEnd_6354449 : Nat := 1087628877160704640921309

theorem tailTrace_6354449 : CollatzResearch.WordTrace tailWord_6354449 prefixEnd_6354449 1087628877160704640921309 := by
  unfold tailWord_6354449
  simp only [CollatzResearch.WordTrace]
  refine ⟨231765795355924001332866401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154510530237282667555244267 231765795355924001332866401)
  ·
    refine ⟨173824346516943000999649801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231765795355924001332866401 173824346516943000999649801)
    ·
      refine ⟨130368259887707250749737351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173824346516943000999649801 130368259887707250749737351)
      ·
        refine ⟨195552389831560876124606027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130368259887707250749737351 195552389831560876124606027)
        ·
          refine ⟨293328584747341314186909041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195552389831560876124606027 293328584747341314186909041)
          ·
            refine ⟨219996438560505985640181781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293328584747341314186909041 219996438560505985640181781)
            ·
              refine ⟨10312333057523718076883521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 219996438560505985640181781 10312333057523718076883521)
              ·
                refine ⟨7734249793142788557662641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312333057523718076883521 7734249793142788557662641)
                ·
                  refine ⟨5800687344857091418246981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7734249793142788557662641 5800687344857091418246981)
                  ·
                    refine ⟨1087628877160704640921309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5800687344857091418246981 1087628877160704640921309)
                    ·
                      rfl

theorem cell23_6354449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 4].length) (baseStart_6354449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354449 prefixEnd_6354449 := by exact prefixLift 6354449
  have htrace : WordTrace (prefixWord ++ tailWord_6354449) baseStart_6354449 baseEnd_6354449 := by
    simpa [prefixWord, tailWord_6354449, baseEnd_6354449] using wordTrace_append hprefix tailTrace_6354449
  have hstable : (prefixWord ++ tailWord_6354449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354449).length < 2 ^ (prefixWord ++ tailWord_6354449).sum := by decide
  have hdescent : baseEnd_6354449 < baseStart_6354449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354489 : List Nat := [1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6354489 : Nat := 118140960795 + 6354489 * 2 ^ 59
def prefixEnd_6354489 : Nat := 4983230072969 + 3 ^ 40 * 6354489 * 2
def baseEnd_6354489 : Nat := 3262907170708293766263743

theorem tailTrace_6354489 : CollatzResearch.WordTrace tailWord_6354489 prefixEnd_6354489 3262907170708293766263743 := by
  unfold tailWord_6354489
  simp only [CollatzResearch.WordTrace]
  refine ⟨231767254275779088164322521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154511502850519392109548347 231767254275779088164322521)
  ·
    refine ⟨173825440706834316123241891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231767254275779088164322521 173825440706834316123241891)
    ·
      refine ⟨260738161060251474184862837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173825440706834316123241891 260738161060251474184862837)
      ·
        refine ⟨24444202599398575704830891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260738161060251474184862837 24444202599398575704830891)
        ·
          refine ⟨36666303899097863557246337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24444202599398575704830891 36666303899097863557246337)
          ·
            refine ⟨27499727924323397667934753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36666303899097863557246337 27499727924323397667934753)
            ·
              refine ⟨20624795943242548250951065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27499727924323397667934753 20624795943242548250951065)
              ·
                refine ⟨15468596957431911188213299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20624795943242548250951065 15468596957431911188213299)
                ·
                  refine ⟨23202895436147866782319949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15468596957431911188213299 23202895436147866782319949)
                  ·
                    refine ⟨8701085788555450043369981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23202895436147866782319949 8701085788555450043369981)
                    ·
                      refine ⟨3262907170708293766263743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701085788555450043369981 3262907170708293766263743)
                      ·
                        rfl

theorem cell23_6354489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6354489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354489 prefixEnd_6354489 := by exact prefixLift 6354489
  have htrace : WordTrace (prefixWord ++ tailWord_6354489) baseStart_6354489 baseEnd_6354489 := by
    simpa [prefixWord, tailWord_6354489, baseEnd_6354489] using wordTrace_append hprefix tailTrace_6354489
  have hstable : (prefixWord ++ tailWord_6354489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354489).length < 2 ^ (prefixWord ++ tailWord_6354489).sum := by decide
  have hdescent : baseEnd_6354489 < baseStart_6354489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354533 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_6354533 : Nat := 118140960795 + 6354533 * 2 ^ 59
def prefixEnd_6354533 : Nat := 4983230072969 + 3 ^ 40 * 6354533 * 2
def baseEnd_6354533 : Nat := 3262929763857091594113541

theorem tailTrace_6354533 : CollatzResearch.WordTrace tailWord_6354533 prefixEnd_6354533 3262929763857091594113541 := by
  unfold tailWord_6354533
  simp only [CollatzResearch.WordTrace]
  refine ⟨231768859087619683678924253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154512572725079789119282835 231768859087619683678924253)
  ·
    refine ⟨86913322157857381379596595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231768859087619683678924253 86913322157857381379596595)
    ·
      refine ⟨130369983236786072069394893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86913322157857381379596595 130369983236786072069394893)
      ·
        refine ⟨48888743713794777026023085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130369983236786072069394893 48888743713794777026023085)
        ·
          refine ⟨18333278892673041384758657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48888743713794777026023085 18333278892673041384758657)
          ·
            refine ⟨13749959169504781038568993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18333278892673041384758657 13749959169504781038568993)
            ·
              refine ⟨10312469377128585778926745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13749959169504781038568993 10312469377128585778926745)
              ·
                refine ⟨7734352032846439334195059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10312469377128585778926745 7734352032846439334195059)
                ·
                  refine ⟨11601528049269659001292589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7734352032846439334195059 11601528049269659001292589)
                  ·
                    refine ⟨4350573018476122125484721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11601528049269659001292589 4350573018476122125484721)
                    ·
                      refine ⟨3262929763857091594113541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350573018476122125484721 3262929763857091594113541)
                      ·
                        rfl

theorem cell23_6354533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_6354533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354533 prefixEnd_6354533 := by exact prefixLift 6354533
  have htrace : WordTrace (prefixWord ++ tailWord_6354533) baseStart_6354533 baseEnd_6354533 := by
    simpa [prefixWord, tailWord_6354533, baseEnd_6354533] using wordTrace_append hprefix tailTrace_6354533
  have hstable : (prefixWord ++ tailWord_6354533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354533).length < 2 ^ (prefixWord ++ tailWord_6354533).sum := by decide
  have hdescent : baseEnd_6354533 < baseStart_6354533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354549 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6354549 : Nat := 118140960795 + 6354549 * 2 ^ 59
def prefixEnd_6354549 : Nat := 4983230072969 + 3 ^ 40 * 6354549 * 2
def baseEnd_6354549 : Nat := 3262937979547563531513467

theorem tailTrace_6354549 : CollatzResearch.WordTrace tailWord_6354549 prefixEnd_6354549 3262937979547563531513467 := by
  unfold tailWord_6354549
  simp only [CollatzResearch.WordTrace]
  refine ⟨231769442655561718411506701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154512961770374478941004467 231769442655561718411506701)
  ·
    refine ⟨86913540995835644404315013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231769442655561718411506701 86913540995835644404315013)
    ·
      refine ⟨16296288936719183325809065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86913540995835644404315013 16296288936719183325809065)
      ·
        refine ⟨12222216702539387494356799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296288936719183325809065 12222216702539387494356799)
        ·
          refine ⟨18333325053809081241535199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222216702539387494356799 18333325053809081241535199)
          ·
            refine ⟨27499987580713621862302799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18333325053809081241535199 27499987580713621862302799)
            ·
              refine ⟨41249981371070432793454199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27499987580713621862302799 41249981371070432793454199)
              ·
                refine ⟨61874972056605649190181299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41249981371070432793454199 61874972056605649190181299)
                ·
                  refine ⟨92812458084908473785271949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61874972056605649190181299 92812458084908473785271949)
                  ·
                    refine ⟨34804671781840677669476981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92812458084908473785271949 34804671781840677669476981)
                    ·
                      refine ⟨3262937979547563531513467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34804671781840677669476981 3262937979547563531513467)
                      ·
                        rfl

theorem cell23_6354549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6354549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354549 prefixEnd_6354549 := by exact prefixLift 6354549
  have htrace : WordTrace (prefixWord ++ tailWord_6354549) baseStart_6354549 baseEnd_6354549 := by
    simpa [prefixWord, tailWord_6354549, baseEnd_6354549] using wordTrace_append hprefix tailTrace_6354549
  have hstable : (prefixWord ++ tailWord_6354549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354549).length < 2 ^ (prefixWord ++ tailWord_6354549).sum := by decide
  have hdescent : baseEnd_6354549 < baseStart_6354549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354569 : List Nat := [1, 2, 1, 1, 4, 1, 2, 6, 5]
def baseStart_6354569 : Nat := 118140960795 + 6354569 * 2 ^ 59
def prefixEnd_6354569 : Nat := 4983230072969 + 3 ^ 40 * 6354569 * 2
def baseEnd_6354569 : Nat := 362549805462294828140375

theorem tailTrace_6354569 : CollatzResearch.WordTrace tailWord_6354569 prefixEnd_6354569 362549805462294828140375 := by
  unfold tailWord_6354569
  simp only [CollatzResearch.WordTrace]
  refine ⟨231770172115489261827234761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154513448076992841218156507 231770172115489261827234761)
  ·
    refine ⟨173827629086616946370426071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231770172115489261827234761 173827629086616946370426071)
    ·
      refine ⟨260741443629925419555639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173827629086616946370426071 260741443629925419555639107)
      ·
        refine ⟨391112165444888129333458661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260741443629925419555639107 391112165444888129333458661)
        ·
          refine ⟨73333531020916524250023499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391112165444888129333458661 73333531020916524250023499)
          ·
            refine ⟨110000296531374786375035249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73333531020916524250023499 110000296531374786375035249)
            ·
              refine ⟨82500222398531089781276437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110000296531374786375035249 82500222398531089781276437)
              ·
                refine ⟨3867197924931144833497333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82500222398531089781276437 3867197924931144833497333)
                ·
                  refine ⟨362549805462294828140375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3867197924931144833497333 362549805462294828140375)
                  ·
                    rfl

theorem cell23_6354569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 5].length) (baseStart_6354569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354569 prefixEnd_6354569 := by exact prefixLift 6354569
  have htrace : WordTrace (prefixWord ++ tailWord_6354569) baseStart_6354569 baseEnd_6354569 := by
    simpa [prefixWord, tailWord_6354569, baseEnd_6354569] using wordTrace_append hprefix tailTrace_6354569
  have hstable : (prefixWord ++ tailWord_6354569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354569).length < 2 ^ (prefixWord ++ tailWord_6354569).sum := by decide
  have hdescent : baseEnd_6354569 < baseStart_6354569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354619 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 3, 6, 2]
def baseStart_6354619 : Nat := 118140960795 + 6354619 * 2 ^ 59
def prefixEnd_6354619 : Nat := 4983230072969 + 3 ^ 40 * 6354619 * 2
def baseEnd_6354619 : Nat := 3262973923193378257638145

theorem tailTrace_6354619 : CollatzResearch.WordTrace tailWord_6354619 prefixEnd_6354619 3262973923193378257638145 := by
  unfold tailWord_6354619
  simp only [CollatzResearch.WordTrace]
  refine ⟨231771995765308120366554911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154514663843538746911036607 231771995765308120366554911)
  ·
    refine ⟨347657993647962180549832367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231771995765308120366554911 347657993647962180549832367)
    ·
      refine ⟨521486990471943270824748551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347657993647962180549832367 521486990471943270824748551)
      ·
        refine ⟨782230485707914906237122827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521486990471943270824748551 782230485707914906237122827)
        ·
          refine ⟨1173345728561872359355684241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782230485707914906237122827 1173345728561872359355684241)
          ·
            refine ⟨880009296421404269516763181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1173345728561872359355684241 880009296421404269516763181)
            ·
              refine ⟨330003486158026601068786193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 880009296421404269516763181 330003486158026601068786193)
              ·
                refine ⟨247502614618519950801589645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330003486158026601068786193 247502614618519950801589645)
                ·
                  refine ⟨92813480481944981550596117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247502614618519950801589645 92813480481944981550596117)
                  ·
                    refine ⟨4350631897591171010184193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92813480481944981550596117 4350631897591171010184193)
                    ·
                      refine ⟨3262973923193378257638145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350631897591171010184193 3262973923193378257638145)
                      ·
                        rfl

theorem cell23_6354619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 6, 2].length) (baseStart_6354619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354619 prefixEnd_6354619 := by exact prefixLift 6354619
  have htrace : WordTrace (prefixWord ++ tailWord_6354619) baseStart_6354619 baseEnd_6354619 := by
    simpa [prefixWord, tailWord_6354619, baseEnd_6354619] using wordTrace_append hprefix tailTrace_6354619
  have hstable : (prefixWord ++ tailWord_6354619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354619).length < 2 ^ (prefixWord ++ tailWord_6354619).sum := by decide
  have hdescent : baseEnd_6354619 < baseStart_6354619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354630 : List Nat := [6, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6354630 : Nat := 118140960795 + 6354630 * 2 ^ 59
def prefixEnd_6354630 : Nat := 4983230072969 + 3 ^ 40 * 6354630 * 2
def baseEnd_6354630 : Nat := 3262979571480577714600595

theorem tailTrace_6354630 : CollatzResearch.WordTrace tailWord_6354630 prefixEnd_6354630 3262979571480577714600595 := by
  unfold tailWord_6354630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242887405258383413912667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154514931312178846163470229 7242887405258383413912667)
  ·
    refine ⟨10864331107887575120869001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7242887405258383413912667 10864331107887575120869001)
    ·
      refine ⟨8148248330915681340651751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10864331107887575120869001 8148248330915681340651751)
      ·
        refine ⟨12222372496373522010977627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148248330915681340651751 12222372496373522010977627)
        ·
          refine ⟨18333558744560283016466441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12222372496373522010977627 18333558744560283016466441)
          ·
            refine ⟨13750169058420212262349831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18333558744560283016466441 13750169058420212262349831)
            ·
              refine ⟨20625253587630318393524747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13750169058420212262349831 20625253587630318393524747)
              ·
                refine ⟨30937880381445477590287121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20625253587630318393524747 30937880381445477590287121)
                ·
                  refine ⟨23203410286084108192715341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30937880381445477590287121 23203410286084108192715341)
                  ·
                    refine ⟨8701278857281540572268253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23203410286084108192715341 8701278857281540572268253)
                    ·
                      refine ⟨3262979571480577714600595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701278857281540572268253 3262979571480577714600595)
                      ·
                        rfl

theorem cell23_6354630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6354630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354630 prefixEnd_6354630 := by exact prefixLift 6354630
  have htrace : WordTrace (prefixWord ++ tailWord_6354630) baseStart_6354630 baseEnd_6354630 := by
    simpa [prefixWord, tailWord_6354630, baseEnd_6354630] using wordTrace_append hprefix tailTrace_6354630
  have hstable : (prefixWord ++ tailWord_6354630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354630).length < 2 ^ (prefixWord ++ tailWord_6354630).sum := by decide
  have hdescent : baseEnd_6354630 < baseStart_6354630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354639 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_6354639 : Nat := 118140960795 + 6354639 * 2 ^ 59
def prefixEnd_6354639 : Nat := 4983230072969 + 3 ^ 40 * 6354639 * 2
def baseEnd_6354639 : Nat := 3262984192806468179388053

theorem tailTrace_6354639 : CollatzResearch.WordTrace tailWord_6354639 prefixEnd_6354639 3262984192806468179388053 := by
  unfold tailWord_6354639
  simp only [CollatzResearch.WordTrace]
  refine ⟨231772725225235663782282971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154515150150157109188188647 231772725225235663782282971)
  ·
    refine ⟨347659087837853495673424457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231772725225235663782282971 347659087837853495673424457)
    ·
      refine ⟨260744315878390121755068343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347659087837853495673424457 260744315878390121755068343)
      ·
        refine ⟨391116473817585182632602515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260744315878390121755068343 391116473817585182632602515)
        ·
          refine ⟨586674710726377773948903773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391116473817585182632602515 586674710726377773948903773)
          ·
            refine ⟨220003016522391665230838915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586674710726377773948903773 220003016522391665230838915)
            ·
              refine ⟨330004524783587497846258373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220003016522391665230838915 330004524783587497846258373)
              ·
                refine ⟨61875848396922655846173445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 330004524783587497846258373 61875848396922655846173445)
                ·
                  refine ⟨11601721574422997971157521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61875848396922655846173445 11601721574422997971157521)
                  ·
                    refine ⟨8701291180817248478368141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11601721574422997971157521 8701291180817248478368141)
                    ·
                      refine ⟨3262984192806468179388053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701291180817248478368141 3262984192806468179388053)
                      ·
                        rfl

theorem cell23_6354639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_6354639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354639 prefixEnd_6354639 := by exact prefixLift 6354639
  have htrace : WordTrace (prefixWord ++ tailWord_6354639) baseStart_6354639 baseEnd_6354639 := by
    simpa [prefixWord, tailWord_6354639, baseEnd_6354639] using wordTrace_append hprefix tailTrace_6354639
  have hstable : (prefixWord ++ tailWord_6354639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354639).length < 2 ^ (prefixWord ++ tailWord_6354639).sum := by decide
  have hdescent : baseEnd_6354639 < baseStart_6354639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354653 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6354653 : Nat := 118140960795 + 6354653 * 2 ^ 59
def prefixEnd_6354653 : Nat := 4983230072969 + 3 ^ 40 * 6354653 * 2
def baseEnd_6354653 : Nat := 3262991381535631124612989

theorem tailTrace_6354653 : CollatzResearch.WordTrace tailWord_6354653 prefixEnd_6354653 3262991381535631124612989 := by
  unfold tailWord_6354653
  simp only [CollatzResearch.WordTrace]
  refine ⟨231773235847184944173292613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154515490564789962782195075 231773235847184944173292613)
  ·
    refine ⟨43457481721347177032492365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231773235847184944173292613 43457481721347177032492365)
    ·
      refine ⟨16296555645505191387184637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43457481721347177032492365 16296555645505191387184637)
      ·
        refine ⟨6111208367064446770194239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16296555645505191387184637 6111208367064446770194239)
        ·
          refine ⟨9166812550596670155291359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111208367064446770194239 9166812550596670155291359)
          ·
            refine ⟨13750218825895005232937039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9166812550596670155291359 13750218825895005232937039)
            ·
              refine ⟨20625328238842507849405559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13750218825895005232937039 20625328238842507849405559)
              ·
                refine ⟨30937992358263761774108339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20625328238842507849405559 30937992358263761774108339)
                ·
                  refine ⟨46406988537395642661162509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30937992358263761774108339 46406988537395642661162509)
                  ·
                    refine ⟨17402620701523365997935941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46406988537395642661162509 17402620701523365997935941)
                    ·
                      refine ⟨3262991381535631124612989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17402620701523365997935941 3262991381535631124612989)
                      ·
                        rfl

theorem cell23_6354653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6354653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354653 prefixEnd_6354653 := by exact prefixLift 6354653
  have htrace : WordTrace (prefixWord ++ tailWord_6354653) baseStart_6354653 baseEnd_6354653 := by
    simpa [prefixWord, tailWord_6354653, baseEnd_6354653] using wordTrace_append hprefix tailTrace_6354653
  have hstable : (prefixWord ++ tailWord_6354653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354653).length < 2 ^ (prefixWord ++ tailWord_6354653).sum := by decide
  have hdescent : baseEnd_6354653 < baseStart_6354653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354656 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3]
def baseStart_6354656 : Nat := 118140960795 + 6354656 * 2 ^ 59
def prefixEnd_6354656 : Nat := 4983230072969 + 3 ^ 40 * 6354656 * 2
def baseEnd_6354656 : Nat := 3262992921977594612875475

theorem tailTrace_6354656 : CollatzResearch.WordTrace tailWord_6354656 prefixEnd_6354656 3262992921977594612875475 := by
  unfold tailWord_6354656
  simp only [CollatzResearch.WordTrace]
  refine ⟨115886672633087037842825911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154515563510782717123767881 115886672633087037842825911)
  ·
    refine ⟨173830008949630556764238867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115886672633087037842825911 173830008949630556764238867)
    ·
      refine ⟨260745013424445835146358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173830008949630556764238867 260745013424445835146358301)
      ·
        refine ⟨97779380034167188179884363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260745013424445835146358301 97779380034167188179884363)
        ·
          refine ⟨146669070051250782269826545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97779380034167188179884363 146669070051250782269826545)
          ·
            refine ⟨110001802538438086702369909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146669070051250782269826545 110001802538438086702369909)
            ·
              refine ⟨10312668987978570628347179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110001802538438086702369909 10312668987978570628347179)
              ·
                refine ⟨15469003481967855942520769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10312668987978570628347179 15469003481967855942520769)
                ·
                  refine ⟨11601752611475891956890577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15469003481967855942520769 11601752611475891956890577)
                  ·
                    refine ⟨8701314458606918967667933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11601752611475891956890577 8701314458606918967667933)
                    ·
                      refine ⟨3262992921977594612875475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701314458606918967667933 3262992921977594612875475)
                      ·
                        rfl

theorem cell23_6354656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_6354656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354656 prefixEnd_6354656 := by exact prefixLift 6354656
  have htrace : WordTrace (prefixWord ++ tailWord_6354656) baseStart_6354656 baseEnd_6354656 := by
    simpa [prefixWord, tailWord_6354656, baseEnd_6354656] using wordTrace_append hprefix tailTrace_6354656
  have hstable : (prefixWord ++ tailWord_6354656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354656).length < 2 ^ (prefixWord ++ tailWord_6354656).sum := by decide
  have hdescent : baseEnd_6354656 < baseStart_6354656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354689 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 5, 5]
def baseStart_6354689 : Nat := 118140960795 + 6354689 * 2 ^ 59
def prefixEnd_6354689 : Nat := 4983230072969 + 3 ^ 40 * 6354689 * 2
def baseEnd_6354689 : Nat := 1087669955613064327920941

theorem tailTrace_6354689 : CollatzResearch.WordTrace tailWord_6354689 prefixEnd_6354689 1087669955613064327920941 := by
  unfold tailWord_6354689
  simp only [CollatzResearch.WordTrace]
  refine ⟨231774548875054522321603121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154516365916703014881068747 231774548875054522321603121)
  ·
    refine ⟨173830911656290891741202341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231774548875054522321603121 173830911656290891741202341)
    ·
      refine ⟨32593295935554542201475439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173830911656290891741202341 32593295935554542201475439)
      ·
        refine ⟨48889943903331813302213159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32593295935554542201475439 48889943903331813302213159)
        ·
          refine ⟨73334915854997719953319739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48889943903331813302213159 73334915854997719953319739)
          ·
            refine ⟨110002373782496579929979609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73334915854997719953319739 110002373782496579929979609)
            ·
              refine ⟨82501780336872434947484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110002373782496579929979609 82501780336872434947484707)
              ·
                refine ⟨123752670505308652421227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82501780336872434947484707 123752670505308652421227061)
                ·
                  refine ⟨11601812859872686164490037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123752670505308652421227061 11601812859872686164490037)
                  ·
                    refine ⟨1087669955613064327920941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11601812859872686164490037 1087669955613064327920941)
                    ·
                      rfl

theorem cell23_6354689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_6354689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354689 prefixEnd_6354689 := by exact prefixLift 6354689
  have htrace : WordTrace (prefixWord ++ tailWord_6354689) baseStart_6354689 baseEnd_6354689 := by
    simpa [prefixWord, tailWord_6354689, baseEnd_6354689] using wordTrace_append hprefix tailTrace_6354689
  have hstable : (prefixWord ++ tailWord_6354689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354689).length < 2 ^ (prefixWord ++ tailWord_6354689).sum := by decide
  have hdescent : baseEnd_6354689 < baseStart_6354689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354696 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2]
def baseStart_6354696 : Nat := 118140960795 + 6354696 * 2 ^ 59
def prefixEnd_6354696 : Nat := 4983230072969 + 3 ^ 40 * 6354696 * 2
def baseEnd_6354696 : Nat := 3263013461203774456375291

theorem tailTrace_6354696 : CollatzResearch.WordTrace tailWord_6354696 prefixEnd_6354696 3263013461203774456375291 := by
  unfold tailWord_6354696
  simp only [CollatzResearch.WordTrace]
  refine ⟨115887402093014581258553971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154516536124019441678071961 115887402093014581258553971)
  ·
    refine ⟨173831103139521871887830957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115887402093014581258553971 173831103139521871887830957)
    ·
      refine ⟨65186663677320701957936609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173831103139521871887830957 65186663677320701957936609)
      ·
        refine ⟨48889997757990526468452457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65186663677320701957936609 48889997757990526468452457)
        ·
          refine ⟨36667498318492894851339343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48889997757990526468452457 36667498318492894851339343)
          ·
            refine ⟨55001247477739342277009015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36667498318492894851339343 55001247477739342277009015)
            ·
              refine ⟨82501871216609013415513523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55001247477739342277009015 82501871216609013415513523)
              ·
                refine ⟨123752806824913520123270285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82501871216609013415513523 123752806824913520123270285)
                ·
                  refine ⟨46407302559342570046226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123752806824913520123270285 46407302559342570046226357)
                  ·
                    refine ⟨4350684614938365941833721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46407302559342570046226357 4350684614938365941833721)
                    ·
                      refine ⟨3263013461203774456375291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350684614938365941833721 3263013461203774456375291)
                      ·
                        rfl

theorem cell23_6354696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_6354696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354696 prefixEnd_6354696 := by exact prefixLift 6354696
  have htrace : WordTrace (prefixWord ++ tailWord_6354696) baseStart_6354696 baseEnd_6354696 := by
    simpa [prefixWord, tailWord_6354696, baseEnd_6354696] using wordTrace_append hprefix tailTrace_6354696
  have hstable : (prefixWord ++ tailWord_6354696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354696).length < 2 ^ (prefixWord ++ tailWord_6354696).sum := by decide
  have hdescent : baseEnd_6354696 < baseStart_6354696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354719 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 6]
def baseStart_6354719 : Nat := 118140960795 + 6354719 * 2 ^ 59
def prefixEnd_6354719 : Nat := 4983230072969 + 3 ^ 40 * 6354719 * 2
def baseEnd_6354719 : Nat := 1087675090419609288795895

theorem tailTrace_6354719 : CollatzResearch.WordTrace tailWord_6354719 prefixEnd_6354719 1087675090419609288795895 := by
  unfold tailWord_6354719
  simp only [CollatzResearch.WordTrace]
  refine ⟨231775643064945837445195211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154517095376630558296796807 231775643064945837445195211)
  ·
    refine ⟨347663464597418756167792817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231775643064945837445195211 347663464597418756167792817)
    ·
      refine ⟨260747598448064067125844613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347663464597418756167792817 260747598448064067125844613)
      ·
        refine ⟨48890174709012012586095865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260747598448064067125844613 48890174709012012586095865)
        ·
          refine ⟨36667631031759009439571899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48890174709012012586095865 36667631031759009439571899)
          ·
            refine ⟨55001446547638514159357849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36667631031759009439571899 55001446547638514159357849)
            ·
              refine ⟨41251084910728885619518387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55001446547638514159357849 41251084910728885619518387)
              ·
                refine ⟨61876627366093328429277581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41251084910728885619518387 61876627366093328429277581)
                ·
                  refine ⟨23203735262284998160979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61876627366093328429277581 23203735262284998160979093)
                  ·
                    refine ⟨1087675090419609288795895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23203735262284998160979093 1087675090419609288795895)
                    ·
                      rfl

theorem cell23_6354719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_6354719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354719 prefixEnd_6354719 := by exact prefixLift 6354719
  have htrace : WordTrace (prefixWord ++ tailWord_6354719) baseStart_6354719 baseEnd_6354719 := by
    simpa [prefixWord, tailWord_6354719, baseEnd_6354719] using wordTrace_append hprefix tailTrace_6354719
  have hstable : (prefixWord ++ tailWord_6354719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354719).length < 2 ^ (prefixWord ++ tailWord_6354719).sum := by decide
  have hdescent : baseEnd_6354719 < baseStart_6354719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354737 : List Nat := [1, 2, 2, 3, 2, 3, 3, 2, 1, 1, 3]
def baseStart_6354737 : Nat := 118140960795 + 6354737 * 2 ^ 59
def prefixEnd_6354737 : Nat := 4983230072969 + 3 ^ 40 * 6354737 * 2
def baseEnd_6354737 : Nat := 3263034513910608795962603

theorem tailTrace_6354737 : CollatzResearch.WordTrace tailWord_6354737 prefixEnd_6354737 3263034513910608795962603 := by
  unfold tailWord_6354737
  simp only [CollatzResearch.WordTrace]
  refine ⟨231776299578880626519350465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154517533052587084346233643 231776299578880626519350465)
  ·
    refine ⟨173832224684160469889512849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231776299578880626519350465 173832224684160469889512849)
    ·
      refine ⟨130374168513120352417134637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173832224684160469889512849 130374168513120352417134637)
      ·
        refine ⟨48890313192420132156425489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130374168513120352417134637 48890313192420132156425489)
        ·
          refine ⟨36667734894315099117319117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48890313192420132156425489 36667734894315099117319117)
          ·
            refine ⟨13750400585368162168994669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36667734894315099117319117 13750400585368162168994669)
            ·
              refine ⟨5156400219513060813373001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13750400585368162168994669 5156400219513060813373001)
              ·
                refine ⟨3867300164634795610029751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5156400219513060813373001 3867300164634795610029751)
                ·
                  refine ⟨5800950246952193415044627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867300164634795610029751 5800950246952193415044627)
                  ·
                    refine ⟨8701425370428290122566941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5800950246952193415044627 8701425370428290122566941)
                    ·
                      refine ⟨3263034513910608795962603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701425370428290122566941 3263034513910608795962603)
                      ·
                        rfl

theorem cell23_6354737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_6354737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354737 prefixEnd_6354737 := by exact prefixLift 6354737
  have htrace : WordTrace (prefixWord ++ tailWord_6354737) baseStart_6354737 baseEnd_6354737 := by
    simpa [prefixWord, tailWord_6354737, baseEnd_6354737] using wordTrace_append hprefix tailTrace_6354737
  have hstable : (prefixWord ++ tailWord_6354737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354737).length < 2 ^ (prefixWord ++ tailWord_6354737).sum := by decide
  have hdescent : baseEnd_6354737 < baseStart_6354737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354743 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_6354743 : Nat := 118140960795 + 6354743 * 2 ^ 59
def prefixEnd_6354743 : Nat := 4983230072969 + 3 ^ 40 * 6354743 * 2
def baseEnd_6354743 : Nat := 3263037594794535772487575

theorem tailTrace_6354743 : CollatzResearch.WordTrace tailWord_6354743 prefixEnd_6354743 3263037594794535772487575 := by
  unfold tailWord_6354743
  simp only [CollatzResearch.WordTrace]
  refine ⟨231776518416858889544068883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154517678944572593029379255 231776518416858889544068883)
  ·
    refine ⟨347664777625288334316103325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231776518416858889544068883 347664777625288334316103325)
    ·
      refine ⟨130374291609483125368538747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347664777625288334316103325 130374291609483125368538747)
      ·
        refine ⟨195561437414224688052808121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130374291609483125368538747 195561437414224688052808121)
        ·
          refine ⟨146671078060668516039606091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195561437414224688052808121 146671078060668516039606091)
          ·
            refine ⟨220006617091002774059409137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146671078060668516039606091 220006617091002774059409137)
            ·
              refine ⟨165004962818252080544556853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220006617091002774059409137 165004962818252080544556853)
              ·
                refine ⟨15469215264211132551052205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165004962818252080544556853 15469215264211132551052205)
                ·
                  refine ⟨5800955724079174706644577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15469215264211132551052205 5800955724079174706644577)
                  ·
                    refine ⟨4350716793059381029983433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5800955724079174706644577 4350716793059381029983433)
                    ·
                      refine ⟨3263037594794535772487575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350716793059381029983433 3263037594794535772487575)
                      ·
                        rfl

theorem cell23_6354743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_6354743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354743 prefixEnd_6354743 := by exact prefixLift 6354743
  have htrace : WordTrace (prefixWord ++ tailWord_6354743) baseStart_6354743 baseEnd_6354743 := by
    simpa [prefixWord, tailWord_6354743, baseEnd_6354743] using wordTrace_append hprefix tailTrace_6354743
  have hstable : (prefixWord ++ tailWord_6354743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354743).length < 2 ^ (prefixWord ++ tailWord_6354743).sum := by decide
  have hdescent : baseEnd_6354743 < baseStart_6354743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354746 : List Nat := [3, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_6354746 : Nat := 118140960795 + 6354746 * 2 ^ 59
def prefixEnd_6354746 : Nat := 4983230072969 + 3 ^ 40 * 6354746 * 2
def baseEnd_6354746 : Nat := 3263039135236499260750061

theorem tailTrace_6354746 : CollatzResearch.WordTrace tailWord_6354746 prefixEnd_6354746 3263039135236499260750061 := by
  unfold tailWord_6354746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57944156958962005264107023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154517751890565347370952061 57944156958962005264107023)
  ·
    refine ⟨86916235438443007896160535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57944156958962005264107023 86916235438443007896160535)
    ·
      refine ⟨130374353157664511844240803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86916235438443007896160535 130374353157664511844240803)
      ·
        refine ⟨195561529736496767766361205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130374353157664511844240803 195561529736496767766361205)
        ·
          refine ⟨18333893412796571978096363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 195561529736496767766361205 18333893412796571978096363)
          ·
            refine ⟨27500840119194857967144545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18333893412796571978096363 27500840119194857967144545)
            ·
              refine ⟨20625630089396143475358409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27500840119194857967144545 20625630089396143475358409)
              ·
                refine ⟨15469222567047107606518807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20625630089396143475358409 15469222567047107606518807)
                ·
                  refine ⟨23203833850570661409778211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469222567047107606518807 23203833850570661409778211)
                  ·
                    refine ⟨34805750775855992114667317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23203833850570661409778211 34805750775855992114667317)
                    ·
                      refine ⟨3263039135236499260750061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34805750775855992114667317 3263039135236499260750061)
                      ·
                        rfl

theorem cell23_6354746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_6354746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354746 prefixEnd_6354746 := by exact prefixLift 6354746
  have htrace : WordTrace (prefixWord ++ tailWord_6354746) baseStart_6354746 baseEnd_6354746 := by
    simpa [prefixWord, tailWord_6354746, baseEnd_6354746] using wordTrace_append hprefix tailTrace_6354746
  have hstable : (prefixWord ++ tailWord_6354746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354746).length < 2 ^ (prefixWord ++ tailWord_6354746).sum := by decide
  have hdescent : baseEnd_6354746 < baseStart_6354746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354780 : List Nat := [2, 2, 4, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6354780 : Nat := 118140960795 + 6354780 * 2 ^ 59
def prefixEnd_6354780 : Nat := 4983230072969 + 3 ^ 40 * 6354780 * 2
def baseEnd_6354780 : Nat := 3263056593578752127724905

theorem tailTrace_6354780 : CollatzResearch.WordTrace tailWord_6354780 prefixEnd_6354780 3263056593578752127724905 := by
  unfold tailWord_6354780
  simp only [CollatzResearch.WordTrace]
  refine ⟨115888933958862422431582897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154518578611816563242110529 115888933958862422431582897)
  ·
    refine ⟨86916700469146816823687173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115888933958862422431582897 86916700469146816823687173)
    ·
      refine ⟨16296881337965028154441345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86916700469146816823687173 16296881337965028154441345)
      ·
        refine ⟨12222661003473771115831009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16296881337965028154441345 12222661003473771115831009)
        ·
          refine ⟨9166995752605328336873257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12222661003473771115831009 9166995752605328336873257)
          ·
            refine ⟨6875246814453996252654943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9166995752605328336873257 6875246814453996252654943)
            ·
              refine ⟨10312870221680994378982415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875246814453996252654943 10312870221680994378982415)
              ·
                refine ⟨15469305332521491568473623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10312870221680994378982415 15469305332521491568473623)
                ·
                  refine ⟨23203957998782237352710435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469305332521491568473623 23203957998782237352710435)
                  ·
                    refine ⟨34805936998173356029065653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23203957998782237352710435 34805936998173356029065653)
                    ·
                      refine ⟨3263056593578752127724905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34805936998173356029065653 3263056593578752127724905)
                      ·
                        rfl

theorem cell23_6354780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6354780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354780 prefixEnd_6354780 := by exact prefixLift 6354780
  have htrace : WordTrace (prefixWord ++ tailWord_6354780) baseStart_6354780 baseEnd_6354780 := by
    simpa [prefixWord, tailWord_6354780, baseEnd_6354780] using wordTrace_append hprefix tailTrace_6354780
  have hstable : (prefixWord ++ tailWord_6354780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354780).length < 2 ^ (prefixWord ++ tailWord_6354780).sum := by decide
  have hdescent : baseEnd_6354780 < baseStart_6354780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354833 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 1, 4, 2]
def baseStart_6354833 : Nat := 118140960795 + 6354833 * 2 ^ 59
def prefixEnd_6354833 : Nat := 4983230072969 + 3 ^ 40 * 6354833 * 2
def baseEnd_6354833 : Nat := 3263083808053440420362161

theorem tailTrace_6354833 : CollatzResearch.WordTrace tailWord_6354833 prefixEnd_6354833 3263083808053440420362161 := by
  unfold tailWord_6354833
  simp only [CollatzResearch.WordTrace]
  refine ⟨231779800986532834914845153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154519867324355223276563435 231779800986532834914845153)
  ·
    refine ⟨173834850739899626186133865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231779800986532834914845153 173834850739899626186133865)
    ·
      refine ⟨130376138054924719639600399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173834850739899626186133865 130376138054924719639600399)
      ·
        refine ⟨195564207082387079459400599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130376138054924719639600399 195564207082387079459400599)
        ·
          refine ⟨293346310623580619189100899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195564207082387079459400599 293346310623580619189100899)
          ·
            refine ⟨440019465935370928783651349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293346310623580619189100899 440019465935370928783651349)
            ·
              refine ⟨20625912465720512286733657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440019465935370928783651349 20625912465720512286733657)
              ·
                refine ⟨15469434349290384215050243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20625912465720512286733657 15469434349290384215050243)
                ·
                  refine ⟨23204151523935576322575365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469434349290384215050243 23204151523935576322575365)
                  ·
                    refine ⟨4350778410737920560482881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23204151523935576322575365 4350778410737920560482881)
                    ·
                      refine ⟨3263083808053440420362161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350778410737920560482881 3263083808053440420362161)
                      ·
                        rfl

theorem cell23_6354833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_6354833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354833 prefixEnd_6354833 := by exact prefixLift 6354833
  have htrace : WordTrace (prefixWord ++ tailWord_6354833) baseStart_6354833 baseEnd_6354833 := by
    simpa [prefixWord, tailWord_6354833, baseEnd_6354833] using wordTrace_append hprefix tailTrace_6354833
  have hstable : (prefixWord ++ tailWord_6354833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354833).length < 2 ^ (prefixWord ++ tailWord_6354833).sum := by decide
  have hdescent : baseEnd_6354833 < baseStart_6354833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354859 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8]
def baseStart_6354859 : Nat := 118140960795 + 6354859 * 2 ^ 59
def prefixEnd_6354859 : Nat := 4983230072969 + 3 ^ 40 * 6354859 * 2
def baseEnd_6354859 : Nat := 3263097158550457318637041

theorem tailTrace_6354859 : CollatzResearch.WordTrace tailWord_6354859 prefixEnd_6354859 3263097158550457318637041 := by
  unfold tailWord_6354859
  simp only [CollatzResearch.WordTrace]
  refine ⟨231780749284438641355291631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154520499522959094236861087 231780749284438641355291631)
  ·
    refine ⟨347671123926657962032937447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231780749284438641355291631 347671123926657962032937447)
    ·
      refine ⟨521506685889986943049406171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347671123926657962032937447 521506685889986943049406171)
      ·
        refine ⟨782260028834980414574109257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521506685889986943049406171 782260028834980414574109257)
        ·
          refine ⟨586695021626235310930581943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782260028834980414574109257 586695021626235310930581943)
          ·
            refine ⟨880042532439352966395872915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586695021626235310930581943 880042532439352966395872915)
            ·
              refine ⟨1320063798659029449593809373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880042532439352966395872915 1320063798659029449593809373)
              ·
                refine ⟨495023924497136043597678515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1320063798659029449593809373 495023924497136043597678515)
                ·
                  refine ⟨742535886745704065396517773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495023924497136043597678515 742535886745704065396517773)
                  ·
                    refine ⟨278450957529639024523694165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742535886745704065396517773 278450957529639024523694165)
                    ·
                      refine ⟨3263097158550457318637041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278450957529639024523694165 3263097158550457318637041)
                      ·
                        rfl

theorem cell23_6354859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_6354859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354859 prefixEnd_6354859 := by exact prefixLift 6354859
  have htrace : WordTrace (prefixWord ++ tailWord_6354859) baseStart_6354859 baseEnd_6354859 := by
    simpa [prefixWord, tailWord_6354859, baseEnd_6354859] using wordTrace_append hprefix tailTrace_6354859
  have hstable : (prefixWord ++ tailWord_6354859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354859).length < 2 ^ (prefixWord ++ tailWord_6354859).sum := by decide
  have hdescent : baseEnd_6354859 < baseStart_6354859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354867 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 2, 2, 2]
def baseStart_6354867 : Nat := 118140960795 + 6354867 * 2 ^ 59
def prefixEnd_6354867 : Nat := 4983230072969 + 3 ^ 40 * 6354867 * 2
def baseEnd_6354867 : Nat := 3263101266395693287337005

theorem tailTrace_6354867 : CollatzResearch.WordTrace tailWord_6354867 prefixEnd_6354867 3263101266395693287337005 := by
  unfold tailWord_6354867
  simp only [CollatzResearch.WordTrace]
  refine ⟨231781041068409658721582855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154520694045606439147721903 231781041068409658721582855)
  ·
    refine ⟨347671561602614488082374283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231781041068409658721582855 347671561602614488082374283)
    ·
      refine ⟨521507342403921732123561425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347671561602614488082374283 521507342403921732123561425)
      ·
        refine ⟨391130506802941299092671069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521507342403921732123561425 391130506802941299092671069)
        ·
          refine ⟨146673940051102987159751651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391130506802941299092671069 146673940051102987159751651)
          ·
            refine ⟨220010910076654480739627477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146673940051102987159751651 220010910076654480739627477)
            ·
              refine ⟨5156505704921589392335019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 220010910076654480739627477 5156505704921589392335019)
              ·
                refine ⟨7734758557382384088502529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156505704921589392335019 7734758557382384088502529)
                ·
                  refine ⟨5801068918036788066376897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7734758557382384088502529 5801068918036788066376897)
                  ·
                    refine ⟨4350801688527591049782673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5801068918036788066376897 4350801688527591049782673)
                    ·
                      refine ⟨3263101266395693287337005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350801688527591049782673 3263101266395693287337005)
                      ·
                        rfl

theorem cell23_6354867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 2, 2, 2].length) (baseStart_6354867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354867 prefixEnd_6354867 := by exact prefixLift 6354867
  have htrace : WordTrace (prefixWord ++ tailWord_6354867) baseStart_6354867 baseEnd_6354867 := by
    simpa [prefixWord, tailWord_6354867, baseEnd_6354867] using wordTrace_append hprefix tailTrace_6354867
  have hstable : (prefixWord ++ tailWord_6354867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354867).length < 2 ^ (prefixWord ++ tailWord_6354867).sum := by decide
  have hdescent : baseEnd_6354867 < baseStart_6354867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354923 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 2, 4, 2]
def baseStart_6354923 : Nat := 118140960795 + 6354923 * 2 ^ 59
def prefixEnd_6354923 : Nat := 4983230072969 + 3 ^ 40 * 6354923 * 2
def baseEnd_6354923 : Nat := 3263130021312345068236747

theorem tailTrace_6354923 : CollatzResearch.WordTrace tailWord_6354923 prefixEnd_6354923 3263130021312345068236747 := by
  unfold tailWord_6354923
  simp only [CollatzResearch.WordTrace]
  refine ⟨231783083556206780285621423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154522055704137853523747615 231783083556206780285621423)
  ·
    refine ⟨347674625334310170428432135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231783083556206780285621423 347674625334310170428432135)
    ·
      refine ⟨521511938001465255642648203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347674625334310170428432135 521511938001465255642648203)
      ·
        refine ⟨782267907002197883463972305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521511938001465255642648203 782267907002197883463972305)
        ·
          refine ⟨586700930251648412597979229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782267907002197883463972305 586700930251648412597979229)
          ·
            refine ⟨220012848844368154724242211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 586700930251648412597979229 220012848844368154724242211)
            ·
              refine ⟨330019273266552232086363317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220012848844368154724242211 330019273266552232086363317)
              ·
                refine ⟨30939306868739271758096561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330019273266552232086363317 30939306868739271758096561)
                ·
                  refine ⟨23204480151554453818572421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30939306868739271758096561 23204480151554453818572421)
                  ·
                    refine ⟨4350840028416460090982329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23204480151554453818572421 4350840028416460090982329)
                    ·
                      refine ⟨3263130021312345068236747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350840028416460090982329 3263130021312345068236747)
                      ·
                        rfl

theorem cell23_6354923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 4, 2].length) (baseStart_6354923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354923 prefixEnd_6354923 := by exact prefixLift 6354923
  have htrace : WordTrace (prefixWord ++ tailWord_6354923) baseStart_6354923 baseEnd_6354923 := by
    simpa [prefixWord, tailWord_6354923, baseEnd_6354923] using wordTrace_append hprefix tailTrace_6354923
  have hstable : (prefixWord ++ tailWord_6354923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354923).length < 2 ^ (prefixWord ++ tailWord_6354923).sum := by decide
  have hdescent : baseEnd_6354923 < baseStart_6354923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354936 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_6354936 : Nat := 118140960795 + 6354936 * 2 ^ 59
def prefixEnd_6354936 : Nat := 4983230072969 + 3 ^ 40 * 6354936 * 2
def baseEnd_6354936 : Nat := 3263136696560853517374187

theorem tailTrace_6354936 : CollatzResearch.WordTrace tailWord_6354936 prefixEnd_6354936 3263136696560853517374187 := by
  unfold tailWord_6354936
  simp only [CollatzResearch.WordTrace]
  refine ⟨115891778852579841752922331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154522371803439789003896441 115891778852579841752922331)
  ·
    refine ⟨173837668278869762629383497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115891778852579841752922331 173837668278869762629383497)
    ·
      refine ⟨130378251209152321972037623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173837668278869762629383497 130378251209152321972037623)
      ·
        refine ⟨195567376813728482958056435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130378251209152321972037623 195567376813728482958056435)
        ·
          refine ⟨293351065220592724437084653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195567376813728482958056435 293351065220592724437084653)
          ·
            refine ⟨110006649457722271663906745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293351065220592724437084653 110006649457722271663906745)
            ·
              refine ⟨82504987093291703747930059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110006649457722271663906745 82504987093291703747930059)
              ·
                refine ⟨123757480639937555621895089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82504987093291703747930059 123757480639937555621895089)
                ·
                  refine ⟨92818110479953166716421317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123757480639937555621895089 92818110479953166716421317)
                  ·
                    refine ⟨17403395714991218759328997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92818110479953166716421317 17403395714991218759328997)
                    ·
                      refine ⟨3263136696560853517374187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17403395714991218759328997 3263136696560853517374187)
                      ·
                        rfl

theorem cell23_6354936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_6354936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354936 prefixEnd_6354936 := by exact prefixLift 6354936
  have htrace : WordTrace (prefixWord ++ tailWord_6354936) baseStart_6354936 baseEnd_6354936 := by
    simpa [prefixWord, tailWord_6354936, baseEnd_6354936] using wordTrace_append hprefix tailTrace_6354936
  have hstable : (prefixWord ++ tailWord_6354936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354936).length < 2 ^ (prefixWord ++ tailWord_6354936).sum := by decide
  have hdescent : baseEnd_6354936 < baseStart_6354936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6354993 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 3, 5]
def baseStart_6354993 : Nat := 118140960795 + 6354993 * 2 ^ 59
def prefixEnd_6354993 : Nat := 4983230072969 + 3 ^ 40 * 6354993 * 2
def baseEnd_6354993 : Nat := 1087721988319386598120475

theorem tailTrace_6354993 : CollatzResearch.WordTrace tailWord_6354993 prefixEnd_6354993 1087721988319386598120475 := by
  unfold tailWord_6354993
  simp only [CollatzResearch.WordTrace]
  refine ⟨231785636665953182240669633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154523757777302121493779755 231785636665953182240669633)
  ·
    refine ⟨173839227499464886680502225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231785636665953182240669633 173839227499464886680502225)
    ·
      refine ⟨130379420624598665010376669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173839227499464886680502225 130379420624598665010376669)
      ·
        refine ⟨48892282734224499378891251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130379420624598665010376669 48892282734224499378891251)
        ·
          refine ⟨73338424101336749068336877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48892282734224499378891251 73338424101336749068336877)
          ·
            refine ⟨27501909038001280900626329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73338424101336749068336877 27501909038001280900626329)
            ·
              refine ⟨20626431778500960675469747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27501909038001280900626329 20626431778500960675469747)
              ·
                refine ⟨30939647667751441013204621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20626431778500960675469747 30939647667751441013204621)
                ·
                  refine ⟨11602367875406790379951733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30939647667751441013204621 11602367875406790379951733)
                  ·
                    refine ⟨1087721988319386598120475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11602367875406790379951733 1087721988319386598120475)
                    ·
                      rfl

theorem cell23_6354993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 5].length) (baseStart_6354993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6354993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6354993 prefixEnd_6354993 := by exact prefixLift 6354993
  have htrace : WordTrace (prefixWord ++ tailWord_6354993) baseStart_6354993 baseEnd_6354993 := by
    simpa [prefixWord, tailWord_6354993, baseEnd_6354993] using wordTrace_append hprefix tailTrace_6354993
  have hstable : (prefixWord ++ tailWord_6354993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6354993).length < 2 ^ (prefixWord ++ tailWord_6354993).sum := by decide
  have hdescent : baseEnd_6354993 < baseStart_6354993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6354993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355007 : List Nat := [1, 1, 2, 2, 3, 1, 3, 5, 1, 1, 3]
def baseStart_6355007 : Nat := 118140960795 + 6355007 * 2 ^ 59
def prefixEnd_6355007 : Nat := 4983230072969 + 3 ^ 40 * 6355007 * 2
def baseEnd_6355007 : Nat := 3263173153687322739586361

theorem tailTrace_6355007 : CollatzResearch.WordTrace tailWord_6355007 prefixEnd_6355007 3263173153687322739586361 := by
  unfold tailWord_6355007
  simp only [CollatzResearch.WordTrace]
  refine ⟨231786147287902462631679275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154524098191934975087786183 231786147287902462631679275)
  ·
    refine ⟨347679220931853693947518913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231786147287902462631679275 347679220931853693947518913)
    ·
      refine ⟨260759415698890270460639185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347679220931853693947518913 260759415698890270460639185)
      ·
        refine ⟨195569561774167702845479389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260759415698890270460639185 195569561774167702845479389)
        ·
          refine ⟨73338585665312888567054771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195569561774167702845479389 73338585665312888567054771)
          ·
            refine ⟨110007878497969332850582157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73338585665312888567054771 110007878497969332850582157)
            ·
              refine ⟨41252954436738499818968309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110007878497969332850582157 41252954436738499818968309)
              ·
                refine ⟨3867464478444234358028279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41252954436738499818968309 3867464478444234358028279)
                ·
                  refine ⟨5801196717666351537042419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867464478444234358028279 5801196717666351537042419)
                  ·
                    refine ⟨8701795076499527305563629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5801196717666351537042419 8701795076499527305563629)
                    ·
                      refine ⟨3263173153687322739586361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701795076499527305563629 3263173153687322739586361)
                      ·
                        rfl

theorem cell23_6355007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_6355007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355007 prefixEnd_6355007 := by exact prefixLift 6355007
  have htrace : WordTrace (prefixWord ++ tailWord_6355007) baseStart_6355007 baseEnd_6355007 := by
    simpa [prefixWord, tailWord_6355007, baseEnd_6355007] using wordTrace_append hprefix tailTrace_6355007
  have hstable : (prefixWord ++ tailWord_6355007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355007).length < 2 ^ (prefixWord ++ tailWord_6355007).sum := by decide
  have hdescent : baseEnd_6355007 < baseStart_6355007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355023 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 4, 4]
def baseStart_6355023 : Nat := 118140960795 + 6355023 * 2 ^ 59
def prefixEnd_6355023 : Nat := 4983230072969 + 3 ^ 40 * 6355023 * 2
def baseEnd_6355023 : Nat := 1087727123125931558995429

theorem tailTrace_6355023 : CollatzResearch.WordTrace tailWord_6355023 prefixEnd_6355023 1087727123125931558995429 := by
  unfold tailWord_6355023
  simp only [CollatzResearch.WordTrace]
  refine ⟨231786730855844497364261723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154524487237229664909507815 231786730855844497364261723)
  ·
    refine ⟨347680096283766746046392585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231786730855844497364261723 347680096283766746046392585)
    ·
      refine ⟨260760072212825059534794439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347680096283766746046392585 260760072212825059534794439)
      ·
        refine ⟨391140108319237589302191659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260760072212825059534794439 391140108319237589302191659)
        ·
          refine ⟨586710162478856383953287489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391140108319237589302191659 586710162478856383953287489)
          ·
            refine ⟨440032621859142287964965617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586710162478856383953287489 440032621859142287964965617)
            ·
              refine ⟨330024466394356715973724213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440032621859142287964965617 330024466394356715973724213)
              ·
                refine ⟨30939793724470942122536645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 330024466394356715973724213 30939793724470942122536645)
                ·
                  refine ⟨5801211323338301647975621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30939793724470942122536645 5801211323338301647975621)
                  ·
                    refine ⟨1087727123125931558995429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801211323338301647975621 1087727123125931558995429)
                    ·
                      rfl

theorem cell23_6355023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_6355023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355023 prefixEnd_6355023 := by exact prefixLift 6355023
  have htrace : WordTrace (prefixWord ++ tailWord_6355023) baseStart_6355023 baseEnd_6355023 := by
    simpa [prefixWord, tailWord_6355023, baseEnd_6355023] using wordTrace_append hprefix tailTrace_6355023
  have hstable : (prefixWord ++ tailWord_6355023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355023).length < 2 ^ (prefixWord ++ tailWord_6355023).sum := by decide
  have hdescent : baseEnd_6355023 < baseStart_6355023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355033 : List Nat := [1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 5]
def baseStart_6355033 : Nat := 118140960795 + 6355033 * 2 ^ 59
def prefixEnd_6355033 : Nat := 4983230072969 + 3 ^ 40 * 6355033 * 2
def baseEnd_6355033 : Nat := 3263186504184339637861241

theorem tailTrace_6355033 : CollatzResearch.WordTrace tailWord_6355033 prefixEnd_6355033 3263186504184339637861241 := by
  unfold tailWord_6355033
  simp only [CollatzResearch.WordTrace]
  refine ⟨231787095585808269072125753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154524730390538846048083835 231787095585808269072125753)
  ·
    refine ⟨173840321689356201804094315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231787095585808269072125753 173840321689356201804094315)
    ·
      refine ⟨260760482534034302706141473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173840321689356201804094315 260760482534034302706141473)
      ·
        refine ⟨195570361900525727029606105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260760482534034302706141473 195570361900525727029606105)
        ·
          refine ⟨146677771425394295272204579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195570361900525727029606105 146677771425394295272204579)
          ·
            refine ⟨220016657138091442908306869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146677771425394295272204579 220016657138091442908306869)
            ·
              refine ⟨20626561606696072772653769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220016657138091442908306869 20626561606696072772653769)
              ·
                refine ⟨15469921205022054579490327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20626561606696072772653769 15469921205022054579490327)
                ·
                  refine ⟨23204881807533081869235491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469921205022054579490327 23204881807533081869235491)
                  ·
                    refine ⟨34807322711299622803853237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23204881807533081869235491 34807322711299622803853237)
                    ·
                      refine ⟨3263186504184339637861241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34807322711299622803853237 3263186504184339637861241)
                      ·
                        rfl

theorem cell23_6355033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_6355033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355033 prefixEnd_6355033 := by exact prefixLift 6355033
  have htrace : WordTrace (prefixWord ++ tailWord_6355033) baseStart_6355033 baseEnd_6355033 := by
    simpa [prefixWord, tailWord_6355033, baseEnd_6355033] using wordTrace_append hprefix tailTrace_6355033
  have hstable : (prefixWord ++ tailWord_6355033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355033).length < 2 ^ (prefixWord ++ tailWord_6355033).sum := by decide
  have hdescent : baseEnd_6355033 < baseStart_6355033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355040 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_6355040 : Nat := 118140960795 + 6355040 * 2 ^ 59
def prefixEnd_6355040 : Nat := 4983230072969 + 3 ^ 40 * 6355040 * 2
def baseEnd_6355040 : Nat := 1087730032849640370157903

theorem tailTrace_6355040 : CollatzResearch.WordTrace tailWord_6355040 prefixEnd_6355040 1087730032849640370157903 := by
  unfold tailWord_6355040
  simp only [CollatzResearch.WordTrace]
  refine ⟨115893675448391454633815287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154524900597855272845087049 115893675448391454633815287)
  ·
    refine ⟨173840513172587181950722931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115893675448391454633815287 173840513172587181950722931)
    ·
      refine ⟨260760769758880772926084397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173840513172587181950722931 260760769758880772926084397)
      ·
        refine ⟨97785288659580289847281649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260760769758880772926084397 97785288659580289847281649)
        ·
          refine ⟨73338966494685217385461237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97785288659580289847281649 73338966494685217385461237)
          ·
            refine ⟨6875528108876739129886991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73338966494685217385461237 6875528108876739129886991)
            ·
              refine ⟨10313292163315108694830487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875528108876739129886991 10313292163315108694830487)
              ·
                refine ⟨15469938244972663042245731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10313292163315108694830487 15469938244972663042245731)
                ·
                  refine ⟨23204907367458994563368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15469938244972663042245731 23204907367458994563368597)
                  ·
                    refine ⟨1087730032849640370157903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23204907367458994563368597 1087730032849640370157903)
                    ·
                      rfl

theorem cell23_6355040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_6355040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355040 prefixEnd_6355040 := by exact prefixLift 6355040
  have htrace : WordTrace (prefixWord ++ tailWord_6355040) baseStart_6355040 baseEnd_6355040 := by
    simpa [prefixWord, tailWord_6355040, baseEnd_6355040] using wordTrace_append hprefix tailTrace_6355040
  have hstable : (prefixWord ++ tailWord_6355040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355040).length < 2 ^ (prefixWord ++ tailWord_6355040).sum := by decide
  have hdescent : baseEnd_6355040 < baseStart_6355040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355047 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_6355047 : Nat := 118140960795 + 6355047 * 2 ^ 59
def prefixEnd_6355047 : Nat := 4983230072969 + 3 ^ 40 * 6355047 * 2
def baseEnd_6355047 : Nat := 3263193692913502583086177

theorem tailTrace_6355047 : CollatzResearch.WordTrace tailWord_6355047 prefixEnd_6355047 3263193692913502583086177 := by
  unfold tailWord_6355047
  simp only [CollatzResearch.WordTrace]
  refine ⟨231787606207757549463135395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154525070805171699642090263 231787606207757549463135395)
  ·
    refine ⟨347681409311636324194703093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231787606207757549463135395 347681409311636324194703093)
    ·
      refine ⟨32595132122965905393253415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 347681409311636324194703093 32595132122965905393253415)
      ·
        refine ⟨48892698184448858089880123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32595132122965905393253415 48892698184448858089880123)
        ·
          refine ⟨73339047276673287134820185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48892698184448858089880123 73339047276673287134820185)
          ·
            refine ⟨55004285457504965351115139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73339047276673287134820185 55004285457504965351115139)
            ·
              refine ⟨82506428186257448026672709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55004285457504965351115139 82506428186257448026672709)
              ·
                refine ⟨15469955284923271505001133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82506428186257448026672709 15469955284923271505001133)
                ·
                  refine ⟨5801233231846226814375425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15469955284923271505001133 5801233231846226814375425)
                  ·
                    refine ⟨4350924923884670110781569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5801233231846226814375425 4350924923884670110781569)
                    ·
                      refine ⟨3263193692913502583086177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350924923884670110781569 3263193692913502583086177)
                      ·
                        rfl

theorem cell23_6355047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_6355047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355047 prefixEnd_6355047 := by exact prefixLift 6355047
  have htrace : WordTrace (prefixWord ++ tailWord_6355047) baseStart_6355047 baseEnd_6355047 := by
    simpa [prefixWord, tailWord_6355047, baseEnd_6355047] using wordTrace_append hprefix tailTrace_6355047
  have hstable : (prefixWord ++ tailWord_6355047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355047).length < 2 ^ (prefixWord ++ tailWord_6355047).sum := by decide
  have hdescent : baseEnd_6355047 < baseStart_6355047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355053 : List Nat := [1, 5, 1, 1, 2, 1, 3, 9]
def baseStart_6355053 : Nat := 118140960795 + 6355053 * 2 ^ 59
def prefixEnd_6355053 : Nat := 4983230072969 + 3 ^ 40 * 6355053 * 2
def baseEnd_6355053 : Nat := 120859139770275168874487

theorem tailTrace_6355053 : CollatzResearch.WordTrace tailWord_6355053 prefixEnd_6355053 120859139770275168874487 := by
  unfold tailWord_6355053
  simp only [CollatzResearch.WordTrace]
  refine ⟨231787825045735812487853813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154525216697157208325235875 231787825045735812487853813)
  ·
    refine ⟨21730108598037732420736295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231787825045735812487853813 21730108598037732420736295)
    ·
      refine ⟨32595162897056598631104443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21730108598037732420736295 32595162897056598631104443)
      ·
        refine ⟨48892744345584897946656665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32595162897056598631104443 48892744345584897946656665)
        ·
          refine ⟨36669558259188673459992499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48892744345584897946656665 36669558259188673459992499)
          ·
            refine ⟨55004337388783010189988749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36669558259188673459992499 55004337388783010189988749)
            ·
              refine ⟨20626626520793628821245781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55004337388783010189988749 20626626520793628821245781)
              ·
                refine ⟨120859139770275168874487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20626626520793628821245781 120859139770275168874487)
                ·
                  rfl

theorem cell23_6355053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 9].length) (baseStart_6355053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355053 prefixEnd_6355053 := by exact prefixLift 6355053
  have htrace : WordTrace (prefixWord ++ tailWord_6355053) baseStart_6355053 baseEnd_6355053 := by
    simpa [prefixWord, tailWord_6355053, baseEnd_6355053] using wordTrace_append hprefix tailTrace_6355053
  have hstable : (prefixWord ++ tailWord_6355053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355053).length < 2 ^ (prefixWord ++ tailWord_6355053).sum := by decide
  have hdescent : baseEnd_6355053 < baseStart_6355053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355081 : List Nat := [1, 2, 1, 1, 4, 2, 5, 2, 1, 2, 2]
def baseStart_6355081 : Nat := 118140960795 + 6355081 * 2 ^ 59
def prefixEnd_6355081 : Nat := 4983230072969 + 3 ^ 40 * 6355081 * 2
def baseEnd_6355081 : Nat := 3263211151255755450061021

theorem tailTrace_6355081 : CollatzResearch.WordTrace tailWord_6355081 prefixEnd_6355081 3263211151255755450061021 := by
  unfold tailWord_6355081
  simp only [CollatzResearch.WordTrace]
  refine ⟨231788846289634373269873097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154525897526422915513248731 231788846289634373269873097)
  ·
    refine ⟨173841634717225779952404823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231788846289634373269873097 173841634717225779952404823)
    ·
      refine ⟨260762452075838669928607235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173841634717225779952404823 260762452075838669928607235)
      ·
        refine ⟨391143678113758004892910853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260762452075838669928607235 391143678113758004892910853)
        ·
          refine ⟨73339439646329625917420785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391143678113758004892910853 73339439646329625917420785)
          ·
            refine ⟨55004579734747219438065589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73339439646329625917420785 55004579734747219438065589)
            ·
              refine ⟨5156679350132551822318649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55004579734747219438065589 5156679350132551822318649)
              ·
                refine ⟨3867509512599413866738987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5156679350132551822318649 3867509512599413866738987)
                ·
                  refine ⟨5801264268899120800108481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867509512599413866738987 5801264268899120800108481)
                  ·
                    refine ⟨4350948201674340600081361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5801264268899120800108481 4350948201674340600081361)
                    ·
                      refine ⟨3263211151255755450061021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350948201674340600081361 3263211151255755450061021)
                      ·
                        rfl

theorem cell23_6355081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2, 1, 2, 2].length) (baseStart_6355081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355081 prefixEnd_6355081 := by exact prefixLift 6355081
  have htrace : WordTrace (prefixWord ++ tailWord_6355081) baseStart_6355081 baseEnd_6355081 := by
    simpa [prefixWord, tailWord_6355081, baseEnd_6355081] using wordTrace_append hprefix tailTrace_6355081
  have hstable : (prefixWord ++ tailWord_6355081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355081).length < 2 ^ (prefixWord ++ tailWord_6355081).sum := by decide
  have hdescent : baseEnd_6355081 < baseStart_6355081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355114 : List Nat := [3, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6355114 : Nat := 118140960795 + 6355114 * 2 ^ 59
def prefixEnd_6355114 : Nat := 4983230072969 + 3 ^ 40 * 6355114 * 2
def baseEnd_6355114 : Nat := 3263228096117353820948369

theorem tailTrace_6355114 : CollatzResearch.WordTrace tailWord_6355114 prefixEnd_6355114 3263228096117353820948369 := by
  unfold tailWord_6355114
  simp only [CollatzResearch.WordTrace]
  refine ⟨57947512474628704976456099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154526699932343213270549597 57947512474628704976456099)
  ·
    refine ⟨86921268711943057464684149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57947512474628704976456099 86921268711943057464684149)
    ·
      refine ⟨8148868941744661637314139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86921268711943057464684149 8148868941744661637314139)
      ·
        refine ⟨12223303412616992455971209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8148868941744661637314139 12223303412616992455971209)
        ·
          refine ⟨9167477559462744341978407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12223303412616992455971209 9167477559462744341978407)
          ·
            refine ⟨13751216339194116512967611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167477559462744341978407 13751216339194116512967611)
            ·
              refine ⟨20626824508791174769451417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751216339194116512967611 20626824508791174769451417)
              ·
                refine ⟨15470118381593381077088563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20626824508791174769451417 15470118381593381077088563)
                ·
                  refine ⟨23205177572390071615632845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15470118381593381077088563 23205177572390071615632845)
                  ·
                    refine ⟨8701941589646276855862317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23205177572390071615632845 8701941589646276855862317)
                    ·
                      refine ⟨3263228096117353820948369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701941589646276855862317 3263228096117353820948369)
                      ·
                        rfl

theorem cell23_6355114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6355114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355114 prefixEnd_6355114 := by exact prefixLift 6355114
  have htrace : WordTrace (prefixWord ++ tailWord_6355114) baseStart_6355114 baseEnd_6355114 := by
    simpa [prefixWord, tailWord_6355114, baseEnd_6355114] using wordTrace_append hprefix tailTrace_6355114
  have hstable : (prefixWord ++ tailWord_6355114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355114).length < 2 ^ (prefixWord ++ tailWord_6355114).sum := by decide
  have hdescent : baseEnd_6355114 < baseStart_6355114 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355118 : List Nat := [4, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6355118 : Nat := 118140960795 + 6355118 * 2 ^ 59
def prefixEnd_6355118 : Nat := 4983230072969 + 3 ^ 40 * 6355118 * 2
def baseEnd_6355118 : Nat := 3263230150039971805298351

theorem tailTrace_6355118 : CollatzResearch.WordTrace tailWord_6355118 prefixEnd_6355118 3263230150039971805298351 := by
  unfold tailWord_6355118
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973774473812541073621251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154526797193666885725980005 28973774473812541073621251)
  ·
    refine ⟨43460661710718811610431877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28973774473812541073621251 43460661710718811610431877)
    ·
      refine ⟨8148874070759777176955977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43460661710718811610431877 8148874070759777176955977)
      ·
        refine ⟨6111655553069832882716983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8148874070759777176955977 6111655553069832882716983)
        ·
          refine ⟨9167483329604749324075475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111655553069832882716983 9167483329604749324075475)
          ·
            refine ⟨13751224994407123986113213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167483329604749324075475 13751224994407123986113213)
            ·
              refine ⟨5156709372902671494792455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13751224994407123986113213 5156709372902671494792455)
              ·
                refine ⟨7735064059354007242188683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156709372902671494792455 7735064059354007242188683)
                ·
                  refine ⟨11602596089031010863283025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7735064059354007242188683 11602596089031010863283025)
                  ·
                    refine ⟨8701947066773258147462269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11602596089031010863283025 8701947066773258147462269)
                    ·
                      refine ⟨3263230150039971805298351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8701947066773258147462269 3263230150039971805298351)
                      ·
                        rfl

theorem cell23_6355118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6355118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355118 prefixEnd_6355118 := by exact prefixLift 6355118
  have htrace : WordTrace (prefixWord ++ tailWord_6355118) baseStart_6355118 baseEnd_6355118 := by
    simpa [prefixWord, tailWord_6355118, baseEnd_6355118] using wordTrace_append hprefix tailTrace_6355118
  have hstable : (prefixWord ++ tailWord_6355118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355118).length < 2 ^ (prefixWord ++ tailWord_6355118).sum := by decide
  have hdescent : baseEnd_6355118 < baseStart_6355118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355133 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_6355133 : Nat := 118140960795 + 6355133 * 2 ^ 59
def prefixEnd_6355133 : Nat := 4983230072969 + 3 ^ 40 * 6355133 * 2
def baseEnd_6355133 : Nat := 3263237852249789246610781

theorem tailTrace_6355133 : CollatzResearch.WordTrace tailWord_6355133 prefixEnd_6355133 3263237852249789246610781 := by
  unfold tailWord_6355133
  simp only [CollatzResearch.WordTrace]
  refine ⟨231790742885445986150766053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154527161923630657433844035 231790742885445986150766053)
  ·
    refine ⟨43460764291021122403268635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231790742885445986150766053 43460764291021122403268635)
    ·
      refine ⟨65191146436531683604902953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43460764291021122403268635 65191146436531683604902953)
      ·
        refine ⟨48893359827398762703677215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65191146436531683604902953 48893359827398762703677215)
        ·
          refine ⟨73340039741098144055515823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48893359827398762703677215 73340039741098144055515823)
          ·
            refine ⟨110010059611647216083273735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73340039741098144055515823 110010059611647216083273735)
            ·
              refine ⟨165015089417470824124910603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110010059611647216083273735 165015089417470824124910603)
              ·
                refine ⟨247522634126206236187365905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165015089417470824124910603 247522634126206236187365905)
                ·
                  refine ⟨185641975594654677140524429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247522634126206236187365905 185641975594654677140524429)
                  ·
                    refine ⟨69615740847995503927696661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 185641975594654677140524429 69615740847995503927696661)
                    ·
                      refine ⟨3263237852249789246610781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69615740847995503927696661 3263237852249789246610781)
                      ·
                        rfl

theorem cell23_6355133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_6355133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355133 prefixEnd_6355133 := by exact prefixLift 6355133
  have htrace : WordTrace (prefixWord ++ tailWord_6355133) baseStart_6355133 baseEnd_6355133 := by
    simpa [prefixWord, tailWord_6355133, baseEnd_6355133] using wordTrace_append hprefix tailTrace_6355133
  have hstable : (prefixWord ++ tailWord_6355133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355133).length < 2 ^ (prefixWord ++ tailWord_6355133).sum := by decide
  have hdescent : baseEnd_6355133 < baseStart_6355133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355150 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6355150 : Nat := 118140960795 + 6355150 * 2 ^ 59
def prefixEnd_6355150 : Nat := 4983230072969 + 3 ^ 40 * 6355150 * 2
def baseEnd_6355150 : Nat := 3263246581420915680098203

theorem tailTrace_6355150 : CollatzResearch.WordTrace tailWord_6355150 prefixEnd_6355150 3263246581420915680098203 := by
  unfold tailWord_6355150
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973920365798049756766863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154527575284256265369423269 28973920365798049756766863)
  ·
    refine ⟨43460880548697074635150295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28973920365798049756766863 43460880548697074635150295)
    ·
      refine ⟨65191320823045611952725443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43460880548697074635150295 65191320823045611952725443)
      ·
        refine ⟨97786981234568417929088165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65191320823045611952725443 97786981234568417929088165)
        ·
          refine ⟨18335058981481578361704031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97786981234568417929088165 18335058981481578361704031)
          ·
            refine ⟨27502588472222367542556047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18335058981481578361704031 27502588472222367542556047)
            ·
              refine ⟨41253882708333551313834071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27502588472222367542556047 41253882708333551313834071)
              ·
                refine ⟨61880824062500326970751107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41253882708333551313834071 61880824062500326970751107)
                ·
                  refine ⟨92821236093750490456126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61880824062500326970751107 92821236093750490456126661)
                  ·
                    refine ⟨17403981767578216960523749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92821236093750490456126661 17403981767578216960523749)
                    ·
                      refine ⟨3263246581420915680098203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17403981767578216960523749 3263246581420915680098203)
                      ·
                        rfl

theorem cell23_6355150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6355150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355150 prefixEnd_6355150 := by exact prefixLift 6355150
  have htrace : WordTrace (prefixWord ++ tailWord_6355150) baseStart_6355150 baseEnd_6355150 := by
    simpa [prefixWord, tailWord_6355150, baseEnd_6355150] using wordTrace_append hprefix tailTrace_6355150
  have hstable : (prefixWord ++ tailWord_6355150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355150).length < 2 ^ (prefixWord ++ tailWord_6355150).sum := by decide
  have hdescent : baseEnd_6355150 < baseStart_6355150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355154 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6355154 : Nat := 118140960795 + 6355154 * 2 ^ 59
def prefixEnd_6355154 : Nat := 4983230072969 + 3 ^ 40 * 6355154 * 2
def baseEnd_6355154 : Nat := 3263248635343533664448185

theorem tailTrace_6355154 : CollatzResearch.WordTrace tailWord_6355154 prefixEnd_6355154 3263248635343533664448185 := by
  unfold tailWord_6355154
  simp only [CollatzResearch.WordTrace]
  refine ⟨57947877204592476684320129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154527672545579937824853677 57947877204592476684320129)
  ·
    refine ⟨43460907903444357513240097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57947877204592476684320129 43460907903444357513240097)
    ·
      refine ⟨32595680927583268134930073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43460907903444357513240097 32595680927583268134930073)
      ·
        refine ⟨24446760695687451101197555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32595680927583268134930073 24446760695687451101197555)
        ·
          refine ⟨36670141043531176651796333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24446760695687451101197555 36670141043531176651796333)
          ·
            refine ⟨13751302891324191244423625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36670141043531176651796333 13751302891324191244423625)
            ·
              refine ⟨10313477168493143433317719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13751302891324191244423625 10313477168493143433317719)
              ·
                refine ⟨15470215752739715149976579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10313477168493143433317719 15470215752739715149976579)
                ·
                  refine ⟨23205323629109572724964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15470215752739715149976579 23205323629109572724964869)
                  ·
                    refine ⟨4350998180458044885930913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23205323629109572724964869 4350998180458044885930913)
                    ·
                      refine ⟨3263248635343533664448185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4350998180458044885930913 3263248635343533664448185)
                      ·
                        rfl

theorem cell23_6355154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6355154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355154 prefixEnd_6355154 := by exact prefixLift 6355154
  have htrace : WordTrace (prefixWord ++ tailWord_6355154) baseStart_6355154 baseEnd_6355154 := by
    simpa [prefixWord, tailWord_6355154, baseEnd_6355154] using wordTrace_append hprefix tailTrace_6355154
  have hstable : (prefixWord ++ tailWord_6355154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355154).length < 2 ^ (prefixWord ++ tailWord_6355154).sum := by decide
  have hdescent : baseEnd_6355154 < baseStart_6355154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355160 : List Nat := [2, 1, 2, 2, 4, 2, 1, 2, 7]
def baseStart_6355160 : Nat := 118140960795 + 6355160 * 2 ^ 59
def prefixEnd_6355160 : Nat := 4983230072969 + 3 ^ 40 * 6355160 * 2
def baseEnd_6355160 : Nat := 362583524025273404552573

theorem tailTrace_6355160 : CollatzResearch.WordTrace tailWord_6355160 prefixEnd_6355160 362583524025273404552573 := by
  unfold tailWord_6355160
  simp only [CollatzResearch.WordTrace]
  refine ⟨115895863828174084880999467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154527818437565446507999289 115895863828174084880999467)
  ·
    refine ⟨173843795742261127321499201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115895863828174084880999467 173843795742261127321499201)
    ·
      refine ⟨130382846806695845491124401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173843795742261127321499201 130382846806695845491124401)
      ·
        refine ⟨97787135105021884118343301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130382846806695845491124401 97787135105021884118343301)
        ·
          refine ⟨18335087832191603272189369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97787135105021884118343301 18335087832191603272189369)
          ·
            refine ⟨13751315874143702454142027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18335087832191603272189369 13751315874143702454142027)
            ·
              refine ⟨20626973811215553681213041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751315874143702454142027 20626973811215553681213041)
              ·
                refine ⟨15470230358411665260909781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20626973811215553681213041 15470230358411665260909781)
                ·
                  refine ⟨362583524025273404552573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15470230358411665260909781 362583524025273404552573)
                  ·
                    rfl

theorem cell23_6355160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_6355160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355160 prefixEnd_6355160 := by exact prefixLift 6355160
  have htrace : WordTrace (prefixWord ++ tailWord_6355160) baseStart_6355160 baseEnd_6355160 := by
    simpa [prefixWord, tailWord_6355160, baseEnd_6355160] using wordTrace_append hprefix tailTrace_6355160
  have hstable : (prefixWord ++ tailWord_6355160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355160).length < 2 ^ (prefixWord ++ tailWord_6355160).sum := by decide
  have hdescent : baseEnd_6355160 < baseStart_6355160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355210 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_6355210 : Nat := 118140960795 + 6355210 * 2 ^ 59
def prefixEnd_6355210 : Nat := 4983230072969 + 3 ^ 40 * 6355210 * 2
def baseEnd_6355210 : Nat := 3263277390260185445347927

theorem tailTrace_6355210 : CollatzResearch.WordTrace tailWord_6355210 prefixEnd_6355210 3263277390260185445347927 := by
  unfold tailWord_6355210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57948387826541757075329771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154529034204111352200879389 57948387826541757075329771)
  ·
    refine ⟨86922581739812635612994657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57948387826541757075329771 86922581739812635612994657)
    ·
      refine ⟨65191936304859476709745993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86922581739812635612994657 65191936304859476709745993)
      ·
        refine ⟨48893952228644607532309495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65191936304859476709745993 48893952228644607532309495)
        ·
          refine ⟨73340928342966911298464243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48893952228644607532309495 73340928342966911298464243)
          ·
            refine ⟨110011392514450366947696365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73340928342966911298464243 110011392514450366947696365)
            ·
              refine ⟨41254272192918887605386137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110011392514450366947696365 41254272192918887605386137)
              ·
                refine ⟨30940704144689165704039603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41254272192918887605386137 30940704144689165704039603)
                ·
                  refine ⟨46411056217033748556059405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30940704144689165704039603 46411056217033748556059405)
                  ·
                    refine ⟨17404146081387655708522277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46411056217033748556059405 17404146081387655708522277)
                    ·
                      refine ⟨3263277390260185445347927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17404146081387655708522277 3263277390260185445347927)
                      ·
                        rfl

theorem cell23_6355210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_6355210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355210 prefixEnd_6355210 := by exact prefixLift 6355210
  have htrace : WordTrace (prefixWord ++ tailWord_6355210) baseStart_6355210 baseEnd_6355210 := by
    simpa [prefixWord, tailWord_6355210, baseEnd_6355210] using wordTrace_append hprefix tailTrace_6355210
  have hstable : (prefixWord ++ tailWord_6355210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355210).length < 2 ^ (prefixWord ++ tailWord_6355210).sum := by decide
  have hdescent : baseEnd_6355210 < baseStart_6355210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355267 : List Nat := [1, 1, 1, 3, 1, 3, 6, 1, 6]
def baseStart_6355267 : Nat := 118140960795 + 6355267 * 2 ^ 59
def prefixEnd_6355267 : Nat := 4983230072969 + 3 ^ 40 * 6355267 * 2
def baseEnd_6355267 : Nat := 362589628739721302481685

theorem tailTrace_6355267 : CollatzResearch.WordTrace tailWord_6355267 prefixEnd_6355267 362589628739721302481685 := by
  unfold tailWord_6355267
  simp only [CollatzResearch.WordTrace]
  refine ⟨231795630266960527036144055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154530420177973684690762703 231795630266960527036144055)
  ·
    refine ⟨347693445400440790554216083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231795630266960527036144055 347693445400440790554216083)
    ·
      refine ⟨521540168100661185831324125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347693445400440790554216083 521540168100661185831324125)
      ·
        refine ⟨195577563037747944686746547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521540168100661185831324125 195577563037747944686746547)
        ·
          refine ⟨293366344556621917030119821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195577563037747944686746547 293366344556621917030119821)
          ·
            refine ⟨110012379208733218886294933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293366344556621917030119821 110012379208733218886294933)
            ·
              refine ⟨5156830275409369635295075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110012379208733218886294933 5156830275409369635295075)
              ·
                refine ⟨7735245413114054452942613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156830275409369635295075 7735245413114054452942613)
                ·
                  refine ⟨362589628739721302481685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7735245413114054452942613 362589628739721302481685)
                  ·
                    rfl

theorem cell23_6355267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 1, 6].length) (baseStart_6355267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355267 prefixEnd_6355267 := by exact prefixLift 6355267
  have htrace : WordTrace (prefixWord ++ tailWord_6355267) baseStart_6355267 baseEnd_6355267 := by
    simpa [prefixWord, tailWord_6355267, baseEnd_6355267] using wordTrace_append hprefix tailTrace_6355267
  have hstable : (prefixWord ++ tailWord_6355267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355267).length < 2 ^ (prefixWord ++ tailWord_6355267).sum := by decide
  have hdescent : baseEnd_6355267 < baseStart_6355267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355348 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6355348 : Nat := 118140960795 + 6355348 * 2 ^ 59
def prefixEnd_6355348 : Nat := 4983230072969 + 3 ^ 40 * 6355348 * 2
def baseEnd_6355348 : Nat := 1087782750196835301807431

theorem tailTrace_6355348 : CollatzResearch.WordTrace tailWord_6355348 prefixEnd_6355348 1087782750196835301807431 := by
  unfold tailWord_6355348
  simp only [CollatzResearch.WordTrace]
  refine ⟨115899292289833538934921349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154532389719778051913228465 115899292289833538934921349)
  ·
    refine ⟨21731117304343788550297753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115899292289833538934921349 21731117304343788550297753)
    ·
      refine ⟨16298337978257841412723315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21731117304343788550297753 16298337978257841412723315)
      ·
        refine ⟨24447506967386762119084973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16298337978257841412723315 24447506967386762119084973)
        ·
          refine ⟨9167815112770035794656865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24447506967386762119084973 9167815112770035794656865)
          ·
            refine ⟨6875861334577526845992649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167815112770035794656865 6875861334577526845992649)
            ·
              refine ⟨5156896000933145134494487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875861334577526845992649 5156896000933145134494487)
              ·
                refine ⟨7735344001399717701741731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5156896000933145134494487 7735344001399717701741731)
                ·
                  refine ⟨11603016002099576552612597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7735344001399717701741731 11603016002099576552612597)
                  ·
                    refine ⟨1087782750196835301807431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11603016002099576552612597 1087782750196835301807431)
                    ·
                      rfl

theorem cell23_6355348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6355348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355348 prefixEnd_6355348 := by exact prefixLift 6355348
  have htrace : WordTrace (prefixWord ++ tailWord_6355348) baseStart_6355348 baseEnd_6355348 := by
    simpa [prefixWord, tailWord_6355348, baseEnd_6355348] using wordTrace_append hprefix tailTrace_6355348
  have hstable : (prefixWord ++ tailWord_6355348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355348).length < 2 ^ (prefixWord ++ tailWord_6355348).sum := by decide
  have hdescent : baseEnd_6355348 < baseStart_6355348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355357 : List Nat := [1, 4, 2, 1, 4, 1, 10]
def baseStart_6355357 : Nat := 118140960795 + 6355357 * 2 ^ 59
def prefixEnd_6355357 : Nat := 4983230072969 + 3 ^ 40 * 6355357 * 2
def baseEnd_6355357 : Nat := 40288307060696251484071

theorem tailTrace_6355357 : CollatzResearch.WordTrace tailWord_6355357 prefixEnd_6355357 40288307060696251484071 := by
  unfold tailWord_6355357
  simp only [CollatzResearch.WordTrace]
  refine ⟨231798912836634472406920325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154532608557756314937946883 231798912836634472406920325)
  ·
    refine ⟨43462296156868963576297561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231798912836634472406920325 43462296156868963576297561)
    ·
      refine ⟨32596722117651722682223171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43462296156868963576297561 32596722117651722682223171)
      ·
        refine ⟨48895083176477584023334757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32596722117651722682223171 48895083176477584023334757)
        ·
          refine ⟨9167828095589547004375267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48895083176477584023334757 9167828095589547004375267)
          ·
            refine ⟨13751742143384320506562901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167828095589547004375267 13751742143384320506562901)
            ·
              refine ⟨40288307060696251484071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13751742143384320506562901 40288307060696251484071)
              ·
                rfl

theorem cell23_6355357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 10].length) (baseStart_6355357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355357 prefixEnd_6355357 := by exact prefixLift 6355357
  have htrace : WordTrace (prefixWord ++ tailWord_6355357) baseStart_6355357 baseEnd_6355357 := by
    simpa [prefixWord, tailWord_6355357, baseEnd_6355357] using wordTrace_append hprefix tailTrace_6355357
  have hstable : (prefixWord ++ tailWord_6355357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355357).length < 2 ^ (prefixWord ++ tailWord_6355357).sum := by decide
  have hdescent : baseEnd_6355357 < baseStart_6355357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355361 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 4, 4]
def baseStart_6355361 : Nat := 118140960795 + 6355361 * 2 ^ 59
def prefixEnd_6355361 : Nat := 4983230072969 + 3 ^ 40 * 6355361 * 2
def baseEnd_6355361 : Nat := 1087784975279671451519911

theorem tailTrace_6355361 : CollatzResearch.WordTrace tailWord_6355361 prefixEnd_6355361 1087784975279671451519911 := by
  unfold tailWord_6355361
  simp only [CollatzResearch.WordTrace]
  refine ⟨231799058728619981090065937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154532705819079987393377291 231799058728619981090065937)
  ·
    refine ⟨173849294046464985817549453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231799058728619981090065937 173849294046464985817549453)
    ·
      refine ⟨65193485267424369681581045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173849294046464985817549453 65193485267424369681581045)
      ·
        refine ⟨6111889243821034657648223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65193485267424369681581045 6111889243821034657648223)
        ·
          refine ⟨9167833865731551986472335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111889243821034657648223 9167833865731551986472335)
          ·
            refine ⟨13751750798597327979708503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167833865731551986472335 13751750798597327979708503)
            ·
              refine ⟨20627626197895991969562755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13751750798597327979708503 20627626197895991969562755)
              ·
                refine ⟨30941439296843987954344133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20627626197895991969562755 30941439296843987954344133)
                ·
                  refine ⟨5801519868158247741439525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30941439296843987954344133 5801519868158247741439525)
                  ·
                    refine ⟨1087784975279671451519911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801519868158247741439525 1087784975279671451519911)
                    ·
                      rfl

theorem cell23_6355361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_6355361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355361 prefixEnd_6355361 := by exact prefixLift 6355361
  have htrace : WordTrace (prefixWord ++ tailWord_6355361) baseStart_6355361 baseEnd_6355361 := by
    simpa [prefixWord, tailWord_6355361, baseEnd_6355361] using wordTrace_append hprefix tailTrace_6355361
  have hstable : (prefixWord ++ tailWord_6355361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355361).length < 2 ^ (prefixWord ++ tailWord_6355361).sum := by decide
  have hdescent : baseEnd_6355361 < baseStart_6355361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355368 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6355368 : Nat := 118140960795 + 6355368 * 2 ^ 59
def prefixEnd_6355368 : Nat := 4983230072969 + 3 ^ 40 * 6355368 * 2
def baseEnd_6355368 : Nat := 3263358520203595827172201

theorem tailTrace_6355368 : CollatzResearch.WordTrace tailWord_6355368 prefixEnd_6355368 3263358520203595827172201 := by
  unfold tailWord_6355368
  simp only [CollatzResearch.WordTrace]
  refine ⟨115899657019797310642785379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154532876026396414190380505 115899657019797310642785379)
  ·
    refine ⟨173849485529695965964178069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115899657019797310642785379 173849485529695965964178069)
    ·
      refine ⟨8149194634204498404570847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173849485529695965964178069 8149194634204498404570847)
      ·
        refine ⟨12223791951306747606856271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8149194634204498404570847 12223791951306747606856271)
        ·
          refine ⟨18335687926960121410284407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12223791951306747606856271 18335687926960121410284407)
          ·
            refine ⟨27503531890440182115426611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18335687926960121410284407 27503531890440182115426611)
            ·
              refine ⟨41255297835660273173139917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27503531890440182115426611 41255297835660273173139917)
              ·
                refine ⟨15470736688372602439927469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41255297835660273173139917 15470736688372602439927469)
                ·
                  refine ⟨5801526258139725914972801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15470736688372602439927469 5801526258139725914972801)
                  ·
                    refine ⟨4351144693604794436229601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5801526258139725914972801 4351144693604794436229601)
                    ·
                      refine ⟨3263358520203595827172201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351144693604794436229601 3263358520203595827172201)
                      ·
                        rfl

theorem cell23_6355368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6355368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355368 prefixEnd_6355368 := by exact prefixLift 6355368
  have htrace : WordTrace (prefixWord ++ tailWord_6355368) baseStart_6355368 baseEnd_6355368 := by
    simpa [prefixWord, tailWord_6355368, baseEnd_6355368] using wordTrace_append hprefix tailTrace_6355368
  have hstable : (prefixWord ++ tailWord_6355368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355368).length < 2 ^ (prefixWord ++ tailWord_6355368).sum := by decide
  have hdescent : baseEnd_6355368 < baseStart_6355368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355381 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_6355381 : Nat := 118140960795 + 6355381 * 2 ^ 59
def prefixEnd_6355381 : Nat := 4983230072969 + 3 ^ 40 * 6355381 * 2
def baseEnd_6355381 : Nat := 3263365195452104276309641

theorem tailTrace_6355381 : CollatzResearch.WordTrace tailWord_6355381 prefixEnd_6355381 3263365195452104276309641 := by
  unfold tailWord_6355381
  simp only [CollatzResearch.WordTrace]
  refine ⟨231799788188547524505793997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154533192125698349670529331 231799788188547524505793997)
  ·
    refine ⟨86924920570705321689672749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231799788188547524505793997 86924920570705321689672749)
    ·
      refine ⟨32596845214014495633627281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86924920570705321689672749 32596845214014495633627281)
      ·
        refine ⟨24447633910510871725220461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32596845214014495633627281 24447633910510871725220461)
        ·
          refine ⟨9167862716441576896957673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24447633910510871725220461 9167862716441576896957673)
          ·
            refine ⟨6875897037331182672718255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9167862716441576896957673 6875897037331182672718255)
            ·
              refine ⟨10313845555996774009077383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6875897037331182672718255 10313845555996774009077383)
              ·
                refine ⟨15470768333995161013616075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10313845555996774009077383 15470768333995161013616075)
                ·
                  refine ⟨23206152500992741520424113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15470768333995161013616075 23206152500992741520424113)
                  ·
                    refine ⟨17404614375744556140318085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23206152500992741520424113 17404614375744556140318085)
                    ·
                      refine ⟨3263365195452104276309641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17404614375744556140318085 3263365195452104276309641)
                      ·
                        rfl

theorem cell23_6355381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_6355381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355381 prefixEnd_6355381 := by exact prefixLift 6355381
  have htrace : WordTrace (prefixWord ++ tailWord_6355381) baseStart_6355381 baseEnd_6355381 := by
    simpa [prefixWord, tailWord_6355381, baseEnd_6355381] using wordTrace_append hprefix tailTrace_6355381
  have hstable : (prefixWord ++ tailWord_6355381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355381).length < 2 ^ (prefixWord ++ tailWord_6355381).sum := by decide
  have hdescent : baseEnd_6355381 < baseStart_6355381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355414 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6355414 : Nat := 118140960795 + 6355414 * 2 ^ 59
def prefixEnd_6355414 : Nat := 4983230072969 + 3 ^ 40 * 6355414 * 2
def baseEnd_6355414 : Nat := 3263382140313702647196989

theorem tailTrace_6355414 : CollatzResearch.WordTrace tailWord_6355414 prefixEnd_6355414 3263382140313702647196989 := by
  unfold tailWord_6355414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487561987339248196359081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154533994531618647427830197 14487561987339248196359081)
  ·
    refine ⟨10865671490504436147269311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14487561987339248196359081 10865671490504436147269311)
    ·
      refine ⟨16298507235756654220903967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865671490504436147269311 16298507235756654220903967)
      ·
        refine ⟨24447760853634981331355951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16298507235756654220903967 24447760853634981331355951)
        ·
          refine ⟨36671641280452471997033927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24447760853634981331355951 36671641280452471997033927)
          ·
            refine ⟨55007461920678707995550891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36671641280452471997033927 55007461920678707995550891)
            ·
              refine ⟨82511192881018061993326337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55007461920678707995550891 82511192881018061993326337)
              ·
                refine ⟨61883394660763546494994753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82511192881018061993326337 61883394660763546494994753)
                ·
                  refine ⟨46412545995572659871246065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61883394660763546494994753 46412545995572659871246065)
                  ·
                    refine ⟨34809409496679494903434549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46412545995572659871246065 34809409496679494903434549)
                    ·
                      refine ⟨3263382140313702647196989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34809409496679494903434549 3263382140313702647196989)
                      ·
                        rfl

theorem cell23_6355414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6355414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355414 prefixEnd_6355414 := by exact prefixLift 6355414
  have htrace : WordTrace (prefixWord ++ tailWord_6355414) baseStart_6355414 baseEnd_6355414 := by
    simpa [prefixWord, tailWord_6355414, baseEnd_6355414] using wordTrace_append hprefix tailTrace_6355414
  have hstable : (prefixWord ++ tailWord_6355414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355414).length < 2 ^ (prefixWord ++ tailWord_6355414).sum := by decide
  have hdescent : baseEnd_6355414 < baseStart_6355414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355464 : List Nat := [2, 1, 3, 2, 1, 1, 1, 7, 5]
def baseStart_6355464 : Nat := 118140960795 + 6355464 * 2 ^ 59
def prefixEnd_6355464 : Nat := 4983230072969 + 3 ^ 40 * 6355464 * 2
def baseEnd_6355464 : Nat := 362600868260714161285751

theorem tailTrace_6355464 : CollatzResearch.WordTrace tailWord_6355464 prefixEnd_6355464 362600868260714161285751 := by
  unfold tailWord_6355464
  simp only [CollatzResearch.WordTrace]
  refine ⟨115901407723623414840532723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154535210298164553120710297 115901407723623414840532723)
  ·
    refine ⟨173852111585435122260799085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115901407723623414840532723 173852111585435122260799085)
    ·
      refine ⟨65194541844538170847799657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173852111585435122260799085 65194541844538170847799657)
      ·
        refine ⟨48895906383403628135849743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65194541844538170847799657 48895906383403628135849743)
        ·
          refine ⟨73343859575105442203774615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48895906383403628135849743 73343859575105442203774615)
          ·
            refine ⟨110015789362658163305661923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73343859575105442203774615 110015789362658163305661923)
            ·
              refine ⟨165023684043987244958492885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110015789362658163305661923 165023684043987244958492885)
              ·
                refine ⟨3867742594780951053714677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165023684043987244958492885 3867742594780951053714677)
                ·
                  refine ⟨362600868260714161285751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3867742594780951053714677 362600868260714161285751)
                  ·
                    rfl

theorem cell23_6355464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 5].length) (baseStart_6355464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355464 prefixEnd_6355464 := by exact prefixLift 6355464
  have htrace : WordTrace (prefixWord ++ tailWord_6355464) baseStart_6355464 baseEnd_6355464 := by
    simpa [prefixWord, tailWord_6355464, baseEnd_6355464] using wordTrace_append hprefix tailTrace_6355464
  have hstable : (prefixWord ++ tailWord_6355464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355464).length < 2 ^ (prefixWord ++ tailWord_6355464).sum := by decide
  have hdescent : baseEnd_6355464 < baseStart_6355464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355514 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_6355514 : Nat := 118140960795 + 6355514 * 2 ^ 59
def prefixEnd_6355514 : Nat := 4983230072969 + 3 ^ 40 * 6355514 * 2
def baseEnd_6355514 : Nat := 3263433488379152255946529

theorem tailTrace_6355514 : CollatzResearch.WordTrace tailWord_6355514 prefixEnd_6355514 3263433488379152255946529 := by
  unfold tailWord_6355514
  simp only [CollatzResearch.WordTrace]
  refine ⟨57951159774266422055096399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154536426064710458813590397 57951159774266422055096399)
  ·
    refine ⟨86926739661399633082644599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57951159774266422055096399 86926739661399633082644599)
    ·
      refine ⟨130390109492099449623966899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86926739661399633082644599 130390109492099449623966899)
      ·
        refine ⟨195585164238149174435950349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130390109492099449623966899 195585164238149174435950349)
        ·
          refine ⟨73344436589305940413481381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195585164238149174435950349 73344436589305940413481381)
          ·
            refine ⟨13752081860494863827527759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73344436589305940413481381 13752081860494863827527759)
            ·
              refine ⟨20628122790742295741291639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752081860494863827527759 20628122790742295741291639)
              ·
                refine ⟨30942184186113443611937459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20628122790742295741291639 30942184186113443611937459)
                ·
                  refine ⟨46413276279170165417906189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30942184186113443611937459 46413276279170165417906189)
                  ·
                    refine ⟨17404978604688812031714821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46413276279170165417906189 17404978604688812031714821)
                    ·
                      refine ⟨3263433488379152255946529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17404978604688812031714821 3263433488379152255946529)
                      ·
                        rfl

theorem cell23_6355514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_6355514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355514 prefixEnd_6355514 := by exact prefixLift 6355514
  have htrace : WordTrace (prefixWord ++ tailWord_6355514) baseStart_6355514 baseEnd_6355514 := by
    simpa [prefixWord, tailWord_6355514, baseEnd_6355514] using wordTrace_append hprefix tailTrace_6355514
  have hstable : (prefixWord ++ tailWord_6355514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355514).length < 2 ^ (prefixWord ++ tailWord_6355514).sum := by decide
  have hdescent : baseEnd_6355514 < baseStart_6355514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355648 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 2, 4]
def baseStart_6355648 : Nat := 118140960795 + 6355648 * 2 ^ 59
def prefixEnd_6355648 : Nat := 4983230072969 + 3 ^ 40 * 6355648 * 2
def baseEnd_6355648 : Nat := 1087834098262284910556971

theorem tailTrace_6355648 : CollatzResearch.WordTrace tailWord_6355648 prefixEnd_6355648 1087834098262284910556971 := by
  unfold tailWord_6355648
  simp only [CollatzResearch.WordTrace]
  refine ⟨115904763239290114552881799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154539684319053486070509065 115904763239290114552881799)
  ·
    refine ⟨173857144858935171829322699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115904763239290114552881799 173857144858935171829322699)
    ·
      refine ⟨260785717288402757743984049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173857144858935171829322699 260785717288402757743984049)
      ·
        refine ⟨195589287966302068307988037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260785717288402757743984049 195589287966302068307988037)
        ·
          refine ⟨36672991493681637807747757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195589287966302068307988037 36672991493681637807747757)
          ·
            refine ⟨13752371810130614177905409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36672991493681637807747757 13752371810130614177905409)
            ·
              refine ⟨10314278857597960633429057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13752371810130614177905409 10314278857597960633429057)
              ·
                refine ⟨7735709143198470475071793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314278857597960633429057 7735709143198470475071793)
                ·
                  refine ⟨5801781857398852856303845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7735709143198470475071793 5801781857398852856303845)
                  ·
                    refine ⟨1087834098262284910556971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5801781857398852856303845 1087834098262284910556971)
                    ·
                      rfl

theorem cell23_6355648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 4].length) (baseStart_6355648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355648 prefixEnd_6355648 := by exact prefixLift 6355648
  have htrace : WordTrace (prefixWord ++ tailWord_6355648) baseStart_6355648 baseEnd_6355648 := by
    simpa [prefixWord, tailWord_6355648, baseEnd_6355648] using wordTrace_append hprefix tailTrace_6355648
  have hstable : (prefixWord ++ tailWord_6355648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355648).length < 2 ^ (prefixWord ++ tailWord_6355648).sum := by decide
  have hdescent : baseEnd_6355648 < baseStart_6355648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355649 : List Nat := [1, 2, 6, 2, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6355649 : Nat := 118140960795 + 6355649 * 2 ^ 59
def prefixEnd_6355649 : Nat := 4983230072969 + 3 ^ 40 * 6355649 * 2
def baseEnd_6355649 : Nat := 3263502808267509227758409

theorem tailTrace_6355649 : CollatzResearch.WordTrace tailWord_6355649 prefixEnd_6355649 3263502808267509227758409 := by
  unfold tailWord_6355649
  simp only [CollatzResearch.WordTrace]
  refine ⟨231809562951576606276550001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154539708634384404184366667 231809562951576606276550001)
  ·
    refine ⟨173857172213682454707412501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231809562951576606276550001 173857172213682454707412501)
    ·
      refine ⟨8149554947516365064409961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 173857172213682454707412501 8149554947516365064409961)
      ·
        refine ⟨6112166210637273798307471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8149554947516365064409961 6112166210637273798307471)
        ·
          refine ⟨9168249315955910697461207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112166210637273798307471 9168249315955910697461207)
          ·
            refine ⟨13752373973933866046191811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168249315955910697461207 13752373973933866046191811)
            ·
              refine ⟨20628560960900799069287717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752373973933866046191811 20628560960900799069287717)
              ·
                refine ⟨3867855180168899825491447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20628560960900799069287717 3867855180168899825491447)
                ·
                  refine ⟨5801782770253349738237171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3867855180168899825491447 5801782770253349738237171)
                  ·
                    refine ⟨8702674155380024607355757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5801782770253349738237171 8702674155380024607355757)
                    ·
                      refine ⟨3263502808267509227758409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8702674155380024607355757 3263502808267509227758409)
                      ·
                        rfl

theorem cell23_6355649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6355649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355649 prefixEnd_6355649 := by exact prefixLift 6355649
  have htrace : WordTrace (prefixWord ++ tailWord_6355649) baseStart_6355649 baseEnd_6355649 := by
    simpa [prefixWord, tailWord_6355649, baseEnd_6355649] using wordTrace_append hprefix tailTrace_6355649
  have hstable : (prefixWord ++ tailWord_6355649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355649).length < 2 ^ (prefixWord ++ tailWord_6355649).sum := by decide
  have hdescent : baseEnd_6355649 < baseStart_6355649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355671 : List Nat := [1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_6355671 : Nat := 118140960795 + 6355671 * 2 ^ 59
def prefixEnd_6355671 : Nat := 4983230072969 + 3 ^ 40 * 6355671 * 2
def baseEnd_6355671 : Nat := 3263514104841908141683307

theorem tailTrace_6355671 : CollatzResearch.WordTrace tailWord_6355671 prefixEnd_6355671 3263514104841908141683307 := by
  unfold tailWord_6355671
  simp only [CollatzResearch.WordTrace]
  refine ⟨231810365357496904033850867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154540243571664602689233911 231810365357496904033850867)
  ·
    refine ⟨347715548036245356050776301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231810365357496904033850867 347715548036245356050776301)
    ·
      refine ⟨130393330513592008519041113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347715548036245356050776301 130393330513592008519041113)
      ·
        refine ⟨97794997885194006389280835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130393330513592008519041113 97794997885194006389280835)
        ·
          refine ⟨146692496827791009583921253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97794997885194006389280835 146692496827791009583921253)
          ·
            refine ⟨27504843155210814296985235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146692496827791009583921253 27504843155210814296985235)
            ·
              refine ⟨41257264732816221445477853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27504843155210814296985235 41257264732816221445477853)
              ·
                refine ⟨15471474274806083042054195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41257264732816221445477853 15471474274806083042054195)
                ·
                  refine ⟨23207211412209124563081293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15471474274806083042054195 23207211412209124563081293)
                  ·
                    refine ⟨8702704279578421711155485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23207211412209124563081293 8702704279578421711155485)
                    ·
                      refine ⟨3263514104841908141683307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8702704279578421711155485 3263514104841908141683307)
                      ·
                        rfl

theorem cell23_6355671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_6355671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355671 prefixEnd_6355671 := by exact prefixLift 6355671
  have htrace : WordTrace (prefixWord ++ tailWord_6355671) baseStart_6355671 baseEnd_6355671 := by
    simpa [prefixWord, tailWord_6355671, baseEnd_6355671] using wordTrace_append hprefix tailTrace_6355671
  have hstable : (prefixWord ++ tailWord_6355671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355671).length < 2 ^ (prefixWord ++ tailWord_6355671).sum := by decide
  have hdescent : baseEnd_6355671 < baseStart_6355671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355674 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_6355674 : Nat := 118140960795 + 6355674 * 2 ^ 59
def prefixEnd_6355674 : Nat := 4983230072969 + 3 ^ 40 * 6355674 * 2
def baseEnd_6355674 : Nat := 1087838548427957209981931

theorem tailTrace_6355674 : CollatzResearch.WordTrace tailWord_6355674 prefixEnd_6355674 1087838548427957209981931 := by
  unfold tailWord_6355674
  simp only [CollatzResearch.WordTrace]
  refine ⟨57952618694121508886552519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154540316517657357030806717 57952618694121508886552519)
  ·
    refine ⟨86928928041182263329828779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57952618694121508886552519 86928928041182263329828779)
    ·
      refine ⟨130393392061773394994743169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86928928041182263329828779 130393392061773394994743169)
      ·
        refine ⟨97795044046330046246057377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130393392061773394994743169 97795044046330046246057377)
        ·
          refine ⟨73346283034747534684543033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97795044046330046246057377 73346283034747534684543033)
          ·
            refine ⟨55009712276060651013407275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73346283034747534684543033 55009712276060651013407275)
            ·
              refine ⟨82514568414090976520110913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55009712276060651013407275 82514568414090976520110913)
              ·
                refine ⟨61885926310568232390083185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82514568414090976520110913 61885926310568232390083185)
                ·
                  refine ⟨46414444732926174292562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61885926310568232390083185 46414444732926174292562389)
                  ·
                    refine ⟨1087838548427957209981931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46414444732926174292562389 1087838548427957209981931)
                    ·
                      rfl

theorem cell23_6355674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_6355674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355674 prefixEnd_6355674 := by exact prefixLift 6355674
  have htrace : WordTrace (prefixWord ++ tailWord_6355674) baseStart_6355674 baseEnd_6355674 := by
    simpa [prefixWord, tailWord_6355674, baseEnd_6355674] using wordTrace_append hprefix tailTrace_6355674
  have hstable : (prefixWord ++ tailWord_6355674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355674).length < 2 ^ (prefixWord ++ tailWord_6355674).sum := by decide
  have hdescent : baseEnd_6355674 < baseStart_6355674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355704 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_6355704 : Nat := 118140960795 + 6355704 * 2 ^ 59
def prefixEnd_6355704 : Nat := 4983230072969 + 3 ^ 40 * 6355704 * 2
def baseEnd_6355704 : Nat := 1087843683234502170856885

theorem tailTrace_6355704 : CollatzResearch.WordTrace tailWord_6355704 prefixEnd_6355704 1087843683234502170856885 := by
  unfold tailWord_6355704
  simp only [CollatzResearch.WordTrace]
  refine ⟨115905784483188675334901083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154541045977584900446534777 115905784483188675334901083)
  ·
    refine ⟨173858676724783013002351625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115905784483188675334901083 173858676724783013002351625)
    ·
      refine ⟨130394007543587259751763719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173858676724783013002351625 130394007543587259751763719)
      ·
        refine ⟨195591011315380889627645579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130394007543587259751763719 195591011315380889627645579)
        ·
          refine ⟨293386516973071334441468369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195591011315380889627645579 293386516973071334441468369)
          ·
            refine ⟨220039887729803500831101277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293386516973071334441468369 220039887729803500831101277)
            ·
              refine ⟨82514957898676312811662979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220039887729803500831101277 82514957898676312811662979)
              ·
                refine ⟨123772436848014469217494469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82514957898676312811662979 123772436848014469217494469)
                ·
                  refine ⟨23207331909002712978280213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123772436848014469217494469 23207331909002712978280213)
                  ·
                    refine ⟨1087843683234502170856885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23207331909002712978280213 1087843683234502170856885)
                    ·
                      rfl

theorem cell23_6355704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_6355704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355704 prefixEnd_6355704 := by exact prefixLift 6355704
  have htrace : WordTrace (prefixWord ++ tailWord_6355704) baseStart_6355704 baseEnd_6355704 := by
    simpa [prefixWord, tailWord_6355704, baseEnd_6355704] using wordTrace_append hprefix tailTrace_6355704
  have hstable : (prefixWord ++ tailWord_6355704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355704).length < 2 ^ (prefixWord ++ tailWord_6355704).sum := by decide
  have hdescent : baseEnd_6355704 < baseStart_6355704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355748 : List Nat := [2, 3, 1, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_6355748 : Nat := 118140960795 + 6355748 * 2 ^ 59
def prefixEnd_6355748 : Nat := 4983230072969 + 3 ^ 40 * 6355748 * 2
def baseEnd_6355748 : Nat := 3263553642852304340420453

theorem tailTrace_6355748 : CollatzResearch.WordTrace tailWord_6355748 prefixEnd_6355748 3263553642852304340420453 := by
  unfold tailWord_6355748
  simp only [CollatzResearch.WordTrace]
  refine ⟨115906586889108973092201949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154542115852145297456269265 115906586889108973092201949)
  ·
    refine ⟨43464970083415864909575731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115906586889108973092201949 43464970083415864909575731)
    ·
      refine ⟨65197455125123797364363597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43464970083415864909575731 65197455125123797364363597)
      ·
        refine ⟨24449045671921424011636349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65197455125123797364363597 24449045671921424011636349)
        ·
          refine ⟨9168392126970534004363631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24449045671921424011636349 9168392126970534004363631)
          ·
            refine ⟨13752588190455801006545447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168392126970534004363631 13752588190455801006545447)
            ·
              refine ⟨20628882285683701509818171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13752588190455801006545447 20628882285683701509818171)
              ·
                refine ⟨30943323428525552264727257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20628882285683701509818171 30943323428525552264727257)
                ·
                  refine ⟨23207492571394164198545443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30943323428525552264727257 23207492571394164198545443)
                  ·
                    refine ⟨34811238857091246297818165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23207492571394164198545443 34811238857091246297818165)
                    ·
                      refine ⟨3263553642852304340420453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34811238857091246297818165 3263553642852304340420453)
                      ·
                        rfl

theorem cell23_6355748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_6355748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355748 prefixEnd_6355748 := by exact prefixLift 6355748
  have htrace : WordTrace (prefixWord ++ tailWord_6355748) baseStart_6355748 baseEnd_6355748 := by
    simpa [prefixWord, tailWord_6355748, baseEnd_6355748] using wordTrace_append hprefix tailTrace_6355748
  have hstable : (prefixWord ++ tailWord_6355748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355748).length < 2 ^ (prefixWord ++ tailWord_6355748).sum := by decide
  have hdescent : baseEnd_6355748 < baseStart_6355748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355821 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6355821 : Nat := 118140960795 + 6355821 * 2 ^ 59
def prefixEnd_6355821 : Nat := 4983230072969 + 3 ^ 40 * 6355821 * 2
def baseEnd_6355821 : Nat := 3263591126940082554807617

theorem tailTrace_6355821 : CollatzResearch.WordTrace tailWord_6355821 prefixEnd_6355821 3263591126940082554807617 := by
  unfold tailWord_6355821
  simp only [CollatzResearch.WordTrace]
  refine ⟨231815836306953479651811317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154543890871302319767874211 231815836306953479651811317)
  ·
    refine ⟨21732734653776888717357311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231815836306953479651811317 21732734653776888717357311)
    ·
      refine ⟨32599101980665333076035967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21732734653776888717357311 32599101980665333076035967)
      ·
        refine ⟨48898652970997999614053951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32599101980665333076035967 48898652970997999614053951)
        ·
          refine ⟨73347979456496999421080927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48898652970997999614053951 73347979456496999421080927)
          ·
            refine ⟨110021969184745499131621391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73347979456496999421080927 110021969184745499131621391)
            ·
              refine ⟨165032953777118248697432087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110021969184745499131621391 165032953777118248697432087)
              ·
                refine ⟨247549430665677373046148131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165032953777118248697432087 247549430665677373046148131)
                ·
                  refine ⟨371324145998516059569222197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247549430665677373046148131 371324145998516059569222197)
                  ·
                    refine ⟨34811638687360880584614581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 371324145998516059569222197 34811638687360880584614581)
                    ·
                      refine ⟨3263591126940082554807617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34811638687360880584614581 3263591126940082554807617)
                      ·
                        rfl

theorem cell23_6355821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6355821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355821 prefixEnd_6355821 := by exact prefixLift 6355821
  have htrace : WordTrace (prefixWord ++ tailWord_6355821) baseStart_6355821 baseEnd_6355821 := by
    simpa [prefixWord, tailWord_6355821, baseEnd_6355821] using wordTrace_append hprefix tailTrace_6355821
  have hstable : (prefixWord ++ tailWord_6355821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355821).length < 2 ^ (prefixWord ++ tailWord_6355821).sum := by decide
  have hdescent : baseEnd_6355821 < baseStart_6355821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355891 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4]
def baseStart_6355891 : Nat := 118140960795 + 6355891 * 2 ^ 59
def prefixEnd_6355891 : Nat := 4983230072969 + 3 ^ 40 * 6355891 * 2
def baseEnd_6355891 : Nat := 3263627070585897280932295

theorem tailTrace_6355891 : CollatzResearch.WordTrace tailWord_6355891 prefixEnd_6355891 3263627070585897280932295 := by
  unfold tailWord_6355891
  simp only [CollatzResearch.WordTrace]
  refine ⟨231818389416699881606859527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154545592944466587737906351 231818389416699881606859527)
  ·
    refine ⟨347727584125049822410289291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231818389416699881606859527 347727584125049822410289291)
    ·
      refine ⟨521591376187574733615433937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347727584125049822410289291 521591376187574733615433937)
      ·
        refine ⟨391193532140681050211575453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521591376187574733615433937 391193532140681050211575453)
        ·
          refine ⟨146697574552755393829340795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391193532140681050211575453 146697574552755393829340795)
          ·
            refine ⟨220046361829133090744011193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146697574552755393829340795 220046361829133090744011193)
            ·
              refine ⟨165034771371849818058008395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220046361829133090744011193 165034771371849818058008395)
              ·
                refine ⟨247552157057774727087012593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165034771371849818058008395 247552157057774727087012593)
                ·
                  refine ⟨185664117793331045315259445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 247552157057774727087012593 185664117793331045315259445)
                  ·
                    refine ⟨17406011043124785498305573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 185664117793331045315259445 17406011043124785498305573)
                    ·
                      refine ⟨3263627070585897280932295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17406011043124785498305573 3263627070585897280932295)
                      ·
                        rfl

theorem cell23_6355891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_6355891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355891 prefixEnd_6355891 := by exact prefixLift 6355891
  have htrace : WordTrace (prefixWord ++ tailWord_6355891) baseStart_6355891 baseEnd_6355891 := by
    simpa [prefixWord, tailWord_6355891, baseEnd_6355891] using wordTrace_append hprefix tailTrace_6355891
  have hstable : (prefixWord ++ tailWord_6355891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355891).length < 2 ^ (prefixWord ++ tailWord_6355891).sum := by decide
  have hdescent : baseEnd_6355891 < baseStart_6355891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355919 : List Nat := [1, 1, 2, 1, 1, 8, 1, 3, 1, 1, 3]
def baseStart_6355919 : Nat := 118140960795 + 6355919 * 2 ^ 59
def prefixEnd_6355919 : Nat := 4983230072969 + 3 ^ 40 * 6355919 * 2
def baseEnd_6355919 : Nat := 3263641448044223171382167

theorem tailTrace_6355919 : CollatzResearch.WordTrace tailWord_6355919 prefixEnd_6355919 3263641448044223171382167 := by
  unfold tailWord_6355919
  simp only [CollatzResearch.WordTrace]
  refine ⟨231819410660598442388878811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154546273773732294925919207 231819410660598442388878811)
  ·
    refine ⟨347729115990897663583318217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231819410660598442388878811 347729115990897663583318217)
    ·
      refine ⟨260796836993173247687488663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347729115990897663583318217 260796836993173247687488663)
      ·
        refine ⟨391195255489759871531232995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260796836993173247687488663 391195255489759871531232995)
        ·
          refine ⟨586792883234639807296849493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391195255489759871531232995 586792883234639807296849493)
          ·
            refine ⟨6876479100405935241759955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 586792883234639807296849493 6876479100405935241759955)
            ·
              refine ⟨10314718650608902862639933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876479100405935241759955 10314718650608902862639933)
              ·
                refine ⟨3868019493978338573489975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10314718650608902862639933 3868019493978338573489975)
                ·
                  refine ⟨5802029240967507860234963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868019493978338573489975 5802029240967507860234963)
                  ·
                    refine ⟨8703043861451261790352445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802029240967507860234963 8703043861451261790352445)
                    ·
                      refine ⟨3263641448044223171382167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703043861451261790352445 3263641448044223171382167)
                      ·
                        rfl

theorem cell23_6355919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 1, 1, 3].length) (baseStart_6355919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355919 prefixEnd_6355919 := by exact prefixLift 6355919
  have htrace : WordTrace (prefixWord ++ tailWord_6355919) baseStart_6355919 baseEnd_6355919 := by
    simpa [prefixWord, tailWord_6355919, baseEnd_6355919] using wordTrace_append hprefix tailTrace_6355919
  have hstable : (prefixWord ++ tailWord_6355919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355919).length < 2 ^ (prefixWord ++ tailWord_6355919).sum := by decide
  have hdescent : baseEnd_6355919 < baseStart_6355919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355928 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_6355928 : Nat := 118140960795 + 6355928 * 2 ^ 59
def prefixEnd_6355928 : Nat := 4983230072969 + 3 ^ 40 * 6355928 * 2
def baseEnd_6355928 : Nat := 3263646069370113636169625

theorem tailTrace_6355928 : CollatzResearch.WordTrace tailWord_6355928 prefixEnd_6355928 3263646069370113636169625 := by
  unfold tailWord_6355928
  simp only [CollatzResearch.WordTrace]
  refine ⟨115909869458782918462978219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154546492611710557950637625 115909869458782918462978219)
  ·
    refine ⟨173864804188174377694467329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115909869458782918462978219 173864804188174377694467329)
    ·
      refine ⟨130398603141130783270850497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173864804188174377694467329 130398603141130783270850497)
      ·
        refine ⟨97798952355848087453137873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130398603141130783270850497 97798952355848087453137873)
        ·
          refine ⟨73349214266886065589853405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97798952355848087453137873 73349214266886065589853405)
          ·
            refine ⟨27505955350082274596195027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73349214266886065589853405 27505955350082274596195027)
            ·
              refine ⟨41258933025123411894292541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27505955350082274596195027 41258933025123411894292541)
              ·
                refine ⟨15472099884421279460359703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41258933025123411894292541 15472099884421279460359703)
                ·
                  refine ⟨23208149826631919190539555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15472099884421279460359703 23208149826631919190539555)
                  ·
                    refine ⟨34812224739947878785809333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23208149826631919190539555 34812224739947878785809333)
                    ·
                      refine ⟨3263646069370113636169625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34812224739947878785809333 3263646069370113636169625)
                      ·
                        rfl

theorem cell23_6355928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_6355928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355928 prefixEnd_6355928 := by exact prefixLift 6355928
  have htrace : WordTrace (prefixWord ++ tailWord_6355928) baseStart_6355928 baseEnd_6355928 := by
    simpa [prefixWord, tailWord_6355928, baseEnd_6355928] using wordTrace_append hprefix tailTrace_6355928
  have hstable : (prefixWord ++ tailWord_6355928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355928).length < 2 ^ (prefixWord ++ tailWord_6355928).sum := by decide
  have hdescent : baseEnd_6355928 < baseStart_6355928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355956 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6355956 : Nat := 118140960795 + 6355956 * 2 ^ 59
def prefixEnd_6355956 : Nat := 4983230072969 + 3 ^ 40 * 6355956 * 2
def baseEnd_6355956 : Nat := 1087886815609479842206499

theorem tailTrace_6355956 : CollatzResearch.WordTrace tailWord_6355956 prefixEnd_6355956 1087886815609479842206499 := by
  unfold tailWord_6355956
  simp only [CollatzResearch.WordTrace]
  refine ⟨115910380080732198853987861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154547173440976265138650481 115910380080732198853987861)
  ·
    refine ⟨5433299066284321821280681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115910380080732198853987861 5433299066284321821280681)
    ·
      refine ⟨4074974299713241365960511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433299066284321821280681 4074974299713241365960511)
      ·
        refine ⟨6112461449569862048940767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074974299713241365960511 6112461449569862048940767)
        ·
          refine ⟨9168692174354793073411151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112461449569862048940767 9168692174354793073411151)
          ·
            refine ⟨13753038261532189610116727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9168692174354793073411151 13753038261532189610116727)
            ·
              refine ⟨20629557392298284415175091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753038261532189610116727 20629557392298284415175091)
              ·
                refine ⟨30944336088447426622762637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20629557392298284415175091 30944336088447426622762637)
                ·
                  refine ⟨11604126033167784983535989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30944336088447426622762637 11604126033167784983535989)
                  ·
                    refine ⟨1087886815609479842206499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11604126033167784983535989 1087886815609479842206499)
                    ·
                      rfl

theorem cell23_6355956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6355956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355956 prefixEnd_6355956 := by exact prefixLift 6355956
  have htrace : WordTrace (prefixWord ++ tailWord_6355956) baseStart_6355956 baseEnd_6355956 := by
    simpa [prefixWord, tailWord_6355956, baseEnd_6355956] using wordTrace_append hprefix tailTrace_6355956
  have hstable : (prefixWord ++ tailWord_6355956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355956).length < 2 ^ (prefixWord ++ tailWord_6355956).sum := by decide
  have hdescent : baseEnd_6355956 < baseStart_6355956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355975 : List Nat := [1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_6355975 : Nat := 118140960795 + 6355975 * 2 ^ 59
def prefixEnd_6355975 : Nat := 4983230072969 + 3 ^ 40 * 6355975 * 2
def baseEnd_6355975 : Nat := 3263670202960874952281909

theorem tailTrace_6355975 : CollatzResearch.WordTrace tailWord_6355975 prefixEnd_6355975 3263670202960874952281909 := by
  unfold tailWord_6355975
  simp only [CollatzResearch.WordTrace]
  refine ⟨231821453148395563952917379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154547635432263709301944919 231821453148395563952917379)
  ·
    refine ⟨347732179722593345929376069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231821453148395563952917379 347732179722593345929376069)
    ·
      refine ⟨65199783697986252361758013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 347732179722593345929376069 65199783697986252361758013)
      ·
        refine ⟨24449918886744844635659255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65199783697986252361758013 24449918886744844635659255)
        ·
          refine ⟨36674878330117266953488883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24449918886744844635659255 36674878330117266953488883)
          ·
            refine ⟨55012317495175900430233325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36674878330117266953488883 55012317495175900430233325)
            ·
              refine ⟨20629619060690962661337497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55012317495175900430233325 20629619060690962661337497)
              ·
                refine ⟨15472214295518221996003123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20629619060690962661337497 15472214295518221996003123)
                ·
                  refine ⟨23208321443277332994004685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15472214295518221996003123 23208321443277332994004685)
                  ·
                    refine ⟨8703120541228999872751757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23208321443277332994004685 8703120541228999872751757)
                    ·
                      refine ⟨3263670202960874952281909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703120541228999872751757 3263670202960874952281909)
                      ·
                        rfl

theorem cell23_6355975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_6355975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355975 prefixEnd_6355975 := by exact prefixLift 6355975
  have htrace : WordTrace (prefixWord ++ tailWord_6355975) baseStart_6355975 baseEnd_6355975 := by
    simpa [prefixWord, tailWord_6355975, baseEnd_6355975] using wordTrace_append hprefix tailTrace_6355975
  have hstable : (prefixWord ++ tailWord_6355975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355975).length < 2 ^ (prefixWord ++ tailWord_6355975).sum := by decide
  have hdescent : baseEnd_6355975 < baseStart_6355975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6355992 : List Nat := [2, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_6355992 : Nat := 118140960795 + 6355992 * 2 ^ 59
def prefixEnd_6355992 : Nat := 4983230072969 + 3 ^ 40 * 6355992 * 2
def baseEnd_6355992 : Nat := 3263678932132001385769331

theorem tailTrace_6355992 : CollatzResearch.WordTrace tailWord_6355992 prefixEnd_6355992 3263678932132001385769331 := by
  unfold tailWord_6355992
  simp only [CollatzResearch.WordTrace]
  refine ⟨115911036594666987928143115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154548048792889317237524153 115911036594666987928143115)
  ·
    refine ⟨173866554892000481892214673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115911036594666987928143115 173866554892000481892214673)
    ·
      refine ⟨130399916169000361419161005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173866554892000481892214673 130399916169000361419161005)
      ·
        refine ⟨48899968563375135532185377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130399916169000361419161005 48899968563375135532185377)
        ·
          refine ⟨36674976422531351649139033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48899968563375135532185377 36674976422531351649139033)
          ·
            refine ⟨27506232316898513736854275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36674976422531351649139033 27506232316898513736854275)
            ·
              refine ⟨41259348475347770605281413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27506232316898513736854275 41259348475347770605281413)
              ·
                refine ⟨7736127839127706988490265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41259348475347770605281413 7736127839127706988490265)
                ·
                  refine ⟨5802095879345780241367699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736127839127706988490265 5802095879345780241367699)
                  ·
                    refine ⟨8703143819018670362051549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802095879345780241367699 8703143819018670362051549)
                    ·
                      refine ⟨3263678932132001385769331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703143819018670362051549 3263678932132001385769331)
                      ·
                        rfl

theorem cell23_6355992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_6355992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6355992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6355992 prefixEnd_6355992 := by exact prefixLift 6355992
  have htrace : WordTrace (prefixWord ++ tailWord_6355992) baseStart_6355992 baseEnd_6355992 := by
    simpa [prefixWord, tailWord_6355992, baseEnd_6355992] using wordTrace_append hprefix tailTrace_6355992
  have hstable : (prefixWord ++ tailWord_6355992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6355992).length < 2 ^ (prefixWord ++ tailWord_6355992).sum := by decide
  have hdescent : baseEnd_6355992 < baseStart_6355992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6355992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356002 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_6356002 : Nat := 118140960795 + 6356002 * 2 ^ 59
def prefixEnd_6356002 : Nat := 4983230072969 + 3 ^ 40 * 6356002 * 2
def baseEnd_6356002 : Nat := 3263684066938546346644285

theorem tailTrace_6356002 : CollatzResearch.WordTrace tailWord_6356002 prefixEnd_6356002 3263684066938546346644285 := by
  unfold tailWord_6356002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57955609479824436891037565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154548291946198498376100173 57955609479824436891037565)
  ·
    refine ⟨21733353554934163834139087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57955609479824436891037565 21733353554934163834139087)
    ·
      refine ⟨32600030332401245751208631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21733353554934163834139087 32600030332401245751208631)
      ·
        refine ⟨48900045498601868626812947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32600030332401245751208631 48900045498601868626812947)
        ·
          refine ⟨73350068247902802940219421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48900045498601868626812947 73350068247902802940219421)
          ·
            refine ⟨27506275592963551102582283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73350068247902802940219421 27506275592963551102582283)
            ·
              refine ⟨41259413389445326653873425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27506275592963551102582283 41259413389445326653873425)
              ·
                refine ⟨30944560042083994990405069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41259413389445326653873425 30944560042083994990405069)
                ·
                  refine ⟨11604210015781498121401901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30944560042083994990405069 11604210015781498121401901)
                  ·
                    refine ⟨4351578755918061795525713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11604210015781498121401901 4351578755918061795525713)
                    ·
                      refine ⟨3263684066938546346644285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351578755918061795525713 3263684066938546346644285)
                      ·
                        rfl

theorem cell23_6356002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_6356002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356002 prefixEnd_6356002 := by exact prefixLift 6356002
  have htrace : WordTrace (prefixWord ++ tailWord_6356002) baseStart_6356002 baseEnd_6356002 := by
    simpa [prefixWord, tailWord_6356002, baseEnd_6356002] using wordTrace_append hprefix tailTrace_6356002
  have hstable : (prefixWord ++ tailWord_6356002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356002).length < 2 ^ (prefixWord ++ tailWord_6356002).sum := by decide
  have hdescent : baseEnd_6356002 < baseStart_6356002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356032 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2]
def baseStart_6356032 : Nat := 118140960795 + 6356032 * 2 ^ 59
def prefixEnd_6356032 : Nat := 4983230072969 + 3 ^ 40 * 6356032 * 2
def baseEnd_6356032 : Nat := 3263699471358181229269147

theorem tailTrace_6356032 : CollatzResearch.WordTrace tailWord_6356032 prefixEnd_6356032 3263699471358181229269147 := by
  unfold tailWord_6356032
  simp only [CollatzResearch.WordTrace]
  refine ⟨115911766054594531343871175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154549021406126041791828233 115911766054594531343871175)
  ·
    refine ⟨173867649081891797015806763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115911766054594531343871175 173867649081891797015806763)
    ·
      refine ⟨260801473622837695523710145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173867649081891797015806763 260801473622837695523710145)
      ·
        refine ⟨195601105217128271642782609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260801473622837695523710145 195601105217128271642782609)
        ·
          refine ⟨146700828912846203732086957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195601105217128271642782609 146700828912846203732086957)
          ·
            refine ⟨55012810842317326399532609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146700828912846203732086957 55012810842317326399532609)
            ·
              refine ⟨41259608131737994799649457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55012810842317326399532609 41259608131737994799649457)
              ·
                refine ⟨30944706098803496099737093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41259608131737994799649457 30944706098803496099737093)
                ·
                  refine ⟨5802132393525655518700705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30944706098803496099737093 5802132393525655518700705)
                  ·
                    refine ⟨4351599295144241639025529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802132393525655518700705 4351599295144241639025529)
                    ·
                      refine ⟨3263699471358181229269147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351599295144241639025529 3263699471358181229269147)
                      ·
                        rfl

theorem cell23_6356032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_6356032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356032 prefixEnd_6356032 := by exact prefixLift 6356032
  have htrace : WordTrace (prefixWord ++ tailWord_6356032) baseStart_6356032 baseEnd_6356032 := by
    simpa [prefixWord, tailWord_6356032, baseEnd_6356032] using wordTrace_append hprefix tailTrace_6356032
  have hstable : (prefixWord ++ tailWord_6356032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356032).length < 2 ^ (prefixWord ++ tailWord_6356032).sum := by decide
  have hdescent : baseEnd_6356032 < baseStart_6356032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356049 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_6356049 : Nat := 118140960795 + 6356049 * 2 ^ 59
def prefixEnd_6356049 : Nat := 4983230072969 + 3 ^ 40 * 6356049 * 2
def baseEnd_6356049 : Nat := 3263708200529307662756569

theorem tailTrace_6356049 : CollatzResearch.WordTrace tailWord_6356049 prefixEnd_6356049 3263708200529307662756569 := by
  unfold tailWord_6356049
  simp only [CollatzResearch.WordTrace]
  refine ⟨231824152150127474591111201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154549434766751649727407467 231824152150127474591111201)
  ·
    refine ⟨173868114112595605943333401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231824152150127474591111201 173868114112595605943333401)
    ·
      refine ⟨130401085584446704457500051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173868114112595605943333401 130401085584446704457500051)
      ·
        refine ⟨195601628376670056686250077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130401085584446704457500051 195601628376670056686250077)
        ·
          refine ⟨73350610641251271257343779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195601628376670056686250077 73350610641251271257343779)
          ·
            refine ⟨110025915961876906886015669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73350610641251271257343779 110025915961876906886015669)
            ·
              refine ⟨10314929621425960020563969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110025915961876906886015669 10314929621425960020563969)
              ·
                refine ⟨7736197216069470015422977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314929621425960020563969 7736197216069470015422977)
                ·
                  refine ⟨5802147912052102511567233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736197216069470015422977 5802147912052102511567233)
                  ·
                    refine ⟨4351610934039076883675425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802147912052102511567233 4351610934039076883675425)
                    ·
                      refine ⟨3263708200529307662756569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351610934039076883675425 3263708200529307662756569)
                      ·
                        rfl

theorem cell23_6356049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_6356049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356049 prefixEnd_6356049 := by exact prefixLift 6356049
  have htrace : WordTrace (prefixWord ++ tailWord_6356049) baseStart_6356049 baseEnd_6356049 := by
    simpa [prefixWord, tailWord_6356049, baseEnd_6356049] using wordTrace_append hprefix tailTrace_6356049
  have hstable : (prefixWord ++ tailWord_6356049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356049).length < 2 ^ (prefixWord ++ tailWord_6356049).sum := by decide
  have hdescent : baseEnd_6356049 < baseStart_6356049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356065 : List Nat := [1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_6356065 : Nat := 118140960795 + 6356065 * 2 ^ 59
def prefixEnd_6356065 : Nat := 4983230072969 + 3 ^ 40 * 6356065 * 2
def baseEnd_6356065 : Nat := 3263716416219779600156495

theorem tailTrace_6356065 : CollatzResearch.WordTrace tailWord_6356065 prefixEnd_6356065 3263716416219779600156495 := by
  unfold tailWord_6356065
  simp only [CollatzResearch.WordTrace]
  refine ⟨231824735718069509323693649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154549823812046339549129099 231824735718069509323693649)
  ·
    refine ⟨173868551788552131992770237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231824735718069509323693649 173868551788552131992770237)
    ·
      refine ⟨65200706920707049497288839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173868551788552131992770237 65200706920707049497288839)
      ·
        refine ⟨97801060381060574245933259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65200706920707049497288839 97801060381060574245933259)
        ·
          refine ⟨146701590571590861368899889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97801060381060574245933259 146701590571590861368899889)
          ·
            refine ⟨110026192928693146026674917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146701590571590861368899889 110026192928693146026674917)
            ·
              refine ⟨20629911174129964880001547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110026192928693146026674917 20629911174129964880001547)
              ·
                refine ⟨30944866761194947320002321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20629911174129964880001547 30944866761194947320002321)
                ·
                  refine ⟨23208650070896210490001741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30944866761194947320002321 23208650070896210490001741)
                  ·
                    refine ⟨8703243776586078933750653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23208650070896210490001741 8703243776586078933750653)
                    ·
                      refine ⟨3263716416219779600156495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703243776586078933750653 3263716416219779600156495)
                      ·
                        rfl

theorem cell23_6356065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_6356065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356065 prefixEnd_6356065 := by exact prefixLift 6356065
  have htrace : WordTrace (prefixWord ++ tailWord_6356065) baseStart_6356065 baseEnd_6356065 := by
    simpa [prefixWord, tailWord_6356065, baseEnd_6356065] using wordTrace_append hprefix tailTrace_6356065
  have hstable : (prefixWord ++ tailWord_6356065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356065).length < 2 ^ (prefixWord ++ tailWord_6356065).sum := by decide
  have hdescent : baseEnd_6356065 < baseStart_6356065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356066 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6356066 : Nat := 118140960795 + 6356066 * 2 ^ 59
def prefixEnd_6356066 : Nat := 4983230072969 + 3 ^ 40 * 6356066 * 2
def baseEnd_6356066 : Nat := 3263716929700434096243991

theorem tailTrace_6356066 : CollatzResearch.WordTrace tailWord_6356066 prefixEnd_6356066 3263716929700434096243991 := by
  unfold tailWord_6356066
  simp only [CollatzResearch.WordTrace]
  refine ⟨57956193047766471623620013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154549848127377257662986701 57956193047766471623620013)
  ·
    refine ⟨21733572392912426858857505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57956193047766471623620013 21733572392912426858857505)
    ·
      refine ⟨16300179294684320144143129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21733572392912426858857505 16300179294684320144143129)
      ·
        refine ⟨12225134471013240108107347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16300179294684320144143129 12225134471013240108107347)
        ·
          refine ⟨18337701706519860162161021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225134471013240108107347 18337701706519860162161021)
          ·
            refine ⟨6876638139944947560810383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18337701706519860162161021 6876638139944947560810383)
            ·
              refine ⟨10314957209917421341215575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876638139944947560810383 10314957209917421341215575)
              ·
                refine ⟨15472435814876132011823363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10314957209917421341215575 15472435814876132011823363)
                ·
                  refine ⟨23208653722314198017735045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15472435814876132011823363 23208653722314198017735045)
                  ·
                    refine ⟨4351622572933912128325321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23208653722314198017735045 4351622572933912128325321)
                    ·
                      refine ⟨3263716929700434096243991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351622572933912128325321 3263716929700434096243991)
                      ·
                        rfl

theorem cell23_6356066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6356066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356066 prefixEnd_6356066 := by exact prefixLift 6356066
  have htrace : WordTrace (prefixWord ++ tailWord_6356066) baseStart_6356066 baseEnd_6356066 := by
    simpa [prefixWord, tailWord_6356066, baseEnd_6356066] using wordTrace_append hprefix tailTrace_6356066
  have hstable : (prefixWord ++ tailWord_6356066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356066).length < 2 ^ (prefixWord ++ tailWord_6356066).sum := by decide
  have hdescent : baseEnd_6356066 < baseStart_6356066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356089 : List Nat := [1, 2, 1, 3, 5, 2, 1, 3, 5]
def baseStart_6356089 : Nat := 118140960795 + 6356089 * 2 ^ 59
def prefixEnd_6356089 : Nat := 4983230072969 + 3 ^ 40 * 6356089 * 2
def baseEnd_6356089 : Nat := 362636526639498611806265

theorem tailTrace_6356089 : CollatzResearch.WordTrace tailWord_6356089 prefixEnd_6356089 362636526639498611806265 := by
  unfold tailWord_6356089
  simp only [CollatzResearch.WordTrace]
  refine ⟨231825611069982561422567321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154550407379988374281711547 231825611069982561422567321)
  ·
    refine ⟨173869208302486921066925491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231825611069982561422567321 173869208302486921066925491)
    ·
      refine ⟨260803812453730381600388237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173869208302486921066925491 260803812453730381600388237)
      ·
        refine ⟨97801429670148893100145589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 260803812453730381600388237 97801429670148893100145589)
        ·
          refine ⟨9168884031576458728138649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97801429670148893100145589 9168884031576458728138649)
          ·
            refine ⟨6876663023682344046103987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9168884031576458728138649 6876663023682344046103987)
            ·
              refine ⟨10314994535523516069155981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6876663023682344046103987 10314994535523516069155981)
              ·
                refine ⟨3868122950821318525933493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10314994535523516069155981 3868122950821318525933493)
                ·
                  refine ⟨362636526639498611806265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868122950821318525933493 362636526639498611806265)
                  ·
                    rfl

theorem cell23_6356089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 3, 5].length) (baseStart_6356089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356089 prefixEnd_6356089 := by exact prefixLift 6356089
  have htrace : WordTrace (prefixWord ++ tailWord_6356089) baseStart_6356089 baseEnd_6356089 := by
    simpa [prefixWord, tailWord_6356089, baseEnd_6356089] using wordTrace_append hprefix tailTrace_6356089
  have hstable : (prefixWord ++ tailWord_6356089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356089).length < 2 ^ (prefixWord ++ tailWord_6356089).sum := by decide
  have hdescent : baseEnd_6356089 < baseStart_6356089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356105 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 4]
def baseStart_6356105 : Nat := 118140960795 + 6356105 * 2 ^ 59
def prefixEnd_6356105 : Nat := 4983230072969 + 3 ^ 40 * 6356105 * 2
def baseEnd_6356105 : Nat := 3263736955445959443656311

theorem tailTrace_6356105 : CollatzResearch.WordTrace tailWord_6356105 prefixEnd_6356105 3263736955445959443656311 := by
  unfold tailWord_6356105
  simp only [CollatzResearch.WordTrace]
  refine ⟨231826194637924596155149769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154550796425283064103433179 231826194637924596155149769)
  ·
    refine ⟨173869645978443447116362327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231826194637924596155149769 173869645978443447116362327)
    ·
      refine ⟨260804468967665170674543491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173869645978443447116362327 260804468967665170674543491)
      ·
        refine ⟨391206703451497756011815237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260804468967665170674543491 391206703451497756011815237)
        ·
          refine ⟨73351256897155829252215357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 391206703451497756011815237 73351256897155829252215357)
          ·
            refine ⟨27506721336433435969580759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73351256897155829252215357 27506721336433435969580759)
            ·
              refine ⟨41260082004650153954371139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27506721336433435969580759 41260082004650153954371139)
              ·
                refine ⟨61890123006975230931556709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41260082004650153954371139 61890123006975230931556709)
                ·
                  refine ⟨11604398063807855799666883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61890123006975230931556709 11604398063807855799666883)
                  ·
                    refine ⟨17406597095711783699500325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11604398063807855799666883 17406597095711783699500325)
                    ·
                      refine ⟨3263736955445959443656311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17406597095711783699500325 3263736955445959443656311)
                      ·
                        rfl

theorem cell23_6356105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_6356105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356105 prefixEnd_6356105 := by exact prefixLift 6356105
  have htrace : WordTrace (prefixWord ++ tailWord_6356105) baseStart_6356105 baseEnd_6356105 := by
    simpa [prefixWord, tailWord_6356105, baseEnd_6356105] using wordTrace_append hprefix tailTrace_6356105
  have hstable : (prefixWord ++ tailWord_6356105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356105).length < 2 ^ (prefixWord ++ tailWord_6356105).sum := by decide
  have hdescent : baseEnd_6356105 < baseStart_6356105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356173 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6356173 : Nat := 118140960795 + 6356173 * 2 ^ 59
def prefixEnd_6356173 : Nat := 4983230072969 + 3 ^ 40 * 6356173 * 2
def baseEnd_6356173 : Nat := 3263771872130465177605999

theorem tailTrace_6356173 : CollatzResearch.WordTrace tailWord_6356173 prefixEnd_6356173 3263771872130465177605999 := by
  unfold tailWord_6356173
  simp only [CollatzResearch.WordTrace]
  refine ⟨231828674801678243768625173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154552449867785495845750115 231828674801678243768625173)
  ·
    refine ⟨10866969131328667676654305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 231828674801678243768625173 10866969131328667676654305)
    ·
      refine ⟨8150226848496500757490729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10866969131328667676654305 8150226848496500757490729)
      ·
        refine ⟨6112670136372375568118047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8150226848496500757490729 6112670136372375568118047)
        ·
          refine ⟨9169005204558563352177071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112670136372375568118047 9169005204558563352177071)
          ·
            refine ⟨13753507806837845028265607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169005204558563352177071 13753507806837845028265607)
            ·
              refine ⟨20630261710256767542398411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753507806837845028265607 20630261710256767542398411)
              ·
                refine ⟨30945392565385151313597617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20630261710256767542398411 30945392565385151313597617)
                ·
                  refine ⟨23209044424038863485198213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30945392565385151313597617 23209044424038863485198213)
                  ·
                    refine ⟨4351695829507286903474665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23209044424038863485198213 4351695829507286903474665)
                    ·
                      refine ⟨3263771872130465177605999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351695829507286903474665 3263771872130465177605999)
                      ·
                        rfl

theorem cell23_6356173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6356173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356173 prefixEnd_6356173 := by exact prefixLift 6356173
  have htrace : WordTrace (prefixWord ++ tailWord_6356173) baseStart_6356173 baseEnd_6356173 := by
    simpa [prefixWord, tailWord_6356173, baseEnd_6356173] using wordTrace_append hprefix tailTrace_6356173
  have hstable : (prefixWord ++ tailWord_6356173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356173).length < 2 ^ (prefixWord ++ tailWord_6356173).sum := by decide
  have hdescent : baseEnd_6356173 < baseStart_6356173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356206 : List Nat := [4, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_6356206 : Nat := 118140960795 + 6356206 * 2 ^ 59
def prefixEnd_6356206 : Nat := 4983230072969 + 3 ^ 40 * 6356206 * 2
def baseEnd_6356206 : Nat := 3263788816992063548493347

theorem tailTrace_6356206 : CollatzResearch.WordTrace tailWord_6356206 prefixEnd_6356206 3263788816992063548493347 := by
  unfold tailWord_6356206
  simp only [CollatzResearch.WordTrace]
  refine ⟨28978734801319836300572059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154553252273705793603050981 28978734801319836300572059)
  ·
    refine ⟨43468102201979754450858089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28978734801319836300572059 43468102201979754450858089)
    ·
      refine ⟨32601076651484815838143567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43468102201979754450858089 32601076651484815838143567)
      ·
        refine ⟨48901614977227223757215351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32601076651484815838143567 48901614977227223757215351)
        ·
          refine ⟨73352422465840835635823027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48901614977227223757215351 73352422465840835635823027)
          ·
            refine ⟨110028633698761253453734541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73352422465840835635823027 110028633698761253453734541)
            ·
              refine ⟨41260737637035470045150453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110028633698761253453734541 41260737637035470045150453)
              ·
                refine ⟨3868194153472075316732855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41260737637035470045150453 3868194153472075316732855)
                ·
                  refine ⟨5802291230208112975099283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868194153472075316732855 5802291230208112975099283)
                  ·
                    refine ⟨8703436845312169462648925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802291230208112975099283 8703436845312169462648925)
                    ·
                      refine ⟨3263788816992063548493347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703436845312169462648925 3263788816992063548493347)
                      ·
                        rfl

theorem cell23_6356206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_6356206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356206 prefixEnd_6356206 := by exact prefixLift 6356206
  have htrace : WordTrace (prefixWord ++ tailWord_6356206) baseStart_6356206 baseEnd_6356206 := by
    simpa [prefixWord, tailWord_6356206, baseEnd_6356206] using wordTrace_append hprefix tailTrace_6356206
  have hstable : (prefixWord ++ tailWord_6356206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356206).length < 2 ^ (prefixWord ++ tailWord_6356206).sum := by decide
  have hdescent : baseEnd_6356206 < baseStart_6356206 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356252 : List Nat := [2, 2, 3, 1, 1, 1, 6, 7]
def baseStart_6356252 : Nat := 118140960795 + 6356252 * 2 ^ 59
def prefixEnd_6356252 : Nat := 4983230072969 + 3 ^ 40 * 6356252 * 2
def baseEnd_6356252 : Nat := 120881942114895198834005

theorem tailTrace_6356252 : CollatzResearch.WordTrace tailWord_6356252 prefixEnd_6356252 120881942114895198834005 := by
  unfold tailWord_6356252
  simp only [CollatzResearch.WordTrace]
  refine ⟨115915778084196020130375505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154554370778928026840500673 115915778084196020130375505)
  ·
    refine ⟨86936833563147015097781629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115915778084196020130375505 86936833563147015097781629)
    ·
      refine ⟨32601312586180130661668111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86936833563147015097781629 32601312586180130661668111)
      ·
        refine ⟨48901968879270195992502167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32601312586180130661668111 48901968879270195992502167)
        ·
          refine ⟨73352953318905293988753251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48901968879270195992502167 73352953318905293988753251)
          ·
            refine ⟨110029429978357940983129877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73352953318905293988753251 110029429978357940983129877)
            ·
              refine ⟨5157629530235528483584213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110029429978357940983129877 5157629530235528483584213)
              ·
                refine ⟨120881942114895198834005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5157629530235528483584213 120881942114895198834005)
                ·
                  rfl

theorem cell23_6356252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 7].length) (baseStart_6356252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356252 prefixEnd_6356252 := by exact prefixLift 6356252
  have htrace : WordTrace (prefixWord ++ tailWord_6356252) baseStart_6356252 baseEnd_6356252 := by
    simpa [prefixWord, tailWord_6356252, baseEnd_6356252] using wordTrace_append hprefix tailTrace_6356252
  have hstable : (prefixWord ++ tailWord_6356252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356252).length < 2 ^ (prefixWord ++ tailWord_6356252).sum := by decide
  have hdescent : baseEnd_6356252 < baseStart_6356252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356266 : List Nat := [3, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6356266 : Nat := 118140960795 + 6356266 * 2 ^ 59
def prefixEnd_6356266 : Nat := 4983230072969 + 3 ^ 40 * 6356266 * 2
def baseEnd_6356266 : Nat := 3263819625831333313743071

theorem tailTrace_6356266 : CollatzResearch.WordTrace tailWord_6356266 prefixEnd_6356266 3263819625831333313743071 := by
  unfold tailWord_6356266
  simp only [CollatzResearch.WordTrace]
  refine ⟨57958016697585330162940163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154554711193560880434507101 57958016697585330162940163)
  ·
    refine ⟨86937025046377995244410245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57958016697585330162940163 86937025046377995244410245)
    ·
      refine ⟨16300692196195874108326921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86937025046377995244410245 16300692196195874108326921)
      ·
        refine ⟨12225519147146905581245191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16300692196195874108326921 12225519147146905581245191)
        ·
          refine ⟨18338278720720358371867787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225519147146905581245191 18338278720720358371867787)
          ·
            refine ⟨27507418081080537557801681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18338278720720358371867787 27507418081080537557801681)
            ·
              refine ⟨20630563560810403168351261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27507418081080537557801681 20630563560810403168351261)
              ·
                refine ⟨7736461335303901188131723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20630563560810403168351261 7736461335303901188131723)
                ·
                  refine ⟨11604692002955851782197585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736461335303901188131723 11604692002955851782197585)
                  ·
                    refine ⟨8703519002216888836648189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11604692002955851782197585 8703519002216888836648189)
                    ·
                      refine ⟨3263819625831333313743071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703519002216888836648189 3263819625831333313743071)
                      ·
                        rfl

theorem cell23_6356266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6356266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356266 prefixEnd_6356266 := by exact prefixLift 6356266
  have htrace : WordTrace (prefixWord ++ tailWord_6356266) baseStart_6356266 baseEnd_6356266 := by
    simpa [prefixWord, tailWord_6356266, baseEnd_6356266] using wordTrace_append hprefix tailTrace_6356266
  have hstable : (prefixWord ++ tailWord_6356266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356266).length < 2 ^ (prefixWord ++ tailWord_6356266).sum := by decide
  have hdescent : baseEnd_6356266 < baseStart_6356266 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356269 : List Nat := [1, 5, 3, 1, 1, 3, 9]
def baseStart_6356269 : Nat := 118140960795 + 6356269 * 2 ^ 59
def prefixEnd_6356269 : Nat := 4983230072969 + 3 ^ 40 * 6356269 * 2
def baseEnd_6356269 : Nat := 40294088472509837061797

theorem tailTrace_6356269 : CollatzResearch.WordTrace tailWord_6356269 prefixEnd_6356269 40294088472509837061797 := by
  unfold tailWord_6356269
  simp only [CollatzResearch.WordTrace]
  refine ⟨231832176209330452164119861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154554784139553634776079907 231832176209330452164119861)
  ·
    refine ⟨21734266519624729890386237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231832176209330452164119861 21734266519624729890386237)
    ·
      refine ⟨8150349944859273708894839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21734266519624729890386237 8150349944859273708894839)
      ·
        refine ⟨12225524917288910563342259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8150349944859273708894839 12225524917288910563342259)
        ·
          refine ⟨18338287375933365845013389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225524917288910563342259 18338287375933365845013389)
          ·
            refine ⟨6876857765975012191880021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18338287375933365845013389 6876857765975012191880021)
            ·
              refine ⟨40294088472509837061797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6876857765975012191880021 40294088472509837061797)
              ·
                rfl

theorem cell23_6356269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 9].length) (baseStart_6356269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356269 prefixEnd_6356269 := by exact prefixLift 6356269
  have htrace : WordTrace (prefixWord ++ tailWord_6356269) baseStart_6356269 baseEnd_6356269 := by
    simpa [prefixWord, tailWord_6356269, baseEnd_6356269] using wordTrace_append hprefix tailTrace_6356269
  have hstable : (prefixWord ++ tailWord_6356269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356269).length < 2 ^ (prefixWord ++ tailWord_6356269).sum := by decide
  have hdescent : baseEnd_6356269 < baseStart_6356269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356310 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6356310 : Nat := 118140960795 + 6356310 * 2 ^ 59
def prefixEnd_6356310 : Nat := 4983230072969 + 3 ^ 40 * 6356310 * 2
def baseEnd_6356310 : Nat := 3263842218980131141592869

theorem tailTrace_6356310 : CollatzResearch.WordTrace tailWord_6356310 prefixEnd_6356310 3263842218980131141592869 := by
  unfold tailWord_6356310
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489604475136369760397649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154555781068121277444241589 14489604475136369760397649)
  ·
    refine ⟨10867203356352277320298237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14489604475136369760397649 10867203356352277320298237)
    ·
      refine ⟨4075201258632103995111839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10867203356352277320298237 4075201258632103995111839)
      ·
        refine ⟨6112801887948155992667759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075201258632103995111839 6112801887948155992667759)
        ·
          refine ⟨9169202831922233989001639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112801887948155992667759 9169202831922233989001639)
          ·
            refine ⟨13753804247883350983502459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169202831922233989001639 13753804247883350983502459)
            ·
              refine ⟨20630706371825026475253689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13753804247883350983502459 20630706371825026475253689)
              ·
                refine ⟨15473029778868769856440267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20630706371825026475253689 15473029778868769856440267)
                ·
                  refine ⟨23209544668303154784660401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15473029778868769856440267 23209544668303154784660401)
                  ·
                    refine ⟨17407158501227366088495301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23209544668303154784660401 17407158501227366088495301)
                    ·
                      refine ⟨3263842218980131141592869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17407158501227366088495301 3263842218980131141592869)
                      ·
                        rfl

theorem cell23_6356310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6356310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356310 prefixEnd_6356310 := by exact prefixLift 6356310
  have htrace : WordTrace (prefixWord ++ tailWord_6356310) baseStart_6356310 baseEnd_6356310 := by
    simpa [prefixWord, tailWord_6356310, baseEnd_6356310] using wordTrace_append hprefix tailTrace_6356310
  have hstable : (prefixWord ++ tailWord_6356310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356310).length < 2 ^ (prefixWord ++ tailWord_6356310).sum := by decide
  have hdescent : baseEnd_6356310 < baseStart_6356310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356317 : List Nat := [1, 4, 5, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6356317 : Nat := 118140960795 + 6356317 * 2 ^ 59
def prefixEnd_6356317 : Nat := 4983230072969 + 3 ^ 40 * 6356317 * 2
def baseEnd_6356317 : Nat := 3263845813344712614205337

theorem tailTrace_6356317 : CollatzResearch.WordTrace tailWord_6356317 prefixEnd_6356317 3263845813344712614205337 := by
  unfold tailWord_6356317
  simp only [CollatzResearch.WordTrace]
  refine ⟨231833926913156556361867205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154555951275437704241244803 231833926913156556361867205)
  ·
    refine ⟨43468861296216854317850101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231833926913156556361867205 43468861296216854317850101)
    ·
      refine ⟨4075205746520330092298447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43468861296216854317850101 4075205746520330092298447)
      ·
        refine ⟨6112808619780495138447671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075205746520330092298447 6112808619780495138447671)
        ·
          refine ⟨9169212929670742707671507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6112808619780495138447671 9169212929670742707671507)
          ·
            refine ⟨13753819394506114061507261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169212929670742707671507 13753819394506114061507261)
            ·
              refine ⟨5157682272939792773065223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13753819394506114061507261 5157682272939792773065223)
              ·
                refine ⟨7736523409409689159597835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157682272939792773065223 7736523409409689159597835)
                ·
                  refine ⟨11604785114114533739396753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736523409409689159597835 11604785114114533739396753)
                  ·
                    refine ⟨8703588835585900304547565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11604785114114533739396753 8703588835585900304547565)
                    ·
                      refine ⟨3263845813344712614205337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703588835585900304547565 3263845813344712614205337)
                      ·
                        rfl

theorem cell23_6356317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6356317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356317 prefixEnd_6356317 := by exact prefixLift 6356317
  have htrace : WordTrace (prefixWord ++ tailWord_6356317) baseStart_6356317 baseEnd_6356317 := by
    simpa [prefixWord, tailWord_6356317, baseEnd_6356317] using wordTrace_append hprefix tailTrace_6356317
  have hstable : (prefixWord ++ tailWord_6356317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356317).length < 2 ^ (prefixWord ++ tailWord_6356317).sum := by decide
  have hdescent : baseEnd_6356317 < baseStart_6356317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356323 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 1, 3, 2]
def baseStart_6356323 : Nat := 118140960795 + 6356323 * 2 ^ 59
def prefixEnd_6356323 : Nat := 4983230072969 + 3 ^ 40 * 6356323 * 2
def baseEnd_6356323 : Nat := 3263848894228639590730309

theorem tailTrace_6356323 : CollatzResearch.WordTrace tailWord_6356323 prefixEnd_6356323 3263848894228639590730309 := by
  unfold tailWord_6356323
  simp only [CollatzResearch.WordTrace]
  refine ⟨231834145751134819386585623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154556097167423212924390415 231834145751134819386585623)
  ·
    refine ⟨347751218626702229079878435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231834145751134819386585623 347751218626702229079878435)
    ·
      refine ⟨521626827940053343619817653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347751218626702229079878435 521626827940053343619817653)
      ·
        refine ⟨48902515119380000964357905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 521626827940053343619817653 48902515119380000964357905)
        ·
          refine ⟨36676886339535000723268429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48902515119380000964357905 36676886339535000723268429)
          ·
            refine ⟨13753832377325625271225661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36676886339535000723268429 13753832377325625271225661)
            ·
              refine ⟨5157687141497109476709623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13753832377325625271225661 5157687141497109476709623)
              ·
                refine ⟨7736530712245664215064435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5157687141497109476709623 7736530712245664215064435)
                ·
                  refine ⟨11604796068368496322596653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736530712245664215064435 11604796068368496322596653)
                  ·
                    refine ⟨4351798525638186120973745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11604796068368496322596653 4351798525638186120973745)
                    ·
                      refine ⟨3263848894228639590730309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351798525638186120973745 3263848894228639590730309)
                      ·
                        rfl

theorem cell23_6356323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_6356323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356323 prefixEnd_6356323 := by exact prefixLift 6356323
  have htrace : WordTrace (prefixWord ++ tailWord_6356323) baseStart_6356323 baseEnd_6356323 := by
    simpa [prefixWord, tailWord_6356323, baseEnd_6356323] using wordTrace_append hprefix tailTrace_6356323
  have hstable : (prefixWord ++ tailWord_6356323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356323).length < 2 ^ (prefixWord ++ tailWord_6356323).sum := by decide
  have hdescent : baseEnd_6356323 < baseStart_6356323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356353 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_6356353 : Nat := 118140960795 + 6356353 * 2 ^ 59
def prefixEnd_6356353 : Nat := 4983230072969 + 3 ^ 40 * 6356353 * 2
def baseEnd_6356353 : Nat := 3263864298648274473355171

theorem tailTrace_6356353 : CollatzResearch.WordTrace tailWord_6356353 prefixEnd_6356353 3263864298648274473355171 := by
  unfold tailWord_6356353
  simp only [CollatzResearch.WordTrace]
  refine ⟨231835239941026134510177713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154556826627350756340118475 231835239941026134510177713)
  ·
    refine ⟨173876429955769600882633285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231835239941026134510177713 173876429955769600882633285)
    ·
      refine ⟨32601830616706800165493741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173876429955769600882633285 32601830616706800165493741)
      ·
        refine ⟨12225686481265050062060153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32601830616706800165493741 12225686481265050062060153)
        ·
          refine ⟨9169264860948787546545115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12225686481265050062060153 9169264860948787546545115)
          ·
            refine ⟨13753897291423181319817673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169264860948787546545115 13753897291423181319817673)
            ·
              refine ⟨10315422968567385989863255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13753897291423181319817673 10315422968567385989863255)
              ·
                refine ⟨15473134452851078984794883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10315422968567385989863255 15473134452851078984794883)
                ·
                  refine ⟨23209701679276618477192325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15473134452851078984794883 23209701679276618477192325)
                  ·
                    refine ⟨4351819064864365964473561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23209701679276618477192325 4351819064864365964473561)
                    ·
                      refine ⟨3263864298648274473355171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351819064864365964473561 3263864298648274473355171)
                      ·
                        rfl

theorem cell23_6356353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_6356353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356353 prefixEnd_6356353 := by exact prefixLift 6356353
  have htrace : WordTrace (prefixWord ++ tailWord_6356353) baseStart_6356353 baseEnd_6356353 := by
    simpa [prefixWord, tailWord_6356353, baseEnd_6356353] using wordTrace_append hprefix tailTrace_6356353
  have hstable : (prefixWord ++ tailWord_6356353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356353).length < 2 ^ (prefixWord ++ tailWord_6356353).sum := by decide
  have hdescent : baseEnd_6356353 < baseStart_6356353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356419 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 3, 4]
def baseStart_6356419 : Nat := 118140960795 + 6356419 * 2 ^ 59
def prefixEnd_6356419 : Nat := 4983230072969 + 3 ^ 40 * 6356419 * 2
def baseEnd_6356419 : Nat := 1087966062790490405043289

theorem tailTrace_6356419 : CollatzResearch.WordTrace tailWord_6356419 prefixEnd_6356419 1087966062790490405043289 := by
  unfold tailWord_6356419
  simp only [CollatzResearch.WordTrace]
  refine ⟨231837647158787027782080311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154558431439191351854720207 231837647158787027782080311)
  ·
    refine ⟨347756470738180541673120467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231837647158787027782080311 347756470738180541673120467)
    ·
      refine ⟨521634706107270812509680701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347756470738180541673120467 521634706107270812509680701)
      ·
        refine ⟨195613014790226554691130263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521634706107270812509680701 195613014790226554691130263)
        ·
          refine ⟨293419522185339832036695395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195613014790226554691130263 293419522185339832036695395)
          ·
            refine ⟨440129283278009748055043093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293419522185339832036695395 440129283278009748055043093)
            ·
              refine ⟨20631060153656706940080145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 440129283278009748055043093 20631060153656706940080145)
              ·
                refine ⟨15473295115242530205060109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20631060153656706940080145 15473295115242530205060109)
                ·
                  refine ⟨5802485668215948826897541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15473295115242530205060109 5802485668215948826897541)
                  ·
                    refine ⟨1087966062790490405043289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802485668215948826897541 1087966062790490405043289)
                    ·
                      rfl

theorem cell23_6356419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 4].length) (baseStart_6356419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356419 prefixEnd_6356419 := by exact prefixLift 6356419
  have htrace : WordTrace (prefixWord ++ tailWord_6356419) baseStart_6356419 baseEnd_6356419 := by
    simpa [prefixWord, tailWord_6356419, baseEnd_6356419] using wordTrace_append hprefix tailTrace_6356419
  have hstable : (prefixWord ++ tailWord_6356419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356419).length < 2 ^ (prefixWord ++ tailWord_6356419).sum := by decide
  have hdescent : baseEnd_6356419 < baseStart_6356419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356452 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_6356452 : Nat := 118140960795 + 6356452 * 2 ^ 59
def prefixEnd_6356452 : Nat := 4983230072969 + 3 ^ 40 * 6356452 * 2
def baseEnd_6356452 : Nat := 3263915133233069586017215

theorem tailTrace_6356452 : CollatzResearch.WordTrace tailWord_6356452 prefixEnd_6356452 3263915133233069586017215 := by
  unfold tailWord_6356452
  simp only [CollatzResearch.WordTrace]
  refine ⟨115919425383833737209015805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154559233845111649612021073 115919425383833737209015805)
  ·
    refine ⟨43469784518937651453380927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115919425383833737209015805 43469784518937651453380927)
    ·
      refine ⟨65204676778406477180071391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43469784518937651453380927 65204676778406477180071391)
      ·
        refine ⟨97807015167609715770107087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65204676778406477180071391 97807015167609715770107087)
        ·
          refine ⟨146710522751414573655160631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97807015167609715770107087 146710522751414573655160631)
          ·
            refine ⟨220065784127121860482740947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146710522751414573655160631 220065784127121860482740947)
            ·
              refine ⟨330098676190682790724111421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220065784127121860482740947 330098676190682790724111421)
              ·
                refine ⟨123787003571506046521541783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330098676190682790724111421 123787003571506046521541783)
                ·
                  refine ⟨185680505357259069782312675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123787003571506046521541783 185680505357259069782312675)
                  ·
                    refine ⟨278520758035888604673469013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 185680505357259069782312675 278520758035888604673469013)
                    ·
                      refine ⟨3263915133233069586017215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 278520758035888604673469013 3263915133233069586017215)
                      ·
                        rfl

theorem cell23_6356452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_6356452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356452 prefixEnd_6356452 := by exact prefixLift 6356452
  have htrace : WordTrace (prefixWord ++ tailWord_6356452) baseStart_6356452 baseEnd_6356452 := by
    simpa [prefixWord, tailWord_6356452, baseEnd_6356452] using wordTrace_append hprefix tailTrace_6356452
  have hstable : (prefixWord ++ tailWord_6356452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356452).length < 2 ^ (prefixWord ++ tailWord_6356452).sum := by decide
  have hdescent : baseEnd_6356452 < baseStart_6356452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356453 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 3, 4]
def baseStart_6356453 : Nat := 118140960795 + 6356453 * 2 ^ 59
def prefixEnd_6356453 : Nat := 4983230072969 + 3 ^ 40 * 6356453 * 2
def baseEnd_6356453 : Nat := 1087971882237908027368237

theorem tailTrace_6356453 : CollatzResearch.WordTrace tailWord_6356453 prefixEnd_6356453 1087971882237908027368237 := by
  unfold tailWord_6356453
  simp only [CollatzResearch.WordTrace]
  refine ⟨231838887240663851588818013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154559258160442567725878675 231838887240663851588818013)
  ·
    refine ⟨86939582715248944345806755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231838887240663851588818013 86939582715248944345806755)
    ·
      refine ⟨130409374072873416518710133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86939582715248944345806755 130409374072873416518710133)
      ·
        refine ⟨12225878819331882798629075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130409374072873416518710133 12225878819331882798629075)
        ·
          refine ⟨18338818228997824197943613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225878819331882798629075 18338818228997824197943613)
          ·
            refine ⟨6877056835874184074228855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18338818228997824197943613 6877056835874184074228855)
            ·
              refine ⟨10315585253811276111343283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877056835874184074228855 10315585253811276111343283)
              ·
                refine ⟨15473377880716914167014925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10315585253811276111343283 15473377880716914167014925)
                ·
                  refine ⟨5802516705268842812630597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15473377880716914167014925 5802516705268842812630597)
                  ·
                    refine ⟨1087971882237908027368237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802516705268842812630597 1087971882237908027368237)
                    ·
                      rfl

theorem cell23_6356453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_6356453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356453 prefixEnd_6356453 := by exact prefixLift 6356453
  have htrace : WordTrace (prefixWord ++ tailWord_6356453) baseStart_6356453 baseEnd_6356453 := by
    simpa [prefixWord, tailWord_6356453, baseEnd_6356453] using wordTrace_append hprefix tailTrace_6356453
  have hstable : (prefixWord ++ tailWord_6356453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356453).length < 2 ^ (prefixWord ++ tailWord_6356453).sum := by decide
  have hdescent : baseEnd_6356453 < baseStart_6356453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356466 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_6356466 : Nat := 118140960795 + 6356466 * 2 ^ 59
def prefixEnd_6356466 : Nat := 4983230072969 + 3 ^ 40 * 6356466 * 2
def baseEnd_6356466 : Nat := 362658035773581392360239

theorem tailTrace_6356466 : CollatzResearch.WordTrace tailWord_6356466 prefixEnd_6356466 362658035773581392360239 := by
  unfold tailWord_6356466
  simp only [CollatzResearch.WordTrace]
  refine ⟨57959840347404188702260313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154559574259744503206027501 57959840347404188702260313)
  ·
    refine ⟨43469880260553141526695235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57959840347404188702260313 43469880260553141526695235)
    ·
      refine ⟨65204820390829712290042853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43469880260553141526695235 65204820390829712290042853)
      ·
        refine ⟨12225903823280571054383035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65204820390829712290042853 12225903823280571054383035)
        ·
          refine ⟨18338855734920856581574553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12225903823280571054383035 18338855734920856581574553)
          ·
            refine ⟨13754141801190642436180915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18338855734920856581574553 13754141801190642436180915)
            ·
              refine ⟨20631212701785963654271373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13754141801190642436180915 20631212701785963654271373)
              ·
                refine ⟨7736704763169736370351765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20631212701785963654271373 7736704763169736370351765)
                ·
                  refine ⟨362658035773581392360239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7736704763169736370351765 362658035773581392360239)
                  ·
                    rfl

theorem cell23_6356466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_6356466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356466 prefixEnd_6356466 := by exact prefixLift 6356466
  have htrace : WordTrace (prefixWord ++ tailWord_6356466) baseStart_6356466 baseEnd_6356466 := by
    simpa [prefixWord, tailWord_6356466, baseEnd_6356466] using wordTrace_append hprefix tailTrace_6356466
  have hstable : (prefixWord ++ tailWord_6356466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356466).length < 2 ^ (prefixWord ++ tailWord_6356466).sum := by decide
  have hdescent : baseEnd_6356466 < baseStart_6356466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356476 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_6356476 : Nat := 118140960795 + 6356476 * 2 ^ 59
def prefixEnd_6356476 : Nat := 4983230072969 + 3 ^ 40 * 6356476 * 2
def baseEnd_6356476 : Nat := 3263927456768777492117105

theorem tailTrace_6356476 : CollatzResearch.WordTrace tailWord_6356476 prefixEnd_6356476 3263927456768777492117105 := by
  unfold tailWord_6356476
  simp only [CollatzResearch.WordTrace]
  refine ⟨115919863059790263258452641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154559817413053684344603521 115919863059790263258452641)
  ·
    refine ⟨86939897294842697443839481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115919863059790263258452641 86939897294842697443839481)
    ·
      refine ⟨65204922971132023082879611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86939897294842697443839481 65204922971132023082879611)
      ·
        refine ⟨97807384456698034624319417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65204922971132023082879611 97807384456698034624319417)
        ·
          refine ⟨73355538342523525968239563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97807384456698034624319417 73355538342523525968239563)
          ·
            refine ⟨110033307513785288952359345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73355538342523525968239563 110033307513785288952359345)
            ·
              refine ⟨82524980635338966714269509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110033307513785288952359345 82524980635338966714269509)
              ·
                refine ⟨15473433869126056258925533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82524980635338966714269509 15473433869126056258925533)
                ·
                  refine ⟨5802537700922271097097075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15473433869126056258925533 5802537700922271097097075)
                  ·
                    refine ⟨8703806551383406645645613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802537700922271097097075 8703806551383406645645613)
                    ·
                      refine ⟨3263927456768777492117105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703806551383406645645613 3263927456768777492117105)
                      ·
                        rfl

theorem cell23_6356476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_6356476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356476 prefixEnd_6356476 := by exact prefixLift 6356476
  have htrace : WordTrace (prefixWord ++ tailWord_6356476) baseStart_6356476 baseEnd_6356476 := by
    simpa [prefixWord, tailWord_6356476, baseEnd_6356476] using wordTrace_append hprefix tailTrace_6356476
  have hstable : (prefixWord ++ tailWord_6356476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356476).length < 2 ^ (prefixWord ++ tailWord_6356476).sum := by decide
  have hdescent : baseEnd_6356476 < baseStart_6356476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356479 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 1, 5]
def baseStart_6356479 : Nat := 118140960795 + 6356479 * 2 ^ 59
def prefixEnd_6356479 : Nat := 4983230072969 + 3 ^ 40 * 6356479 * 2
def baseEnd_6356479 : Nat := 1087976332403580326793197

theorem tailTrace_6356479 : CollatzResearch.WordTrace tailWord_6356479 prefixEnd_6356479 1087976332403580326793197 := by
  unfold tailWord_6356479
  simp only [CollatzResearch.WordTrace]
  refine ⟨231839835538569658029264491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154559890359046438686176327 231839835538569658029264491)
  ·
    refine ⟨347759753307854487043896737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231839835538569658029264491 347759753307854487043896737)
    ·
      refine ⟨260819814980890865282922553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347759753307854487043896737 260819814980890865282922553)
      ·
        refine ⟨195614861235668148962191915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260819814980890865282922553 195614861235668148962191915)
        ·
          refine ⟨293422291853502223443287873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195614861235668148962191915 293422291853502223443287873)
          ·
            refine ⟨220066718890126667582465905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293422291853502223443287873 220066718890126667582465905)
            ·
              refine ⟨165050039167595000686849429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220066718890126667582465905 165050039167595000686849429)
              ·
                refine ⟨7736720585981015657196067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165050039167595000686849429 7736720585981015657196067)
                ·
                  refine ⟨11605080878971523485794101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7736720585981015657196067 11605080878971523485794101)
                  ·
                    refine ⟨1087976332403580326793197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11605080878971523485794101 1087976332403580326793197)
                    ·
                      rfl

theorem cell23_6356479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_6356479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356479 prefixEnd_6356479 := by exact prefixLift 6356479
  have htrace : WordTrace (prefixWord ++ tailWord_6356479) baseStart_6356479 baseEnd_6356479 := by
    simpa [prefixWord, tailWord_6356479, baseEnd_6356479] using wordTrace_append hprefix tailTrace_6356479
  have hstable : (prefixWord ++ tailWord_6356479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356479).length < 2 ^ (prefixWord ++ tailWord_6356479).sum := by decide
  have hdescent : baseEnd_6356479 < baseStart_6356479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356509 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_6356509 : Nat := 118140960795 + 6356509 * 2 ^ 59
def prefixEnd_6356509 : Nat := 4983230072969 + 3 ^ 40 * 6356509 * 2
def baseEnd_6356509 : Nat := 1087981467210125287668151

theorem tailTrace_6356509 : CollatzResearch.WordTrace tailWord_6356509 prefixEnd_6356509 1087981467210125287668151 := by
  unfold tailWord_6356509
  simp only [CollatzResearch.WordTrace]
  refine ⟨231840929728460973152856581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154560619818973982101904387 231840929728460973152856581)
  ·
    refine ⟨43470174324086432466160609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231840929728460973152856581 43470174324086432466160609)
    ·
      refine ⟨32602630743064824349620457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43470174324086432466160609 32602630743064824349620457)
      ·
        refine ⟨24451973057298618262215343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32602630743064824349620457 24451973057298618262215343)
        ·
          refine ⟨36677959585947927393323015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24451973057298618262215343 36677959585947927393323015)
          ·
            refine ⟨55016939378921891089984523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36677959585947927393323015 55016939378921891089984523)
            ·
              refine ⟨82525409068382836634976785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55016939378921891089984523 82525409068382836634976785)
              ·
                refine ⟨61894056801287127476232589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82525409068382836634976785 61894056801287127476232589)
                ·
                  refine ⟨23210271300482672803587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61894056801287127476232589 23210271300482672803587221)
                  ·
                    refine ⟨1087981467210125287668151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23210271300482672803587221 1087981467210125287668151)
                    ·
                      rfl

theorem cell23_6356509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_6356509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356509 prefixEnd_6356509 := by exact prefixLift 6356509
  have htrace : WordTrace (prefixWord ++ tailWord_6356509) baseStart_6356509 baseEnd_6356509 := by
    simpa [prefixWord, tailWord_6356509, baseEnd_6356509] using wordTrace_append hprefix tailTrace_6356509
  have hstable : (prefixWord ++ tailWord_6356509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356509).length < 2 ^ (prefixWord ++ tailWord_6356509).sum := by decide
  have hdescent : baseEnd_6356509 < baseStart_6356509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356526 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6356526 : Nat := 118140960795 + 6356526 * 2 ^ 59
def prefixEnd_6356526 : Nat := 4983230072969 + 3 ^ 40 * 6356526 * 2
def baseEnd_6356526 : Nat := 1087984376933834098830625

theorem tailTrace_6356526 : CollatzResearch.WordTrace tailWord_6356526 prefixEnd_6356526 1087984376933834098830625 := by
  unfold tailWord_6356526
  simp only [CollatzResearch.WordTrace]
  refine ⟨28980193721174923132028179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154561033179599590037483621 28980193721174923132028179)
  ·
    refine ⟨43470290581762384698042269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28980193721174923132028179 43470290581762384698042269)
    ·
      refine ⟨16301358968160894261765851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43470290581762384698042269 16301358968160894261765851)
      ·
        refine ⟨24452038452241341392648777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16301358968160894261765851 24452038452241341392648777)
        ·
          refine ⟨18339028839181006044486583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24452038452241341392648777 18339028839181006044486583)
          ·
            refine ⟨27508543258771509066729875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18339028839181006044486583 27508543258771509066729875)
            ·
              refine ⟨41262814888157263600094813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27508543258771509066729875 41262814888157263600094813)
              ·
                refine ⟨15473555583058973850035555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41262814888157263600094813 15473555583058973850035555)
                ·
                  refine ⟨23210333374588460775053333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15473555583058973850035555 23210333374588460775053333)
                  ·
                    refine ⟨1087984376933834098830625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23210333374588460775053333 1087984376933834098830625)
                    ·
                      rfl

theorem cell23_6356526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6356526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356526 prefixEnd_6356526 := by exact prefixLift 6356526
  have htrace : WordTrace (prefixWord ++ tailWord_6356526) baseStart_6356526 baseEnd_6356526 := by
    simpa [prefixWord, tailWord_6356526, baseEnd_6356526] using wordTrace_append hprefix tailTrace_6356526
  have hstable : (prefixWord ++ tailWord_6356526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356526).length < 2 ^ (prefixWord ++ tailWord_6356526).sum := by decide
  have hdescent : baseEnd_6356526 < baseStart_6356526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356533 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_6356533 : Nat := 118140960795 + 6356533 * 2 ^ 59
def prefixEnd_6356533 : Nat := 4983230072969 + 3 ^ 40 * 6356533 * 2
def baseEnd_6356533 : Nat := 3263956725166083769104343

theorem tailTrace_6356533 : CollatzResearch.WordTrace tailWord_6356533 prefixEnd_6356533 3263956725166083769104343 := by
  unfold tailWord_6356533
  simp only [CollatzResearch.WordTrace]
  refine ⟨231841805080374025251730253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154561203386916016834486835 231841805080374025251730253)
  ·
    refine ⟨86940676905140259469398845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231841805080374025251730253 86940676905140259469398845)
    ·
      refine ⟨32602753839427597301024567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86940676905140259469398845 32602753839427597301024567)
      ·
        refine ⟨48904130759141395951536851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32602753839427597301024567 48904130759141395951536851)
        ·
          refine ⟨73356196138712093927305277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48904130759141395951536851 73356196138712093927305277)
          ·
            refine ⟨27508573552017035222739479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73356196138712093927305277 27508573552017035222739479)
            ·
              refine ⟨41262860328025552834109219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27508573552017035222739479 41262860328025552834109219)
              ·
                refine ⟨61894290492038329251163829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41262860328025552834109219 61894290492038329251163829)
                ·
                  refine ⟨5802589733628593367296609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61894290492038329251163829 5802589733628593367296609)
                  ·
                    refine ⟨4351942300221445025472457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802589733628593367296609 4351942300221445025472457)
                    ·
                      refine ⟨3263956725166083769104343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4351942300221445025472457 3263956725166083769104343)
                      ·
                        rfl

theorem cell23_6356533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_6356533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356533 prefixEnd_6356533 := by exact prefixLift 6356533
  have htrace : WordTrace (prefixWord ++ tailWord_6356533) baseStart_6356533 baseEnd_6356533 := by
    simpa [prefixWord, tailWord_6356533, baseEnd_6356533] using wordTrace_append hprefix tailTrace_6356533
  have hstable : (prefixWord ++ tailWord_6356533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356533).length < 2 ^ (prefixWord ++ tailWord_6356533).sum := by decide
  have hdescent : baseEnd_6356533 < baseStart_6356533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356536 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_6356536 : Nat := 118140960795 + 6356536 * 2 ^ 59
def prefixEnd_6356536 : Nat := 4983230072969 + 3 ^ 40 * 6356536 * 2
def baseEnd_6356536 : Nat := 3263958265608047257366829

theorem tailTrace_6356536 : CollatzResearch.WordTrace tailWord_6356536 prefixEnd_6356536 3263958265608047257366829 := by
  unfold tailWord_6356536
  simp only [CollatzResearch.WordTrace]
  refine ⟨115920957249681578382044731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154561276332908771176059641 115920957249681578382044731)
  ·
    refine ⟨173881435874522367573067097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115920957249681578382044731 173881435874522367573067097)
    ·
      refine ⟨130411076905891775679800323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173881435874522367573067097 130411076905891775679800323)
      ·
        refine ⟨195616615358837663519700485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130411076905891775679800323 195616615358837663519700485)
        ·
          refine ⟨36678115379782061909943841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195616615358837663519700485 36678115379782061909943841)
          ·
            refine ⟨27508586534836546432457881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36678115379782061909943841 27508586534836546432457881)
            ·
              refine ⟨20631439901127409824343411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27508586534836546432457881 20631439901127409824343411)
              ·
                refine ⟨30947159851691114736515117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20631439901127409824343411 30947159851691114736515117)
                ·
                  refine ⟨11605184944384168026193169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30947159851691114736515117 11605184944384168026193169)
                  ·
                    refine ⟨8703888708288126019644877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11605184944384168026193169 8703888708288126019644877)
                    ·
                      refine ⟨3263958265608047257366829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703888708288126019644877 3263958265608047257366829)
                      ·
                        rfl

theorem cell23_6356536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_6356536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356536 prefixEnd_6356536 := by exact prefixLift 6356536
  have htrace : WordTrace (prefixWord ++ tailWord_6356536) baseStart_6356536 baseEnd_6356536 := by
    simpa [prefixWord, tailWord_6356536, baseEnd_6356536] using wordTrace_append hprefix tailTrace_6356536
  have hstable : (prefixWord ++ tailWord_6356536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356536).length < 2 ^ (prefixWord ++ tailWord_6356536).sum := by decide
  have hdescent : baseEnd_6356536 < baseStart_6356536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356583 : List Nat := [1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_6356583 : Nat := 118140960795 + 6356583 * 2 ^ 59
def prefixEnd_6356583 : Nat := 4983230072969 + 3 ^ 40 * 6356583 * 2
def baseEnd_6356583 : Nat := 3263982399198808573479113

theorem tailTrace_6356583 : CollatzResearch.WordTrace tailWord_6356583 prefixEnd_6356583 3263982399198808573479113 := by
  unfold tailWord_6356583
  simp only [CollatzResearch.WordTrace]
  refine ⟨231843628730192883791050403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154562419153461922527366935 231843628730192883791050403)
  ·
    refine ⟨347765443095289325686575605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231843628730192883791050403 347765443095289325686575605)
    ·
      refine ⟨32603010290183374283116463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 347765443095289325686575605 32603010290183374283116463)
      ·
        refine ⟨48904515435275061424674695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32603010290183374283116463 48904515435275061424674695)
        ·
          refine ⟨73356773152912592137012043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48904515435275061424674695 73356773152912592137012043)
          ·
            refine ⟨110035159729368888205518065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73356773152912592137012043 110035159729368888205518065)
            ·
              refine ⟨82526369797026666154138549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110035159729368888205518065 82526369797026666154138549)
              ·
                refine ⟨7736847168471249951950489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82526369797026666154138549 7736847168471249951950489)
                ·
                  refine ⟨5802635376353437463962867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7736847168471249951950489 5802635376353437463962867)
                  ·
                    refine ⟨8703953064530156195944301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802635376353437463962867 8703953064530156195944301)
                    ·
                      refine ⟨3263982399198808573479113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8703953064530156195944301 3263982399198808573479113)
                      ·
                        rfl

theorem cell23_6356583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_6356583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356583 prefixEnd_6356583 := by exact prefixLift 6356583
  have htrace : WordTrace (prefixWord ++ tailWord_6356583) baseStart_6356583 baseEnd_6356583 := by
    simpa [prefixWord, tailWord_6356583, baseEnd_6356583] using wordTrace_append hprefix tailTrace_6356583
  have hstable : (prefixWord ++ tailWord_6356583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356583).length < 2 ^ (prefixWord ++ tailWord_6356583).sum := by decide
  have hdescent : baseEnd_6356583 < baseStart_6356583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356590 : List Nat := [4, 1, 2, 2, 4, 1, 2, 7]
def baseStart_6356590 : Nat := 118140960795 + 6356590 * 2 ^ 59
def prefixEnd_6356590 : Nat := 4983230072969 + 3 ^ 40 * 6356590 * 2
def baseEnd_6356590 : Nat := 120888370131977409114503

theorem tailTrace_6356590 : CollatzResearch.WordTrace tailWord_6356590 prefixEnd_6356590 120888370131977409114503 := by
  unfold tailWord_6356590
  simp only [CollatzResearch.WordTrace]
  refine ⟨28980485505145940498319403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154562589360778349324370149 28980485505145940498319403)
  ·
    refine ⟨43470728257718910747479105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28980485505145940498319403 43470728257718910747479105)
    ·
      refine ⟨32603046193289183060609329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43470728257718910747479105 32603046193289183060609329)
      ·
        refine ⟨24452284644966887295456997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32603046193289183060609329 24452284644966887295456997)
        ·
          refine ⟨4584803370931291367898187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24452284644966887295456997 4584803370931291367898187)
          ·
            refine ⟨6877205056396937051847281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4584803370931291367898187 6877205056396937051847281)
            ·
              refine ⟨5157903792297702788885461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877205056396937051847281 5157903792297702788885461)
              ·
                refine ⟨120888370131977409114503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5157903792297702788885461 120888370131977409114503)
                ·
                  rfl

theorem cell23_6356590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_6356590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356590 prefixEnd_6356590 := by exact prefixLift 6356590
  have htrace : WordTrace (prefixWord ++ tailWord_6356590) baseStart_6356590 baseEnd_6356590 := by
    simpa [prefixWord, tailWord_6356590, baseEnd_6356590] using wordTrace_append hprefix tailTrace_6356590
  have hstable : (prefixWord ++ tailWord_6356590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356590).length < 2 ^ (prefixWord ++ tailWord_6356590).sum := by decide
  have hdescent : baseEnd_6356590 < baseStart_6356590 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356686 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6356686 : Nat := 118140960795 + 6356686 * 2 ^ 59
def prefixEnd_6356686 : Nat := 4983230072969 + 3 ^ 40 * 6356686 * 2
def baseEnd_6356686 : Nat := 3264035287706221670491139

theorem tailTrace_6356686 : CollatzResearch.WordTrace tailWord_6356686 prefixEnd_6356686 3264035287706221670491139 := by
  unfold tailWord_6356686
  simp only [CollatzResearch.WordTrace]
  refine ⟨28980923181102466547756239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154564923632546488254699941 28980923181102466547756239)
  ·
    refine ⟨43471384771653699821634359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28980923181102466547756239 43471384771653699821634359)
    ·
      refine ⟨65207077157480549732451539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43471384771653699821634359 65207077157480549732451539)
      ·
        refine ⟨97810615736220824598677309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65207077157480549732451539 97810615736220824598677309)
        ·
          refine ⟨36678980901082809224503991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97810615736220824598677309 36678980901082809224503991)
          ·
            refine ⟨55018471351624213836755987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36678980901082809224503991 55018471351624213836755987)
            ·
              refine ⟨82527707027436320755133981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55018471351624213836755987 82527707027436320755133981)
              ·
                refine ⟨30947890135288620283175243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82527707027436320755133981 30947890135288620283175243)
                ·
                  refine ⟨46421835202932930424762865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30947890135288620283175243 46421835202932930424762865)
                  ·
                    refine ⟨34816376402199697818572149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46421835202932930424762865 34816376402199697818572149)
                    ·
                      refine ⟨3264035287706221670491139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34816376402199697818572149 3264035287706221670491139)
                      ·
                        rfl

theorem cell23_6356686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6356686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356686 prefixEnd_6356686 := by exact prefixLift 6356686
  have htrace : WordTrace (prefixWord ++ tailWord_6356686) baseStart_6356686 baseEnd_6356686 := by
    simpa [prefixWord, tailWord_6356686, baseEnd_6356686] using wordTrace_append hprefix tailTrace_6356686
  have hstable : (prefixWord ++ tailWord_6356686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356686).length < 2 ^ (prefixWord ++ tailWord_6356686).sum := by decide
  have hdescent : baseEnd_6356686 < baseStart_6356686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356696 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6356696 : Nat := 118140960795 + 6356696 * 2 ^ 59
def prefixEnd_6356696 : Nat := 4983230072969 + 3 ^ 40 * 6356696 * 2
def baseEnd_6356696 : Nat := 3264040422512766631366093

theorem tailTrace_6356696 : CollatzResearch.WordTrace tailWord_6356696 prefixEnd_6356696 3264040422512766631366093 := by
  unfold tailWord_6356696
  simp only [CollatzResearch.WordTrace]
  refine ⟨115923875089391752044956971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154565166785855669393275961 115923875089391752044956971)
  ·
    refine ⟨173885812634087628067435457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115923875089391752044956971 173885812634087628067435457)
    ·
      refine ⟨130414359475565721050576593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173885812634087628067435457 130414359475565721050576593)
      ·
        refine ⟨97810769606674290787932445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130414359475565721050576593 97810769606674290787932445)
        ·
          refine ⟨36679038602502859045474667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97810769606674290787932445 36679038602502859045474667)
          ·
            refine ⟨55018557903754288568212001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36679038602502859045474667 55018557903754288568212001)
            ·
              refine ⟨41263918427815716426159001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55018557903754288568212001 41263918427815716426159001)
              ·
                refine ⟨30947938820861787319619251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41263918427815716426159001 30947938820861787319619251)
                ·
                  refine ⟨46421908231292680979428877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30947938820861787319619251 46421908231292680979428877)
                  ·
                    refine ⟨17408215586734755367285829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46421908231292680979428877 17408215586734755367285829)
                    ·
                      refine ⟨3264040422512766631366093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17408215586734755367285829 3264040422512766631366093)
                      ·
                        rfl

theorem cell23_6356696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6356696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356696 prefixEnd_6356696 := by exact prefixLift 6356696
  have htrace : WordTrace (prefixWord ++ tailWord_6356696) baseStart_6356696 baseEnd_6356696 := by
    simpa [prefixWord, tailWord_6356696, baseEnd_6356696] using wordTrace_append hprefix tailTrace_6356696
  have hstable : (prefixWord ++ tailWord_6356696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356696).length < 2 ^ (prefixWord ++ tailWord_6356696).sum := by decide
  have hdescent : baseEnd_6356696 < baseStart_6356696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356740 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_6356740 : Nat := 118140960795 + 6356740 * 2 ^ 59
def prefixEnd_6356740 : Nat := 4983230072969 + 3 ^ 40 * 6356740 * 2
def baseEnd_6356740 : Nat := 1088021005220521486405297

theorem tailTrace_6356740 : CollatzResearch.WordTrace tailWord_6356740 prefixEnd_6356740 1088021005220521486405297 := by
  unfold tailWord_6356740
  simp only [CollatzResearch.WordTrace]
  refine ⟨115924677495312049802257837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154566236660416066403010449 115924677495312049802257837)
  ·
    refine ⟨43471754060742018675846689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115924677495312049802257837 43471754060742018675846689)
    ·
      refine ⟨32603815545556514006885017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43471754060742018675846689 32603815545556514006885017)
      ·
        refine ⟨24452861659167385505163763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32603815545556514006885017 24452861659167385505163763)
        ·
          refine ⟨36679292488751078257745645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24452861659167385505163763 36679292488751078257745645)
          ·
            refine ⟨13754734683281654346654617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36679292488751078257745645 13754734683281654346654617)
            ·
              refine ⟨10316051012461240759990963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13754734683281654346654617 10316051012461240759990963)
              ·
                refine ⟨15474076518691861139986445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10316051012461240759990963 15474076518691861139986445)
                ·
                  refine ⟨5802778694509447927494917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15474076518691861139986445 5802778694509447927494917)
                  ·
                    refine ⟨1088021005220521486405297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5802778694509447927494917 1088021005220521486405297)
                    ·
                      rfl

theorem cell23_6356740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_6356740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356740 prefixEnd_6356740 := by exact prefixLift 6356740
  have htrace : WordTrace (prefixWord ++ tailWord_6356740) baseStart_6356740 baseEnd_6356740 := by
    simpa [prefixWord, tailWord_6356740, baseEnd_6356740] using wordTrace_append hprefix tailTrace_6356740
  have hstable : (prefixWord ++ tailWord_6356740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356740).length < 2 ^ (prefixWord ++ tailWord_6356740).sum := by decide
  have hdescent : baseEnd_6356740 < baseStart_6356740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356742 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6356742 : Nat := 118140960795 + 6356742 * 2 ^ 59
def prefixEnd_6356742 : Nat := 4983230072969 + 3 ^ 40 * 6356742 * 2
def baseEnd_6356742 : Nat := 3264064042622873451390883

theorem tailTrace_6356742 : CollatzResearch.WordTrace tailWord_6356742 prefixEnd_6356742 3264064042622873451390883 := by
  unfold tailWord_6356742
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245294623019276685815265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154566285291077902630725653 7245294623019276685815265)
  ·
    refine ⟨5433970967264457514361449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7245294623019276685815265 5433970967264457514361449)
    ·
      refine ⟨4075478225448343135771087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433970967264457514361449 4075478225448343135771087)
      ·
        refine ⟨6113217338172514703656631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075478225448343135771087 6113217338172514703656631)
        ·
          refine ⟨9169826007258772055484947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113217338172514703656631 9169826007258772055484947)
          ·
            refine ⟨13754739010888158083227421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9169826007258772055484947 13754739010888158083227421)
            ·
              refine ⟨5158027129083059281210283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13754739010888158083227421 5158027129083059281210283)
              ·
                refine ⟨7737040693624588921815425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158027129083059281210283 7737040693624588921815425)
                ·
                  refine ⟨5802780520218441691361569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7737040693624588921815425 5802780520218441691361569)
                  ·
                    refine ⟨4352085390163831268521177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802780520218441691361569 4352085390163831268521177)
                    ·
                      refine ⟨3264064042622873451390883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352085390163831268521177 3264064042622873451390883)
                      ·
                        rfl

theorem cell23_6356742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6356742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356742 prefixEnd_6356742 := by exact prefixLift 6356742
  have htrace : WordTrace (prefixWord ++ tailWord_6356742) baseStart_6356742 baseEnd_6356742 := by
    simpa [prefixWord, tailWord_6356742, baseEnd_6356742] using wordTrace_append hprefix tailTrace_6356742
  have hstable : (prefixWord ++ tailWord_6356742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356742).length < 2 ^ (prefixWord ++ tailWord_6356742).sum := by decide
  have hdescent : baseEnd_6356742 < baseStart_6356742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356797 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6356797 : Nat := 118140960795 + 6356797 * 2 ^ 59
def prefixEnd_6356797 : Nat := 4983230072969 + 3 ^ 40 * 6356797 * 2
def baseEnd_6356797 : Nat := 3264092284058870736203129

theorem tailTrace_6356797 : CollatzResearch.WordTrace tailWord_6356797 prefixEnd_6356797 3264092284058870736203129 := by
  unfold tailWord_6356797
  simp only [CollatzResearch.WordTrace]
  refine ⟨231851433951417598339340645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154567622634278398892893763 231851433951417598339340645)
  ·
    refine ⟨43472143865890799688626371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231851433951417598339340645 43472143865890799688626371)
    ·
      refine ⟨65208215798836199532939557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43472143865890799688626371 65208215798836199532939557)
      ·
        refine ⟨12226540462281787412426167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65208215798836199532939557 12226540462281787412426167)
        ·
          refine ⟨18339810693422681118639251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12226540462281787412426167 18339810693422681118639251)
          ·
            refine ⟨27509716040134021677958877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18339810693422681118639251 27509716040134021677958877)
            ·
              refine ⟨10316143515050258129234579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27509716040134021677958877 10316143515050258129234579)
              ·
                refine ⟨15474215272575387193851869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10316143515050258129234579 15474215272575387193851869)
                ·
                  refine ⟨5802830727215770197694451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15474215272575387193851869 5802830727215770197694451)
                  ·
                    refine ⟨8704246090823655296541677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5802830727215770197694451 8704246090823655296541677)
                    ·
                      refine ⟨3264092284058870736203129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704246090823655296541677 3264092284058870736203129)
                      ·
                        rfl

theorem cell23_6356797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6356797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356797 prefixEnd_6356797 := by exact prefixLift 6356797
  have htrace : WordTrace (prefixWord ++ tailWord_6356797) baseStart_6356797 baseEnd_6356797 := by
    simpa [prefixWord, tailWord_6356797, baseEnd_6356797] using wordTrace_append hprefix tailTrace_6356797
  have hstable : (prefixWord ++ tailWord_6356797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356797).length < 2 ^ (prefixWord ++ tailWord_6356797).sum := by decide
  have hdescent : baseEnd_6356797 < baseStart_6356797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356820 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6356820 : Nat := 118140960795 + 6356820 * 2 ^ 59
def prefixEnd_6356820 : Nat := 4983230072969 + 3 ^ 40 * 6356820 * 2
def baseEnd_6356820 : Nat := 3264104094113924146215523

theorem tailTrace_6356820 : CollatzResearch.WordTrace tailWord_6356820 prefixEnd_6356820 3264104094113924146215523 := by
  unfold tailWord_6356820
  simp only [CollatzResearch.WordTrace]
  refine ⟨115926136415167136633713957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154568181886889515511618609 115926136415167136633713957)
  ·
    refine ⟨21736150577843838118821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115926136415167136633713957 21736150577843838118821367)
    ·
      refine ⟨32604225866765757178232051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21736150577843838118821367 32604225866765757178232051)
      ·
        refine ⟨48906338800148635767348077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32604225866765757178232051 48906338800148635767348077)
        ·
          refine ⟨18339877050055738412755529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48906338800148635767348077 18339877050055738412755529)
          ·
            refine ⟨13754907787541803809566647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18339877050055738412755529 13754907787541803809566647)
            ·
              refine ⟨20632361681312705714349971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13754907787541803809566647 20632361681312705714349971)
              ·
                refine ⟨30948542521969058571524957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20632361681312705714349971 30948542521969058571524957)
                ·
                  refine ⟨11605703445738396964321859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30948542521969058571524957 11605703445738396964321859)
                  ·
                    refine ⟨17408555168607595446482789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11605703445738396964321859 17408555168607595446482789)
                    ·
                      refine ⟨3264104094113924146215523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17408555168607595446482789 3264104094113924146215523)
                      ·
                        rfl

theorem cell23_6356820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6356820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356820 prefixEnd_6356820 := by exact prefixLift 6356820
  have htrace : WordTrace (prefixWord ++ tailWord_6356820) baseStart_6356820 baseEnd_6356820 := by
    simpa [prefixWord, tailWord_6356820, baseEnd_6356820] using wordTrace_append hprefix tailTrace_6356820
  have hstable : (prefixWord ++ tailWord_6356820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356820).length < 2 ^ (prefixWord ++ tailWord_6356820).sum := by decide
  have hdescent : baseEnd_6356820 < baseStart_6356820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356826 : List Nat := [3, 1, 1, 2, 1, 3, 1, 11]
def baseStart_6356826 : Nat := 118140960795 + 6356826 * 2 ^ 59
def prefixEnd_6356826 : Nat := 4983230072969 + 3 ^ 40 * 6356826 * 2
def baseEnd_6356826 : Nat := 120892858333253745286685

theorem tailTrace_6356826 : CollatzResearch.WordTrace tailWord_6356826 prefixEnd_6356826 120892858333253745286685 := by
  unfold tailWord_6356826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57963122917078134073036583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154568327778875024194764221 57963122917078134073036583)
  ·
    refine ⟨86944684375617201109554875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57963122917078134073036583 86944684375617201109554875)
    ·
      refine ⟨130417026563425801664332313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86944684375617201109554875 130417026563425801664332313)
      ·
        refine ⟨97812769922569351248249235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130417026563425801664332313 97812769922569351248249235)
        ·
          refine ⟨146719154883854026872373853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97812769922569351248249235 146719154883854026872373853)
          ·
            refine ⟨55019683081445260077140195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146719154883854026872373853 55019683081445260077140195)
            ·
              refine ⟨82529524622167890115710293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55019683081445260077140195 82529524622167890115710293)
              ·
                refine ⟨120892858333253745286685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82529524622167890115710293 120892858333253745286685)
                ·
                  rfl

theorem cell23_6356826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_6356826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356826 prefixEnd_6356826 := by exact prefixLift 6356826
  have htrace : WordTrace (prefixWord ++ tailWord_6356826) baseStart_6356826 baseEnd_6356826 := by
    simpa [prefixWord, tailWord_6356826, baseEnd_6356826] using wordTrace_append hprefix tailTrace_6356826
  have hstable : (prefixWord ++ tailWord_6356826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356826).length < 2 ^ (prefixWord ++ tailWord_6356826).sum := by decide
  have hdescent : baseEnd_6356826 < baseStart_6356826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356833 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_6356833 : Nat := 118140960795 + 6356833 * 2 ^ 59
def prefixEnd_6356833 : Nat := 4983230072969 + 3 ^ 40 * 6356833 * 2
def baseEnd_6356833 : Nat := 3264110769362432595352963

theorem tailTrace_6356833 : CollatzResearch.WordTrace tailWord_6356833 prefixEnd_6356833 3264110769362432595352963 := by
  unfold tailWord_6356833
  simp only [CollatzResearch.WordTrace]
  refine ⟨231852746979287176487651153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154568497986191450991767435 231852746979287176487651153)
  ·
    refine ⟨173889560234465382365738365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231852746979287176487651153 173889560234465382365738365)
    ·
      refine ⟨65208585087924518387151887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173889560234465382365738365 65208585087924518387151887)
      ·
        refine ⟨97812877631886777580727831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65208585087924518387151887 97812877631886777580727831)
        ·
          refine ⟨146719316447830166371091747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97812877631886777580727831 146719316447830166371091747)
          ·
            refine ⟨220078974671745249556637621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146719316447830166371091747 220078974671745249556637621)
            ·
              refine ⟨20632403875476117145934777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220078974671745249556637621 20632403875476117145934777)
              ·
                refine ⟨15474302906607087859451083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20632403875476117145934777 15474302906607087859451083)
                ·
                  refine ⟨23211454359910631789176625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15474302906607087859451083 23211454359910631789176625)
                  ·
                    refine ⟨17408590769932973841882469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23211454359910631789176625 17408590769932973841882469)
                    ·
                      refine ⟨3264110769362432595352963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17408590769932973841882469 3264110769362432595352963)
                      ·
                        rfl

theorem cell23_6356833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_6356833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356833 prefixEnd_6356833 := by exact prefixLift 6356833
  have htrace : WordTrace (prefixWord ++ tailWord_6356833) baseStart_6356833 baseEnd_6356833 := by
    simpa [prefixWord, tailWord_6356833, baseEnd_6356833] using wordTrace_append hprefix tailTrace_6356833
  have hstable : (prefixWord ++ tailWord_6356833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356833).length < 2 ^ (prefixWord ++ tailWord_6356833).sum := by decide
  have hdescent : baseEnd_6356833 < baseStart_6356833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356888 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6356888 : Nat := 118140960795 + 6356888 * 2 ^ 59
def prefixEnd_6356888 : Nat := 4983230072969 + 3 ^ 40 * 6356888 * 2
def baseEnd_6356888 : Nat := 3264139010798429880165211

theorem tailTrace_6356888 : CollatzResearch.WordTrace tailWord_6356888 prefixEnd_6356888 3264139010798429880165211 := by
  unfold tailWord_6356888
  simp only [CollatzResearch.WordTrace]
  refine ⟨115927376497043960440451659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154569835329391947253935545 115927376497043960440451659)
  ·
    refine ⟨173891064745565940660677489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115927376497043960440451659 173891064745565940660677489)
    ·
      refine ⟨130418298559174455495508117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173891064745565940660677489 130418298559174455495508117)
      ·
        refine ⟨6113357744961302601351943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130418298559174455495508117 6113357744961302601351943)
        ·
          refine ⟨9170036617441953902027915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113357744961302601351943 9170036617441953902027915)
          ·
            refine ⟨13755054926162930853041873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170036617441953902027915 13755054926162930853041873)
            ·
              refine ⟨10316291194622198139781405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13755054926162930853041873 10316291194622198139781405)
              ·
                refine ⟨3868609197983324302418027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10316291194622198139781405 3868609197983324302418027)
                ·
                  refine ⟨5802913796974986453627041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868609197983324302418027 5802913796974986453627041)
                  ·
                    refine ⟨4352185347731239840220281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5802913796974986453627041 4352185347731239840220281)
                    ·
                      refine ⟨3264139010798429880165211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352185347731239840220281 3264139010798429880165211)
                      ·
                        rfl

theorem cell23_6356888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6356888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356888 prefixEnd_6356888 := by exact prefixLift 6356888
  have htrace : WordTrace (prefixWord ++ tailWord_6356888) baseStart_6356888 baseEnd_6356888 := by
    simpa [prefixWord, tailWord_6356888, baseEnd_6356888] using wordTrace_append hprefix tailTrace_6356888
  have hstable : (prefixWord ++ tailWord_6356888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356888).length < 2 ^ (prefixWord ++ tailWord_6356888).sum := by decide
  have hdescent : baseEnd_6356888 < baseStart_6356888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6356967 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 7]
def baseStart_6356967 : Nat := 118140960795 + 6356967 * 2 ^ 59
def prefixEnd_6356967 : Nat := 4983230072969 + 3 ^ 40 * 6356967 * 2
def baseEnd_6356967 : Nat := 362686619530015007897483

theorem tailTrace_6356967 : CollatzResearch.WordTrace tailWord_6356967 prefixEnd_6356967 362686619530015007897483 := by
  unfold tailWord_6356967
  simp only [CollatzResearch.WordTrace]
  refine ⟨231857634360801717373029155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154571756240534478248686103 231857634360801717373029155)
  ·
    refine ⟨347786451541202576059543733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231857634360801717373029155 347786451541202576059543733)
    ·
      refine ⟨32604979831987741505582225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 347786451541202576059543733 32604979831987741505582225)
      ·
        refine ⟨24453734873990806129186669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32604979831987741505582225 24453734873990806129186669)
        ·
          refine ⟨9170150577746552298445001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24453734873990806129186669 9170150577746552298445001)
          ·
            refine ⟨6877612933309914223833751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170150577746552298445001 6877612933309914223833751)
            ·
              refine ⟨10316419399964871335750627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877612933309914223833751 10316419399964871335750627)
              ·
                refine ⟨15474629099947307003625941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10316419399964871335750627 15474629099947307003625941)
                ·
                  refine ⟨362686619530015007897483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15474629099947307003625941 362686619530015007897483)
                  ·
                    rfl

theorem cell23_6356967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 7].length) (baseStart_6356967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6356967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6356967 prefixEnd_6356967 := by exact prefixLift 6356967
  have htrace : WordTrace (prefixWord ++ tailWord_6356967) baseStart_6356967 baseEnd_6356967 := by
    simpa [prefixWord, tailWord_6356967, baseEnd_6356967] using wordTrace_append hprefix tailTrace_6356967
  have hstable : (prefixWord ++ tailWord_6356967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6356967).length < 2 ^ (prefixWord ++ tailWord_6356967).sum := by decide
  have hdescent : baseEnd_6356967 < baseStart_6356967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6356967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357034 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6357034 : Nat := 118140960795 + 6357034 * 2 ^ 59
def prefixEnd_6357034 : Nat := 4983230072969 + 3 ^ 40 * 6357034 * 2
def baseEnd_6357034 : Nat := 3264213978973986308939539

theorem tailTrace_6357034 : CollatzResearch.WordTrace tailWord_6357034 prefixEnd_6357034 3264213978973986308939539 := by
  unfold tailWord_6357034
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965019512889746953929539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154573385367705991877145437 57965019512889746953929539)
  ·
    refine ⟨86947529269334620430894309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57965019512889746953929539 86947529269334620430894309)
    ·
      refine ⟨16302661738000241330792683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86947529269334620430894309 16302661738000241330792683)
      ·
        refine ⟨24453992607000361996189025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16302661738000241330792683 24453992607000361996189025)
        ·
          refine ⟨18340494455250271497141769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24453992607000361996189025 18340494455250271497141769)
          ·
            refine ⟨13755370841437703622856327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18340494455250271497141769 13755370841437703622856327)
            ·
              refine ⟨20633056262156555434284491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13755370841437703622856327 20633056262156555434284491)
              ·
                refine ⟨30949584393234833151426737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20633056262156555434284491 30949584393234833151426737)
                ·
                  refine ⟨23212188294926124863570053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30949584393234833151426737 23212188294926124863570053)
                  ·
                    refine ⟨4352285305298648411919385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23212188294926124863570053 4352285305298648411919385)
                    ·
                      refine ⟨3264213978973986308939539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352285305298648411919385 3264213978973986308939539)
                      ·
                        rfl

theorem cell23_6357034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6357034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357034 prefixEnd_6357034 := by exact prefixLift 6357034
  have htrace : WordTrace (prefixWord ++ tailWord_6357034) baseStart_6357034 baseEnd_6357034 := by
    simpa [prefixWord, tailWord_6357034, baseEnd_6357034] using wordTrace_append hprefix tailTrace_6357034
  have hstable : (prefixWord ++ tailWord_6357034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357034).length < 2 ^ (prefixWord ++ tailWord_6357034).sum := by decide
  have hdescent : baseEnd_6357034 < baseStart_6357034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357040 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 6]
def baseStart_6357040 : Nat := 118140960795 + 6357040 * 2 ^ 59
def prefixEnd_6357040 : Nat := 4983230072969 + 3 ^ 40 * 6357040 * 2
def baseEnd_6357040 : Nat := 362690784428657031718279

theorem tailTrace_6357040 : CollatzResearch.WordTrace tailWord_6357040 prefixEnd_6357040 362690784428657031718279 := by
  unfold tailWord_6357040
  simp only [CollatzResearch.WordTrace]
  refine ⟨115930148444768625420218287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154573531259691500560291049 115930148444768625420218287)
  ·
    refine ⟨173895222667152938130327431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115930148444768625420218287 173895222667152938130327431)
    ·
      refine ⟨260842834000729407195491147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173895222667152938130327431 260842834000729407195491147)
      ·
        refine ⟨391264251001094110793236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260842834000729407195491147 391264251001094110793236721)
        ·
          refine ⟨293448188250820583094927541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391264251001094110793236721 293448188250820583094927541)
          ·
            refine ⟨27510767648514429665149457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 293448188250820583094927541 27510767648514429665149457)
            ·
              refine ⟨20633075736385822248862093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27510767648514429665149457 20633075736385822248862093)
              ·
                refine ⟨7737403401144683343323285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20633075736385822248862093 7737403401144683343323285)
                ·
                  refine ⟨362690784428657031718279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7737403401144683343323285 362690784428657031718279)
                  ·
                    rfl

theorem cell23_6357040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 6].length) (baseStart_6357040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357040 prefixEnd_6357040 := by exact prefixLift 6357040
  have htrace : WordTrace (prefixWord ++ tailWord_6357040) baseStart_6357040 baseEnd_6357040 := by
    simpa [prefixWord, tailWord_6357040, baseEnd_6357040] using wordTrace_append hprefix tailTrace_6357040
  have hstable : (prefixWord ++ tailWord_6357040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357040).length < 2 ^ (prefixWord ++ tailWord_6357040).sum := by decide
  have hdescent : baseEnd_6357040 < baseStart_6357040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357054 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6357054 : Nat := 118140960795 + 6357054 * 2 ^ 59
def prefixEnd_6357054 : Nat := 4983230072969 + 3 ^ 40 * 6357054 * 2
def baseEnd_6357054 : Nat := 3264224248587076230689447

theorem tailTrace_6357054 : CollatzResearch.WordTrace tailWord_6357054 prefixEnd_6357054 3264224248587076230689447 := by
  unfold tailWord_6357054
  simp only [CollatzResearch.WordTrace]
  refine ⟨28982600938935816403930777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154573871674324354154297477 28982600938935816403930777)
  ·
    refine ⟨21736950704201862302948083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28982600938935816403930777 21736950704201862302948083)
    ·
      refine ⟨32605426056302793454422125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21736950704201862302948083 32605426056302793454422125)
      ·
        refine ⟨12227034771113547545408297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32605426056302793454422125 12227034771113547545408297)
        ·
          refine ⟨9170276078335160659056223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12227034771113547545408297 9170276078335160659056223)
          ·
            refine ⟨13755414117502740988584335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170276078335160659056223 13755414117502740988584335)
            ·
              refine ⟨20633121176254111482876503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13755414117502740988584335 20633121176254111482876503)
              ·
                refine ⟨30949681764381167224314755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20633121176254111482876503 30949681764381167224314755)
                ·
                  refine ⟨46424522646571750836472133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30949681764381167224314755 46424522646571750836472133)
                  ·
                    refine ⟨8704597996232203281838525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46424522646571750836472133 8704597996232203281838525)
                    ·
                      refine ⟨3264224248587076230689447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704597996232203281838525 3264224248587076230689447)
                      ·
                        rfl

theorem cell23_6357054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6357054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357054 prefixEnd_6357054 := by exact prefixLift 6357054
  have htrace : WordTrace (prefixWord ++ tailWord_6357054) baseStart_6357054 baseEnd_6357054 := by
    simpa [prefixWord, tailWord_6357054, baseEnd_6357054] using wordTrace_append hprefix tailTrace_6357054
  have hstable : (prefixWord ++ tailWord_6357054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357054).length < 2 ^ (prefixWord ++ tailWord_6357054).sum := by decide
  have hdescent : baseEnd_6357054 < baseStart_6357054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357074 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_6357074 : Nat := 118140960795 + 6357074 * 2 ^ 59
def prefixEnd_6357074 : Nat := 4983230072969 + 3 ^ 40 * 6357074 * 2
def baseEnd_6357074 : Nat := 362692724244462905826595

theorem tailTrace_6357074 : CollatzResearch.WordTrace tailWord_6357074 prefixEnd_6357074 362692724244462905826595 := by
  unfold tailWord_6357074
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965384242853518661793569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154574357980942716431449517 57965384242853518661793569)
  ·
    refine ⟨43474038182140138996345177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57965384242853518661793569 43474038182140138996345177)
    ·
      refine ⟨32605528636605104247258883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43474038182140138996345177 32605528636605104247258883)
      ·
        refine ⟨48908292954907656370888325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32605528636605104247258883 48908292954907656370888325)
        ·
          refine ⟨9170304929045185569541561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48908292954907656370888325 9170304929045185569541561)
          ·
            refine ⟨6877728696783889177156171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170304929045185569541561 6877728696783889177156171)
            ·
              refine ⟨10316593045175833765734257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877728696783889177156171 10316593045175833765734257)
              ·
                refine ⟨7737444783881875324300693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10316593045175833765734257 7737444783881875324300693)
                ·
                  refine ⟨362692724244462905826595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7737444783881875324300693 362692724244462905826595)
                  ·
                    rfl

theorem cell23_6357074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_6357074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357074 prefixEnd_6357074 := by exact prefixLift 6357074
  have htrace : WordTrace (prefixWord ++ tailWord_6357074) baseStart_6357074 baseEnd_6357074 := by
    simpa [prefixWord, tailWord_6357074, baseEnd_6357074] using wordTrace_append hprefix tailTrace_6357074
  have hstable : (prefixWord ++ tailWord_6357074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357074).length < 2 ^ (prefixWord ++ tailWord_6357074).sum := by decide
  have hdescent : baseEnd_6357074 < baseStart_6357074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357078 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6357078 : Nat := 118140960795 + 6357078 * 2 ^ 59
def prefixEnd_6357078 : Nat := 4983230072969 + 3 ^ 40 * 6357078 * 2
def baseEnd_6357078 : Nat := 1088078857374261378929779

theorem tailTrace_6357078 : CollatzResearch.WordTrace tailWord_6357078 prefixEnd_6357078 1088078857374261378929779 := by
  unfold tailWord_6357078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491355178962473958144993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154574455242266388886879925 14491355178962473958144993)
  ·
    refine ⟨10868516384221855468608745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14491355178962473958144993 10868516384221855468608745)
    ·
      refine ⟨8151387288166391601456559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10868516384221855468608745 8151387288166391601456559)
      ·
        refine ⟨12227080932249587402184839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151387288166391601456559 12227080932249587402184839)
        ·
          refine ⟨18340621398374381103277259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227080932249587402184839 18340621398374381103277259)
          ·
            refine ⟨27510932097561571654915889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18340621398374381103277259 27510932097561571654915889)
            ·
              refine ⟨20633199073171178741186917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27510932097561571654915889 20633199073171178741186917)
              ·
                refine ⟨3868724826219596013972547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20633199073171178741186917 3868724826219596013972547)
                ·
                  refine ⟨5803087239329394020958821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868724826219596013972547 5803087239329394020958821)
                  ·
                    refine ⟨1088078857374261378929779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803087239329394020958821 1088078857374261378929779)
                    ·
                      rfl

theorem cell23_6357078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6357078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357078 prefixEnd_6357078 := by exact prefixLift 6357078
  have htrace : WordTrace (prefixWord ++ tailWord_6357078) baseStart_6357078 baseEnd_6357078 := by
    simpa [prefixWord, tailWord_6357078, baseEnd_6357078] using wordTrace_append hprefix tailTrace_6357078
  have hstable : (prefixWord ++ tailWord_6357078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357078).length < 2 ^ (prefixWord ++ tailWord_6357078).sum := by decide
  have hdescent : baseEnd_6357078 < baseStart_6357078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357084 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_6357084 : Nat := 118140960795 + 6357084 * 2 ^ 59
def prefixEnd_6357084 : Nat := 4983230072969 + 3 ^ 40 * 6357084 * 2
def baseEnd_6357084 : Nat := 3264239653006711113314309

theorem tailTrace_6357084 : CollatzResearch.WordTrace tailWord_6357084 prefixEnd_6357084 3264239653006711113314309 := by
  unfold tailWord_6357084
  simp only [CollatzResearch.WordTrace]
  refine ⟨115930950850688923177519153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154574601134251897570025537 115930950850688923177519153)
  ·
    refine ⟨86948213138016692383139365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115930950850688923177519153 86948213138016692383139365)
    ·
      refine ⟨16302789963378129821838631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86948213138016692383139365 16302789963378129821838631)
      ·
        refine ⟨24454184945067194732757947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16302789963378129821838631 24454184945067194732757947)
        ·
          refine ⟨36681277417600792099136921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24454184945067194732757947 36681277417600792099136921)
          ·
            refine ⟨27510958063200594074352691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36681277417600792099136921 27510958063200594074352691)
            ·
              refine ⟨41266437094800891111529037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27510958063200594074352691 41266437094800891111529037)
              ·
                refine ⟨15474913910550334166823389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41266437094800891111529037 15474913910550334166823389)
                ·
                  refine ⟨5803092716456375312558771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15474913910550334166823389 5803092716456375312558771)
                  ·
                    refine ⟨8704639074684562968838157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803092716456375312558771 8704639074684562968838157)
                    ·
                      refine ⟨3264239653006711113314309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704639074684562968838157 3264239653006711113314309)
                      ·
                        rfl

theorem cell23_6357084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_6357084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357084 prefixEnd_6357084 := by exact prefixLift 6357084
  have htrace : WordTrace (prefixWord ++ tailWord_6357084) baseStart_6357084 baseEnd_6357084 := by
    simpa [prefixWord, tailWord_6357084, baseEnd_6357084] using wordTrace_append hprefix tailTrace_6357084
  have hstable : (prefixWord ++ tailWord_6357084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357084).length < 2 ^ (prefixWord ++ tailWord_6357084).sum := by decide
  have hdescent : baseEnd_6357084 < baseStart_6357084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357117 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_6357117 : Nat := 118140960795 + 6357117 * 2 ^ 59
def prefixEnd_6357117 : Nat := 4983230072969 + 3 ^ 40 * 6357117 * 2
def baseEnd_6357117 : Nat := 1088085532622769828067219

theorem tailTrace_6357117 : CollatzResearch.WordTrace tailWord_6357117 prefixEnd_6357117 1088085532622769828067219 := by
  unfold tailWord_6357117
  simp only [CollatzResearch.WordTrace]
  refine ⟨231863105310258292990989605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154575403540172195327326403 231863105310258292990989605)
  ·
    refine ⟨43474332245673429935810551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231863105310258292990989605 43474332245673429935810551)
    ·
      refine ⟨65211498368510144903715827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43474332245673429935810551 65211498368510144903715827)
      ·
        refine ⟨97817247552765217355573741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65211498368510144903715827 97817247552765217355573741)
        ·
          refine ⟨36681467832286956508340153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97817247552765217355573741 36681467832286956508340153)
          ·
            refine ⟨27511100874215217381255115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36681467832286956508340153 27511100874215217381255115)
            ·
              refine ⟨41266651311322826071882673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27511100874215217381255115 41266651311322826071882673)
              ·
                refine ⟨30949988483492119553912005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41266651311322826071882673 30949988483492119553912005)
                ·
                  refine ⟨5803122840654772416358501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30949988483492119553912005 5803122840654772416358501)
                  ·
                    refine ⟨1088085532622769828067219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803122840654772416358501 1088085532622769828067219)
                    ·
                      rfl

theorem cell23_6357117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_6357117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357117 prefixEnd_6357117 := by exact prefixLift 6357117
  have htrace : WordTrace (prefixWord ++ tailWord_6357117) baseStart_6357117 baseEnd_6357117 := by
    simpa [prefixWord, tailWord_6357117, baseEnd_6357117] using wordTrace_append hprefix tailTrace_6357117
  have hstable : (prefixWord ++ tailWord_6357117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357117).length < 2 ^ (prefixWord ++ tailWord_6357117).sum := by decide
  have hdescent : baseEnd_6357117 < baseStart_6357117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357120 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4]
def baseStart_6357120 : Nat := 118140960795 + 6357120 * 2 ^ 59
def prefixEnd_6357120 : Nat := 4983230072969 + 3 ^ 40 * 6357120 * 2
def baseEnd_6357120 : Nat := 3264258138310272972464143

theorem tailTrace_6357120 : CollatzResearch.WordTrace tailWord_6357120 prefixEnd_6357120 3264258138310272972464143 := by
  unfold tailWord_6357120
  simp only [CollatzResearch.WordTrace]
  refine ⟨115931607364623712251674407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154575476486164949668899209 115931607364623712251674407)
  ·
    refine ⟨173897411046935568377511611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115931607364623712251674407 173897411046935568377511611)
    ·
      refine ⟨260846116570403352566267417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173897411046935568377511611 260846116570403352566267417)
      ·
        refine ⟨195634587427802514424700563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260846116570403352566267417 195634587427802514424700563)
        ·
          refine ⟨293451881141703771637050845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195634587427802514424700563 293451881141703771637050845)
          ·
            refine ⟨110044455428138914363894067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293451881141703771637050845 110044455428138914363894067)
            ·
              refine ⟨165066683142208371545841101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110044455428138914363894067 165066683142208371545841101)
              ·
                refine ⟨61900006178328139329690413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165066683142208371545841101 61900006178328139329690413)
                ·
                  refine ⟨23212502316873052248633905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61900006178328139329690413 23212502316873052248633905)
                  ·
                    refine ⟨17409376737654789186475429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23212502316873052248633905 17409376737654789186475429)
                    ·
                      refine ⟨3264258138310272972464143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17409376737654789186475429 3264258138310272972464143)
                      ·
                        rfl

theorem cell23_6357120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_6357120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357120 prefixEnd_6357120 := by exact prefixLift 6357120
  have htrace : WordTrace (prefixWord ++ tailWord_6357120) baseStart_6357120 baseEnd_6357120 := by
    simpa [prefixWord, tailWord_6357120, baseEnd_6357120] using wordTrace_append hprefix tailTrace_6357120
  have hstable : (prefixWord ++ tailWord_6357120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357120).length < 2 ^ (prefixWord ++ tailWord_6357120).sum := by decide
  have hdescent : baseEnd_6357120 < baseStart_6357120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357130 : List Nat := [3, 1, 2, 3, 1, 2, 11]
def baseStart_6357130 : Nat := 118140960795 + 6357130 * 2 ^ 59
def prefixEnd_6357130 : Nat := 4983230072969 + 3 ^ 40 * 6357130 * 2
def baseEnd_6357130 : Nat := 40299546581689110288137

theorem tailTrace_6357130 : CollatzResearch.WordTrace tailWord_6357130 prefixEnd_6357130 40299546581689110288137 := by
  unfold tailWord_6357130
  simp only [CollatzResearch.WordTrace]
  refine ⟨57965894864802799052803211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154575719639474130807475229 57965894864802799052803211)
  ·
    refine ⟨86948842297204198579204817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57965894864802799052803211 86948842297204198579204817)
    ·
      refine ⟨65211631722903148934403613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86948842297204198579204817 65211631722903148934403613)
      ·
        refine ⟨24454361896088680850401355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65211631722903148934403613 24454361896088680850401355)
        ·
          refine ⟨36681542844133021275602033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24454361896088680850401355 36681542844133021275602033)
          ·
            refine ⟨27511157133099765956701525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36681542844133021275602033 27511157133099765956701525)
            ·
              refine ⟨40299546581689110288137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 27511157133099765956701525 40299546581689110288137)
              ·
                rfl

theorem cell23_6357130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 11].length) (baseStart_6357130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357130 prefixEnd_6357130 := by exact prefixLift 6357130
  have htrace : WordTrace (prefixWord ++ tailWord_6357130) baseStart_6357130 baseEnd_6357130 := by
    simpa [prefixWord, tailWord_6357130, baseEnd_6357130] using wordTrace_append hprefix tailTrace_6357130
  have hstable : (prefixWord ++ tailWord_6357130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357130).length < 2 ^ (prefixWord ++ tailWord_6357130).sum := by decide
  have hdescent : baseEnd_6357130 < baseStart_6357130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357142 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6357142 : Nat := 118140960795 + 6357142 * 2 ^ 59
def prefixEnd_6357142 : Nat := 4983230072969 + 3 ^ 40 * 6357142 * 2
def baseEnd_6357142 : Nat := 362696603876074654043227

theorem tailTrace_6357142 : CollatzResearch.WordTrace tailWord_6357142 prefixEnd_6357142 362696603876074654043227 := by
  unfold tailWord_6357142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491501070947982641290605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154576011423445148173766453 14491501070947982641290605)
  ·
    refine ⟨5434312901605493490483977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14491501070947982641290605 5434312901605493490483977)
    ·
      refine ⟨4075734676204120117862983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5434312901605493490483977 4075734676204120117862983)
      ·
        refine ⟨6113602014306180176794475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075734676204120117862983 6113602014306180176794475)
        ·
          refine ⟨9170403021459270265191713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113602014306180176794475 9170403021459270265191713)
          ·
            refine ⟨6877802266094452698893785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170403021459270265191713 6877802266094452698893785)
            ·
              refine ⟨5158351699570839524170339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6877802266094452698893785 5158351699570839524170339)
              ·
                refine ⟨7737527549356259286255509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158351699570839524170339 7737527549356259286255509)
                ·
                  refine ⟨362696603876074654043227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7737527549356259286255509 362696603876074654043227)
                  ·
                    rfl

theorem cell23_6357142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6357142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357142 prefixEnd_6357142 := by exact prefixLift 6357142
  have htrace : WordTrace (prefixWord ++ tailWord_6357142) baseStart_6357142 baseEnd_6357142 := by
    simpa [prefixWord, tailWord_6357142, baseEnd_6357142] using wordTrace_append hprefix tailTrace_6357142
  have hstable : (prefixWord ++ tailWord_6357142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357142).length < 2 ^ (prefixWord ++ tailWord_6357142).sum := by decide
  have hdescent : baseEnd_6357142 < baseStart_6357142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357151 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 2, 4]
def baseStart_6357151 : Nat := 118140960795 + 6357151 * 2 ^ 59
def prefixEnd_6357151 : Nat := 4983230072969 + 3 ^ 40 * 6357151 * 2
def baseEnd_6357151 : Nat := 1088091352070187450392167

theorem tailTrace_6357151 : CollatzResearch.WordTrace tailWord_6357151 prefixEnd_6357151 1088091352070187450392167 := by
  unfold tailWord_6357151
  simp only [CollatzResearch.WordTrace]
  refine ⟨231864345392135116797727307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154576230261423411198484871 231864345392135116797727307)
  ·
    refine ⟨347796518088202675196590961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231864345392135116797727307 347796518088202675196590961)
    ·
      refine ⟨260847388566152006397443221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347796518088202675196590961 260847388566152006397443221)
      ·
        refine ⟨12227221339038375299880151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 260847388566152006397443221 12227221339038375299880151)
        ·
          refine ⟨18340832008557562949820227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12227221339038375299880151 18340832008557562949820227)
          ·
            refine ⟨27511248012836344424730341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18340832008557562949820227 27511248012836344424730341)
            ·
              refine ⟨5158359002406814579636939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27511248012836344424730341 5158359002406814579636939)
              ·
                refine ⟨7737538503610221869455409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158359002406814579636939 7737538503610221869455409)
                ·
                  refine ⟨5803153877707666402091557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7737538503610221869455409 5803153877707666402091557)
                  ·
                    refine ⟨1088091352070187450392167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803153877707666402091557 1088091352070187450392167)
                    ·
                      rfl

theorem cell23_6357151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_6357151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357151 prefixEnd_6357151 := by exact prefixLift 6357151
  have htrace : WordTrace (prefixWord ++ tailWord_6357151) baseStart_6357151 baseEnd_6357151 := by
    simpa [prefixWord, tailWord_6357151, baseEnd_6357151] using wordTrace_append hprefix tailTrace_6357151
  have hstable : (prefixWord ++ tailWord_6357151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357151).length < 2 ^ (prefixWord ++ tailWord_6357151).sum := by decide
  have hdescent : baseEnd_6357151 < baseStart_6357151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357157 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_6357157 : Nat := 118140960795 + 6357157 * 2 ^ 59
def prefixEnd_6357157 : Nat := 4983230072969 + 3 ^ 40 * 6357157 * 2
def baseEnd_6357157 : Nat := 3264277137094489327701473

theorem tailTrace_6357157 : CollatzResearch.WordTrace tailWord_6357157 prefixEnd_6357157 3264277137094489327701473 := by
  unfold tailWord_6357157
  simp only [CollatzResearch.WordTrace]
  refine ⟨231864564230113379822445725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154576376153408919881630483 231864564230113379822445725)
  ·
    refine ⟨86949211586292517433417147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231864564230113379822445725 86949211586292517433417147)
    ·
      refine ⟨130423817379438776150125721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86949211586292517433417147 130423817379438776150125721)
      ·
        refine ⟨97817863034579082112594291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130423817379438776150125721 97817863034579082112594291)
        ·
          refine ⟨146726794551868623168891437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97817863034579082112594291 146726794551868623168891437)
          ·
            refine ⟨55022547956950733688334289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 146726794551868623168891437 55022547956950733688334289)
            ·
              refine ⟨41266910967713050266250717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55022547956950733688334289 41266910967713050266250717)
              ·
                refine ⟨15475091612892393849844019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41266910967713050266250717 15475091612892393849844019)
                ·
                  refine ⟨23212637419338590774766029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15475091612892393849844019 23212637419338590774766029)
                  ·
                    refine ⟨8704739032251971540537261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23212637419338590774766029 8704739032251971540537261)
                    ·
                      refine ⟨3264277137094489327701473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704739032251971540537261 3264277137094489327701473)
                      ·
                        rfl

theorem cell23_6357157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_6357157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357157 prefixEnd_6357157 := by exact prefixLift 6357157
  have htrace : WordTrace (prefixWord ++ tailWord_6357157) baseStart_6357157 baseEnd_6357157 := by
    simpa [prefixWord, tailWord_6357157, baseEnd_6357157] using wordTrace_append hprefix tailTrace_6357157
  have hstable : (prefixWord ++ tailWord_6357157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357157).length < 2 ^ (prefixWord ++ tailWord_6357157).sum := by decide
  have hdescent : baseEnd_6357157 < baseStart_6357157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357217 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_6357217 : Nat := 118140960795 + 6357217 * 2 ^ 59
def prefixEnd_6357217 : Nat := 4983230072969 + 3 ^ 40 * 6357217 * 2
def baseEnd_6357217 : Nat := 3264307945933759092951197

theorem tailTrace_6357217 : CollatzResearch.WordTrace tailWord_6357217 prefixEnd_6357217 3264307945933759092951197 := by
  unfold tailWord_6357217
  simp only [CollatzResearch.WordTrace]
  refine ⟨231866752609896010069629905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154577835073264006713086603 231866752609896010069629905)
  ·
    refine ⟨173900064457422007552222429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231866752609896010069629905 173900064457422007552222429)
    ·
      refine ⟨65212524171533252832083411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173900064457422007552222429 65212524171533252832083411)
      ·
        refine ⟨97818786257299879248125117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65212524171533252832083411 97818786257299879248125117)
        ·
          refine ⟨36682044846487454718046919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97818786257299879248125117 36682044846487454718046919)
          ·
            refine ⟨55023067269731182077070379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36682044846487454718046919 55023067269731182077070379)
            ·
              refine ⟨82534600904596773115605569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55023067269731182077070379 82534600904596773115605569)
              ·
                refine ⟨61900950678447579836704177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82534600904596773115605569 61900950678447579836704177)
                ·
                  refine ⟨46425713008835684877528133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61900950678447579836704177 46425713008835684877528133)
                  ·
                    refine ⟨8704821189156690914536525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46425713008835684877528133 8704821189156690914536525)
                    ·
                      refine ⟨3264307945933759092951197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704821189156690914536525 3264307945933759092951197)
                      ·
                        rfl

theorem cell23_6357217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_6357217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357217 prefixEnd_6357217 := by exact prefixLift 6357217
  have htrace : WordTrace (prefixWord ++ tailWord_6357217) baseStart_6357217 baseEnd_6357217 := by
    simpa [prefixWord, tailWord_6357217, baseEnd_6357217] using wordTrace_append hprefix tailTrace_6357217
  have hstable : (prefixWord ++ tailWord_6357217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357217).length < 2 ^ (prefixWord ++ tailWord_6357217).sum := by decide
  have hdescent : baseEnd_6357217 < baseStart_6357217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357247 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_6357247 : Nat := 118140960795 + 6357247 * 2 ^ 59
def prefixEnd_6357247 : Nat := 4983230072969 + 3 ^ 40 * 6357247 * 2
def baseEnd_6357247 : Nat := 3264323350353393975576059

theorem tailTrace_6357247 : CollatzResearch.WordTrace tailWord_6357247 prefixEnd_6357247 3264323350353393975576059 := by
  unfold tailWord_6357247
  simp only [CollatzResearch.WordTrace]
  refine ⟨231867846799787325193221995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154578564533191550128814663 231867846799787325193221995)
  ·
    refine ⟨347801770199680987789832993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231867846799787325193221995 347801770199680987789832993)
    ·
      refine ⟨260851327649760740842374745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347801770199680987789832993 260851327649760740842374745)
      ·
        refine ⟨195638495737320555631781059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260851327649760740842374745 195638495737320555631781059)
        ·
          refine ⟨293457743605980833447671589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 195638495737320555631781059 293457743605980833447671589)
          ·
            refine ⟨55023326926121406271438423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 293457743605980833447671589 55023326926121406271438423)
            ·
              refine ⟨82534990389182109407157635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55023326926121406271438423 82534990389182109407157635)
              ·
                refine ⟨123802485583773164110736453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82534990389182109407157635 123802485583773164110736453)
                ·
                  refine ⟨23212966046957468270763085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123802485583773164110736453 23212966046957468270763085)
                  ·
                    refine ⟨8704862267609050601536157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23212966046957468270763085 8704862267609050601536157)
                    ·
                      refine ⟨3264323350353393975576059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704862267609050601536157 3264323350353393975576059)
                      ·
                        rfl

theorem cell23_6357247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_6357247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357247 prefixEnd_6357247 := by exact prefixLift 6357247
  have htrace : WordTrace (prefixWord ++ tailWord_6357247) baseStart_6357247 baseEnd_6357247 := by
    simpa [prefixWord, tailWord_6357247, baseEnd_6357247] using wordTrace_append hprefix tailTrace_6357247
  have hstable : (prefixWord ++ tailWord_6357247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357247).length < 2 ^ (prefixWord ++ tailWord_6357247).sum := by decide
  have hdescent : baseEnd_6357247 < baseStart_6357247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357288 : List Nat := [2, 1, 5, 1, 3, 2, 1, 3, 5]
def baseStart_6357288 : Nat := 118140960795 + 6357288 * 2 ^ 59
def prefixEnd_6357288 : Nat := 4983230072969 + 3 ^ 40 * 6357288 * 2
def baseEnd_6357288 : Nat := 362704933673358701684819

theorem tailTrace_6357288 : CollatzResearch.WordTrace tailWord_6357288 prefixEnd_6357288 362704933673358701684819 := by
  unfold tailWord_6357288
  simp only [CollatzResearch.WordTrace]
  refine ⟨115934671096319394597732259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154579561461759192796976345 115934671096319394597732259)
  ·
    refine ⟨173902006644479091896598389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115934671096319394597732259 173902006644479091896598389)
    ·
      refine ⟨16303313122919914865306099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173902006644479091896598389 16303313122919914865306099)
      ·
        refine ⟨24454969684379872297959149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303313122919914865306099 24454969684379872297959149)
        ·
          refine ⟨9170613631642452111734681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24454969684379872297959149 9170613631642452111734681)
          ·
            refine ⟨6877960223731839083801011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170613631642452111734681 6877960223731839083801011)
            ·
              refine ⟨10316940335597758625701517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877960223731839083801011 10316940335597758625701517)
              ·
                refine ⟨3868852625849159484638069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10316940335597758625701517 3868852625849159484638069)
                ·
                  refine ⟨362704933673358701684819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868852625849159484638069 362704933673358701684819)
                  ·
                    rfl

theorem cell23_6357288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 5].length) (baseStart_6357288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357288 prefixEnd_6357288 := by exact prefixLift 6357288
  have htrace : WordTrace (prefixWord ++ tailWord_6357288) baseStart_6357288 baseEnd_6357288 := by
    simpa [prefixWord, tailWord_6357288, baseEnd_6357288] using wordTrace_append hprefix tailTrace_6357288
  have hstable : (prefixWord ++ tailWord_6357288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357288).length < 2 ^ (prefixWord ++ tailWord_6357288).sum := by decide
  have hdescent : baseEnd_6357288 < baseStart_6357288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357304 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_6357304 : Nat := 118140960795 + 6357304 * 2 ^ 59
def prefixEnd_6357304 : Nat := 4983230072969 + 3 ^ 40 * 6357304 * 2
def baseEnd_6357304 : Nat := 3264352618750700252563297

theorem tailTrace_6357304 : CollatzResearch.WordTrace tailWord_6357304 prefixEnd_6357304 3264352618750700252563297 := by
  unfold tailWord_6357304
  simp only [CollatzResearch.WordTrace]
  refine ⟨115934962880290411964023483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154579950507053882618697977 115934962880290411964023483)
  ·
    refine ⟨173902444320435617946035225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115934962880290411964023483 173902444320435617946035225)
    ·
      refine ⟨130426833240326713459526419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173902444320435617946035225 130426833240326713459526419)
      ·
        refine ⟨195640249860490070189289629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130426833240326713459526419 195640249860490070189289629)
        ·
          refine ⟨73365093697683776320983611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195640249860490070189289629 73365093697683776320983611)
          ·
            refine ⟨110047640546525664481475417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73365093697683776320983611 110047640546525664481475417)
            ·
              refine ⟨82535730409894248361106563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110047640546525664481475417 82535730409894248361106563)
              ·
                refine ⟨123803595614841372541659845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82535730409894248361106563 123803595614841372541659845)
                ·
                  refine ⟨23213174177782757351561221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 123803595614841372541659845 23213174177782757351561221)
                  ·
                    refine ⟨4352470158334267003417729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23213174177782757351561221 4352470158334267003417729)
                    ·
                      refine ⟨3264352618750700252563297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352470158334267003417729 3264352618750700252563297)
                      ·
                        rfl

theorem cell23_6357304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_6357304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357304 prefixEnd_6357304 := by exact prefixLift 6357304
  have htrace : WordTrace (prefixWord ++ tailWord_6357304) baseStart_6357304 baseEnd_6357304 := by
    simpa [prefixWord, tailWord_6357304, baseEnd_6357304] using wordTrace_append hprefix tailTrace_6357304
  have hstable : (prefixWord ++ tailWord_6357304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357304).length < 2 ^ (prefixWord ++ tailWord_6357304).sum := by decide
  have hdescent : baseEnd_6357304 < baseStart_6357304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357324 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6357324 : Nat := 118140960795 + 6357324 * 2 ^ 59
def prefixEnd_6357324 : Nat := 4983230072969 + 3 ^ 40 * 6357324 * 2
def baseEnd_6357324 : Nat := 3264362888363790174313205

theorem tailTrace_6357324 : CollatzResearch.WordTrace tailWord_6357324 prefixEnd_6357324 3264362888363790174313205 := by
  unfold tailWord_6357324
  simp only [CollatzResearch.WordTrace]
  refine ⟨115935327610254183671887513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154580436813672244895850017 115935327610254183671887513)
  ·
    refine ⟨86951495707690637753915635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115935327610254183671887513 86951495707690637753915635)
    ·
      refine ⟨130427243561535956630873453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86951495707690637753915635 130427243561535956630873453)
      ·
        refine ⟨48910216335575983736577545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130427243561535956630873453 48910216335575983736577545)
        ·
          refine ⟨36682662251681987802433159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48910216335575983736577545 36682662251681987802433159)
          ·
            refine ⟨55023993377522981703649739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36682662251681987802433159 55023993377522981703649739)
            ·
              refine ⟨82535990066284472555474609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55023993377522981703649739 82535990066284472555474609)
              ·
                refine ⟨61901992549713354416605957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82535990066284472555474609 61901992549713354416605957)
                ·
                  refine ⟨11606623603071253953113617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61901992549713354416605957 11606623603071253953113617)
                  ·
                    refine ⟨8704967702303440464835213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11606623603071253953113617 8704967702303440464835213)
                    ·
                      refine ⟨3264362888363790174313205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8704967702303440464835213 3264362888363790174313205)
                      ·
                        rfl

theorem cell23_6357324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6357324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357324 prefixEnd_6357324 := by exact prefixLift 6357324
  have htrace : WordTrace (prefixWord ++ tailWord_6357324) baseStart_6357324 baseEnd_6357324 := by
    simpa [prefixWord, tailWord_6357324, baseEnd_6357324] using wordTrace_append hprefix tailTrace_6357324
  have hstable : (prefixWord ++ tailWord_6357324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357324).length < 2 ^ (prefixWord ++ tailWord_6357324).sum := by decide
  have hdescent : baseEnd_6357324 < baseStart_6357324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357365 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6357365 : Nat := 118140960795 + 6357365 * 2 ^ 59
def prefixEnd_6357365 : Nat := 4983230072969 + 3 ^ 40 * 6357365 * 2
def baseEnd_6357365 : Nat := 1088127980356874837966839

theorem tailTrace_6357365 : CollatzResearch.WordTrace tailWord_6357365 prefixEnd_6357365 1088127980356874837966839 := by
  unfold tailWord_6357365
  simp only [CollatzResearch.WordTrace]
  refine ⟨231872150613359831346017549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154581433742239887564011699 231872150613359831346017549)
  ·
    refine ⟨86952056480009936754756581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231872150613359831346017549 86952056480009936754756581)
    ·
      refine ⟨16303510590001863141516859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86952056480009936754756581 16303510590001863141516859)
      ·
        refine ⟨24455265885002794712275289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303510590001863141516859 24455265885002794712275289)
        ·
          refine ⟨18341449413752096034206467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24455265885002794712275289 18341449413752096034206467)
          ·
            refine ⟨27512174120628144051309701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18341449413752096034206467 27512174120628144051309701)
            ·
              refine ⟨5158532647617777009620569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27512174120628144051309701 5158532647617777009620569)
              ·
                refine ⟨3868899485713332757215427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5158532647617777009620569 3868899485713332757215427)
                ·
                  refine ⟨5803349228569999135823141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3868899485713332757215427 5803349228569999135823141)
                  ·
                    refine ⟨1088127980356874837966839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803349228569999135823141 1088127980356874837966839)
                    ·
                      rfl

theorem cell23_6357365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6357365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357365 prefixEnd_6357365 := by exact prefixLift 6357365
  have htrace : WordTrace (prefixWord ++ tailWord_6357365) baseStart_6357365 baseEnd_6357365 := by
    simpa [prefixWord, tailWord_6357365, baseEnd_6357365] using wordTrace_append hprefix tailTrace_6357365
  have hstable : (prefixWord ++ tailWord_6357365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357365).length < 2 ^ (prefixWord ++ tailWord_6357365).sum := by decide
  have hdescent : baseEnd_6357365 < baseStart_6357365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357408 : List Nat := [2, 1, 1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_6357408 : Nat := 118140960795 + 6357408 * 2 ^ 59
def prefixEnd_6357408 : Nat := 4983230072969 + 3 ^ 40 * 6357408 * 2
def baseEnd_6357408 : Nat := 1088135340246255948554273

theorem tailTrace_6357408 : CollatzResearch.WordTrace tailWord_6357408 prefixEnd_6357408 1088135340246255948554273 := by
  unfold tailWord_6357408
  simp only [CollatzResearch.WordTrace]
  refine ⟨115936859476102024844916439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154582479301469366459888585 115936859476102024844916439)
  ·
    refine ⟨173905289214153037267374659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115936859476102024844916439 173905289214153037267374659)
    ·
      refine ⟨260857933821229555901061989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173905289214153037267374659 260857933821229555901061989)
      ·
        refine ⟨48910862591480541731449123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 260857933821229555901061989 48910862591480541731449123)
        ·
          refine ⟨73366293887220812597173685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48910862591480541731449123 73366293887220812597173685)
          ·
            refine ⟨6878090051926951180985033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73366293887220812597173685 6878090051926951180985033)
            ·
              refine ⟨5158567538945213385738775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878090051926951180985033 5158567538945213385738775)
              ·
                refine ⟨7737851308417820078608163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158567538945213385738775 7737851308417820078608163)
                ·
                  refine ⟨11606776962626730117912245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7737851308417820078608163 11606776962626730117912245)
                  ·
                    refine ⟨1088135340246255948554273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11606776962626730117912245 1088135340246255948554273)
                    ·
                      rfl

theorem cell23_6357408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_6357408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357408 prefixEnd_6357408 := by exact prefixLift 6357408
  have htrace : WordTrace (prefixWord ++ tailWord_6357408) baseStart_6357408 baseEnd_6357408 := by
    simpa [prefixWord, tailWord_6357408, baseEnd_6357408] using wordTrace_append hprefix tailTrace_6357408
  have hstable : (prefixWord ++ tailWord_6357408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357408).length < 2 ^ (prefixWord ++ tailWord_6357408).sum := by decide
  have hdescent : baseEnd_6357408 < baseStart_6357408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357411 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 4]
def baseStart_6357411 : Nat := 118140960795 + 6357411 * 2 ^ 59
def prefixEnd_6357411 : Nat := 4983230072969 + 3 ^ 40 * 6357411 * 2
def baseEnd_6357411 : Nat := 3264407561180731333925305

theorem tailTrace_6357411 : CollatzResearch.WordTrace tailWord_6357411 prefixEnd_6357411 3264407561180731333925305 := by
  unfold tailWord_6357411
  simp only [CollatzResearch.WordTrace]
  refine ⟨231873828371193181202192087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154582552247462120801461391 231873828371193181202192087)
  ·
    refine ⟨347810742556789771803288131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231873828371193181202192087 347810742556789771803288131)
    ·
      refine ⟨521716113835184657704932197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347810742556789771803288131 521716113835184657704932197)
      ·
        refine ⟨97821771344097123319674787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 521716113835184657704932197 97821771344097123319674787)
        ·
          refine ⟨146732657016145684979512181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97821771344097123319674787 146732657016145684979512181)
          ·
            refine ⟨13756186595263657966829267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146732657016145684979512181 13756186595263657966829267)
            ·
              refine ⟨20634279892895486950243901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13756186595263657966829267 20634279892895486950243901)
              ·
                refine ⟨7737854959835807606341463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20634279892895486950243901 7737854959835807606341463)
                ·
                  refine ⟨11606782439753711409512195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7737854959835807606341463 11606782439753711409512195)
                  ·
                    refine ⟨17410173659630567114268293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11606782439753711409512195 17410173659630567114268293)
                    ·
                      refine ⟨3264407561180731333925305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17410173659630567114268293 3264407561180731333925305)
                      ·
                        rfl

theorem cell23_6357411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_6357411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357411 prefixEnd_6357411 := by exact prefixLift 6357411
  have htrace : WordTrace (prefixWord ++ tailWord_6357411) baseStart_6357411 baseEnd_6357411 := by
    simpa [prefixWord, tailWord_6357411, baseEnd_6357411] using wordTrace_append hprefix tailTrace_6357411
  have hstable : (prefixWord ++ tailWord_6357411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357411).length < 2 ^ (prefixWord ++ tailWord_6357411).sum := by decide
  have hdescent : baseEnd_6357411 < baseStart_6357411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357427 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_6357427 : Nat := 118140960795 + 6357427 * 2 ^ 59
def prefixEnd_6357427 : Nat := 4983230072969 + 3 ^ 40 * 6357427 * 2
def baseEnd_6357427 : Nat := 3264415776871203271325231

theorem tailTrace_6357427 : CollatzResearch.WordTrace tailWord_6357427 prefixEnd_6357427 3264415776871203271325231 := by
  unfold tailWord_6357427
  simp only [CollatzResearch.WordTrace]
  refine ⟨231874411939135215934774535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154582941292756810623183023 231874411939135215934774535)
  ·
    refine ⟨347811617908702823902161803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231874411939135215934774535 347811617908702823902161803)
    ·
      refine ⟨521717426863054235853242705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347811617908702823902161803 521717426863054235853242705)
      ·
        refine ⟨391288070147290676889932029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521717426863054235853242705 391288070147290676889932029)
        ·
          refine ⟨146733026305234003833724511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 391288070147290676889932029 146733026305234003833724511)
          ·
            refine ⟨220099539457851005750586767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146733026305234003833724511 220099539457851005750586767)
            ·
              refine ⟨330149309186776508625880151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220099539457851005750586767 330149309186776508625880151)
              ·
                refine ⟨495223963780164762938820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330149309186776508625880151 495223963780164762938820227)
                ·
                  refine ⟨742835945670247144408230341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495223963780164762938820227 742835945670247144408230341)
                  ·
                    refine ⟨139281739813171339576543189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 742835945670247144408230341 139281739813171339576543189)
                    ·
                      refine ⟨3264415776871203271325231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139281739813171339576543189 3264415776871203271325231)
                      ·
                        rfl

theorem cell23_6357427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_6357427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357427 prefixEnd_6357427 := by exact prefixLift 6357427
  have htrace : WordTrace (prefixWord ++ tailWord_6357427) baseStart_6357427 baseEnd_6357427 := by
    simpa [prefixWord, tailWord_6357427, baseEnd_6357427] using wordTrace_append hprefix tailTrace_6357427
  have hstable : (prefixWord ++ tailWord_6357427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357427).length < 2 ^ (prefixWord ++ tailWord_6357427).sum := by decide
  have hdescent : baseEnd_6357427 < baseStart_6357427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357448 : List Nat := [2, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_6357448 : Nat := 118140960795 + 6357448 * 2 ^ 59
def prefixEnd_6357448 : Nat := 4983230072969 + 3 ^ 40 * 6357448 * 2
def baseEnd_6357448 : Nat := 3264426559964947689162635

theorem tailTrace_6357448 : CollatzResearch.WordTrace tailWord_6357448 prefixEnd_6357448 3264426559964947689162635 := by
  unfold tailWord_6357448
  simp only [CollatzResearch.WordTrace]
  refine ⟨115937588936029568260644499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154583451914706091014192665 115937588936029568260644499)
  ·
    refine ⟨173906383404044352390966749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115937588936029568260644499 173906383404044352390966749)
    ·
      refine ⟨65214893776516632146612531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173906383404044352390966749 65214893776516632146612531)
      ·
        refine ⟨97822340664774948219918797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65214893776516632146612531 97822340664774948219918797)
        ·
          refine ⟨36683377749290605582469549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97822340664774948219918797 36683377749290605582469549)
          ·
            refine ⟨13756266655983977093426081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36683377749290605582469549 13756266655983977093426081)
            ·
              refine ⟨10317199991987982820069561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13756266655983977093426081 10317199991987982820069561)
              ·
                refine ⟨7737899993990987115052171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317199991987982820069561 7737899993990987115052171)
                ·
                  refine ⟨11606849990986480672578257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7737899993990987115052171 11606849990986480672578257)
                  ·
                    refine ⟨8705137493239860504433693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11606849990986480672578257 8705137493239860504433693)
                    ·
                      refine ⟨3264426559964947689162635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8705137493239860504433693 3264426559964947689162635)
                      ·
                        rfl

theorem cell23_6357448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_6357448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357448 prefixEnd_6357448 := by exact prefixLift 6357448
  have htrace : WordTrace (prefixWord ++ tailWord_6357448) baseStart_6357448 baseEnd_6357448 := by
    simpa [prefixWord, tailWord_6357448, baseEnd_6357448] using wordTrace_append hprefix tailTrace_6357448
  have hstable : (prefixWord ++ tailWord_6357448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357448).length < 2 ^ (prefixWord ++ tailWord_6357448).sum := by decide
  have hdescent : baseEnd_6357448 < baseStart_6357448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357484 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_6357484 : Nat := 118140960795 + 6357484 * 2 ^ 59
def prefixEnd_6357484 : Nat := 4983230072969 + 3 ^ 40 * 6357484 * 2
def baseEnd_6357484 : Nat := 3264445045268509548312469

theorem tailTrace_6357484 : CollatzResearch.WordTrace tailWord_6357484 prefixEnd_6357484 3264445045268509548312469 := by
  unfold tailWord_6357484
  simp only [CollatzResearch.WordTrace]
  refine ⟨115938245449964357334799753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154584327266619143113066337 115938245449964357334799753)
  ·
    refine ⟨86953684087473268001099815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115938245449964357334799753 86953684087473268001099815)
    ·
      refine ⟨130430526131209902001649723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86953684087473268001099815 130430526131209902001649723)
      ·
        refine ⟨195645789196814853002474585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130430526131209902001649723 195645789196814853002474585)
        ·
          refine ⟨146734341897611139751855939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195645789196814853002474585 146734341897611139751855939)
          ·
            refine ⟨220101512846416709627783909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146734341897611139751855939 220101512846416709627783909)
            ·
              refine ⟨41269033658703133055209483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220101512846416709627783909 41269033658703133055209483)
              ·
                refine ⟨61903550488054699582814225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41269033658703133055209483 61903550488054699582814225)
                ·
                  refine ⟨46427662866041024687110669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61903550488054699582814225 46427662866041024687110669)
                  ·
                    refine ⟨17410373574765384257666501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46427662866041024687110669 17410373574765384257666501)
                    ·
                      refine ⟨3264445045268509548312469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17410373574765384257666501 3264445045268509548312469)
                      ·
                        rfl

theorem cell23_6357484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_6357484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357484 prefixEnd_6357484 := by exact prefixLift 6357484
  have htrace : WordTrace (prefixWord ++ tailWord_6357484) baseStart_6357484 baseEnd_6357484 := by
    simpa [prefixWord, tailWord_6357484, baseEnd_6357484] using wordTrace_append hprefix tailTrace_6357484
  have hstable : (prefixWord ++ tailWord_6357484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357484).length < 2 ^ (prefixWord ++ tailWord_6357484).sum := by decide
  have hdescent : baseEnd_6357484 < baseStart_6357484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357505 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_6357505 : Nat := 118140960795 + 6357505 * 2 ^ 59
def prefixEnd_6357505 : Nat := 4983230072969 + 3 ^ 40 * 6357505 * 2
def baseEnd_6357505 : Nat := 3264455828362253966149873

theorem tailTrace_6357505 : CollatzResearch.WordTrace tailWord_6357505 prefixEnd_6357505 3264455828362253966149873 := by
  unfold tailWord_6357505
  simp only [CollatzResearch.WordTrace]
  refine ⟨231877256832852635256113969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154584837888568423504075979 231877256832852635256113969)
  ·
    refine ⟨173907942624639476442085477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231877256832852635256113969 173907942624639476442085477)
    ·
      refine ⟨32607739242119901832891027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173907942624639476442085477 32607739242119901832891027)
      ·
        refine ⟨48911608863179852749336541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32607739242119901832891027 48911608863179852749336541)
        ·
          refine ⟨18341853323692444781001203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48911608863179852749336541 18341853323692444781001203)
          ·
            refine ⟨27512779985538667171501805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18341853323692444781001203 27512779985538667171501805)
            ·
              refine ⟨10317292494577000189313177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27512779985538667171501805 10317292494577000189313177)
              ·
                refine ⟨7737969370932750141984883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10317292494577000189313177 7737969370932750141984883)
                ·
                  refine ⟨11606954056399125212977325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7737969370932750141984883 11606954056399125212977325)
                  ·
                    refine ⟨4352607771149671954866497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11606954056399125212977325 4352607771149671954866497)
                    ·
                      refine ⟨3264455828362253966149873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352607771149671954866497 3264455828362253966149873)
                      ·
                        rfl

theorem cell23_6357505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_6357505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357505 prefixEnd_6357505 := by exact prefixLift 6357505
  have htrace : WordTrace (prefixWord ++ tailWord_6357505) baseStart_6357505 baseEnd_6357505 := by
    simpa [prefixWord, tailWord_6357505, baseEnd_6357505] using wordTrace_append hprefix tailTrace_6357505
  have hstable : (prefixWord ++ tailWord_6357505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357505).length < 2 ^ (prefixWord ++ tailWord_6357505).sum := by decide
  have hdescent : baseEnd_6357505 < baseStart_6357505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357518 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6357518 : Nat := 118140960795 + 6357518 * 2 ^ 59
def prefixEnd_6357518 : Nat := 4983230072969 + 3 ^ 40 * 6357518 * 2
def baseEnd_6357518 : Nat := 3264462503610762415287313

theorem tailTrace_6357518 : CollatzResearch.WordTrace tailWord_6357518 prefixEnd_6357518 3264462503610762415287313 := by
  unfold tailWord_6357518
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984716372725692309542151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154585153987870358984224805 28984716372725692309542151)
  ·
    refine ⟨43477074559088538464313227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28984716372725692309542151 43477074559088538464313227)
    ·
      refine ⟨65215611838632807696469841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43477074559088538464313227 65215611838632807696469841)
      ·
        refine ⟨48911708878974605772352381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65215611838632807696469841 48911708878974605772352381)
        ·
          refine ⟨18341890829615477164632143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48911708878974605772352381 18341890829615477164632143)
          ·
            refine ⟨27512836244423215746948215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18341890829615477164632143 27512836244423215746948215)
            ·
              refine ⟨41269254366634823620422323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27512836244423215746948215 41269254366634823620422323)
              ·
                refine ⟨61903881549952235430633485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41269254366634823620422323 61903881549952235430633485)
                ·
                  refine ⟨23213955581232088286487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61903881549952235430633485 23213955581232088286487557)
                  ·
                    refine ⟨4352616671481016553716417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23213955581232088286487557 4352616671481016553716417)
                    ·
                      refine ⟨3264462503610762415287313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352616671481016553716417 3264462503610762415287313)
                      ·
                        rfl

theorem cell23_6357518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6357518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357518 prefixEnd_6357518 := by exact prefixLift 6357518
  have htrace : WordTrace (prefixWord ++ tailWord_6357518) baseStart_6357518 baseEnd_6357518 := by
    simpa [prefixWord, tailWord_6357518, baseEnd_6357518] using wordTrace_append hprefix tailTrace_6357518
  have hstable : (prefixWord ++ tailWord_6357518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357518).length < 2 ^ (prefixWord ++ tailWord_6357518).sum := by decide
  have hdescent : baseEnd_6357518 < baseStart_6357518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357558 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_6357558 : Nat := 118140960795 + 6357558 * 2 ^ 59
def prefixEnd_6357558 : Nat := 4983230072969 + 3 ^ 40 * 6357558 * 2
def baseEnd_6357558 : Nat := 362720338092993584309681

theorem tailTrace_6357558 : CollatzResearch.WordTrace tailWord_6357558 prefixEnd_6357558 362720338092993584309681 := by
  unfold tailWord_6357558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492449368853789081737083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 154586126601107083538528885 14492449368853789081737083)
  ·
    refine ⟨21738674053280683622605625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492449368853789081737083 21738674053280683622605625)
    ·
      refine ⟨16304005539960512716954219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21738674053280683622605625 16304005539960512716954219)
      ·
        refine ⟨24456008309940769075431329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16304005539960512716954219 24456008309940769075431329)
        ·
          refine ⟨18342006232455576806573497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24456008309940769075431329 18342006232455576806573497)
          ·
            refine ⟨13756504674341682604930123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18342006232455576806573497 13756504674341682604930123)
            ·
              refine ⟨20634757011512523907395185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13756504674341682604930123 20634757011512523907395185)
              ·
                refine ⟨15476067758634392930546389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20634757011512523907395185 15476067758634392930546389)
                ·
                  refine ⟨362720338092993584309681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15476067758634392930546389 362720338092993584309681)
                  ·
                    rfl

theorem cell23_6357558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_6357558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357558 prefixEnd_6357558 := by exact prefixLift 6357558
  have htrace : WordTrace (prefixWord ++ tailWord_6357558) baseStart_6357558 baseEnd_6357558 := by
    simpa [prefixWord, tailWord_6357558, baseEnd_6357558] using wordTrace_append hprefix tailTrace_6357558
  have hstable : (prefixWord ++ tailWord_6357558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357558).length < 2 ^ (prefixWord ++ tailWord_6357558).sum := by decide
  have hdescent : baseEnd_6357558 < baseStart_6357558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357591 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_6357591 : Nat := 118140960795 + 6357591 * 2 ^ 59
def prefixEnd_6357591 : Nat := 4983230072969 + 3 ^ 40 * 6357591 * 2
def baseEnd_6357591 : Nat := 3264499987698540629674477

theorem tailTrace_6357591 : CollatzResearch.WordTrace tailWord_6357591 prefixEnd_6357591 3264499987698540629674477 := by
  unfold tailWord_6357591
  simp only [CollatzResearch.WordTrace]
  refine ⟨231880393510541071943744627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154586929007027381295829751 231880393510541071943744627)
  ·
    refine ⟨347820590265811607915616941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231880393510541071943744627 347820590265811607915616941)
    ·
      refine ⟨130432721349679352968356353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347820590265811607915616941 130432721349679352968356353)
      ·
        refine ⟨97824541012259514726267265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130432721349679352968356353 97824541012259514726267265)
        ·
          refine ⟨73368405759194636044700449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97824541012259514726267265 73368405759194636044700449)
          ·
            refine ⟨55026304319395977033525337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73368405759194636044700449 55026304319395977033525337)
            ·
              refine ⟨41269728239546982775144003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55026304319395977033525337 41269728239546982775144003)
              ·
                refine ⟨61904592359320474162716005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41269728239546982775144003 61904592359320474162716005)
                ·
                  refine ⟨11607111067372588905509251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61904592359320474162716005 11607111067372588905509251)
                  ·
                    refine ⟨17410666601058883358263877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11607111067372588905509251 17410666601058883358263877)
                    ·
                      refine ⟨3264499987698540629674477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17410666601058883358263877 3264499987698540629674477)
                      ·
                        rfl

theorem cell23_6357591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_6357591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357591 prefixEnd_6357591 := by exact prefixLift 6357591
  have htrace : WordTrace (prefixWord ++ tailWord_6357591) baseStart_6357591 baseEnd_6357591 := by
    simpa [prefixWord, tailWord_6357591, baseEnd_6357591] using wordTrace_append hprefix tailTrace_6357591
  have hstable : (prefixWord ++ tailWord_6357591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357591).length < 2 ^ (prefixWord ++ tailWord_6357591).sum := by decide
  have hdescent : baseEnd_6357591 < baseStart_6357591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3]
def baseStart_6357611 : Nat := 118140960795 + 6357611 * 2 ^ 59
def prefixEnd_6357611 : Nat := 4983230072969 + 3 ^ 40 * 6357611 * 2
def baseEnd_6357611 : Nat := 3264510257311630551424385

theorem tailTrace_6357611 : CollatzResearch.WordTrace tailWord_6357611 prefixEnd_6357611 3264510257311630551424385 := by
  unfold tailWord_6357611
  simp only [CollatzResearch.WordTrace]
  refine ⟨231881122970468615359472687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154587415313645743572981791 231881122970468615359472687)
  ·
    refine ⟨347821684455702923039209031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231881122970468615359472687 347821684455702923039209031)
    ·
      refine ⟨521732526683554384558813547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347821684455702923039209031 521732526683554384558813547)
      ·
        refine ⟨782598790025331576838220321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521732526683554384558813547 782598790025331576838220321)
        ·
          refine ⟨586949092518998682628665241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782598790025331576838220321 586949092518998682628665241)
          ·
            refine ⟨440211819389249011971498931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586949092518998682628665241 440211819389249011971498931)
            ·
              refine ⟨660317729083873517957248397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440211819389249011971498931 660317729083873517957248397)
              ·
                refine ⟨247619148406452569233968149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660317729083873517957248397 247619148406452569233968149)
                ·
                  refine ⟨11607147581552464182842257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 247619148406452569233968149 11607147581552464182842257)
                  ·
                    refine ⟨8705360686164348137131693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11607147581552464182842257 8705360686164348137131693)
                    ·
                      refine ⟨3264510257311630551424385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8705360686164348137131693 3264510257311630551424385)
                      ·
                        rfl

theorem cell23_6357611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 3].length) (baseStart_6357611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357611 prefixEnd_6357611 := by exact prefixLift 6357611
  have htrace : WordTrace (prefixWord ++ tailWord_6357611) baseStart_6357611 baseEnd_6357611 := by
    simpa [prefixWord, tailWord_6357611, baseEnd_6357611] using wordTrace_append hprefix tailTrace_6357611
  have hstable : (prefixWord ++ tailWord_6357611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357611).length < 2 ^ (prefixWord ++ tailWord_6357611).sum := by decide
  have hdescent : baseEnd_6357611 < baseStart_6357611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357635 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 1, 4]
def baseStart_6357635 : Nat := 118140960795 + 6357635 * 2 ^ 59
def prefixEnd_6357635 : Nat := 4983230072969 + 3 ^ 40 * 6357635 * 2
def baseEnd_6357635 : Nat := 1088174193615779485841425

theorem tailTrace_6357635 : CollatzResearch.WordTrace tailWord_6357635 prefixEnd_6357635 1088174193615779485841425 := by
  unfold tailWord_6357635
  simp only [CollatzResearch.WordTrace]
  refine ⟨231881998322381667458346359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154587998881587778305564239 231881998322381667458346359)
  ·
    refine ⟨347822997483572501187519539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231881998322381667458346359 347822997483572501187519539)
    ·
      refine ⟨521734496225358751781279309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347822997483572501187519539 521734496225358751781279309)
      ·
        refine ⟨195650436084509531917979741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 521734496225358751781279309 195650436084509531917979741)
        ·
          refine ⟨73368913531691074469242403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195650436084509531917979741 73368913531691074469242403)
          ·
            refine ⟨110053370297536611703863605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73368913531691074469242403 110053370297536611703863605)
            ·
              refine ⟨10317503465394057347237213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110053370297536611703863605 10317503465394057347237213)
              ·
                refine ⟨3869063799522771505213955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10317503465394057347237213 3869063799522771505213955)
                ·
                  refine ⟨5803595699284157257820933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869063799522771505213955 5803595699284157257820933)
                  ·
                    refine ⟨1088174193615779485841425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803595699284157257820933 1088174193615779485841425)
                    ·
                      rfl

theorem cell23_6357635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 1, 4].length) (baseStart_6357635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357635 prefixEnd_6357635 := by exact prefixLift 6357635
  have htrace : WordTrace (prefixWord ++ tailWord_6357635) baseStart_6357635 baseEnd_6357635 := by
    simpa [prefixWord, tailWord_6357635, baseEnd_6357635] using wordTrace_append hprefix tailTrace_6357635
  have hstable : (prefixWord ++ tailWord_6357635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357635).length < 2 ^ (prefixWord ++ tailWord_6357635).sum := by decide
  have hdescent : baseEnd_6357635 < baseStart_6357635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357652 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6357652 : Nat := 118140960795 + 6357652 * 2 ^ 59
def prefixEnd_6357652 : Nat := 4983230072969 + 3 ^ 40 * 6357652 * 2
def baseEnd_6357652 : Nat := 1088177103339488297003899

theorem tailTrace_6357652 : CollatzResearch.WordTrace tailWord_6357652 prefixEnd_6357652 1088177103339488297003899 := by
  unfold tailWord_6357652
  simp only [CollatzResearch.WordTrace]
  refine ⟨115941309181660039680857605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154588412242213386241143473 115941309181660039680857605)
  ·
    refine ⟨21738995471561257440160801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115941309181660039680857605 21738995471561257440160801)
    ·
      refine ⟨16304246603670943080120601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21738995471561257440160801 16304246603670943080120601)
      ·
        refine ⟨12228184952753207310090451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16304246603670943080120601 12228184952753207310090451)
        ·
          refine ⟨18342277429129810965135677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228184952753207310090451 18342277429129810965135677)
          ·
            refine ⟨6878354035923679111925879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18342277429129810965135677 6878354035923679111925879)
            ·
              refine ⟨10317531053885518667888819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878354035923679111925879 10317531053885518667888819)
              ·
                refine ⟨15476296580828278001833229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10317531053885518667888819 15476296580828278001833229)
                ·
                  refine ⟨5803611217810604250687461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15476296580828278001833229 5803611217810604250687461)
                  ·
                    refine ⟨1088177103339488297003899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803611217810604250687461 1088177103339488297003899)
                    ·
                      rfl

theorem cell23_6357652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6357652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357652 prefixEnd_6357652 := by exact prefixLift 6357652
  have htrace : WordTrace (prefixWord ++ tailWord_6357652) baseStart_6357652 baseEnd_6357652 := by
    simpa [prefixWord, tailWord_6357652, baseEnd_6357652] using wordTrace_append hprefix tailTrace_6357652
  have hstable : (prefixWord ++ tailWord_6357652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357652).length < 2 ^ (prefixWord ++ tailWord_6357652).sum := by decide
  have hdescent : baseEnd_6357652 < baseStart_6357652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357692 : List Nat := [2, 2, 2, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_6357692 : Nat := 118140960795 + 6357692 * 2 ^ 59
def prefixEnd_6357692 : Nat := 4983230072969 + 3 ^ 40 * 6357692 * 2
def baseEnd_6357692 : Nat := 3264551849244644734511513

theorem tailTrace_6357692 : CollatzResearch.WordTrace tailWord_6357692 prefixEnd_6357692 3264551849244644734511513 := by
  unfold tailWord_6357692
  simp only [CollatzResearch.WordTrace]
  refine ⟨115942038641587583096585665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154589384855450110795447553 115942038641587583096585665)
  ·
    refine ⟨86956528981190687322439249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115942038641587583096585665 86956528981190687322439249)
    ·
      refine ⟨65217396735893015491829437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86956528981190687322439249 65217396735893015491829437)
      ·
        refine ⟨24456523775959880809436039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65217396735893015491829437 24456523775959880809436039)
        ·
          refine ⟨36684785663939821214154059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24456523775959880809436039 36684785663939821214154059)
          ·
            refine ⟨55027178495909731821231089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36684785663939821214154059 55027178495909731821231089)
            ·
              refine ⟨41270383871932298865923317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55027178495909731821231089 41270383871932298865923317)
              ·
                refine ⟨3869098487993653018680311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41270383871932298865923317 3869098487993653018680311)
                ·
                  refine ⟨5803647731990479528020467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869098487993653018680311 5803647731990479528020467)
                  ·
                    refine ⟨8705471597985719292030701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5803647731990479528020467 8705471597985719292030701)
                    ·
                      refine ⟨3264551849244644734511513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8705471597985719292030701 3264551849244644734511513)
                      ·
                        rfl

theorem cell23_6357692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_6357692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357692 prefixEnd_6357692 := by exact prefixLift 6357692
  have htrace : WordTrace (prefixWord ++ tailWord_6357692) baseStart_6357692 baseEnd_6357692 := by
    simpa [prefixWord, tailWord_6357692, baseEnd_6357692] using wordTrace_append hprefix tailTrace_6357692
  have hstable : (prefixWord ++ tailWord_6357692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357692).length < 2 ^ (prefixWord ++ tailWord_6357692).sum := by decide
  have hdescent : baseEnd_6357692 < baseStart_6357692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357695 : List Nat := [1, 1, 2, 2, 2, 5, 3, 1, 1, 5]
def baseStart_6357695 : Nat := 118140960795 + 6357695 * 2 ^ 59
def prefixEnd_6357695 : Nat := 4983230072969 + 3 ^ 40 * 6357695 * 2
def baseEnd_6357695 : Nat := 1088184463228869407591333

theorem tailTrace_6357695 : CollatzResearch.WordTrace tailWord_6357695 prefixEnd_6357695 1088184463228869407591333 := by
  unfold tailWord_6357695
  simp only [CollatzResearch.WordTrace]
  refine ⟨231884186702164297705530539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154589457801442865137020359 231884186702164297705530539)
  ·
    refine ⟨347826280053246446558295809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231884186702164297705530539 347826280053246446558295809)
    ·
      refine ⟨260869710039934834918721857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347826280053246446558295809 260869710039934834918721857)
      ·
        refine ⟨195652282529951126189041393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260869710039934834918721857 195652282529951126189041393)
        ·
          refine ⟨146739211897463344641781045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195652282529951126189041393 146739211897463344641781045)
          ·
            refine ⟨13756801115387188560166973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146739211897463344641781045 13756801115387188560166973)
            ·
              refine ⟨5158800418270195710062615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13756801115387188560166973 5158800418270195710062615)
              ·
                refine ⟨7738200627405293565093923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5158800418270195710062615 7738200627405293565093923)
                ·
                  refine ⟨11607300941107940347640885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738200627405293565093923 11607300941107940347640885)
                  ·
                    refine ⟨1088184463228869407591333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11607300941107940347640885 1088184463228869407591333)
                    ·
                      rfl

theorem cell23_6357695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_6357695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357695 prefixEnd_6357695 := by exact prefixLift 6357695
  have htrace : WordTrace (prefixWord ++ tailWord_6357695) baseStart_6357695 baseEnd_6357695 := by
    simpa [prefixWord, tailWord_6357695, baseEnd_6357695] using wordTrace_append hprefix tailTrace_6357695
  have hstable : (prefixWord ++ tailWord_6357695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357695).length < 2 ^ (prefixWord ++ tailWord_6357695).sum := by decide
  have hdescent : baseEnd_6357695 < baseStart_6357695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357732 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 3, 2, 2]
def baseStart_6357732 : Nat := 118140960795 + 6357732 * 2 ^ 59
def prefixEnd_6357732 : Nat := 4983230072969 + 3 ^ 40 * 6357732 * 2
def baseEnd_6357732 : Nat := 3264572388470824578011329

theorem tailTrace_6357732 : CollatzResearch.WordTrace tailWord_6357732 prefixEnd_6357732 3264572388470824578011329 := by
  unfold tailWord_6357732
  simp only [CollatzResearch.WordTrace]
  refine ⟨115942768101515126512313725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154590357468686835349751633 115942768101515126512313725)
  ·
    refine ⟨43478538038068172442117647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115942768101515126512313725 43478538038068172442117647)
    ·
      refine ⟨65217807057102258663176471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43478538038068172442117647 65217807057102258663176471)
      ·
        refine ⟨97826710585653387994764707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65217807057102258663176471 97826710585653387994764707)
        ·
          refine ⟨146740065878480081992147061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97826710585653387994764707 146740065878480081992147061)
          ·
            refine ⟨13756881176107507686763787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 146740065878480081992147061 13756881176107507686763787)
            ·
              refine ⟨20635321764161261530145681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13756881176107507686763787 20635321764161261530145681)
              ·
                refine ⟨15476491323120946147609261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20635321764161261530145681 15476491323120946147609261)
                ·
                  refine ⟨5803684246170354805353473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15476491323120946147609261 5803684246170354805353473)
                  ·
                    refine ⟨4352763184627766104015105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5803684246170354805353473 4352763184627766104015105)
                    ·
                      refine ⟨3264572388470824578011329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352763184627766104015105 3264572388470824578011329)
                      ·
                        rfl

theorem cell23_6357732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 3, 2, 2].length) (baseStart_6357732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357732 prefixEnd_6357732 := by exact prefixLift 6357732
  have htrace : WordTrace (prefixWord ++ tailWord_6357732) baseStart_6357732 baseEnd_6357732 := by
    simpa [prefixWord, tailWord_6357732, baseEnd_6357732] using wordTrace_append hprefix tailTrace_6357732
  have hstable : (prefixWord ++ tailWord_6357732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357732).length < 2 ^ (prefixWord ++ tailWord_6357732).sum := by decide
  have hdescent : baseEnd_6357732 < baseStart_6357732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357789 : List Nat := [1, 4, 2, 4, 2, 1, 2, 7]
def baseStart_6357789 : Nat := 118140960795 + 6357789 * 2 ^ 59
def prefixEnd_6357789 : Nat := 4983230072969 + 3 ^ 40 * 6357789 * 2
def baseEnd_6357789 : Nat := 120911172476597439074021

theorem tailTrace_6357789 : CollatzResearch.WordTrace tailWord_6357789 prefixEnd_6357789 120911172476597439074021 := by
  unfold tailWord_6357789
  simp only [CollatzResearch.WordTrace]
  refine ⟨231887615163823751759452421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154591743442549167839634947 231887615163823751759452421)
  ·
    refine ⟨43478927843216953454897329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 231887615163823751759452421 43478927843216953454897329)
    ·
      refine ⟨32609195882412715091172997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43478927843216953454897329 32609195882412715091172997)
      ·
        refine ⟨6114224227952384079594937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32609195882412715091172997 6114224227952384079594937)
        ·
          refine ⟨4585668170964288059696203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6114224227952384079594937 4585668170964288059696203)
          ·
            refine ⟨6878502256446432089544305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585668170964288059696203 6878502256446432089544305)
            ·
              refine ⟨5158876692334824067158229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6878502256446432089544305 5158876692334824067158229)
              ·
                refine ⟨120911172476597439074021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5158876692334824067158229 120911172476597439074021)
                ·
                  rfl

theorem cell23_6357789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 7].length) (baseStart_6357789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357789 prefixEnd_6357789 := by exact prefixLift 6357789
  have htrace : WordTrace (prefixWord ++ tailWord_6357789) baseStart_6357789 baseEnd_6357789 := by
    simpa [prefixWord, tailWord_6357789, baseEnd_6357789] using wordTrace_append hprefix tailTrace_6357789
  have hstable : (prefixWord ++ tailWord_6357789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357789).length < 2 ^ (prefixWord ++ tailWord_6357789).sum := by decide
  have hdescent : baseEnd_6357789 < baseStart_6357789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357792 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6357792 : Nat := 118140960795 + 6357792 * 2 ^ 59
def prefixEnd_6357792 : Nat := 4983230072969 + 3 ^ 40 * 6357792 * 2
def baseEnd_6357792 : Nat := 3264603197310094343261053

theorem tailTrace_6357792 : CollatzResearch.WordTrace tailWord_6357792 prefixEnd_6357792 3264603197310094343261053 := by
  unfold tailWord_6357792
  simp only [CollatzResearch.WordTrace]
  refine ⟨115943862291406441635905815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154591816388541922181207753 115943862291406441635905815)
  ·
    refine ⟨173915793437109662453858723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115943862291406441635905815 173915793437109662453858723)
    ·
      refine ⟨260873690155664493680788085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173915793437109662453858723 260873690155664493680788085)
      ·
        refine ⟨24456908452093546282573883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 260873690155664493680788085 24456908452093546282573883)
        ·
          refine ⟨36685362678140319423860825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24456908452093546282573883 36685362678140319423860825)
          ·
            refine ⟨27514022008605239567895619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36685362678140319423860825 27514022008605239567895619)
            ·
              refine ⟨41271033012907859351843429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27514022008605239567895619 41271033012907859351843429)
              ·
                refine ⟨7738318689920223628470643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41271033012907859351843429 7738318689920223628470643)
                ·
                  refine ⟨11607478034880335442705965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738318689920223628470643 11607478034880335442705965)
                  ·
                    refine ⟨4352804263080125791014737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11607478034880335442705965 4352804263080125791014737)
                    ·
                      refine ⟨3264603197310094343261053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4352804263080125791014737 3264603197310094343261053)
                      ·
                        rfl

theorem cell23_6357792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6357792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357792 prefixEnd_6357792 := by exact prefixLift 6357792
  have htrace : WordTrace (prefixWord ++ tailWord_6357792) baseStart_6357792 baseEnd_6357792 := by
    simpa [prefixWord, tailWord_6357792, baseEnd_6357792] using wordTrace_append hprefix tailTrace_6357792
  have hstable : (prefixWord ++ tailWord_6357792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357792).length < 2 ^ (prefixWord ++ tailWord_6357792).sum := by decide
  have hdescent : baseEnd_6357792 < baseStart_6357792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357868 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_6357868 : Nat := 118140960795 + 6357868 * 2 ^ 59
def prefixEnd_6357868 : Nat := 4983230072969 + 3 ^ 40 * 6357868 * 2
def baseEnd_6357868 : Nat := 3264642221839836045910703

theorem tailTrace_6357868 : CollatzResearch.WordTrace tailWord_6357868 prefixEnd_6357868 3264642221839836045910703 := by
  unfold tailWord_6357868
  simp only [CollatzResearch.WordTrace]
  refine ⟨115945248265268774125789129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154593664353691698834385505 115945248265268774125789129)
  ·
    refine ⟨86958936198951580594341847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115945248265268774125789129 86958936198951580594341847)
    ·
      refine ⟨130438404298427370891512771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86958936198951580594341847 130438404298427370891512771)
      ·
        refine ⟨195657606447641056337269157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130438404298427370891512771 195657606447641056337269157)
        ·
          refine ⟨36685801208932698063237967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195657606447641056337269157 36685801208932698063237967)
          ·
            refine ⟨55028701813399047094856951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36685801208932698063237967 55028701813399047094856951)
            ·
              refine ⟨82543052720098570642285427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55028701813399047094856951 82543052720098570642285427)
              ·
                refine ⟨123814579080147855963428141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82543052720098570642285427 123814579080147855963428141)
                ·
                  refine ⟨46430467155055445986285553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123814579080147855963428141 46430467155055445986285553)
                  ·
                    refine ⟨34822850366291584489714165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46430467155055445986285553 34822850366291584489714165)
                    ·
                      refine ⟨3264642221839836045910703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34822850366291584489714165 3264642221839836045910703)
                      ·
                        rfl

theorem cell23_6357868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_6357868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357868 prefixEnd_6357868 := by exact prefixLift 6357868
  have htrace : WordTrace (prefixWord ++ tailWord_6357868) baseStart_6357868 baseEnd_6357868 := by
    simpa [prefixWord, tailWord_6357868, baseEnd_6357868] using wordTrace_append hprefix tailTrace_6357868
  have hstable : (prefixWord ++ tailWord_6357868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357868).length < 2 ^ (prefixWord ++ tailWord_6357868).sum := by decide
  have hdescent : baseEnd_6357868 < baseStart_6357868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357952 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 6]
def baseStart_6357952 : Nat := 118140960795 + 6357952 * 2 ^ 59
def prefixEnd_6357952 : Nat := 4983230072969 + 3 ^ 40 * 6357952 * 2
def baseEnd_6357952 : Nat := 362742817134979301917813

theorem tailTrace_6357952 : CollatzResearch.WordTrace tailWord_6357952 prefixEnd_6357952 362742817134979301917813 := by
  unfold tailWord_6357952
  simp only [CollatzResearch.WordTrace]
  refine ⟨115946780131116615298818055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154595706841488820398424073 115946780131116615298818055)
  ·
    refine ⟨173920170196674922948227083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115946780131116615298818055 173920170196674922948227083)
    ·
      refine ⟨260880255295012384422340625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173920170196674922948227083 260880255295012384422340625)
      ·
        refine ⟨195660191471259288316755469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260880255295012384422340625 195660191471259288316755469)
        ·
          refine ⟨73372571801722233118783301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195660191471259288316755469 73372571801722233118783301)
          ·
            refine ⟨13757357212822918709771869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73372571801722233118783301 13757357212822918709771869)
            ·
              refine ⟨5159008954808594516164451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13757357212822918709771869 5159008954808594516164451)
              ·
                refine ⟨7738513432212891774246677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159008954808594516164451 7738513432212891774246677)
                ·
                  refine ⟨362742817134979301917813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7738513432212891774246677 362742817134979301917813)
                  ·
                    rfl

theorem cell23_6357952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 6].length) (baseStart_6357952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357952 prefixEnd_6357952 := by exact prefixLift 6357952
  have htrace : WordTrace (prefixWord ++ tailWord_6357952) baseStart_6357952 baseEnd_6357952 := by
    simpa [prefixWord, tailWord_6357952, baseEnd_6357952] using wordTrace_append hprefix tailTrace_6357952
  have hstable : (prefixWord ++ tailWord_6357952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357952).length < 2 ^ (prefixWord ++ tailWord_6357952).sum := by decide
  have hdescent : baseEnd_6357952 < baseStart_6357952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357973 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6357973 : Nat := 118140960795 + 6357973 * 2 ^ 59
def prefixEnd_6357973 : Nat := 4983230072969 + 3 ^ 40 * 6357973 * 2
def baseEnd_6357973 : Nat := 1088232045769519378365907

theorem tailTrace_6357973 : CollatzResearch.WordTrace tailWord_6357973 prefixEnd_6357973 1088232045769519378365907 := by
  unfold tailWord_6357973
  simp only [CollatzResearch.WordTrace]
  refine ⟨231894326195157151184150573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154596217463438100789433715 231894326195157151184150573)
  ·
    refine ⟨86960372323183931694056465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231894326195157151184150573 86960372323183931694056465)
    ·
      refine ⟨65220279242387948770542349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86960372323183931694056465 65220279242387948770542349)
      ·
        refine ⟨24457604715895480788953381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65220279242387948770542349 24457604715895480788953381)
        ·
          refine ⟨4585800884230402647928759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24457604715895480788953381 4585800884230402647928759)
          ·
            refine ⟨6878701326345603971893139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4585800884230402647928759 6878701326345603971893139)
            ·
              refine ⟨10318051989518405957839709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878701326345603971893139 10318051989518405957839709)
              ·
                refine ⟨3869269496069402234189891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10318051989518405957839709 3869269496069402234189891)
                ·
                  refine ⟨5803904244104103351284837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869269496069402234189891 5803904244104103351284837)
                  ·
                    refine ⟨1088232045769519378365907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5803904244104103351284837 1088232045769519378365907)
                    ·
                      rfl

theorem cell23_6357973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6357973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357973 prefixEnd_6357973 := by exact prefixLift 6357973
  have htrace : WordTrace (prefixWord ++ tailWord_6357973) baseStart_6357973 baseEnd_6357973 := by
    simpa [prefixWord, tailWord_6357973, baseEnd_6357973] using wordTrace_append hprefix tailTrace_6357973
  have hstable : (prefixWord ++ tailWord_6357973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357973).length < 2 ^ (prefixWord ++ tailWord_6357973).sum := by decide
  have hdescent : baseEnd_6357973 < baseStart_6357973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6357985 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_6357985 : Nat := 118140960795 + 6357985 * 2 ^ 59
def prefixEnd_6357985 : Nat := 4983230072969 + 3 ^ 40 * 6357985 * 2
def baseEnd_6357985 : Nat := 3264702299076412088147665

theorem tailTrace_6357985 : CollatzResearch.WordTrace tailWord_6357985 prefixEnd_6357985 3264702299076412088147665 := by
  unfold tailWord_6357985
  simp only [CollatzResearch.WordTrace]
  refine ⟨231894763871113677233587409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154596509247409118155724939 231894763871113677233587409)
  ·
    refine ⟨173921072903335257925190557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 231894763871113677233587409 173921072903335257925190557)
    ·
      refine ⟨65220402338750721721946459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173921072903335257925190557 65220402338750721721946459)
      ·
        refine ⟨97830603508126082582919689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65220402338750721721946459 97830603508126082582919689)
        ·
          refine ⟨73372952631094561937189767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97830603508126082582919689 73372952631094561937189767)
          ·
            refine ⟨110059428946641842905784651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73372952631094561937189767 110059428946641842905784651)
            ·
              refine ⟨165089143419962764358676977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110059428946641842905784651 165089143419962764358676977)
              ·
                refine ⟨123816857564972073269007733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165089143419962764358676977 123816857564972073269007733)
                ·
                  refine ⟨11607830396716131868969475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123816857564972073269007733 11607830396716131868969475)
                  ·
                    refine ⟨17411745595074197803454213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11607830396716131868969475 17411745595074197803454213)
                    ·
                      refine ⟨3264702299076412088147665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17411745595074197803454213 3264702299076412088147665)
                      ·
                        rfl

theorem cell23_6357985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_6357985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6357985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6357985 prefixEnd_6357985 := by exact prefixLift 6357985
  have htrace : WordTrace (prefixWord ++ tailWord_6357985) baseStart_6357985 baseEnd_6357985 := by
    simpa [prefixWord, tailWord_6357985, baseEnd_6357985] using wordTrace_append hprefix tailTrace_6357985
  have hstable : (prefixWord ++ tailWord_6357985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6357985).length < 2 ^ (prefixWord ++ tailWord_6357985).sum := by decide
  have hdescent : baseEnd_6357985 < baseStart_6357985 := by decide
  rcases family_descends (prefixWord ++ tailWord_6357985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358039 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6358039 : Nat := 118140960795 + 6358039 * 2 ^ 59
def prefixEnd_6358039 : Nat := 4983230072969 + 3 ^ 40 * 6358039 * 2
def baseEnd_6358039 : Nat := 3264730027031754876872417

theorem tailTrace_6358039 : CollatzResearch.WordTrace tailWord_6358039 prefixEnd_6358039 3264730027031754876872417 := by
  unfold tailWord_6358039
  simp only [CollatzResearch.WordTrace]
  refine ⟨231896733412918044456053171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154597822275278696304035447 231896733412918044456053171)
  ·
    refine ⟨347845100119377066684079757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231896733412918044456053171 347845100119377066684079757)
    ·
      refine ⟨130441912544766400006529909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347845100119377066684079757 130441912544766400006529909)
      ·
        refine ⟨12228929301071850000612179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130441912544766400006529909 12228929301071850000612179)
        ·
          refine ⟨18343393951607775000918269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12228929301071850000612179 18343393951607775000918269)
          ·
            refine ⟨6878772731852915625344351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18343393951607775000918269 6878772731852915625344351)
            ·
              refine ⟨10318159097779373438016527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6878772731852915625344351 10318159097779373438016527)
              ·
                refine ⟨15477238646669060157024791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318159097779373438016527 15477238646669060157024791)
                ·
                  refine ⟨23215857970003590235537187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15477238646669060157024791 23215857970003590235537187)
                  ·
                    refine ⟨34823786955005385353305781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23215857970003590235537187 34823786955005385353305781)
                    ·
                      refine ⟨3264730027031754876872417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34823786955005385353305781 3264730027031754876872417)
                      ·
                        rfl

theorem cell23_6358039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6358039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358039 prefixEnd_6358039 := by exact prefixLift 6358039
  have htrace : WordTrace (prefixWord ++ tailWord_6358039) baseStart_6358039 baseEnd_6358039 := by
    simpa [prefixWord, tailWord_6358039, baseEnd_6358039] using wordTrace_append hprefix tailTrace_6358039
  have hstable : (prefixWord ++ tailWord_6358039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358039).length < 2 ^ (prefixWord ++ tailWord_6358039).sum := by decide
  have hdescent : baseEnd_6358039 < baseStart_6358039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358079 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 1, 3, 2]
def baseStart_6358079 : Nat := 118140960795 + 6358079 * 2 ^ 59
def prefixEnd_6358079 : Nat := 4983230072969 + 3 ^ 40 * 6358079 * 2
def baseEnd_6358079 : Nat := 3264750566257934720372233

theorem tailTrace_6358079 : CollatzResearch.WordTrace tailWord_6358079 prefixEnd_6358079 3264750566257934720372233 := by
  unfold tailWord_6358079
  simp only [CollatzResearch.WordTrace]
  refine ⟨231898192332773131287509291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154598794888515420858339527 231898192332773131287509291)
  ·
    refine ⟨347847288499159696931263937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231898192332773131287509291 347847288499159696931263937)
    ·
      refine ⟨260885466374369772698447953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347847288499159696931263937 260885466374369772698447953)
      ·
        refine ⟨195664099780777329523835965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 260885466374369772698447953 195664099780777329523835965)
        ·
          refine ⟨73374037417791498571438487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195664099780777329523835965 73374037417791498571438487)
          ·
            refine ⟨110061056126687247857157731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73374037417791498571438487 110061056126687247857157731)
            ·
              refine ⟨165091584190030871785736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110061056126687247857157731 165091584190030871785736597)
              ·
                refine ⟨7738668008907697114956403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 165091584190030871785736597 7738668008907697114956403)
                ·
                  refine ⟨11608002013361545672434605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7738668008907697114956403 11608002013361545672434605)
                  ·
                    refine ⟨4353000755010579627162977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11608002013361545672434605 4353000755010579627162977)
                    ·
                      refine ⟨3264750566257934720372233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353000755010579627162977 3264750566257934720372233)
                      ·
                        rfl

theorem cell23_6358079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_6358079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358079 prefixEnd_6358079 := by exact prefixLift 6358079
  have htrace : WordTrace (prefixWord ++ tailWord_6358079) baseStart_6358079 baseEnd_6358079 := by
    simpa [prefixWord, tailWord_6358079, baseEnd_6358079] using wordTrace_append hprefix tailTrace_6358079
  have hstable : (prefixWord ++ tailWord_6358079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358079).length < 2 ^ (prefixWord ++ tailWord_6358079).sum := by decide
  have hdescent : baseEnd_6358079 < baseStart_6358079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358086 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6358086 : Nat := 118140960795 + 6358086 * 2 ^ 59
def prefixEnd_6358086 : Nat := 4983230072969 + 3 ^ 40 * 6358086 * 2
def baseEnd_6358086 : Nat := 3264754160622516192984701

theorem tailTrace_6358086 : CollatzResearch.WordTrace tailWord_6358086 prefixEnd_6358086 3264754160622516192984701 := by
  unfold tailWord_6358086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246826488867117858844191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 154598965095831847655342741 7246826488867117858844191)
  ·
    refine ⟨10870239733300676788266287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246826488867117858844191 10870239733300676788266287)
    ·
      refine ⟨16305359599951015182399431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10870239733300676788266287 16305359599951015182399431)
      ·
        refine ⟨24458039399926522773599147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16305359599951015182399431 24458039399926522773599147)
        ·
          refine ⟨36687059099889784160398721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24458039399926522773599147 36687059099889784160398721)
          ·
            refine ⟨27515294324917338120299041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36687059099889784160398721 27515294324917338120299041)
            ·
              refine ⟨20636470743688003590224281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27515294324917338120299041 20636470743688003590224281)
              ·
                refine ⟨15477353057766002692668211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20636470743688003590224281 15477353057766002692668211)
                ·
                  refine ⟨23216029586649004039002317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15477353057766002692668211 23216029586649004039002317)
                  ·
                    refine ⟨8706011094993376514625869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23216029586649004039002317 8706011094993376514625869)
                    ·
                      refine ⟨3264754160622516192984701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706011094993376514625869 3264754160622516192984701)
                      ·
                        rfl

theorem cell23_6358086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6358086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358086 prefixEnd_6358086 := by exact prefixLift 6358086
  have htrace : WordTrace (prefixWord ++ tailWord_6358086) baseStart_6358086 baseEnd_6358086 := by
    simpa [prefixWord, tailWord_6358086, baseEnd_6358086] using wordTrace_append hprefix tailTrace_6358086
  have hstable : (prefixWord ++ tailWord_6358086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358086).length < 2 ^ (prefixWord ++ tailWord_6358086).sum := by decide
  have hdescent : baseEnd_6358086 < baseStart_6358086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358120 : List Nat := [2, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6358120 : Nat := 118140960795 + 6358120 * 2 ^ 59
def prefixEnd_6358120 : Nat := 4983230072969 + 3 ^ 40 * 6358120 * 2
def baseEnd_6358120 : Nat := 3264771618964769059959545

theorem tailTrace_6358120 : CollatzResearch.WordTrace tailWord_6358120 prefixEnd_6358120 3264771618964769059959545 := by
  unfold tailWord_6358120
  simp only [CollatzResearch.WordTrace]
  refine ⟨115949843862812297644875907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154599791817083063526501209 115949843862812297644875907)
  ·
    refine ⟨173924765794218446467313861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115949843862812297644875907 173924765794218446467313861)
    ·
      refine ⟨32610893586415958712621349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 173924765794218446467313861 32610893586415958712621349)
      ·
        refine ⟨6114542547452992258616503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32610893586415958712621349 6114542547452992258616503)
        ·
          refine ⟨9171813821179488387924755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114542547452992258616503 9171813821179488387924755)
          ·
            refine ⟨13757720731769232581887133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9171813821179488387924755 13757720731769232581887133)
            ·
              refine ⟨5159145274413462218207675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13757720731769232581887133 5159145274413462218207675)
              ·
                refine ⟨7738717911620193327311513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159145274413462218207675 7738717911620193327311513)
                ·
                  refine ⟨5804038433715144995483635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7738717911620193327311513 5804038433715144995483635)
                  ·
                    refine ⟨8706057650572717493225453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804038433715144995483635 8706057650572717493225453)
                    ·
                      refine ⟨3264771618964769059959545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706057650572717493225453 3264771618964769059959545)
                      ·
                        rfl

theorem cell23_6358120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6358120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358120 prefixEnd_6358120 := by exact prefixLift 6358120
  have htrace : WordTrace (prefixWord ++ tailWord_6358120) baseStart_6358120 baseEnd_6358120 := by
    simpa [prefixWord, tailWord_6358120, baseEnd_6358120] using wordTrace_append hprefix tailTrace_6358120
  have hstable : (prefixWord ++ tailWord_6358120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358120).length < 2 ^ (prefixWord ++ tailWord_6358120).sum := by decide
  have hdescent : baseEnd_6358120 < baseStart_6358120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358126 : List Nat := [4, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6358126 : Nat := 118140960795 + 6358126 * 2 ^ 59
def prefixEnd_6358126 : Nat := 4983230072969 + 3 ^ 40 * 6358126 * 2
def baseEnd_6358126 : Nat := 3264774699848696036484517

theorem tailTrace_6358126 : CollatzResearch.WordTrace tailWord_6358126 prefixEnd_6358126 3264774699848696036484517 := by
  unfold tailWord_6358126
  simp only [CollatzResearch.WordTrace]
  refine ⟨28987488320450357289308779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 154599937709068572209646821 28987488320450357289308779)
  ·
    refine ⟨43481232480675535933963169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28987488320450357289308779 43481232480675535933963169)
    ·
      refine ⟨32610924360506651950472377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43481232480675535933963169 32610924360506651950472377)
      ·
        refine ⟨24458193270379988962854283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32610924360506651950472377 24458193270379988962854283)
        ·
          refine ⟨36687289905569983444281425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24458193270379988962854283 36687289905569983444281425)
          ·
            refine ⟨27515467429177487583211069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36687289905569983444281425 27515467429177487583211069)
            ·
              refine ⟨10318300285941557843704151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27515467429177487583211069 10318300285941557843704151)
              ·
                refine ⟨15477450428912336765556227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318300285941557843704151 15477450428912336765556227)
                ·
                  refine ⟨23216175643368505148334341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15477450428912336765556227 23216175643368505148334341)
                  ·
                    refine ⟨4353032933131594715312689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23216175643368505148334341 4353032933131594715312689)
                    ·
                      refine ⟨3264774699848696036484517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353032933131594715312689 3264774699848696036484517)
                      ·
                        rfl

theorem cell23_6358126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6358126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358126 prefixEnd_6358126 := by exact prefixLift 6358126
  have htrace : WordTrace (prefixWord ++ tailWord_6358126) baseStart_6358126 baseEnd_6358126 := by
    simpa [prefixWord, tailWord_6358126, baseEnd_6358126] using wordTrace_append hprefix tailTrace_6358126
  have hstable : (prefixWord ++ tailWord_6358126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358126).length < 2 ^ (prefixWord ++ tailWord_6358126).sum := by decide
  have hdescent : baseEnd_6358126 < baseStart_6358126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358155 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_6358155 : Nat := 118140960795 + 6358155 * 2 ^ 59
def prefixEnd_6358155 : Nat := 4983230072969 + 3 ^ 40 * 6358155 * 2
def baseEnd_6358155 : Nat := 3264789590787676423021883

theorem tailTrace_6358155 : CollatzResearch.WordTrace tailWord_6358155 prefixEnd_6358155 3264789590787676423021883 := by
  unfold tailWord_6358155
  simp only [CollatzResearch.WordTrace]
  refine ⟨231900964280497796267275919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154600642853665197511517279 231900964280497796267275919)
  ·
    refine ⟨347851446420746694400913879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231900964280497796267275919 347851446420746694400913879)
    ·
      refine ⟨521777169631120041601370819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347851446420746694400913879 521777169631120041601370819)
      ·
        refine ⟨782665754446680062402056229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521777169631120041601370819 782665754446680062402056229)
        ·
          refine ⟨146749828958752511700385543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 782665754446680062402056229 146749828958752511700385543)
          ·
            refine ⟨220124743438128767550578315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146749828958752511700385543 220124743438128767550578315)
            ·
              refine ⟨330187115157193151325867473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220124743438128767550578315 330187115157193151325867473)
              ·
                refine ⟨247640336367894863494400605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330187115157193151325867473 247640336367894863494400605)
                ·
                  refine ⟨92865126137960573810400227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 247640336367894863494400605 92865126137960573810400227)
                  ·
                    refine ⟨139297689206940860715600341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92865126137960573810400227 139297689206940860715600341)
                    ·
                      refine ⟨3264789590787676423021883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139297689206940860715600341 3264789590787676423021883)
                      ·
                        rfl

theorem cell23_6358155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_6358155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358155 prefixEnd_6358155 := by exact prefixLift 6358155
  have htrace : WordTrace (prefixWord ++ tailWord_6358155) baseStart_6358155 baseEnd_6358155 := by
    simpa [prefixWord, tailWord_6358155, baseEnd_6358155] using wordTrace_append hprefix tailTrace_6358155
  have hstable : (prefixWord ++ tailWord_6358155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358155).length < 2 ^ (prefixWord ++ tailWord_6358155).sum := by decide
  have hdescent : baseEnd_6358155 < baseStart_6358155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358172 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6358172 : Nat := 118140960795 + 6358172 * 2 ^ 59
def prefixEnd_6358172 : Nat := 4983230072969 + 3 ^ 40 * 6358172 * 2
def baseEnd_6358172 : Nat := 3264798319958802856509305

theorem tailTrace_6358172 : CollatzResearch.WordTrace tailWord_6358172 prefixEnd_6358172 3264798319958802856509305 := by
  unfold tailWord_6358172
  simp only [CollatzResearch.WordTrace]
  refine ⟨115950792160718104085322385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154601056214290805447096513 115950792160718104085322385)
  ·
    refine ⟨86963094120538578063991789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115950792160718104085322385 86963094120538578063991789)
    ·
      refine ⟨32611160295201966773996921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86963094120538578063991789 32611160295201966773996921)
      ·
        refine ⟨24458370221401475080497691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32611160295201966773996921 24458370221401475080497691)
        ·
          refine ⟨36687555332102212620746537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24458370221401475080497691 36687555332102212620746537)
          ·
            refine ⟨27515666499076659465559903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36687555332102212620746537 27515666499076659465559903)
            ·
              refine ⟨41273499748614989198339855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27515666499076659465559903 41273499748614989198339855)
              ·
                refine ⟨61910249622922483797509783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41273499748614989198339855 61910249622922483797509783)
                ·
                  refine ⟨92865374434383725696264675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61910249622922483797509783 92865374434383725696264675)
                  ·
                    refine ⟨139298061651575588544397013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92865374434383725696264675 139298061651575588544397013)
                    ·
                      refine ⟨3264798319958802856509305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 139298061651575588544397013 3264798319958802856509305)
                      ·
                        rfl

theorem cell23_6358172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6358172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358172 prefixEnd_6358172 := by exact prefixLift 6358172
  have htrace : WordTrace (prefixWord ++ tailWord_6358172) baseStart_6358172 baseEnd_6358172 := by
    simpa [prefixWord, tailWord_6358172, baseEnd_6358172] using wordTrace_append hprefix tailTrace_6358172
  have hstable : (prefixWord ++ tailWord_6358172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358172).length < 2 ^ (prefixWord ++ tailWord_6358172).sum := by decide
  have hdescent : baseEnd_6358172 < baseStart_6358172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358199 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_6358199 : Nat := 118140960795 + 6358199 * 2 ^ 59
def prefixEnd_6358199 : Nat := 4983230072969 + 3 ^ 40 * 6358199 * 2
def baseEnd_6358199 : Nat := 3264812183936474250871681

theorem tailTrace_6358199 : CollatzResearch.WordTrace tailWord_6358199 prefixEnd_6358199 3264812183936474250871681 := by
  unfold tailWord_6358199
  simp only [CollatzResearch.WordTrace]
  refine ⟨231902569092338391781877651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154601712728225594521251767 231902569092338391781877651)
  ·
    refine ⟨347853853638507587672816477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231902569092338391781877651 347853853638507587672816477)
    ·
      refine ⟨130445195114440345377306179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 347853853638507587672816477 130445195114440345377306179)
      ·
        refine ⟨195667792671660518065959269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130445195114440345377306179 195667792671660518065959269)
        ·
          refine ⟨36687711125936347137367363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 195667792671660518065959269 36687711125936347137367363)
          ·
            refine ⟨55031566688904520706051045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36687711125936347137367363 55031566688904520706051045)
            ·
              refine ⟨10318418754169597632384571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55031566688904520706051045 10318418754169597632384571)
              ·
                refine ⟨15477628131254396448576857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318418754169597632384571 15477628131254396448576857)
                ·
                  refine ⟨11608221098440797336432643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15477628131254396448576857 11608221098440797336432643)
                  ·
                    refine ⟨17412331647661196004648965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11608221098440797336432643 17412331647661196004648965)
                    ·
                      refine ⟨3264812183936474250871681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17412331647661196004648965 3264812183936474250871681)
                      ·
                        rfl

theorem cell23_6358199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_6358199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358199 prefixEnd_6358199 := by exact prefixLift 6358199
  have htrace : WordTrace (prefixWord ++ tailWord_6358199) baseStart_6358199 baseEnd_6358199 := by
    simpa [prefixWord, tailWord_6358199, baseEnd_6358199] using wordTrace_append hprefix tailTrace_6358199
  have hstable : (prefixWord ++ tailWord_6358199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358199).length < 2 ^ (prefixWord ++ tailWord_6358199).sum := by decide
  have hdescent : baseEnd_6358199 < baseStart_6358199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358253 : List Nat := [1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_6358253 : Nat := 118140960795 + 6358253 * 2 ^ 59
def prefixEnd_6358253 : Nat := 4983230072969 + 3 ^ 40 * 6358253 * 2
def baseEnd_6358253 : Nat := 3264839911891817039596433

theorem tailTrace_6358253 : CollatzResearch.WordTrace tailWord_6358253 prefixEnd_6358253 3264839911891817039596433 := by
  unfold tailWord_6358253
  simp only [CollatzResearch.WordTrace]
  refine ⟨231904538634142759004343413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154603025756095172669562275 231904538634142759004343413)
  ·
    refine ⟨21741050496950883656657195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231904538634142759004343413 21741050496950883656657195)
    ·
      refine ⟨32611575745426325484985793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21741050496950883656657195 32611575745426325484985793)
      ·
        refine ⟨24458681809069744113739345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32611575745426325484985793 24458681809069744113739345)
        ·
          refine ⟨18344011356802308085304509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24458681809069744113739345 18344011356802308085304509)
          ·
            refine ⟨6879004258800865531989191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18344011356802308085304509 6879004258800865531989191)
            ·
              refine ⟨10318506388201298297983787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6879004258800865531989191 10318506388201298297983787)
              ·
                refine ⟨15477759582301947446975681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10318506388201298297983787 15477759582301947446975681)
                ·
                  refine ⟨11608319686726460585231761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15477759582301947446975681 11608319686726460585231761)
                  ·
                    refine ⟨8706239765044845438923821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11608319686726460585231761 8706239765044845438923821)
                    ·
                      refine ⟨3264839911891817039596433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706239765044845438923821 3264839911891817039596433)
                      ·
                        rfl

theorem cell23_6358253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_6358253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358253 prefixEnd_6358253 := by exact prefixLift 6358253
  have htrace : WordTrace (prefixWord ++ tailWord_6358253) baseStart_6358253 baseEnd_6358253 := by
    simpa [prefixWord, tailWord_6358253, baseEnd_6358253] using wordTrace_append hprefix tailTrace_6358253
  have hstable : (prefixWord ++ tailWord_6358253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358253).length < 2 ^ (prefixWord ++ tailWord_6358253).sum := by decide
  have hdescent : baseEnd_6358253 < baseStart_6358253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358283 : List Nat := [1, 1, 1, 1, 5, 3, 2, 4, 1, 1, 3]
def baseStart_6358283 : Nat := 118140960795 + 6358283 * 2 ^ 59
def prefixEnd_6358283 : Nat := 4983230072969 + 3 ^ 40 * 6358283 * 2
def baseEnd_6358283 : Nat := 3264855316311451922221295

theorem tailTrace_6358283 : CollatzResearch.WordTrace tailWord_6358283 prefixEnd_6358283 3264855316311451922221295 := by
  unfold tailWord_6358283
  simp only [CollatzResearch.WordTrace]
  refine ⟨231905632824034074127935503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154603755216022716085290335 231905632824034074127935503)
  ·
    refine ⟨347858449236051111191903255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 231905632824034074127935503 347858449236051111191903255)
    ·
      refine ⟨521787673854076666787854883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347858449236051111191903255 521787673854076666787854883)
      ·
        refine ⟨782681510781115000181782325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521787673854076666787854883 782681510781115000181782325)
        ·
          refine ⟨73376391635729531267042093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 782681510781115000181782325 73376391635729531267042093)
          ·
            refine ⟨27516146863398574225140785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73376391635729531267042093 27516146863398574225140785)
            ·
              refine ⟨20637110147548930668855589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27516146863398574225140785 20637110147548930668855589)
              ·
                refine ⟨3869458152665424500410423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20637110147548930668855589 3869458152665424500410423)
                ·
                  refine ⟨5804187228998136750615635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869458152665424500410423 5804187228998136750615635)
                  ·
                    refine ⟨8706280843497205125923453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804187228998136750615635 8706280843497205125923453)
                    ·
                      refine ⟨3264855316311451922221295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706280843497205125923453 3264855316311451922221295)
                      ·
                        rfl

theorem cell23_6358283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 1, 1, 3].length) (baseStart_6358283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358283 prefixEnd_6358283 := by exact prefixLift 6358283
  have htrace : WordTrace (prefixWord ++ tailWord_6358283) baseStart_6358283 baseEnd_6358283 := by
    simpa [prefixWord, tailWord_6358283, baseEnd_6358283] using wordTrace_append hprefix tailTrace_6358283
  have hstable : (prefixWord ++ tailWord_6358283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358283).length < 2 ^ (prefixWord ++ tailWord_6358283).sum := by decide
  have hdescent : baseEnd_6358283 < baseStart_6358283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358290 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_6358290 : Nat := 118140960795 + 6358290 * 2 ^ 59
def prefixEnd_6358290 : Nat := 4983230072969 + 3 ^ 40 * 6358290 * 2
def baseEnd_6358290 : Nat := 362762101186225932759307

theorem tailTrace_6358290 : CollatzResearch.WordTrace tailWord_6358290 prefixEnd_6358290 362762101186225932759307 := by
  unfold tailWord_6358290
  simp only [CollatzResearch.WordTrace]
  refine ⟨57976472033752178580860081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 154603925423339142882293549 57976472033752178580860081)
  ·
    refine ⟨43482354025314133935645061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57976472033752178580860081 43482354025314133935645061)
    ·
      refine ⟨8152941379746400112933449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43482354025314133935645061 8152941379746400112933449)
      ·
        refine ⟨6114706034809800084700087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8152941379746400112933449 6114706034809800084700087)
        ·
          refine ⟨9172059052214700127050131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114706034809800084700087 9172059052214700127050131)
          ·
            refine ⟨13758088578322050190575197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172059052214700127050131 13758088578322050190575197)
            ·
              refine ⟨5159283216870768821465699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13758088578322050190575197 5159283216870768821465699)
              ·
                refine ⟨7738924825306153232198549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5159283216870768821465699 7738924825306153232198549)
                ·
                  refine ⟨362762101186225932759307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7738924825306153232198549 362762101186225932759307)
                  ·
                    rfl

theorem cell23_6358290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_6358290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358290 prefixEnd_6358290 := by exact prefixLift 6358290
  have htrace : WordTrace (prefixWord ++ tailWord_6358290) baseStart_6358290 baseEnd_6358290 := by
    simpa [prefixWord, tailWord_6358290, baseEnd_6358290] using wordTrace_append hprefix tailTrace_6358290
  have hstable : (prefixWord ++ tailWord_6358290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358290).length < 2 ^ (prefixWord ++ tailWord_6358290).sum := by decide
  have hdescent : baseEnd_6358290 < baseStart_6358290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358317 : List Nat := [1, 5, 3, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6358317 : Nat := 118140960795 + 6358317 * 2 ^ 59
def prefixEnd_6358317 : Nat := 4983230072969 + 3 ^ 40 * 6358317 * 2
def baseEnd_6358317 : Nat := 3264872774653704789196139

theorem tailTrace_6358317 : CollatzResearch.WordTrace tailWord_6358317 prefixEnd_6358317 3264872774653704789196139 := by
  unfold tailWord_6358317
  simp only [CollatzResearch.WordTrace]
  refine ⟨231906872905910897934673205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154604581937273931956448803 231906872905910897934673205)
  ·
    refine ⟨21741269334929146681375613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 231906872905910897934673205 21741269334929146681375613)
    ·
      refine ⟨8152976000598430005515855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21741269334929146681375613 8152976000598430005515855)
      ·
        refine ⟨12229464000897645008273783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8152976000598430005515855 12229464000897645008273783)
        ·
          refine ⟨18344196001346467512410675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12229464000897645008273783 18344196001346467512410675)
          ·
            refine ⟨27516294002019701268616013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18344196001346467512410675 27516294002019701268616013)
            ·
              refine ⟨10318610250757387975731005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27516294002019701268616013 10318610250757387975731005)
              ·
                refine ⟨3869478844034020490899127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10318610250757387975731005 3869478844034020490899127)
                ·
                  refine ⟨5804218266051030736348691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3869478844034020490899127 5804218266051030736348691)
                  ·
                    refine ⟨8706327399076546104523037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5804218266051030736348691 8706327399076546104523037)
                    ·
                      refine ⟨3264872774653704789196139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706327399076546104523037 3264872774653704789196139)
                      ·
                        rfl

theorem cell23_6358317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6358317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358317 prefixEnd_6358317 := by exact prefixLift 6358317
  have htrace : WordTrace (prefixWord ++ tailWord_6358317) baseStart_6358317 baseEnd_6358317 := by
    simpa [prefixWord, tailWord_6358317, baseEnd_6358317] using wordTrace_append hprefix tailTrace_6358317
  have hstable : (prefixWord ++ tailWord_6358317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358317).length < 2 ^ (prefixWord ++ tailWord_6358317).sum := by decide
  have hdescent : baseEnd_6358317 < baseStart_6358317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358356 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_6358356 : Nat := 118140960795 + 6358356 * 2 ^ 59
def prefixEnd_6358356 : Nat := 4983230072969 + 3 ^ 40 * 6358356 * 2
def baseEnd_6358356 : Nat := 3264892800399230136608459

theorem tailTrace_6358356 : CollatzResearch.WordTrace tailWord_6358356 prefixEnd_6358356 3264892800399230136608459 := by
  unfold tailWord_6358356
  simp only [CollatzResearch.WordTrace]
  refine ⟨115954147676384803797671461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154605530235179738396895281 115954147676384803797671461)
  ·
    refine ⟨21741402689322150712063399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115954147676384803797671461 21741402689322150712063399)
    ·
      refine ⟨32612104033983226068095099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21741402689322150712063399 32612104033983226068095099)
      ·
        refine ⟨48918156050974839102142649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32612104033983226068095099 48918156050974839102142649)
        ·
          refine ⟨36688617038231129326606987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48918156050974839102142649 36688617038231129326606987)
          ·
            refine ⟨55032925557346693989910481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36688617038231129326606987 55032925557346693989910481)
            ·
              refine ⟨41274694168010020492432861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55032925557346693989910481 41274694168010020492432861)
              ·
                refine ⟨15478010313003757684662323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41274694168010020492432861 15478010313003757684662323)
                ·
                  refine ⟨23217015469505636526993485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15478010313003757684662323 23217015469505636526993485)
                  ·
                    refine ⟨8706380801064613697622557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23217015469505636526993485 8706380801064613697622557)
                    ·
                      refine ⟨3264892800399230136608459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8706380801064613697622557 3264892800399230136608459)
                      ·
                        rfl

theorem cell23_6358356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_6358356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358356 prefixEnd_6358356 := by exact prefixLift 6358356
  have htrace : WordTrace (prefixWord ++ tailWord_6358356) baseStart_6358356 baseEnd_6358356 := by
    simpa [prefixWord, tailWord_6358356, baseEnd_6358356] using wordTrace_append hprefix tailTrace_6358356
  have hstable : (prefixWord ++ tailWord_6358356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358356).length < 2 ^ (prefixWord ++ tailWord_6358356).sum := by decide
  have hdescent : baseEnd_6358356 < baseStart_6358356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358396 : List Nat := [2, 2, 2, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_6358396 : Nat := 118140960795 + 6358396 * 2 ^ 59
def prefixEnd_6358396 : Nat := 4983230072969 + 3 ^ 40 * 6358396 * 2
def baseEnd_6358396 : Nat := 3264913339625409980108275

theorem tailTrace_6358396 : CollatzResearch.WordTrace tailWord_6358396 prefixEnd_6358396 3264913339625409980108275 := by
  unfold tailWord_6358396
  simp only [CollatzResearch.WordTrace]
  refine ⟨115954877136312347213399521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154606502848416462951199361 115954877136312347213399521)
  ·
    refine ⟨86966157852234260410049641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115954877136312347213399521 86966157852234260410049641)
    ·
      refine ⟨65224618389175695307537231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86966157852234260410049641 65224618389175695307537231)
      ·
        refine ⟨97836927583763542961305847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65224618389175695307537231 97836927583763542961305847)
        ·
          refine ⟨146755391375645314441958771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97836927583763542961305847 146755391375645314441958771)
          ·
            refine ⟨220133087063467971662938157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146755391375645314441958771 220133087063467971662938157)
            ·
              refine ⟨82549907648800489373601809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220133087063467971662938157 82549907648800489373601809)
              ·
                refine ⟨61912430736600367030201357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82549907648800489373601809 61912430736600367030201357)
                ·
                  refine ⟨23217161526225137636325509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61912430736600367030201357 23217161526225137636325509)
                  ·
                    refine ⟨4353217786167213306811033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23217161526225137636325509 4353217786167213306811033)
                    ·
                      refine ⟨3264913339625409980108275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353217786167213306811033 3264913339625409980108275)
                      ·
                        rfl

theorem cell23_6358396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_6358396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358396 prefixEnd_6358396 := by exact prefixLift 6358396
  have htrace : WordTrace (prefixWord ++ tailWord_6358396) baseStart_6358396 baseEnd_6358396 := by
    simpa [prefixWord, tailWord_6358396, baseEnd_6358396] using wordTrace_append hprefix tailTrace_6358396
  have hstable : (prefixWord ++ tailWord_6358396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358396).length < 2 ^ (prefixWord ++ tailWord_6358396).sum := by decide
  have hdescent : baseEnd_6358396 < baseStart_6358396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358453 : List Nat := [1, 3, 3, 2, 2, 1, 2, 4, 5]
def baseStart_6358453 : Nat := 118140960795 + 6358453 * 2 ^ 59
def prefixEnd_6358453 : Nat := 4983230072969 + 3 ^ 40 * 6358453 * 2
def baseEnd_6358453 : Nat := 362771400891412917455057

theorem tailTrace_6358453 : CollatzResearch.WordTrace tailWord_6358453 prefixEnd_6358453 362771400891412917455057 := by
  unfold tailWord_6358453
  simp only [CollatzResearch.WordTrace]
  refine ⟨231911833233418193161624013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 154607888822278795441082675 231911833233418193161624013)
  ·
    refine ⟨86966937462531822435609005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 231911833233418193161624013 86966937462531822435609005)
    ·
      refine ⟨32612601548449433413353377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86966937462531822435609005 32612601548449433413353377)
      ·
        refine ⟨24459451161337075060015033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32612601548449433413353377 24459451161337075060015033)
        ·
          refine ⟨18344588371002806295011275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24459451161337075060015033 18344588371002806295011275)
          ·
            refine ⟨27516882556504209442516913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18344588371002806295011275 27516882556504209442516913)
            ·
              refine ⟨20637661917378157081887685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27516882556504209442516913 20637661917378157081887685)
              ·
                refine ⟨3869561609508404452853941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20637661917378157081887685 3869561609508404452853941)
                ·
                  refine ⟨362771400891412917455057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3869561609508404452853941 362771400891412917455057)
                  ·
                    rfl

theorem cell23_6358453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 4, 5].length) (baseStart_6358453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358453 prefixEnd_6358453 := by exact prefixLift 6358453
  have htrace : WordTrace (prefixWord ++ tailWord_6358453) baseStart_6358453 baseEnd_6358453 := by
    simpa [prefixWord, tailWord_6358453, baseEnd_6358453] using wordTrace_append hprefix tailTrace_6358453
  have hstable : (prefixWord ++ tailWord_6358453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358453).length < 2 ^ (prefixWord ++ tailWord_6358453).sum := by decide
  have hdescent : baseEnd_6358453 < baseStart_6358453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6358456 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_6358456 : Nat := 118140960795 + 6358456 * 2 ^ 59
def prefixEnd_6358456 : Nat := 4983230072969 + 3 ^ 40 * 6358456 * 2
def baseEnd_6358456 : Nat := 3264944148464679745357999

theorem tailTrace_6358456 : CollatzResearch.WordTrace tailWord_6358456 prefixEnd_6358456 3264944148464679745357999 := by
  unfold tailWord_6358456
  simp only [CollatzResearch.WordTrace]
  refine ⟨115955971326203662336991611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 154607961768271549782655481 115955971326203662336991611)
  ·
    refine ⟨173933956989305493505487417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115955971326203662336991611 173933956989305493505487417)
    ·
      refine ⟨130450467741979120129115563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 173933956989305493505487417 130450467741979120129115563)
      ·
        refine ⟨195675701612968680193673345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130450467741979120129115563 195675701612968680193673345)
        ·
          refine ⟨146756776209726510145255009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 195675701612968680193673345 146756776209726510145255009)
          ·
            refine ⟨110067582157294882608941257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 146756776209726510145255009 110067582157294882608941257)
            ·
              refine ⟨82550686617971161956705943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110067582157294882608941257 82550686617971161956705943)
              ·
                refine ⟨123826029926956742935058915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82550686617971161956705943 123826029926956742935058915)
                ·
                  refine ⟨185739044890435114402588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123826029926956742935058915 185739044890435114402588373)
                  ·
                    refine ⟨4353258864619572993810665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 185739044890435114402588373 4353258864619572993810665)
                    ·
                      refine ⟨3264944148464679745357999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4353258864619572993810665 3264944148464679745357999)
                      ·
                        rfl

theorem cell23_6358456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_6358456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6358456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6358456 prefixEnd_6358456 := by exact prefixLift 6358456
  have htrace : WordTrace (prefixWord ++ tailWord_6358456) baseStart_6358456 baseEnd_6358456 := by
    simpa [prefixWord, tailWord_6358456, baseEnd_6358456] using wordTrace_append hprefix tailTrace_6358456
  have hstable : (prefixWord ++ tailWord_6358456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6358456).length < 2 ^ (prefixWord ++ tailWord_6358456).sum := by decide
  have hdescent : baseEnd_6358456 < baseStart_6358456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6358456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
