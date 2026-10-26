import V185TrunkScan23Chunk0867

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5137033 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_5137033 : Nat := 118140960795 + 5137033 * 2 ^ 59
def prefixEnd_5137033 : Nat := 4983230072969 + 3 ^ 40 * 5137033 * 2
def baseEnd_5137033 : Nat := 2637767067008105068462721

theorem tailTrace_5137033 : CollatzResearch.WordTrace tailWord_5137033 prefixEnd_5137033 2637767067008105068462721 := by
  unfold tailWord_5137033
  simp only [CollatzResearch.WordTrace]
  refine ⟨187362985998414251233271753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124908657332276167488847835 187362985998414251233271753)
  ·
    refine ⟨140522239498810688424953815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187362985998414251233271753 140522239498810688424953815)
    ·
      refine ⟨210783359248216032637430723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140522239498810688424953815 210783359248216032637430723)
      ·
        refine ⟨316175038872324048956146085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210783359248216032637430723 316175038872324048956146085)
        ·
          refine ⟨59282819788560759179277391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 316175038872324048956146085 59282819788560759179277391)
          ·
            refine ⟨88924229682841138768916087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59282819788560759179277391 88924229682841138768916087)
            ·
              refine ⟨133386344524261708153374131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88924229682841138768916087 133386344524261708153374131)
              ·
                refine ⟨200079516786392562230061197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133386344524261708153374131 200079516786392562230061197)
                ·
                  refine ⟨75029818794897210836272949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200079516786392562230061197 75029818794897210836272949)
                  ·
                    refine ⟨7034045512021613515900589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75029818794897210836272949 7034045512021613515900589)
                    ·
                      refine ⟨2637767067008105068462721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7034045512021613515900589 2637767067008105068462721)
                      ·
                        rfl

theorem cell23_5137033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_5137033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137033 prefixEnd_5137033 := by exact prefixLift 5137033
  have htrace : WordTrace (prefixWord ++ tailWord_5137033) baseStart_5137033 baseEnd_5137033 := by
    simpa [prefixWord, tailWord_5137033, baseEnd_5137033] using wordTrace_append hprefix tailTrace_5137033
  have hstable : (prefixWord ++ tailWord_5137033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137033).length < 2 ^ (prefixWord ++ tailWord_5137033).sum := by decide
  have hdescent : baseEnd_5137033 < baseStart_5137033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137113 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 8]
def baseStart_5137113 : Nat := 118140960795 + 5137113 * 2 ^ 59
def prefixEnd_5137113 : Nat := 4983230072969 + 3 ^ 40 * 5137113 * 2
def baseEnd_5137113 : Nat := 293089793940051639495817

theorem tailTrace_5137113 : CollatzResearch.WordTrace tailWord_5137113 prefixEnd_5137113 293089793940051639495817 := by
  unfold tailWord_5137113
  simp only [CollatzResearch.WordTrace]
  refine ⟨187365903838124424896183993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124910602558749616597455995 187365903838124424896183993)
  ·
    refine ⟨140524427878593318672137995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187365903838124424896183993 140524427878593318672137995)
    ·
      refine ⟨210786641817889978008206993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140524427878593318672137995 210786641817889978008206993)
      ·
        refine ⟨158089981363417483506155245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210786641817889978008206993 158089981363417483506155245)
        ·
          refine ⟨59283743011281556314808217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158089981363417483506155245 59283743011281556314808217)
          ·
            refine ⟨44462807258461167236106163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59283743011281556314808217 44462807258461167236106163)
            ·
              refine ⟨66694210887691750854159245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44462807258461167236106163 66694210887691750854159245)
              ·
                refine ⟨25010329082884406570309717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66694210887691750854159245 25010329082884406570309717)
                ·
                  refine ⟨293089793940051639495817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25010329082884406570309717 293089793940051639495817)
                  ·
                    rfl

theorem cell23_5137113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_5137113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137113 prefixEnd_5137113 := by exact prefixLift 5137113
  have htrace : WordTrace (prefixWord ++ tailWord_5137113) baseStart_5137113 baseEnd_5137113 := by
    simpa [prefixWord, tailWord_5137113, baseEnd_5137113] using wordTrace_append hprefix tailTrace_5137113
  have hstable : (prefixWord ++ tailWord_5137113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137113).length < 2 ^ (prefixWord ++ tailWord_5137113).sum := by decide
  have hdescent : baseEnd_5137113 < baseStart_5137113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137167 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 2, 3, 2]
def baseStart_5137167 : Nat := 118140960795 + 5137167 * 2 ^ 59
def prefixEnd_5137167 : Nat := 4983230072969 + 3 ^ 40 * 5137167 * 2
def baseEnd_5137167 : Nat := 2637835873415807544187105

theorem tailTrace_5137167 : CollatzResearch.WordTrace tailWord_5137167 prefixEnd_5137167 2637835873415807544187105 := by
  unfold tailWord_5137167
  simp only [CollatzResearch.WordTrace]
  refine ⟨187367873379928792118649755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124911915586619194745766503 187367873379928792118649755)
  ·
    refine ⟨281051810069893188177974633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187367873379928792118649755 281051810069893188177974633)
    ·
      refine ⟨210788857552419891133480975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281051810069893188177974633 210788857552419891133480975)
      ·
        refine ⟨316183286328629836700221463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210788857552419891133480975 316183286328629836700221463)
        ·
          refine ⟨474274929492944755050332195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316183286328629836700221463 474274929492944755050332195)
          ·
            refine ⟨711412394239417132575498293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474274929492944755050332195 711412394239417132575498293)
            ·
              refine ⟨66694911959945356178952965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711412394239417132575498293 66694911959945356178952965)
              ·
                refine ⟨12505295992489754283553681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66694911959945356178952965 12505295992489754283553681)
                ·
                  refine ⟨9378971994367315712665261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12505295992489754283553681 9378971994367315712665261)
                  ·
                    refine ⟨3517114497887743392249473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9378971994367315712665261 3517114497887743392249473)
                    ·
                      refine ⟨2637835873415807544187105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517114497887743392249473 2637835873415807544187105)
                      ·
                        rfl

theorem cell23_5137167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 3, 2].length) (baseStart_5137167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137167 prefixEnd_5137167 := by exact prefixLift 5137167
  have htrace : WordTrace (prefixWord ++ tailWord_5137167) baseStart_5137167 baseEnd_5137167 := by
    simpa [prefixWord, tailWord_5137167, baseEnd_5137167] using wordTrace_append hprefix tailTrace_5137167
  have hstable : (prefixWord ++ tailWord_5137167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137167).length < 2 ^ (prefixWord ++ tailWord_5137167).sum := by decide
  have hdescent : baseEnd_5137167 < baseStart_5137167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137244 : List Nat := [2, 2, 4, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_5137244 : Nat := 118140960795 + 5137244 * 2 ^ 59
def prefixEnd_5137244 : Nat := 4983230072969 + 3 ^ 40 * 5137244 * 2
def baseEnd_5137244 : Nat := 2637875411426203742924251

theorem tailTrace_5137244 : CollatzResearch.WordTrace tailWord_5137244 prefixEnd_5137244 2637875411426203742924251 := by
  unfold tailWord_5137244
  simp only [CollatzResearch.WordTrace]
  refine ⟨93685340900324917134601393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124913787867099889512801857 93685340900324917134601393)
  ·
    refine ⟨70264005675243687850951045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93685340900324917134601393 70264005675243687850951045)
    ·
      refine ⟨13174501064108191472053321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70264005675243687850951045 13174501064108191472053321)
      ·
        refine ⟨9880875798081143604039991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13174501064108191472053321 9880875798081143604039991)
        ·
          refine ⟨14821313697121715406059987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9880875798081143604039991 14821313697121715406059987)
          ·
            refine ⟨22231970545682573109089981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14821313697121715406059987 22231970545682573109089981)
            ·
              refine ⟨8336988954630964915908743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22231970545682573109089981 8336988954630964915908743)
              ·
                refine ⟨12505483431946447373863115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8336988954630964915908743 12505483431946447373863115)
                ·
                  refine ⟨18758225147919671060794673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12505483431946447373863115 18758225147919671060794673)
                  ·
                    refine ⟨14068668860939753295596005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18758225147919671060794673 14068668860939753295596005)
                    ·
                      refine ⟨2637875411426203742924251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14068668860939753295596005 2637875411426203742924251)
                      ·
                        rfl

theorem cell23_5137244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_5137244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137244 prefixEnd_5137244 := by exact prefixLift 5137244
  have htrace : WordTrace (prefixWord ++ tailWord_5137244) baseStart_5137244 baseEnd_5137244 := by
    simpa [prefixWord, tailWord_5137244, baseEnd_5137244] using wordTrace_append hprefix tailTrace_5137244
  have hstable : (prefixWord ++ tailWord_5137244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137244).length < 2 ^ (prefixWord ++ tailWord_5137244).sum := by decide
  have hdescent : baseEnd_5137244 < baseStart_5137244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137260 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_5137260 : Nat := 118140960795 + 5137260 * 2 ^ 59
def prefixEnd_5137260 : Nat := 4983230072969 + 3 ^ 40 * 5137260 * 2
def baseEnd_5137260 : Nat := 2637883627116675680324177

theorem tailTrace_5137260 : CollatzResearch.WordTrace tailWord_5137260 prefixEnd_5137260 2637883627116675680324177 := by
  unfold tailWord_5137260
  simp only [CollatzResearch.WordTrace]
  refine ⟨93685632684295934500892617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124914176912394579334523489 93685632684295934500892617)
  ·
    refine ⟨70264224513221950875669463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93685632684295934500892617 70264224513221950875669463)
    ·
      refine ⟨105396336769832926313504195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70264224513221950875669463 105396336769832926313504195)
      ·
        refine ⟨158094505154749389470256293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105396336769832926313504195 158094505154749389470256293)
        ·
          refine ⟨29642719716515510525673055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158094505154749389470256293 29642719716515510525673055)
          ·
            refine ⟨44464079574773265788509583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29642719716515510525673055 44464079574773265788509583)
            ·
              refine ⟨66696119362159898682764375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44464079574773265788509583 66696119362159898682764375)
              ·
                refine ⟨100044179043239848024146563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66696119362159898682764375 100044179043239848024146563)
                ·
                  refine ⟨150066268564859772036219845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100044179043239848024146563 150066268564859772036219845)
                  ·
                    refine ⟨28137425355911207256791221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150066268564859772036219845 28137425355911207256791221)
                    ·
                      refine ⟨2637883627116675680324177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28137425355911207256791221 2637883627116675680324177)
                      ·
                        rfl

theorem cell23_5137260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_5137260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137260 prefixEnd_5137260 := by exact prefixLift 5137260
  have htrace : WordTrace (prefixWord ++ tailWord_5137260) baseStart_5137260 baseEnd_5137260 := by
    simpa [prefixWord, tailWord_5137260, baseEnd_5137260] using wordTrace_append hprefix tailTrace_5137260
  have hstable : (prefixWord ++ tailWord_5137260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137260).length < 2 ^ (prefixWord ++ tailWord_5137260).sum := by decide
  have hdescent : baseEnd_5137260 < baseStart_5137260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137280 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 2, 6]
def baseStart_5137280 : Nat := 118140960795 + 5137280 * 2 ^ 59
def prefixEnd_5137280 : Nat := 4983230072969 + 3 ^ 40 * 5137280 * 2
def baseEnd_5137280 : Nat := 879297965576588534024695

theorem tailTrace_5137280 : CollatzResearch.WordTrace tailWord_5137280 prefixEnd_5137280 879297965576588534024695 := by
  unfold tailWord_5137280
  simp only [CollatzResearch.WordTrace]
  refine ⟨93685997414259706208756647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124914663219012941611675529 93685997414259706208756647)
  ·
    refine ⟨140528996121389559313134971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93685997414259706208756647 140528996121389559313134971)
    ·
      refine ⟨210793494182084338969702457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140528996121389559313134971 210793494182084338969702457)
      ·
        refine ⟨158095120636563254227276843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210793494182084338969702457 158095120636563254227276843)
        ·
          refine ⟨237142680954844881340915265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158095120636563254227276843 237142680954844881340915265)
          ·
            refine ⟨177857010716133661005686449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237142680954844881340915265 177857010716133661005686449)
            ·
              refine ⟨133392758037100245754264837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177857010716133661005686449 133392758037100245754264837)
              ·
                refine ⟨25011142131956296078924657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133392758037100245754264837 25011142131956296078924657)
                ·
                  refine ⟨18758356598967222059193493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25011142131956296078924657 18758356598967222059193493)
                  ·
                    refine ⟨879297965576588534024695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18758356598967222059193493 879297965576588534024695)
                    ·
                      rfl

theorem cell23_5137280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 2, 6].length) (baseStart_5137280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137280 prefixEnd_5137280 := by exact prefixLift 5137280
  have htrace : WordTrace (prefixWord ++ tailWord_5137280) baseStart_5137280 baseEnd_5137280 := by
    simpa [prefixWord, tailWord_5137280, baseEnd_5137280] using wordTrace_append hprefix tailTrace_5137280
  have hstable : (prefixWord ++ tailWord_5137280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137280).length < 2 ^ (prefixWord ++ tailWord_5137280).sum := by decide
  have hdescent : baseEnd_5137280 < baseStart_5137280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137282 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5137282 : Nat := 118140960795 + 5137282 * 2 ^ 59
def prefixEnd_5137282 : Nat := 4983230072969 + 3 ^ 40 * 5137282 * 2
def baseEnd_5137282 : Nat := 2637894923691074594249077

theorem tailTrace_5137282 : CollatzResearch.WordTrace tailWord_5137282 prefixEnd_5137282 2637894923691074594249077 := by
  unfold tailWord_5137282
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843016943628041689771525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124914711849674777839390733 46843016943628041689771525)
  ·
    refine ⟨8783065676930257816832161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46843016943628041689771525 8783065676930257816832161)
    ·
      refine ⟨6587299257697693362624121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8783065676930257816832161 6587299257697693362624121)
      ·
        refine ⟨4940474443273270021968091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587299257697693362624121 4940474443273270021968091)
        ·
          refine ⟨7410711664909905032952137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940474443273270021968091 7410711664909905032952137)
          ·
            refine ⟨5558033748682428774714103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7410711664909905032952137 5558033748682428774714103)
            ·
              refine ⟨8337050623023643162071155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558033748682428774714103 8337050623023643162071155)
              ·
                refine ⟨12505575934535464743106733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8337050623023643162071155 12505575934535464743106733)
                ·
                  refine ⟨4689590975450799278665025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12505575934535464743106733 4689590975450799278665025)
                  ·
                    refine ⟨3517193231588099458998769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689590975450799278665025 3517193231588099458998769)
                    ·
                      refine ⟨2637894923691074594249077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517193231588099458998769 2637894923691074594249077)
                      ·
                        rfl

theorem cell23_5137282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5137282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137282 prefixEnd_5137282 := by exact prefixLift 5137282
  have htrace : WordTrace (prefixWord ++ tailWord_5137282) baseStart_5137282 baseEnd_5137282 := by
    simpa [prefixWord, tailWord_5137282, baseEnd_5137282] using wordTrace_append hprefix tailTrace_5137282
  have hstable : (prefixWord ++ tailWord_5137282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137282).length < 2 ^ (prefixWord ++ tailWord_5137282).sum := by decide
  have hdescent : baseEnd_5137282 < baseStart_5137282 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137298 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5137298 : Nat := 118140960795 + 5137298 * 2 ^ 59
def prefixEnd_5137298 : Nat := 4983230072969 + 3 ^ 40 * 5137298 * 2
def baseEnd_5137298 : Nat := 2637903139381546531649003

theorem tailTrace_5137298 : CollatzResearch.WordTrace tailWord_5137298 prefixEnd_5137298 2637903139381546531649003 := by
  unfold tailWord_5137298
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843162835613550372917137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124915100894969467661112365 46843162835613550372917137)
  ·
    refine ⟨35132372126710162779687853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46843162835613550372917137 35132372126710162779687853)
    ·
      refine ⟨13174639547516311042382945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35132372126710162779687853 13174639547516311042382945)
      ·
        refine ⟨9880979660637233281787209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13174639547516311042382945 9880979660637233281787209)
        ·
          refine ⟨7410734745477924961340407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9880979660637233281787209 7410734745477924961340407)
          ·
            refine ⟨11116102118216887442010611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410734745477924961340407 11116102118216887442010611)
            ·
              refine ⟨16674153177325331163015917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116102118216887442010611 16674153177325331163015917)
              ·
                refine ⟨6252807441496999186130969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16674153177325331163015917 6252807441496999186130969)
                ·
                  refine ⟨4689605581122749389598227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6252807441496999186130969 4689605581122749389598227)
                  ·
                    refine ⟨7034408371684124084397341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4689605581122749389598227 7034408371684124084397341)
                    ·
                      refine ⟨2637903139381546531649003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7034408371684124084397341 2637903139381546531649003)
                      ·
                        rfl

theorem cell23_5137298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5137298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137298 prefixEnd_5137298 := by exact prefixLift 5137298
  have htrace : WordTrace (prefixWord ++ tailWord_5137298) baseStart_5137298 baseEnd_5137298 := by
    simpa [prefixWord, tailWord_5137298, baseEnd_5137298] using wordTrace_append hprefix tailTrace_5137298
  have hstable : (prefixWord ++ tailWord_5137298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137298).length < 2 ^ (prefixWord ++ tailWord_5137298).sum := by decide
  have hdescent : baseEnd_5137298 < baseStart_5137298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137344 : List Nat := [2, 1, 1, 2, 3, 4, 1, 4, 5]
def baseStart_5137344 : Nat := 118140960795 + 5137344 * 2 ^ 59
def prefixEnd_5137344 : Nat := 4983230072969 + 3 ^ 40 * 5137344 * 2
def baseEnd_5137344 : Nat := 293102973276850372408199

theorem tailTrace_5137344 : CollatzResearch.WordTrace tailWord_5137344 prefixEnd_5137344 293102973276850372408199 := by
  unfold tailWord_5137344
  simp only [CollatzResearch.WordTrace]
  refine ⟨93687164550143775673921543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124916219400191700898562057 93687164550143775673921543)
  ·
    refine ⟨140530746825215663510882315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93687164550143775673921543 140530746825215663510882315)
    ·
      refine ⟨210796120237823495266323473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140530746825215663510882315 210796120237823495266323473)
      ·
        refine ⟨158097090178367621449742605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210796120237823495266323473 158097090178367621449742605)
        ·
          refine ⟨59286408816887858043653477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158097090178367621449742605 59286408816887858043653477)
          ·
            refine ⟨11116201653166473383185027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59286408816887858043653477 11116201653166473383185027)
            ·
              refine ⟨16674302479749710074777541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116201653166473383185027 16674302479749710074777541)
              ·
                refine ⟨3126431714953070639020789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16674302479749710074777541 3126431714953070639020789)
                ·
                  refine ⟨293102973276850372408199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126431714953070639020789 293102973276850372408199)
                  ·
                    rfl

theorem cell23_5137344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 5].length) (baseStart_5137344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137344 prefixEnd_5137344 := by exact prefixLift 5137344
  have htrace : WordTrace (prefixWord ++ tailWord_5137344) baseStart_5137344 baseEnd_5137344 := by
    simpa [prefixWord, tailWord_5137344, baseEnd_5137344] using wordTrace_append hprefix tailTrace_5137344
  have hstable : (prefixWord ++ tailWord_5137344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137344).length < 2 ^ (prefixWord ++ tailWord_5137344).sum := by decide
  have hdescent : baseEnd_5137344 < baseStart_5137344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137378 : List Nat := [3, 3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_5137378 : Nat := 118140960795 + 5137378 * 2 ^ 59
def prefixEnd_5137378 : Nat := 4983230072969 + 3 ^ 40 * 5137378 * 2
def baseEnd_5137378 : Nat := 293104913092656246516515

theorem tailTrace_5137378 : CollatzResearch.WordTrace tailWord_5137378 prefixEnd_5137378 293104913092656246516515 := by
  unfold tailWord_5137378
  simp only [CollatzResearch.WordTrace]
  refine ⟨46843892295541093788645197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124917046121442916769720525 46843892295541093788645197)
  ·
    refine ⟨17566459610827910170741949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46843892295541093788645197 17566459610827910170741949)
    ·
      refine ⟨6587422354060466314028231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17566459610827910170741949 6587422354060466314028231)
      ·
        refine ⟨9881133531090699471042347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6587422354060466314028231 9881133531090699471042347)
        ·
          refine ⟨14821700296636049206563521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9881133531090699471042347 14821700296636049206563521)
          ·
            refine ⟨11116275222477036904922641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14821700296636049206563521 11116275222477036904922641)
            ·
              refine ⟨8337206416857777678691981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11116275222477036904922641 8337206416857777678691981)
              ·
                refine ⟨3126452406321666629509493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8337206416857777678691981 3126452406321666629509493)
                ·
                  refine ⟨293104913092656246516515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126452406321666629509493 293104913092656246516515)
                  ·
                    rfl

theorem cell23_5137378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_5137378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137378 prefixEnd_5137378 := by exact prefixLift 5137378
  have htrace : WordTrace (prefixWord ++ tailWord_5137378) baseStart_5137378 baseEnd_5137378 := by
    simpa [prefixWord, tailWord_5137378, baseEnd_5137378] using wordTrace_append hprefix tailTrace_5137378
  have hstable : (prefixWord ++ tailWord_5137378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137378).length < 2 ^ (prefixWord ++ tailWord_5137378).sum := by decide
  have hdescent : baseEnd_5137378 < baseStart_5137378 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137404 : List Nat := [2, 2, 2, 1, 2, 3, 1, 3, 3, 4]
def baseStart_5137404 : Nat := 118140960795 + 5137404 * 2 ^ 59
def prefixEnd_5137404 : Nat := 4983230072969 + 3 ^ 40 * 5137404 * 2
def baseEnd_5137404 : Nat := 879319189443641038974505

theorem tailTrace_5137404 : CollatzResearch.WordTrace tailWord_5137404 prefixEnd_5137404 879319189443641038974505 := by
  unfold tailWord_5137404
  simp only [CollatzResearch.WordTrace]
  refine ⟨93688258740035090797513633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124917678320046787730018177 93688258740035090797513633)
  ·
    refine ⟨70266194055026318098135225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93688258740035090797513633 70266194055026318098135225)
    ·
      refine ⟨52699645541269738573601419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70266194055026318098135225 52699645541269738573601419)
      ·
        refine ⟨79049468311904607860402129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52699645541269738573601419 79049468311904607860402129)
        ·
          refine ⟨59287101233928455895301597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79049468311904607860402129 59287101233928455895301597)
          ·
            refine ⟨22232662962723170960738099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59287101233928455895301597 22232662962723170960738099)
            ·
              refine ⟨33348994444084756441107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22232662962723170960738099 33348994444084756441107149)
              ·
                refine ⟨12505872916531783665415181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33348994444084756441107149 12505872916531783665415181)
                ·
                  refine ⟨4689702343699418874530693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12505872916531783665415181 4689702343699418874530693)
                  ·
                    refine ⟨879319189443641038974505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689702343699418874530693 879319189443641038974505)
                    ·
                      rfl

theorem cell23_5137404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_5137404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137404 prefixEnd_5137404 := by exact prefixLift 5137404
  have htrace : WordTrace (prefixWord ++ tailWord_5137404) baseStart_5137404 baseEnd_5137404 := by
    simpa [prefixWord, tailWord_5137404, baseEnd_5137404] using wordTrace_append hprefix tailTrace_5137404
  have hstable : (prefixWord ++ tailWord_5137404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137404).length < 2 ^ (prefixWord ++ tailWord_5137404).sum := by decide
  have hdescent : baseEnd_5137404 < baseStart_5137404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137417 : List Nat := [1, 2, 1, 1, 3, 1, 1, 7, 6]
def baseStart_5137417 : Nat := 118140960795 + 5137417 * 2 ^ 59
def prefixEnd_5137417 : Nat := 4983230072969 + 3 ^ 40 * 5137417 * 2
def baseEnd_5137417 : Nat := 293107138175492396228995

theorem tailTrace_5137417 : CollatzResearch.WordTrace tailWord_5137417 prefixEnd_5137417 293107138175492396228995 := by
  unfold tailWord_5137417
  simp only [CollatzResearch.WordTrace]
  refine ⟨187376991629023084815250505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124917994419348723210167003 187376991629023084815250505)
  ·
    refine ⟨140532743721767313611437879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187376991629023084815250505 140532743721767313611437879)
    ·
      refine ⟨210799115582650970417156819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140532743721767313611437879 210799115582650970417156819)
      ·
        refine ⟨316198673373976455625735229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210799115582650970417156819 316198673373976455625735229)
        ·
          refine ⟨118574502515241170859650711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316198673373976455625735229 118574502515241170859650711)
          ·
            refine ⟨177861753772861756289476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118574502515241170859650711 177861753772861756289476067)
            ·
              refine ⟨266792630659292634434214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177861753772861756289476067 266792630659292634434214101)
              ·
                refine ⟨6252952281077171119551893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266792630659292634434214101 6252952281077171119551893)
                ·
                  refine ⟨293107138175492396228995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6252952281077171119551893 293107138175492396228995)
                  ·
                    rfl

theorem cell23_5137417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_5137417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137417 prefixEnd_5137417 := by exact prefixLift 5137417
  have htrace : WordTrace (prefixWord ++ tailWord_5137417) baseStart_5137417 baseEnd_5137417 := by
    simpa [prefixWord, tailWord_5137417, baseEnd_5137417] using wordTrace_append hprefix tailTrace_5137417
  have hstable : (prefixWord ++ tailWord_5137417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137417).length < 2 ^ (prefixWord ++ tailWord_5137417).sum := by decide
  have hdescent : baseEnd_5137417 < baseStart_5137417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137427 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3]
def baseStart_5137427 : Nat := 118140960795 + 5137427 * 2 ^ 59
def prefixEnd_5137427 : Nat := 4983230072969 + 3 ^ 40 * 5137427 * 2
def baseEnd_5137427 : Nat := 2637969378385976526935909

theorem tailTrace_5137427 : CollatzResearch.WordTrace tailWord_5137427 prefixEnd_5137427 2637969378385976526935909 := by
  unfold tailWord_5137427
  simp only [CollatzResearch.WordTrace]
  refine ⟨187377356358986856523114535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124918237572657904348743023 187377356358986856523114535)
  ·
    refine ⟨281066034538480284784671803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187377356358986856523114535 281066034538480284784671803)
    ·
      refine ⟨421599051807720427177007705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281066034538480284784671803 421599051807720427177007705)
      ·
        refine ⟨316199288855790320382755779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421599051807720427177007705 316199288855790320382755779)
        ·
          refine ⟨474298933283685480574133669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316199288855790320382755779 474298933283685480574133669)
          ·
            refine ⟨88931049990691027607650063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 474298933283685480574133669 88931049990691027607650063)
            ·
              refine ⟨133396574986036541411475095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88931049990691027607650063 133396574986036541411475095)
              ·
                refine ⟨200094862479054812117212643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133396574986036541411475095 200094862479054812117212643)
                ·
                  refine ⟨300142293718582218175818965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200094862479054812117212643 300142293718582218175818965)
                  ·
                    refine ⟨7034585009029270738495757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 300142293718582218175818965 7034585009029270738495757)
                    ·
                      refine ⟨2637969378385976526935909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7034585009029270738495757 2637969378385976526935909)
                      ·
                        rfl

theorem cell23_5137427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 7, 3].length) (baseStart_5137427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137427 prefixEnd_5137427 := by exact prefixLift 5137427
  have htrace : WordTrace (prefixWord ++ tailWord_5137427) baseStart_5137427 baseEnd_5137427 := by
    simpa [prefixWord, tailWord_5137427, baseEnd_5137427] using wordTrace_append hprefix tailTrace_5137427
  have hstable : (prefixWord ++ tailWord_5137427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137427).length < 2 ^ (prefixWord ++ tailWord_5137427).sum := by decide
  have hdescent : baseEnd_5137427 < baseStart_5137427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137497 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_5137497 : Nat := 118140960795 + 5137497 * 2 ^ 59
def prefixEnd_5137497 : Nat := 4983230072969 + 3 ^ 40 * 5137497 * 2
def baseEnd_5137497 : Nat := 2638005322031791253060587

theorem tailTrace_5137497 : CollatzResearch.WordTrace tailWord_5137497 prefixEnd_5137497 2638005322031791253060587 := by
  unfold tailWord_5137497
  simp only [CollatzResearch.WordTrace]
  refine ⟨187379909468733258478162745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124919939645822172318775163 187379909468733258478162745)
  ·
    refine ⟨140534932101549943858622059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187379909468733258478162745 140534932101549943858622059)
    ·
      refine ⟨210802398152324915787933089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140534932101549943858622059 210802398152324915787933089)
      ·
        refine ⟨158101798614243686840949817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210802398152324915787933089 158101798614243686840949817)
        ·
          refine ⟨118576348960682765130712363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158101798614243686840949817 118576348960682765130712363)
          ·
            refine ⟨177864523441024147696068545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118576348960682765130712363 177864523441024147696068545)
            ·
              refine ⟨133398392580768110772051409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177864523441024147696068545 133398392580768110772051409)
              ·
                refine ⟨100048794435576083079038557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133398392580768110772051409 100048794435576083079038557)
                ·
                  refine ⟨37518297913341031154639459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100048794435576083079038557 37518297913341031154639459)
                  ·
                    refine ⟨56277446870011546731959189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37518297913341031154639459 56277446870011546731959189)
                    ·
                      refine ⟨2638005322031791253060587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56277446870011546731959189 2638005322031791253060587)
                      ·
                        rfl

theorem cell23_5137497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_5137497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137497 prefixEnd_5137497 := by exact prefixLift 5137497
  have htrace : WordTrace (prefixWord ++ tailWord_5137497) baseStart_5137497 baseEnd_5137497 := by
    simpa [prefixWord, tailWord_5137497, baseEnd_5137497] using wordTrace_append hprefix tailTrace_5137497
  have hstable : (prefixWord ++ tailWord_5137497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137497).length < 2 ^ (prefixWord ++ tailWord_5137497).sum := by decide
  have hdescent : baseEnd_5137497 < baseStart_5137497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137511 : List Nat := [1, 1, 5, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5137511 : Nat := 118140960795 + 5137511 * 2 ^ 59
def prefixEnd_5137511 : Nat := 4983230072969 + 3 ^ 40 * 5137511 * 2
def baseEnd_5137511 : Nat := 879337503586984732761841

theorem tailTrace_5137511 : CollatzResearch.WordTrace tailWord_5137511 prefixEnd_5137511 879337503586984732761841 := by
  unfold tailWord_5137511
  simp only [CollatzResearch.WordTrace]
  refine ⟨187380420090682538869172387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124920280060455025912781591 187380420090682538869172387)
  ·
    refine ⟨281070630136023808303758581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187380420090682538869172387 281070630136023808303758581)
    ·
      refine ⟨26350371575252232028477367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 281070630136023808303758581 26350371575252232028477367)
      ·
        refine ⟨39525557362878348042716051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26350371575252232028477367 39525557362878348042716051)
        ·
          refine ⟨59288336044317522064074077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39525557362878348042716051 59288336044317522064074077)
          ·
            refine ⟨22233126016619070774027779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59288336044317522064074077 22233126016619070774027779)
            ·
              refine ⟨33349689024928606161041669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22233126016619070774027779 33349689024928606161041669)
              ·
                refine ⟨6253066692174113655195313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33349689024928606161041669 6253066692174113655195313)
                ·
                  refine ⟨4689800019130585241396485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253066692174113655195313 4689800019130585241396485)
                  ·
                    refine ⟨879337503586984732761841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689800019130585241396485 879337503586984732761841)
                    ·
                      rfl

theorem cell23_5137511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5137511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137511 prefixEnd_5137511 := by exact prefixLift 5137511
  have htrace : WordTrace (prefixWord ++ tailWord_5137511) baseStart_5137511 baseEnd_5137511 := by
    simpa [prefixWord, tailWord_5137511, baseEnd_5137511] using wordTrace_append hprefix tailTrace_5137511
  have hstable : (prefixWord ++ tailWord_5137511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137511).length < 2 ^ (prefixWord ++ tailWord_5137511).sum := by decide
  have hdescent : baseEnd_5137511 < baseStart_5137511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137512 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5137512 : Nat := 118140960795 + 5137512 * 2 ^ 59
def prefixEnd_5137512 : Nat := 4983230072969 + 3 ^ 40 * 5137512 * 2
def baseEnd_5137512 : Nat := 2638013024241608694373019

theorem tailTrace_5137512 : CollatzResearch.WordTrace tailWord_5137512 prefixEnd_5137512 2638013024241608694373019 := by
  unfold tailWord_5137512
  simp only [CollatzResearch.WordTrace]
  refine ⟨93690228281839458019979395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124920304375785944026639193 93690228281839458019979395)
  ·
    refine ⟨140535342422759187029969093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93690228281839458019979395 140535342422759187029969093)
    ·
      refine ⟨26350376704267347568119205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140535342422759187029969093 26350376704267347568119205)
      ·
        refine ⟨4940695632050127669022351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26350376704267347568119205 4940695632050127669022351)
        ·
          refine ⟨7411043448075191503533527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940695632050127669022351 7411043448075191503533527)
          ·
            refine ⟨11116565172112787255300291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411043448075191503533527 11116565172112787255300291)
            ·
              refine ⟨16674847758169180882950437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116565172112787255300291 16674847758169180882950437)
              ·
                refine ⟨3126533954656721415553207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16674847758169180882950437 3126533954656721415553207)
                ·
                  refine ⟨4689800931985082123329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126533954656721415553207 4689800931985082123329811)
                  ·
                    refine ⟨7034701397977623184994717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4689800931985082123329811 7034701397977623184994717)
                    ·
                      refine ⟨2638013024241608694373019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7034701397977623184994717 2638013024241608694373019)
                      ·
                        rfl

theorem cell23_5137512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5137512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137512 prefixEnd_5137512 := by exact prefixLift 5137512
  have htrace : WordTrace (prefixWord ++ tailWord_5137512) baseStart_5137512 baseEnd_5137512 := by
    simpa [prefixWord, tailWord_5137512, baseEnd_5137512] using wordTrace_append hprefix tailTrace_5137512
  have hstable : (prefixWord ++ tailWord_5137512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137512).length < 2 ^ (prefixWord ++ tailWord_5137512).sum := by decide
  have hdescent : baseEnd_5137512 < baseStart_5137512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137541 : List Nat := [1, 3, 1, 1, 6, 1, 3, 7]
def baseStart_5137541 : Nat := 118140960795 + 5137541 * 2 ^ 59
def prefixEnd_5137541 : Nat := 4983230072969 + 3 ^ 40 * 5137541 * 2
def baseEnd_5137541 : Nat := 97704737599281077070755

theorem tailTrace_5137541 : CollatzResearch.WordTrace tailWord_5137541 prefixEnd_5137541 97704737599281077070755 := by
  unfold tailWord_5137541
  simp only [CollatzResearch.WordTrace]
  refine ⟨187381514280573853992764477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124921009520382569328509651 187381514280573853992764477)
  ·
    refine ⟨70268067855215195247286679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187381514280573853992764477 70268067855215195247286679)
    ·
      refine ⟨105402101782822792870930019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70268067855215195247286679 105402101782822792870930019)
      ·
        refine ⟨158103152674234189306395029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105402101782822792870930019 158103152674234189306395029)
        ·
          refine ⟨7411085281604727623737267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158103152674234189306395029 7411085281604727623737267)
          ·
            refine ⟨11116627922407091435605901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411085281604727623737267 11116627922407091435605901)
            ·
              refine ⟨4168735470902659288352213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11116627922407091435605901 4168735470902659288352213)
              ·
                refine ⟨97704737599281077070755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4168735470902659288352213 97704737599281077070755)
                ·
                  rfl

theorem cell23_5137541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 7].length) (baseStart_5137541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137541 prefixEnd_5137541 := by exact prefixLift 5137541
  have htrace : WordTrace (prefixWord ++ tailWord_5137541) baseStart_5137541 baseEnd_5137541 := by
    simpa [prefixWord, tailWord_5137541, baseEnd_5137541] using wordTrace_append hprefix tailTrace_5137541
  have hstable : (prefixWord ++ tailWord_5137541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137541).length < 2 ^ (prefixWord ++ tailWord_5137541).sum := by decide
  have hdescent : baseEnd_5137541 < baseStart_5137541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137594 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_5137594 : Nat := 118140960795 + 5137594 * 2 ^ 59
def prefixEnd_5137594 : Nat := 4983230072969 + 3 ^ 40 * 5137594 * 2
def baseEnd_5137594 : Nat := 2638055129655277373547641

theorem tailTrace_5137594 : CollatzResearch.WordTrace tailWord_5137594 prefixEnd_5137594 2638055129655277373547641 := by
  unfold tailWord_5137594
  simp only [CollatzResearch.WordTrace]
  refine ⟨46845861837345461011110959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124922298232921229362962557 46845861837345461011110959)
  ·
    refine ⟨70268792756018191516666439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46845861837345461011110959 70268792756018191516666439)
    ·
      refine ⟨105403189134027287274999659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70268792756018191516666439 105403189134027287274999659)
      ·
        refine ⟨158104783701040930912499489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105403189134027287274999659 158104783701040930912499489)
        ·
          refine ⟨118578587775780698184374617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158104783701040930912499489 118578587775780698184374617)
          ·
            refine ⟨88933940831835523638280963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118578587775780698184374617 88933940831835523638280963)
            ·
              refine ⟨133400911247753285457421445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88933940831835523638280963 133400911247753285457421445)
              ·
                refine ⟨25012670858953741023266521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133400911247753285457421445 25012670858953741023266521)
                ·
                  refine ⟨18759503144215305767449891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25012670858953741023266521 18759503144215305767449891)
                  ·
                    refine ⟨28139254716322958651174837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18759503144215305767449891 28139254716322958651174837)
                    ·
                      refine ⟨2638055129655277373547641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28139254716322958651174837 2638055129655277373547641)
                      ·
                        rfl

theorem cell23_5137594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_5137594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137594 prefixEnd_5137594 := by exact prefixLift 5137594
  have htrace : WordTrace (prefixWord ++ tailWord_5137594) baseStart_5137594 baseEnd_5137594 := by
    simpa [prefixWord, tailWord_5137594, baseEnd_5137594] using wordTrace_append hprefix tailTrace_5137594
  have hstable : (prefixWord ++ tailWord_5137594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137594).length < 2 ^ (prefixWord ++ tailWord_5137594).sum := by decide
  have hdescent : baseEnd_5137594 < baseStart_5137594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137608 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_5137608 : Nat := 118140960795 + 5137608 * 2 ^ 59
def prefixEnd_5137608 : Nat := 4983230072969 + 3 ^ 40 * 5137608 * 2
def baseEnd_5137608 : Nat := 2638062318384440318772577

theorem tailTrace_5137608 : CollatzResearch.WordTrace tailWord_5137608 prefixEnd_5137608 2638062318384440318772577 := by
  unfold tailWord_5137608
  simp only [CollatzResearch.WordTrace]
  refine ⟨93691978985665562217726739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124922638647554082956968985 93691978985665562217726739)
  ·
    refine ⟨140537968478498343326590109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93691978985665562217726739 140537968478498343326590109)
    ·
      refine ⟨52701738179436878747471291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140537968478498343326590109 52701738179436878747471291)
      ·
        refine ⟨79052607269155318121206937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52701738179436878747471291 79052607269155318121206937)
        ·
          refine ⟨59289455451866488590905203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79052607269155318121206937 59289455451866488590905203)
          ·
            refine ⟨88934183177799732886357805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59289455451866488590905203 88934183177799732886357805)
            ·
              refine ⟨33350318691674899832384177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88934183177799732886357805 33350318691674899832384177)
              ·
                refine ⟨25012739018756174874288133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33350318691674899832384177 25012739018756174874288133)
                ·
                  refine ⟨4689888566016782788929025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25012739018756174874288133 4689888566016782788929025)
                  ·
                    refine ⟨3517416424512587091696769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689888566016782788929025 3517416424512587091696769)
                    ·
                      refine ⟨2638062318384440318772577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517416424512587091696769 2638062318384440318772577)
                      ·
                        rfl

theorem cell23_5137608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_5137608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137608 prefixEnd_5137608 := by exact prefixLift 5137608
  have htrace : WordTrace (prefixWord ++ tailWord_5137608) baseStart_5137608 baseEnd_5137608 := by
    simpa [prefixWord, tailWord_5137608, baseEnd_5137608] using wordTrace_append hprefix tailTrace_5137608
  have hstable : (prefixWord ++ tailWord_5137608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137608).length < 2 ^ (prefixWord ++ tailWord_5137608).sum := by decide
  have hdescent : baseEnd_5137608 < baseStart_5137608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137631 : List Nat := [1, 1, 2, 3, 2, 1, 2, 6, 5]
def baseStart_5137631 : Nat := 118140960795 + 5137631 * 2 ^ 59
def prefixEnd_5137631 : Nat := 4983230072969 + 3 ^ 40 * 5137631 * 2
def baseEnd_5137631 : Nat := 293119347604388192087219

theorem tailTrace_5137631 : CollatzResearch.WordTrace tailWord_5137631 prefixEnd_5137631 293119347604388192087219 := by
  unfold tailWord_5137631
  simp only [CollatzResearch.WordTrace]
  refine ⟨187384796850247799363540747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124923197900165199575693831 187384796850247799363540747)
  ·
    refine ⟨281077195275371699045311121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187384796850247799363540747 281077195275371699045311121)
    ·
      refine ⟨210807896456528774283983341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281077195275371699045311121 210807896456528774283983341)
      ·
        refine ⟨79052961171198290356493753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210807896456528774283983341 79052961171198290356493753)
        ·
          refine ⟨59289720878398717767370315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79052961171198290356493753 59289720878398717767370315)
          ·
            refine ⟨88934581317598076651055473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59289720878398717767370315 88934581317598076651055473)
            ·
              refine ⟨66700935988198557488291605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88934581317598076651055473 66700935988198557488291605)
              ·
                refine ⟨3126606374446807382263669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66700935988198557488291605 3126606374446807382263669)
                ·
                  refine ⟨293119347604388192087219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126606374446807382263669 293119347604388192087219)
                  ·
                    rfl

theorem cell23_5137631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 5].length) (baseStart_5137631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137631 prefixEnd_5137631 := by exact prefixLift 5137631
  have htrace : WordTrace (prefixWord ++ tailWord_5137631) baseStart_5137631 baseEnd_5137631 := by
    simpa [prefixWord, tailWord_5137631, baseEnd_5137631] using wordTrace_append hprefix tailTrace_5137631
  have hstable : (prefixWord ++ tailWord_5137631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137631).length < 2 ^ (prefixWord ++ tailWord_5137631).sum := by decide
  have hdescent : baseEnd_5137631 < baseStart_5137631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137642 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_5137642 : Nat := 118140960795 + 5137642 * 2 ^ 59
def prefixEnd_5137642 : Nat := 4983230072969 + 3 ^ 40 * 5137642 * 2
def baseEnd_5137642 : Nat := 2638079776726693185747421

theorem tailTrace_5137642 : CollatzResearch.WordTrace tailWord_5137642 prefixEnd_5137642 2638079776726693185747421 := by
  unfold tailWord_5137642
  simp only [CollatzResearch.WordTrace]
  refine ⟨46846299513301987060547795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124923465368805298828127453 46846299513301987060547795)
  ·
    refine ⟨70269449269952980590821693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46846299513301987060547795 70269449269952980590821693)
    ·
      refine ⟨26351043476232367721558135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70269449269952980590821693 26351043476232367721558135)
      ·
        refine ⟨39526565214348551582337203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26351043476232367721558135 39526565214348551582337203)
        ·
          refine ⟨59289847821522827373505805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39526565214348551582337203 59289847821522827373505805)
          ·
            refine ⟨22233692933071060265064677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59289847821522827373505805 22233692933071060265064677)
            ·
              refine ⟨4168817424950823799699627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22233692933071060265064677 4168817424950823799699627)
              ·
                refine ⟨6253226137426235699549441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4168817424950823799699627 6253226137426235699549441)
                ·
                  refine ⟨4689919603069676774662081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253226137426235699549441 4689919603069676774662081)
                  ·
                    refine ⟨3517439702302257580996561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4689919603069676774662081 3517439702302257580996561)
                    ·
                      refine ⟨2638079776726693185747421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517439702302257580996561 2638079776726693185747421)
                      ·
                        rfl

theorem cell23_5137642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_5137642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137642 prefixEnd_5137642 := by exact prefixLift 5137642
  have htrace : WordTrace (prefixWord ++ tailWord_5137642) baseStart_5137642 baseEnd_5137642 := by
    simpa [prefixWord, tailWord_5137642, baseEnd_5137642] using wordTrace_append hprefix tailTrace_5137642
  have hstable : (prefixWord ++ tailWord_5137642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137642).length < 2 ^ (prefixWord ++ tailWord_5137642).sum := by decide
  have hdescent : baseEnd_5137642 < baseStart_5137642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137681 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_5137681 : Nat := 118140960795 + 5137681 * 2 ^ 59
def prefixEnd_5137681 : Nat := 4983230072969 + 3 ^ 40 * 5137681 * 2
def baseEnd_5137681 : Nat := 2638099802472218533159741

theorem tailTrace_5137681 : CollatzResearch.WordTrace tailWord_5137681 prefixEnd_5137681 2638099802472218533159741 := by
  unfold tailWord_5137681
  simp only [CollatzResearch.WordTrace]
  refine ⟨187386620500066657902860897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124924413666711105268573931 187386620500066657902860897)
  ·
    refine ⟨140539965375049993427145673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187386620500066657902860897 140539965375049993427145673)
    ·
      refine ⟨105404974031287495070359255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140539965375049993427145673 105404974031287495070359255)
      ·
        refine ⟨158107461046931242605538883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105404974031287495070359255 158107461046931242605538883)
        ·
          refine ⟨237161191570396863908308325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158107461046931242605538883 237161191570396863908308325)
          ·
            refine ⟨44467723419449411982807811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237161191570396863908308325 44467723419449411982807811)
            ·
              refine ⟨66701585129174117974211717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44467723419449411982807811 66701585129174117974211717)
              ·
                refine ⟨12506547211720147120164697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66701585129174117974211717 12506547211720147120164697)
                ·
                  refine ⟨9379910408790110340123523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12506547211720147120164697 9379910408790110340123523)
                  ·
                    refine ⟨14069865613185165510185285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9379910408790110340123523 14069865613185165510185285)
                    ·
                      refine ⟨2638099802472218533159741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14069865613185165510185285 2638099802472218533159741)
                      ·
                        rfl

theorem cell23_5137681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_5137681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137681 prefixEnd_5137681 := by exact prefixLift 5137681
  have htrace : WordTrace (prefixWord ++ tailWord_5137681) baseStart_5137681 baseEnd_5137681 := by
    simpa [prefixWord, tailWord_5137681, baseEnd_5137681] using wordTrace_append hprefix tailTrace_5137681
  have hstable : (prefixWord ++ tailWord_5137681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137681).length < 2 ^ (prefixWord ++ tailWord_5137681).sum := by decide
  have hdescent : baseEnd_5137681 < baseStart_5137681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137682 : List Nat := [3, 2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_5137682 : Nat := 118140960795 + 5137682 * 2 ^ 59
def prefixEnd_5137682 : Nat := 4983230072969 + 3 ^ 40 * 5137682 * 2
def baseEnd_5137682 : Nat := 293122257328097003249693

theorem tailTrace_5137682 : CollatzResearch.WordTrace tailWord_5137682 prefixEnd_5137682 293122257328097003249693 := by
  unfold tailWord_5137682
  simp only [CollatzResearch.WordTrace]
  refine ⟨46846664243265758768411825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124924437982042023382431533 46846664243265758768411825)
  ·
    refine ⟨35134998182449319076308869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46846664243265758768411825 35134998182449319076308869)
    ·
      refine ⟨6587812159209247326807913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35134998182449319076308869 6587812159209247326807913)
      ·
        refine ⟨4940859119406935495105935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587812159209247326807913 4940859119406935495105935)
        ·
          refine ⟨7411288679110403242658903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940859119406935495105935 7411288679110403242658903)
          ·
            refine ⟨11116933018665604863988355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411288679110403242658903 11116933018665604863988355)
            ·
              refine ⟨16675399527998407295982533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11116933018665604863988355 16675399527998407295982533)
              ·
                refine ⟨3126637411499701367996725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16675399527998407295982533 3126637411499701367996725)
                ·
                  refine ⟨293122257328097003249693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126637411499701367996725 293122257328097003249693)
                  ·
                    rfl

theorem cell23_5137682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_5137682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137682 prefixEnd_5137682 := by exact prefixLift 5137682
  have htrace : WordTrace (prefixWord ++ tailWord_5137682) baseStart_5137682 baseEnd_5137682 := by
    simpa [prefixWord, tailWord_5137682, baseEnd_5137682] using wordTrace_append hprefix tailTrace_5137682
  have hstable : (prefixWord ++ tailWord_5137682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137682).length < 2 ^ (prefixWord ++ tailWord_5137682).sum := by decide
  have hdescent : baseEnd_5137682 < baseStart_5137682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137691 : List Nat := [1, 1, 1, 1, 1, 1, 5, 5, 3, 4]
def baseStart_5137691 : Nat := 118140960795 + 5137691 * 2 ^ 59
def prefixEnd_5137691 : Nat := 4983230072969 + 3 ^ 40 * 5137691 * 2
def baseEnd_5137691 : Nat := 879368312426254498011565

theorem tailTrace_5137691 : CollatzResearch.WordTrace tailWord_5137691 prefixEnd_5137691 879368312426254498011565 := by
  unfold tailWord_5137691
  simp only [CollatzResearch.WordTrace]
  refine ⟨187386985230030429610724927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124924656820020286407149951 187386985230030429610724927)
  ·
    refine ⟨281080477845045644416087391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187386985230030429610724927 281080477845045644416087391)
    ·
      refine ⟨421620716767568466624131087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281080477845045644416087391 421620716767568466624131087)
      ·
        refine ⟨632431075151352699936196631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421620716767568466624131087 632431075151352699936196631)
        ·
          refine ⟨948646612727029049904294947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632431075151352699936196631 948646612727029049904294947)
          ·
            refine ⟨1422969919090543574856442421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948646612727029049904294947 1422969919090543574856442421)
            ·
              refine ⟨133403429914738460142791477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1422969919090543574856442421 133403429914738460142791477)
              ·
                refine ⟨12506571554506730638386701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133403429914738460142791477 12506571554506730638386701)
                ·
                  refine ⟨4689964332940023989395013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12506571554506730638386701 4689964332940023989395013)
                  ·
                    refine ⟨879368312426254498011565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4689964332940023989395013 879368312426254498011565)
                    ·
                      rfl

theorem cell23_5137691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3, 4].length) (baseStart_5137691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137691 prefixEnd_5137691 := by exact prefixLift 5137691
  have htrace : WordTrace (prefixWord ++ tailWord_5137691) baseStart_5137691 baseEnd_5137691 := by
    simpa [prefixWord, tailWord_5137691, baseEnd_5137691] using wordTrace_append hprefix tailTrace_5137691
  have hstable : (prefixWord ++ tailWord_5137691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137691).length < 2 ^ (prefixWord ++ tailWord_5137691).sum := by decide
  have hdescent : baseEnd_5137691 < baseStart_5137691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137788 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 1, 1, 4]
def baseStart_5137788 : Nat := 118140960795 + 5137788 * 2 ^ 59
def prefixEnd_5137788 : Nat := 4983230072969 + 3 ^ 40 * 5137788 * 2
def baseEnd_5137788 : Nat := 2638154744902249614521749

theorem tailTrace_5137788 : CollatzResearch.WordTrace tailWord_5137788 prefixEnd_5137788 2638154744902249614521749 := by
  unfold tailWord_5137788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93695261555339507588503009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124927015407119343451337345 93695261555339507588503009)
  ·
    refine ⟨70271446166504630691377257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93695261555339507588503009 70271446166504630691377257)
    ·
      refine ⟨52703584624878473018532943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70271446166504630691377257 52703584624878473018532943)
      ·
        refine ⟨79055376937317709527799415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52703584624878473018532943 79055376937317709527799415)
        ·
          refine ⟨118583065405976564291699123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79055376937317709527799415 118583065405976564291699123)
          ·
            refine ⟨177874598108964846437548685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118583065405976564291699123 177874598108964846437548685)
            ·
              refine ⟨66702974290861817414080757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177874598108964846437548685 66702974290861817414080757)
              ·
                refine ⟨6253403839768295382570071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66702974290861817414080757 6253403839768295382570071)
                ·
                  refine ⟨9380105759652443073855107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6253403839768295382570071 9380105759652443073855107)
                  ·
                    refine ⟨14070158639478664610782661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9380105759652443073855107 14070158639478664610782661)
                    ·
                      refine ⟨2638154744902249614521749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14070158639478664610782661 2638154744902249614521749)
                      ·
                        rfl

theorem cell23_5137788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_5137788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137788 prefixEnd_5137788 := by exact prefixLift 5137788
  have htrace : WordTrace (prefixWord ++ tailWord_5137788) baseStart_5137788 baseEnd_5137788 := by
    simpa [prefixWord, tailWord_5137788, baseEnd_5137788] using wordTrace_append hprefix tailTrace_5137788
  have hstable : (prefixWord ++ tailWord_5137788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137788).length < 2 ^ (prefixWord ++ tailWord_5137788).sum := by decide
  have hdescent : baseEnd_5137788 < baseStart_5137788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137799 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 1, 1, 3]
def baseStart_5137799 : Nat := 118140960795 + 5137799 * 2 ^ 59
def prefixEnd_5137799 : Nat := 4983230072969 + 3 ^ 40 * 5137799 * 2
def baseEnd_5137799 : Nat := 2638160393189449071484199

theorem tailTrace_5137799 : CollatzResearch.WordTrace tailWord_5137799 prefixEnd_5137799 2638160393189449071484199 := by
  unfold tailWord_5137799
  simp only [CollatzResearch.WordTrace]
  refine ⟨187390924313639164055656451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124927282875759442703770967 187390924313639164055656451)
  ·
    refine ⟨281086386470458746083484677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187390924313639164055656451 281086386470458746083484677)
    ·
      refine ⟨52703697463211014890653377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281086386470458746083484677 52703697463211014890653377)
      ·
        refine ⟨39527773097408261167990033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52703697463211014890653377 39527773097408261167990033)
        ·
          refine ⟨29645829823056195875992525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39527773097408261167990033 29645829823056195875992525)
          ·
            refine ⟨11117186183646073453497197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29645829823056195875992525 11117186183646073453497197)
            ·
              refine ⟨4168944818867277545061449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11117186183646073453497197 4168944818867277545061449)
              ·
                refine ⟨3126708614150458158796087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4168944818867277545061449 3126708614150458158796087)
                ·
                  refine ⟨4690062921225687238194131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126708614150458158796087 4690062921225687238194131)
                  ·
                    refine ⟨7035094381838530857291197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690062921225687238194131 7035094381838530857291197)
                    ·
                      refine ⟨2638160393189449071484199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035094381838530857291197 2638160393189449071484199)
                      ·
                        rfl

theorem cell23_5137799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_5137799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137799 prefixEnd_5137799 := by exact prefixLift 5137799
  have htrace : WordTrace (prefixWord ++ tailWord_5137799) baseStart_5137799 baseEnd_5137799 := by
    simpa [prefixWord, tailWord_5137799, baseEnd_5137799] using wordTrace_append hprefix tailTrace_5137799
  have hstable : (prefixWord ++ tailWord_5137799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137799).length < 2 ^ (prefixWord ++ tailWord_5137799).sum := by decide
  have hdescent : baseEnd_5137799 < baseStart_5137799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137818 : List Nat := [3, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5137818 : Nat := 118140960795 + 5137818 * 2 ^ 59
def prefixEnd_5137818 : Nat := 4983230072969 + 3 ^ 40 * 5137818 * 2
def baseEnd_5137818 : Nat := 2638170149321884497146611

theorem tailTrace_5137818 : CollatzResearch.WordTrace tailWord_5137818 prefixEnd_5137818 2638170149321884497146611 := by
  unfold tailWord_5137818
  simp only [CollatzResearch.WordTrace]
  refine ⟨46847904325142582575149527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124927744867046886867065405 46847904325142582575149527)
  ·
    refine ⟨70271856487713873862724291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46847904325142582575149527 70271856487713873862724291)
    ·
      refine ⟨105407784731570810794086437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70271856487713873862724291 105407784731570810794086437)
      ·
        refine ⟨19763959637169527023891207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105407784731570810794086437 19763959637169527023891207)
        ·
          refine ⟨29645939455754290535836811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19763959637169527023891207 29645939455754290535836811)
          ·
            refine ⟨44468909183631435803755217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29645939455754290535836811 44468909183631435803755217)
            ·
              refine ⟨33351681887723576852816413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44468909183631435803755217 33351681887723576852816413)
              ·
                refine ⟨12506880707896341319806155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33351681887723576852816413 12506880707896341319806155)
                ·
                  refine ⟨18760321061844511979709233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12506880707896341319806155 18760321061844511979709233)
                  ·
                    refine ⟨14070240796383383984781925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18760321061844511979709233 14070240796383383984781925)
                    ·
                      refine ⟨2638170149321884497146611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14070240796383383984781925 2638170149321884497146611)
                      ·
                        rfl

theorem cell23_5137818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5137818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137818 prefixEnd_5137818 := by exact prefixLift 5137818
  have htrace : WordTrace (prefixWord ++ tailWord_5137818) baseStart_5137818 baseEnd_5137818 := by
    simpa [prefixWord, tailWord_5137818, baseEnd_5137818] using wordTrace_append hprefix tailTrace_5137818
  have hstable : (prefixWord ++ tailWord_5137818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137818).length < 2 ^ (prefixWord ++ tailWord_5137818).sum := by decide
  have hdescent : baseEnd_5137818 < baseStart_5137818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137822 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5137822 : Nat := 118140960795 + 5137822 * 2 ^ 59
def prefixEnd_5137822 : Nat := 4983230072969 + 3 ^ 40 * 5137822 * 2
def baseEnd_5137822 : Nat := 2638172203244502481496593

theorem tailTrace_5137822 : CollatzResearch.WordTrace tailWord_5137822 prefixEnd_5137822 2638172203244502481496593 := by
  unfold tailWord_5137822
  simp only [CollatzResearch.WordTrace]
  refine ⟨23423970399069479872967965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124927842128370559322495813 23423970399069479872967965)
  ·
    refine ⟨8783988899651054952362987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23423970399069479872967965 8783988899651054952362987)
    ·
      refine ⟨13175983349476582428544481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8783988899651054952362987 13175983349476582428544481)
      ·
        refine ⟨9881987512107436821408361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13175983349476582428544481 9881987512107436821408361)
        ·
          refine ⟨7411490634080577616056271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9881987512107436821408361 7411490634080577616056271)
          ·
            refine ⟨11117235951120866424084407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411490634080577616056271 11117235951120866424084407)
            ·
              refine ⟨16675853926681299636126611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117235951120866424084407 16675853926681299636126611)
              ·
                refine ⟨25013780890021949454189917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16675853926681299636126611 25013780890021949454189917)
                ·
                  refine ⟨9380167833758231045321219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25013780890021949454189917 9380167833758231045321219)
                  ·
                    refine ⟨14070251750637346567981829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9380167833758231045321219 14070251750637346567981829)
                    ·
                      refine ⟨2638172203244502481496593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14070251750637346567981829 2638172203244502481496593)
                      ·
                        rfl

theorem cell23_5137822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5137822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137822 prefixEnd_5137822 := by exact prefixLift 5137822
  have htrace : WordTrace (prefixWord ++ tailWord_5137822) baseStart_5137822 baseEnd_5137822 := by
    simpa [prefixWord, tailWord_5137822, baseEnd_5137822] using wordTrace_append hprefix tailTrace_5137822
  have hstable : (prefixWord ++ tailWord_5137822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137822).length < 2 ^ (prefixWord ++ tailWord_5137822).sum := by decide
  have hdescent : baseEnd_5137822 < baseStart_5137822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137871 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 8]
def baseStart_5137871 : Nat := 118140960795 + 5137871 * 2 ^ 59
def prefixEnd_5137871 : Nat := 4983230072969 + 3 ^ 40 * 5137871 * 2
def baseEnd_5137871 : Nat := 879399121265524263261289

theorem tailTrace_5137871 : CollatzResearch.WordTrace tailWord_5137871 prefixEnd_5137871 879399121265524263261289 := by
  unfold tailWord_5137871
  simp only [CollatzResearch.WordTrace]
  refine ⟨187393550369378320352277467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124929033579585546901518311 187393550369378320352277467)
  ·
    refine ⟨281090325554067480528416201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187393550369378320352277467 281090325554067480528416201)
    ·
      refine ⟨210817744165550610396312151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281090325554067480528416201 210817744165550610396312151)
      ·
        refine ⟨316226616248325915594468227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210817744165550610396312151 316226616248325915594468227)
        ·
          refine ⟨474339924372488873391702341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316226616248325915594468227 474339924372488873391702341)
          ·
            refine ⟨88938735819841663760944189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 474339924372488873391702341 88938735819841663760944189)
            ·
              refine ⟨33352025932440623910354071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88938735819841663760944189 33352025932440623910354071)
              ·
                refine ⟨50028038898660935865531107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33352025932440623910354071 50028038898660935865531107)
                ·
                  refine ⟨75042058347991403798296661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50028038898660935865531107 75042058347991403798296661)
                  ·
                    refine ⟨879399121265524263261289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75042058347991403798296661 879399121265524263261289)
                    ·
                      rfl

theorem cell23_5137871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 8].length) (baseStart_5137871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137871 prefixEnd_5137871 := by exact prefixLift 5137871
  have htrace : WordTrace (prefixWord ++ tailWord_5137871) baseStart_5137871 baseEnd_5137871 := by
    simpa [prefixWord, tailWord_5137871, baseEnd_5137871] using wordTrace_append hprefix tailTrace_5137871
  have hstable : (prefixWord ++ tailWord_5137871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137871).length < 2 ^ (prefixWord ++ tailWord_5137871).sum := by decide
  have hdescent : baseEnd_5137871 < baseStart_5137871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137911 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9]
def baseStart_5137911 : Nat := 118140960795 + 5137911 * 2 ^ 59
def prefixEnd_5137911 : Nat := 4983230072969 + 3 ^ 40 * 5137911 * 2
def baseEnd_5137911 : Nat := 2638217903022752633283683

theorem tailTrace_5137911 : CollatzResearch.WordTrace tailWord_5137911 prefixEnd_5137911 2638217903022752633283683 := by
  unfold tailWord_5137911
  simp only [CollatzResearch.WordTrace]
  refine ⟨187395009289233407183733587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124930006192822271455822391 187395009289233407183733587)
  ·
    refine ⟨281092513933850110775600381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187395009289233407183733587 281092513933850110775600381)
    ·
      refine ⟨105409692725193791540850143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281092513933850110775600381 105409692725193791540850143)
      ·
        refine ⟨158114539087790687311275215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105409692725193791540850143 158114539087790687311275215)
        ·
          refine ⟨237171808631686030966912823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158114539087790687311275215 237171808631686030966912823)
          ·
            refine ⟨355757712947529046450369235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237171808631686030966912823 355757712947529046450369235)
            ·
              refine ⟨533636569421293569675553853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355757712947529046450369235 533636569421293569675553853)
              ·
                refine ⟨200113713532985088628332695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533636569421293569675553853 200113713532985088628332695)
                ·
                  refine ⟨300170570299477632942499043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 200113713532985088628332695 300170570299477632942499043)
                  ·
                    refine ⟨450255855449216449413748565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300170570299477632942499043 450255855449216449413748565)
                    ·
                      refine ⟨2638217903022752633283683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 450255855449216449413748565 2638217903022752633283683)
                      ·
                        rfl

theorem cell23_5137911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_5137911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137911 prefixEnd_5137911 := by exact prefixLift 5137911
  have htrace : WordTrace (prefixWord ++ tailWord_5137911) baseStart_5137911 baseEnd_5137911 := by
    simpa [prefixWord, tailWord_5137911, baseEnd_5137911] using wordTrace_append hprefix tailTrace_5137911
  have hstable : (prefixWord ++ tailWord_5137911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137911).length < 2 ^ (prefixWord ++ tailWord_5137911).sum := by decide
  have hdescent : baseEnd_5137911 < baseStart_5137911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137912 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2]
def baseStart_5137912 : Nat := 118140960795 + 5137912 * 2 ^ 59
def prefixEnd_5137912 : Nat := 4983230072969 + 3 ^ 40 * 5137912 * 2
def baseEnd_5137912 : Nat := 2638218416503407129371179

theorem tailTrace_5137912 : CollatzResearch.WordTrace tailWord_5137912 prefixEnd_5137912 2638218416503407129371179 := by
  unfold tailWord_5137912
  simp only [CollatzResearch.WordTrace]
  refine ⟨93697522881114892177259995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124930030508153189569679993 93697522881114892177259995)
  ·
    refine ⟨140546284321672338265889993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93697522881114892177259995 140546284321672338265889993)
    ·
      refine ⟨105409713241254253699417495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140546284321672338265889993 105409713241254253699417495)
      ·
        refine ⟨158114569861881380549126243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105409713241254253699417495 158114569861881380549126243)
        ·
          refine ⟨237171854792822070823689365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158114569861881380549126243 237171854792822070823689365)
          ·
            refine ⟨11117430693413534569860439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 237171854792822070823689365 11117430693413534569860439)
            ·
              refine ⟨16676146040120301854790659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117430693413534569860439 16676146040120301854790659)
              ·
                refine ⟨25014219060180452782185989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16676146040120301854790659 25014219060180452782185989)
                ·
                  refine ⟨4690166073783834896659873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25014219060180452782185989 4690166073783834896659873)
                  ·
                    refine ⟨3517624555337876172494905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690166073783834896659873 3517624555337876172494905)
                    ·
                      refine ⟨2638218416503407129371179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517624555337876172494905 2638218416503407129371179)
                      ·
                        rfl

theorem cell23_5137912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 4, 2, 2].length) (baseStart_5137912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137912 prefixEnd_5137912 := by exact prefixLift 5137912
  have htrace : WordTrace (prefixWord ++ tailWord_5137912) baseStart_5137912 baseEnd_5137912 := by
    simpa [prefixWord, tailWord_5137912, baseEnd_5137912] using wordTrace_append hprefix tailTrace_5137912
  have hstable : (prefixWord ++ tailWord_5137912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137912).length < 2 ^ (prefixWord ++ tailWord_5137912).sum := by decide
  have hdescent : baseEnd_5137912 < baseStart_5137912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137929 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 2, 2, 2]
def baseStart_5137929 : Nat := 118140960795 + 5137929 * 2 ^ 59
def prefixEnd_5137929 : Nat := 4983230072969 + 3 ^ 40 * 5137929 * 2
def baseEnd_5137929 : Nat := 2638227145674533562858601

theorem tailTrace_5137929 : CollatzResearch.WordTrace tailWord_5137929 prefixEnd_5137929 2638227145674533562858601 := by
  unfold tailWord_5137929
  simp only [CollatzResearch.WordTrace]
  refine ⟨187395665803168196257888841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124930443868778797505259227 187395665803168196257888841)
  ·
    refine ⟨140546749352376147193416631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187395665803168196257888841 140546749352376147193416631)
    ·
      refine ⟨210820124028564220790124947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140546749352376147193416631 210820124028564220790124947)
      ·
        refine ⟨316230186042846331185187421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210820124028564220790124947 316230186042846331185187421)
        ·
          refine ⟨118586319766067374194445283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316230186042846331185187421 118586319766067374194445283)
          ·
            refine ⟨177879479649101061291667925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118586319766067374194445283 177879479649101061291667925)
            ·
              refine ⟨4169050304275806124023467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 177879479649101061291667925 4169050304275806124023467)
              ·
                refine ⟨6253575456413709186035201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169050304275806124023467 6253575456413709186035201)
                ·
                  refine ⟨4690181592310281889526401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253575456413709186035201 4690181592310281889526401)
                  ·
                    refine ⟨3517636194232711417144801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690181592310281889526401 3517636194232711417144801)
                    ·
                      refine ⟨2638227145674533562858601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517636194232711417144801 2638227145674533562858601)
                      ·
                        rfl

theorem cell23_5137929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 2, 2, 2].length) (baseStart_5137929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137929 prefixEnd_5137929 := by exact prefixLift 5137929
  have htrace : WordTrace (prefixWord ++ tailWord_5137929) baseStart_5137929 baseEnd_5137929 := by
    simpa [prefixWord, tailWord_5137929, baseEnd_5137929] using wordTrace_append hprefix tailTrace_5137929
  have hstable : (prefixWord ++ tailWord_5137929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137929).length < 2 ^ (prefixWord ++ tailWord_5137929).sum := by decide
  have hdescent : baseEnd_5137929 < baseStart_5137929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137933 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_5137933 : Nat := 118140960795 + 5137933 * 2 ^ 59
def prefixEnd_5137933 : Nat := 4983230072969 + 3 ^ 40 * 5137933 * 2
def baseEnd_5137933 : Nat := 2638229199597151547208583

theorem tailTrace_5137933 : CollatzResearch.WordTrace tailWord_5137933 prefixEnd_5137933 2638229199597151547208583 := by
  unfold tailWord_5137933
  simp only [CollatzResearch.WordTrace]
  refine ⟨187395811695153704941034453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124930541130102469960689635 187395811695153704941034453)
  ·
    refine ⟨4392089336605164959555495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 187395811695153704941034453 4392089336605164959555495)
    ·
      refine ⟨6588134004907747439333243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4392089336605164959555495 6588134004907747439333243)
      ·
        refine ⟨9882201007361621158999865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6588134004907747439333243 9882201007361621158999865)
        ·
          refine ⟨7411650755521215869249899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9882201007361621158999865 7411650755521215869249899)
          ·
            refine ⟨11117476133281823803874849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7411650755521215869249899 11117476133281823803874849)
            ·
              refine ⟨8338107099961367852906137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11117476133281823803874849 8338107099961367852906137)
              ·
                refine ⟨6253580324971025889679603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8338107099961367852906137 6253580324971025889679603)
                ·
                  refine ⟨9380370487456538834519405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6253580324971025889679603 9380370487456538834519405)
                  ·
                    refine ⟨3517638932796202062944777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9380370487456538834519405 3517638932796202062944777)
                    ·
                      refine ⟨2638229199597151547208583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517638932796202062944777 2638229199597151547208583)
                      ·
                        rfl

theorem cell23_5137933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_5137933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137933 prefixEnd_5137933 := by exact prefixLift 5137933
  have htrace : WordTrace (prefixWord ++ tailWord_5137933) baseStart_5137933 baseEnd_5137933 := by
    simpa [prefixWord, tailWord_5137933, baseEnd_5137933] using wordTrace_append hprefix tailTrace_5137933
  have hstable : (prefixWord ++ tailWord_5137933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137933).length < 2 ^ (prefixWord ++ tailWord_5137933).sum := by decide
  have hdescent : baseEnd_5137933 < baseStart_5137933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137948 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_5137948 : Nat := 118140960795 + 5137948 * 2 ^ 59
def prefixEnd_5137948 : Nat := 4983230072969 + 3 ^ 40 * 5137948 * 2
def baseEnd_5137948 : Nat := 879412300602322996173671

theorem tailTrace_5137948 : CollatzResearch.WordTrace tailWord_5137948 prefixEnd_5137948 879412300602322996173671 := by
  unfold tailWord_5137948
  simp only [CollatzResearch.WordTrace]
  refine ⟨93698179395049681251415249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124930905860066241668553665 93698179395049681251415249)
  ·
    refine ⟨70273634546287260938561437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93698179395049681251415249 70273634546287260938561437)
    ·
      refine ⟨26352612954857722851960539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70273634546287260938561437 26352612954857722851960539)
      ·
        refine ⟨39528919432286584277940809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26352612954857722851960539 39528919432286584277940809)
        ·
          refine ⟨29646689574214938208455607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39528919432286584277940809 29646689574214938208455607)
          ·
            refine ⟨44470034361322407312683411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29646689574214938208455607 44470034361322407312683411)
            ·
              refine ⟨66705051541983610969025117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44470034361322407312683411 66705051541983610969025117)
              ·
                refine ⟨25014394328243854113384419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66705051541983610969025117 25014394328243854113384419)
                ·
                  refine ⟨37521591492365781170076629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25014394328243854113384419 37521591492365781170076629)
                  ·
                    refine ⟨879412300602322996173671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37521591492365781170076629 879412300602322996173671)
                    ·
                      rfl

theorem cell23_5137948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_5137948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137948 prefixEnd_5137948 := by exact prefixLift 5137948
  have htrace : WordTrace (prefixWord ++ tailWord_5137948) baseStart_5137948 baseEnd_5137948 := by
    simpa [prefixWord, tailWord_5137948, baseEnd_5137948] using wordTrace_append hprefix tailTrace_5137948
  have hstable : (prefixWord ++ tailWord_5137948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137948).length < 2 ^ (prefixWord ++ tailWord_5137948).sum := by decide
  have hdescent : baseEnd_5137948 < baseStart_5137948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137952 : List Nat := [2, 1, 1, 6, 1, 1, 3, 3, 5]
def baseStart_5137952 : Nat := 118140960795 + 5137952 * 2 ^ 59
def prefixEnd_5137952 : Nat := 4983230072969 + 3 ^ 40 * 5137952 * 2
def baseEnd_5137952 : Nat := 293137661747731885874555

theorem tailTrace_5137952 : CollatzResearch.WordTrace tailWord_5137952 prefixEnd_5137952 293137661747731885874555 := by
  unfold tailWord_5137952
  simp only [CollatzResearch.WordTrace]
  refine ⟨93698252341042435592988055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124931003121389914123984073 93698252341042435592988055)
  ·
    refine ⟨140547378511563653389482083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93698252341042435592988055 140547378511563653389482083)
    ·
      refine ⟨210821067767345480084223125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140547378511563653389482083 210821067767345480084223125)
      ·
        refine ⟨9882237551594319378947959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 210821067767345480084223125 9882237551594319378947959)
        ·
          refine ⟨14823356327391479068421939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882237551594319378947959 14823356327391479068421939)
          ·
            refine ⟨22235034491087218602632909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14823356327391479068421939 22235034491087218602632909)
            ·
              refine ⟨8338137934157706975987341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22235034491087218602632909 8338137934157706975987341)
              ·
                refine ⟨3126801725309140115995253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8338137934157706975987341 3126801725309140115995253)
                ·
                  refine ⟨293137661747731885874555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3126801725309140115995253 293137661747731885874555)
                  ·
                    rfl

theorem cell23_5137952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 5].length) (baseStart_5137952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137952 prefixEnd_5137952 := by exact prefixLift 5137952
  have htrace : WordTrace (prefixWord ++ tailWord_5137952) baseStart_5137952 baseEnd_5137952 := by
    simpa [prefixWord, tailWord_5137952, baseEnd_5137952] using wordTrace_append hprefix tailTrace_5137952
  have hstable : (prefixWord ++ tailWord_5137952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137952).length < 2 ^ (prefixWord ++ tailWord_5137952).sum := by decide
  have hdescent : baseEnd_5137952 < baseStart_5137952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137985 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_5137985 : Nat := 118140960795 + 5137985 * 2 ^ 59
def prefixEnd_5137985 : Nat := 4983230072969 + 3 ^ 40 * 5137985 * 2
def baseEnd_5137985 : Nat := 2638255900591185343758343

theorem tailTrace_5137985 : CollatzResearch.WordTrace tailWord_5137985 prefixEnd_5137985 2638255900591185343758343 := by
  unfold tailWord_5137985
  simp only [CollatzResearch.WordTrace]
  refine ⟨187397708290965317821927409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124931805527310211881284939 187397708290965317821927409)
  ·
    refine ⟨140548281218223988366445557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187397708290965317821927409 140548281218223988366445557)
    ·
      refine ⟨13176401364208498909354271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140548281218223988366445557 13176401364208498909354271)
      ·
        refine ⟨19764602046312748364031407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13176401364208498909354271 19764602046312748364031407)
        ·
          refine ⟨29646903069469122546047111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19764602046312748364031407 29646903069469122546047111)
          ·
            refine ⟨44470354604203683819070667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29646903069469122546047111 44470354604203683819070667)
            ·
              refine ⟨66705531906305525728606001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44470354604203683819070667 66705531906305525728606001)
              ·
                refine ⟨50029148929729144296454501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66705531906305525728606001 50029148929729144296454501)
                ·
                  refine ⟨9380465424324214555585219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50029148929729144296454501 9380465424324214555585219)
                  ·
                    refine ⟨14070698136486321833377829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9380465424324214555585219 14070698136486321833377829)
                    ·
                      refine ⟨2638255900591185343758343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14070698136486321833377829 2638255900591185343758343)
                      ·
                        rfl

theorem cell23_5137985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_5137985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137985 prefixEnd_5137985 := by exact prefixLift 5137985
  have htrace : WordTrace (prefixWord ++ tailWord_5137985) baseStart_5137985 baseEnd_5137985 := by
    simpa [prefixWord, tailWord_5137985, baseEnd_5137985] using wordTrace_append hprefix tailTrace_5137985
  have hstable : (prefixWord ++ tailWord_5137985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137985).length < 2 ^ (prefixWord ++ tailWord_5137985).sum := by decide
  have hdescent : baseEnd_5137985 < baseStart_5137985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5137998 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_5137998 : Nat := 118140960795 + 5137998 * 2 ^ 59
def prefixEnd_5137998 : Nat := 4983230072969 + 3 ^ 40 * 5137998 * 2
def baseEnd_5137998 : Nat := 2638262575839693792895783

theorem tailTrace_5137998 : CollatzResearch.WordTrace tailWord_5137998 prefixEnd_5137998 2638262575839693792895783 := by
  unfold tailWord_5137998
  simp only [CollatzResearch.WordTrace]
  refine ⟨23424772804989777630268831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124932121626612147361433765 23424772804989777630268831)
  ·
    refine ⟨35137159207484666445403247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23424772804989777630268831 35137159207484666445403247)
    ·
      refine ⟨52705738811226999668104871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35137159207484666445403247 52705738811226999668104871)
      ·
        refine ⟨79058608216840499502157307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52705738811226999668104871 79058608216840499502157307)
        ·
          refine ⟨118587912325260749253235961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79058608216840499502157307 118587912325260749253235961)
          ·
            refine ⟨88940934243945561939926971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118587912325260749253235961 88940934243945561939926971)
            ·
              refine ⟨133411401365918342909890457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88940934243945561939926971 133411401365918342909890457)
              ·
                refine ⟨100058551024438757182417843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133411401365918342909890457 100058551024438757182417843)
                ·
                  refine ⟨150087826536658135773626765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100058551024438757182417843 150087826536658135773626765)
                  ·
                    refine ⟨56282934951246800915110037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 150087826536658135773626765 56282934951246800915110037)
                    ·
                      refine ⟨2638262575839693792895783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56282934951246800915110037 2638262575839693792895783)
                      ·
                        rfl

theorem cell23_5137998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_5137998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5137998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5137998 prefixEnd_5137998 := by exact prefixLift 5137998
  have htrace : WordTrace (prefixWord ++ tailWord_5137998) baseStart_5137998 baseEnd_5137998 := by
    simpa [prefixWord, tailWord_5137998, baseEnd_5137998] using wordTrace_append hprefix tailTrace_5137998
  have hstable : (prefixWord ++ tailWord_5137998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5137998).length < 2 ^ (prefixWord ++ tailWord_5137998).sum := by decide
  have hdescent : baseEnd_5137998 < baseStart_5137998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5137998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138002 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_5138002 : Nat := 118140960795 + 5138002 * 2 ^ 59
def prefixEnd_5138002 : Nat := 4983230072969 + 3 ^ 40 * 5138002 * 2
def baseEnd_5138002 : Nat := 2638264629762311777245765

theorem tailTrace_5138002 : CollatzResearch.WordTrace tailWord_5138002 prefixEnd_5138002 2638264629762311777245765 := by
  unfold tailWord_5138002
  simp only [CollatzResearch.WordTrace]
  refine ⟨46849582082975932431324065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124932218887935819816864173 46849582082975932431324065)
  ·
    refine ⟨35137186562231949323493049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46849582082975932431324065 35137186562231949323493049)
    ·
      refine ⟨26352889921673961992619787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35137186562231949323493049 26352889921673961992619787)
      ·
        refine ⟨39529334882510942988929681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26352889921673961992619787 39529334882510942988929681)
        ·
          refine ⟨29647001161883207241697261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39529334882510942988929681 29647001161883207241697261)
          ·
            refine ⟨11117625435706202715636473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29647001161883207241697261 11117625435706202715636473)
            ·
              refine ⟨8338219076779652036727355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11117625435706202715636473 8338219076779652036727355)
              ·
                refine ⟨12507328615169478055091033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338219076779652036727355 12507328615169478055091033)
                ·
                  refine ⟨9380496461377108541318275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12507328615169478055091033 9380496461377108541318275)
                  ·
                    refine ⟨14070744692065662811977413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9380496461377108541318275 14070744692065662811977413)
                    ·
                      refine ⟨2638264629762311777245765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14070744692065662811977413 2638264629762311777245765)
                      ·
                        rfl

theorem cell23_5138002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_5138002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138002 prefixEnd_5138002 := by exact prefixLift 5138002
  have htrace : WordTrace (prefixWord ++ tailWord_5138002) baseStart_5138002 baseEnd_5138002 := by
    simpa [prefixWord, tailWord_5138002, baseEnd_5138002] using wordTrace_append hprefix tailTrace_5138002
  have hstable : (prefixWord ++ tailWord_5138002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138002).length < 2 ^ (prefixWord ++ tailWord_5138002).sum := by decide
  have hdescent : baseEnd_5138002 < baseStart_5138002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138028 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_5138028 : Nat := 118140960795 + 5138028 * 2 ^ 59
def prefixEnd_5138028 : Nat := 4983230072969 + 3 ^ 40 * 5138028 * 2
def baseEnd_5138028 : Nat := 2638277980259328675520645

theorem tailTrace_5138028 : CollatzResearch.WordTrace tailWord_5138028 prefixEnd_5138028 2638277980259328675520645 := by
  unfold tailWord_5138028
  simp only [CollatzResearch.WordTrace]
  refine ⟨93699638314904768082871369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124932851086539690777161825 93699638314904768082871369)
  ·
    refine ⟨70274728736178576062153527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93699638314904768082871369 70274728736178576062153527)
    ·
      refine ⟨105412093104267864093230291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70274728736178576062153527 105412093104267864093230291)
      ·
        refine ⟨158118139656401796139845437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105412093104267864093230291 158118139656401796139845437)
        ·
          refine ⟨59294302371150673552442039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158118139656401796139845437 59294302371150673552442039)
          ·
            refine ⟨88941453556726010328663059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59294302371150673552442039 88941453556726010328663059)
            ·
              refine ⟨133412180335089015492994589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88941453556726010328663059 133412180335089015492994589)
              ·
                refine ⟨50029567625658380809872971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133412180335089015492994589 50029567625658380809872971)
                ·
                  refine ⟨75044351438487571214809457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50029567625658380809872971 75044351438487571214809457)
                  ·
                    refine ⟨56283263578865678411107093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75044351438487571214809457 56283263578865678411107093)
                    ·
                      refine ⟨2638277980259328675520645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56283263578865678411107093 2638277980259328675520645)
                      ·
                        rfl

theorem cell23_5138028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_5138028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138028 prefixEnd_5138028 := by exact prefixLift 5138028
  have htrace : WordTrace (prefixWord ++ tailWord_5138028) baseStart_5138028 baseEnd_5138028 := by
    simpa [prefixWord, tailWord_5138028, baseEnd_5138028] using wordTrace_append hprefix tailTrace_5138028
  have hstable : (prefixWord ++ tailWord_5138028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138028).length < 2 ^ (prefixWord ++ tailWord_5138028).sum := by decide
  have hdescent : baseEnd_5138028 < baseStart_5138028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138048 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_5138048 : Nat := 118140960795 + 5138048 * 2 ^ 59
def prefixEnd_5138048 : Nat := 4983230072969 + 3 ^ 40 * 5138048 * 2
def baseEnd_5138048 : Nat := 2638288249872418597270553

theorem tailTrace_5138048 : CollatzResearch.WordTrace tailWord_5138048 prefixEnd_5138048 2638288249872418597270553 := by
  unfold tailWord_5138048
  simp only [CollatzResearch.WordTrace]
  refine ⟨93700003044868539790735399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124933337393158053054313865 93700003044868539790735399)
  ·
    refine ⟨140550004567302809686103099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93700003044868539790735399 140550004567302809686103099)
    ·
      refine ⟨210825006850954214529154649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140550004567302809686103099 210825006850954214529154649)
      ·
        refine ⟨158118755138215660896865987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210825006850954214529154649 158118755138215660896865987)
        ·
          refine ⟨237178132707323491345298981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158118755138215660896865987 237178132707323491345298981)
          ·
            refine ⟨44470899882623154627243559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237178132707323491345298981 44470899882623154627243559)
            ·
              refine ⟨66706349823934731940865339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44470899882623154627243559 66706349823934731940865339)
              ·
                refine ⟨100059524735902097911298009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66706349823934731940865339 100059524735902097911298009)
                ·
                  refine ⟨75044643551926573433473507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100059524735902097911298009 75044643551926573433473507)
                  ·
                    refine ⟨112566965327889860150210261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75044643551926573433473507 112566965327889860150210261)
                    ·
                      refine ⟨2638288249872418597270553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112566965327889860150210261 2638288249872418597270553)
                      ·
                        rfl

theorem cell23_5138048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_5138048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138048 prefixEnd_5138048 := by exact prefixLift 5138048
  have htrace : WordTrace (prefixWord ++ tailWord_5138048) baseStart_5138048 baseEnd_5138048 := by
    simpa [prefixWord, tailWord_5138048, baseEnd_5138048] using wordTrace_append hprefix tailTrace_5138048
  have hstable : (prefixWord ++ tailWord_5138048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138048).length < 2 ^ (prefixWord ++ tailWord_5138048).sum := by decide
  have hdescent : baseEnd_5138048 < baseStart_5138048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138055 : List Nat := [1, 1, 4, 2, 1, 3, 2, 1, 3, 5]
def baseStart_5138055 : Nat := 118140960795 + 5138055 * 2 ^ 59
def prefixEnd_5138055 : Nat := 4983230072969 + 3 ^ 40 * 5138055 * 2
def baseEnd_5138055 : Nat := 879430614745666689961007

theorem tailTrace_5138055 : CollatzResearch.WordTrace tailWord_5138055 prefixEnd_5138055 879430614745666689961007 := by
  unfold tailWord_5138055
  simp only [CollatzResearch.WordTrace]
  refine ⟨187400261400711719776975619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124933507600474479851317079 187400261400711719776975619)
  ·
    refine ⟨281100392101067579665463429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187400261400711719776975619 281100392101067579665463429)
    ·
      refine ⟨52706323518950171187274393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281100392101067579665463429 52706323518950171187274393)
      ·
        refine ⟨39529742639212628390455795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52706323518950171187274393 39529742639212628390455795)
        ·
          refine ⟨59294613958818942585683693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39529742639212628390455795 59294613958818942585683693)
          ·
            refine ⟨22235480234557103469631385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59294613958818942585683693 22235480234557103469631385)
            ·
              refine ⟨16676610175917827602223539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22235480234557103469631385 16676610175917827602223539)
              ·
                refine ⟨25014915263876741403335309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16676610175917827602223539 25014915263876741403335309)
                ·
                  refine ⟨9380593223953778026250741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25014915263876741403335309 9380593223953778026250741)
                  ·
                    refine ⟨879430614745666689961007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9380593223953778026250741 879430614745666689961007)
                    ·
                      rfl

theorem cell23_5138055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_5138055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138055 prefixEnd_5138055 := by exact prefixLift 5138055
  have htrace : WordTrace (prefixWord ++ tailWord_5138055) baseStart_5138055 baseEnd_5138055 := by
    simpa [prefixWord, tailWord_5138055, baseEnd_5138055] using wordTrace_append hprefix tailTrace_5138055
  have hstable : (prefixWord ++ tailWord_5138055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138055).length < 2 ^ (prefixWord ++ tailWord_5138055).sum := by decide
  have hdescent : baseEnd_5138055 < baseStart_5138055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138056 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_5138056 : Nat := 118140960795 + 5138056 * 2 ^ 59
def prefixEnd_5138056 : Nat := 4983230072969 + 3 ^ 40 * 5138056 * 2
def baseEnd_5138056 : Nat := 2638292357717654565970517

theorem tailTrace_5138056 : CollatzResearch.WordTrace tailWord_5138056 prefixEnd_5138056 2638292357717654565970517 := by
  unfold tailWord_5138056
  simp only [CollatzResearch.WordTrace]
  refine ⟨93700148936854048473881011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124933531915805397965174681 93700148936854048473881011)
  ·
    refine ⟨140550223405281072710821517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93700148936854048473881011 140550223405281072710821517)
    ·
      refine ⟨52706333776980402266558069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140550223405281072710821517 52706333776980402266558069)
      ·
        refine ⟨4941218791591912712489819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52706333776980402266558069 4941218791591912712489819)
        ·
          refine ⟨7411828187387869068734729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4941218791591912712489819 7411828187387869068734729)
          ·
            refine ⟨5558871140540901801551047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7411828187387869068734729 5558871140540901801551047)
            ·
              refine ⟨8338306710811352702326571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5558871140540901801551047 8338306710811352702326571)
              ·
                refine ⟨12507460066217029053489857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338306710811352702326571 12507460066217029053489857)
                ·
                  refine ⟨9380595049662771790117393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12507460066217029053489857 9380595049662771790117393)
                  ·
                    refine ⟨7035446287247078842588045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9380595049662771790117393 7035446287247078842588045)
                    ·
                      refine ⟨2638292357717654565970517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035446287247078842588045 2638292357717654565970517)
                      ·
                        rfl

theorem cell23_5138056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_5138056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138056 prefixEnd_5138056 := by exact prefixLift 5138056
  have htrace : WordTrace (prefixWord ++ tailWord_5138056) baseStart_5138056 baseEnd_5138056 := by
    simpa [prefixWord, tailWord_5138056, baseEnd_5138056] using wordTrace_append hprefix tailTrace_5138056
  have hstable : (prefixWord ++ tailWord_5138056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138056).length < 2 ^ (prefixWord ++ tailWord_5138056).sum := by decide
  have hdescent : baseEnd_5138056 < baseStart_5138056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138072 : List Nat := [2, 1, 2, 4, 1, 3, 1, 3, 1, 5]
def baseStart_5138072 : Nat := 118140960795 + 5138072 * 2 ^ 59
def prefixEnd_5138072 : Nat := 4983230072969 + 3 ^ 40 * 5138072 * 2
def baseEnd_5138072 : Nat := 879433524469375501123481

theorem tailTrace_5138072 : CollatzResearch.WordTrace tailWord_5138072 prefixEnd_5138072 879433524469375501123481 := by
  unfold tailWord_5138072
  simp only [CollatzResearch.WordTrace]
  refine ⟨93700440720825065840172235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124933920961100087786896313 93700440720825065840172235)
  ·
    refine ⟨140550661081237598760258353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93700440720825065840172235 140550661081237598760258353)
    ·
      refine ⟨105412995810928199070193765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140550661081237598760258353 105412995810928199070193765)
      ·
        refine ⟨19764936714549037325661331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105412995810928199070193765 19764936714549037325661331)
        ·
          refine ⟨29647405071823555988491997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19764936714549037325661331 29647405071823555988491997)
          ·
            refine ⟨11117776901933833495684499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29647405071823555988491997 11117776901933833495684499)
            ·
              refine ⟨16676665352900750243526749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11117776901933833495684499 16676665352900750243526749)
              ·
                refine ⟨6253749507337781341322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16676665352900750243526749 6253749507337781341322531)
                ·
                  refine ⟨9380624261006672011983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6253749507337781341322531 9380624261006672011983797)
                  ·
                    refine ⟨879433524469375501123481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9380624261006672011983797 879433524469375501123481)
                    ·
                      rfl

theorem cell23_5138072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_5138072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138072 prefixEnd_5138072 := by exact prefixLift 5138072
  have htrace : WordTrace (prefixWord ++ tailWord_5138072) baseStart_5138072 baseEnd_5138072 := by
    simpa [prefixWord, tailWord_5138072, baseEnd_5138072] using wordTrace_append hprefix tailTrace_5138072
  have hstable : (prefixWord ++ tailWord_5138072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138072).length < 2 ^ (prefixWord ++ tailWord_5138072).sum := by decide
  have hdescent : baseEnd_5138072 < baseStart_5138072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138095 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5]
def baseStart_5138095 : Nat := 118140960795 + 5138095 * 2 ^ 59
def prefixEnd_5138095 : Nat := 4983230072969 + 3 ^ 40 * 5138095 * 2
def baseEnd_5138095 : Nat := 2638312383463179913382837

theorem tailTrace_5138095 : CollatzResearch.WordTrace tailWord_5138095 prefixEnd_5138095 2638312383463179913382837 := by
  unfold tailWord_5138095
  simp only [CollatzResearch.WordTrace]
  refine ⟨187401720320566806608431739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124934480213711204405621159 187401720320566806608431739)
  ·
    refine ⟨281102580480850209912647609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187401720320566806608431739 281102580480850209912647609)
    ·
      refine ⟨210826935360637657434485707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281102580480850209912647609 210826935360637657434485707)
      ·
        refine ⟨316240403040956486151728561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210826935360637657434485707 316240403040956486151728561)
        ·
          refine ⟨237180302280717364613796421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316240403040956486151728561 237180302280717364613796421)
          ·
            refine ⟨44471306677634505865086829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237180302280717364613796421 44471306677634505865086829)
            ·
              refine ⟨16676740004112939699407561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44471306677634505865086829 16676740004112939699407561)
              ·
                refine ⟨12507555003084704774555671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16676740004112939699407561 12507555003084704774555671)
                ·
                  refine ⟨18761332504627057161833507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12507555003084704774555671 18761332504627057161833507)
                  ·
                    refine ⟨28141998756940585742750261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18761332504627057161833507 28141998756940585742750261)
                    ·
                      refine ⟨2638312383463179913382837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28141998756940585742750261 2638312383463179913382837)
                      ·
                        rfl

theorem cell23_5138095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_5138095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138095 prefixEnd_5138095 := by exact prefixLift 5138095
  have htrace : WordTrace (prefixWord ++ tailWord_5138095) baseStart_5138095 baseEnd_5138095 := by
    simpa [prefixWord, tailWord_5138095, baseEnd_5138095] using wordTrace_append hprefix tailTrace_5138095
  have hstable : (prefixWord ++ tailWord_5138095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138095).length < 2 ^ (prefixWord ++ tailWord_5138095).sum := by decide
  have hdescent : baseEnd_5138095 < baseStart_5138095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138109 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_5138109 : Nat := 118140960795 + 5138109 * 2 ^ 59
def prefixEnd_5138109 : Nat := 4983230072969 + 3 ^ 40 * 5138109 * 2
def baseEnd_5138109 : Nat := 2638319572192342858607773

theorem tailTrace_5138109 : CollatzResearch.WordTrace tailWord_5138109 prefixEnd_5138109 2638319572192342858607773 := by
  unfold tailWord_5138109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187402230942516086999441381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124934820628344057999627587 187402230942516086999441381)
  ·
    refine ⟨35137918301721766312395259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187402230942516086999441381 35137918301721766312395259)
    ·
      refine ⟨52706877452582649468592889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35137918301721766312395259 52706877452582649468592889)
      ·
        refine ⟨39530158089436987101444667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52706877452582649468592889 39530158089436987101444667)
        ·
          refine ⟨59295237134155480652167001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39530158089436987101444667 59295237134155480652167001)
          ·
            refine ⟨44471427850616610489125251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59295237134155480652167001 44471427850616610489125251)
            ·
              refine ⟨66707141775924915733687877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44471427850616610489125251 66707141775924915733687877)
              ·
                refine ⟨12507589082985921700066477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66707141775924915733687877 12507589082985921700066477)
                ·
                  refine ⟨4690345906119720637524929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12507589082985921700066477 4690345906119720637524929)
                  ·
                    refine ⟨3517759429589790478143697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690345906119720637524929 3517759429589790478143697)
                    ·
                      refine ⟨2638319572192342858607773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517759429589790478143697 2638319572192342858607773)
                      ·
                        rfl

theorem cell23_5138109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_5138109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138109 prefixEnd_5138109 := by exact prefixLift 5138109
  have htrace : WordTrace (prefixWord ++ tailWord_5138109) baseStart_5138109 baseEnd_5138109 := by
    simpa [prefixWord, tailWord_5138109, baseEnd_5138109] using wordTrace_append hprefix tailTrace_5138109
  have hstable : (prefixWord ++ tailWord_5138109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138109).length < 2 ^ (prefixWord ++ tailWord_5138109).sum := by decide
  have hdescent : baseEnd_5138109 < baseStart_5138109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138132 : List Nat := [2, 4, 1, 3, 1, 3, 9]
def baseStart_5138132 : Nat := 118140960795 + 5138132 * 2 ^ 59
def prefixEnd_5138132 : Nat := 4983230072969 + 3 ^ 40 * 5138132 * 2
def baseEnd_5138132 : Nat := 32571992373424645291607

theorem tailTrace_5138132 : CollatzResearch.WordTrace tailWord_5138132 prefixEnd_5138132 32571992373424645291607 := by
  unfold tailWord_5138132
  simp only [CollatzResearch.WordTrace]
  refine ⟨93701534910716380963764325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124935379880955174618352433 93701534910716380963764325)
  ·
    refine ⟨17569037795759321430705811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93701534910716380963764325 17569037795759321430705811)
    ·
      refine ⟨26353556693638982146058717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17569037795759321430705811 26353556693638982146058717)
      ·
        refine ⟨9882583760114618304772019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26353556693638982146058717 9882583760114618304772019)
        ·
          refine ⟨14823875640171927457158029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882583760114618304772019 14823875640171927457158029)
          ·
            refine ⟨5558953365064472796434261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14823875640171927457158029 5558953365064472796434261)
            ·
              refine ⟨32571992373424645291607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5558953365064472796434261 32571992373424645291607)
              ·
                rfl

theorem cell23_5138132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 9].length) (baseStart_5138132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138132 prefixEnd_5138132 := by exact prefixLift 5138132
  have htrace : WordTrace (prefixWord ++ tailWord_5138132) baseStart_5138132 baseEnd_5138132 := by
    simpa [prefixWord, tailWord_5138132, baseEnd_5138132] using wordTrace_append hprefix tailTrace_5138132
  have hstable : (prefixWord ++ tailWord_5138132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138132).length < 2 ^ (prefixWord ++ tailWord_5138132).sum := by decide
  have hdescent : baseEnd_5138132 < baseStart_5138132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138143 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 1, 2, 2]
def baseStart_5138143 : Nat := 118140960795 + 5138143 * 2 ^ 59
def prefixEnd_5138143 : Nat := 4983230072969 + 3 ^ 40 * 5138143 * 2
def baseEnd_5138143 : Nat := 2638337030534595725582617

theorem tailTrace_5138143 : CollatzResearch.WordTrace tailWord_5138143 prefixEnd_5138143 2638337030534595725582617 := by
  unfold tailWord_5138143
  simp only [CollatzResearch.WordTrace]
  refine ⟨187403471024392910806179083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124935647349595273870786055 187403471024392910806179083)
  ·
    refine ⟨281105206536589366209268625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187403471024392910806179083 281105206536589366209268625)
    ·
      refine ⟨210828904902442024656951469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281105206536589366209268625 210828904902442024656951469)
      ·
        refine ⟨79060839338415759246356801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210828904902442024656951469 79060839338415759246356801)
        ·
          refine ⟨59295629503811819434767601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79060839338415759246356801 59295629503811819434767601)
          ·
            refine ⟨44471722127858864576075701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59295629503811819434767601 44471722127858864576075701)
            ·
              refine ⟨4169223949486768554007097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44471722127858864576075701 4169223949486768554007097)
              ·
                refine ⟨3126917962115076415505323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4169223949486768554007097 3126917962115076415505323)
                ·
                  refine ⟨4690376943172614623257985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3126917962115076415505323 4690376943172614623257985)
                  ·
                    refine ⟨3517782707379460967443489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690376943172614623257985 3517782707379460967443489)
                    ·
                      refine ⟨2638337030534595725582617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517782707379460967443489 2638337030534595725582617)
                      ·
                        rfl

theorem cell23_5138143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_5138143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138143 prefixEnd_5138143 := by exact prefixLift 5138143
  have htrace : WordTrace (prefixWord ++ tailWord_5138143) baseStart_5138143 baseEnd_5138143 := by
    simpa [prefixWord, tailWord_5138143, baseEnd_5138143] using wordTrace_append hprefix tailTrace_5138143
  have hstable : (prefixWord ++ tailWord_5138143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138143).length < 2 ^ (prefixWord ++ tailWord_5138143).sum := by decide
  have hdescent : baseEnd_5138143 < baseStart_5138143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138159 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 3]
def baseStart_5138159 : Nat := 118140960795 + 5138159 * 2 ^ 59
def prefixEnd_5138159 : Nat := 4983230072969 + 3 ^ 40 * 5138159 * 2
def baseEnd_5138159 : Nat := 2638345246225067662982543

theorem tailTrace_5138159 : CollatzResearch.WordTrace tailWord_5138159 prefixEnd_5138159 2638345246225067662982543 := by
  unfold tailWord_5138159
  simp only [CollatzResearch.WordTrace]
  refine ⟨187404054592334945538761531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124936036394889963692507687 187404054592334945538761531)
  ·
    refine ⟨281106081888502418308142297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187404054592334945538761531 281106081888502418308142297)
    ·
      refine ⟨210829561416376813731106723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281106081888502418308142297 210829561416376813731106723)
      ·
        refine ⟨316244342124565220596660085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210829561416376813731106723 316244342124565220596660085)
        ·
          refine ⟨29647907074177989430936883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 316244342124565220596660085 29647907074177989430936883)
          ·
            refine ⟨44471860611266984146405325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29647907074177989430936883 44471860611266984146405325)
            ·
              refine ⟨16676947729225119054901997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44471860611266984146405325 16676947729225119054901997)
              ·
                refine ⟨6253855398459419645588249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16676947729225119054901997 6253855398459419645588249)
                ·
                  refine ⟨4690391548844564734191187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6253855398459419645588249 4690391548844564734191187)
                  ·
                    refine ⟨7035587323266847101286781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690391548844564734191187 7035587323266847101286781)
                    ·
                      refine ⟨2638345246225067662982543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035587323266847101286781 2638345246225067662982543)
                      ·
                        rfl

theorem cell23_5138159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_5138159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138159 prefixEnd_5138159 := by exact prefixLift 5138159
  have htrace : WordTrace (prefixWord ++ tailWord_5138159) baseStart_5138159 baseEnd_5138159 := by
    simpa [prefixWord, tailWord_5138159, baseEnd_5138159] using wordTrace_append hprefix tailTrace_5138159
  have hstable : (prefixWord ++ tailWord_5138159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138159).length < 2 ^ (prefixWord ++ tailWord_5138159).sum := by decide
  have hdescent : baseEnd_5138159 < baseStart_5138159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138202 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3]
def baseStart_5138202 : Nat := 118140960795 + 5138202 * 2 ^ 59
def prefixEnd_5138202 : Nat := 4983230072969 + 3 ^ 40 * 5138202 * 2
def baseEnd_5138202 : Nat := 2638367325893210994744845

theorem tailTrace_5138202 : CollatzResearch.WordTrace tailWord_5138202 prefixEnd_5138202 2638367325893210994744845 := by
  unfold tailWord_5138202
  simp only [CollatzResearch.WordTrace]
  refine ⟨46851405732794790970644215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124937081954119442588384573 46851405732794790970644215)
  ·
    refine ⟨70277108599192186455966323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46851405732794790970644215 70277108599192186455966323)
    ·
      refine ⟨105415662898788279683949485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70277108599192186455966323 105415662898788279683949485)
      ·
        refine ⟨39530873587045604881481057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105415662898788279683949485 39530873587045604881481057)
        ·
          refine ⟨29648155190284203661110793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39530873587045604881481057 29648155190284203661110793)
          ·
            refine ⟨22236116392713152745833095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29648155190284203661110793 22236116392713152745833095)
            ·
              refine ⟨33354174589069729118749643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236116392713152745833095 33354174589069729118749643)
              ·
                refine ⟨50031261883604593678124465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33354174589069729118749643 50031261883604593678124465)
                ·
                  refine ⟨37523446412703445258593349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50031261883604593678124465 37523446412703445258593349)
                  ·
                    refine ⟨7035646202381895985986253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37523446412703445258593349 7035646202381895985986253)
                    ·
                      refine ⟨2638367325893210994744845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035646202381895985986253 2638367325893210994744845)
                      ·
                        rfl

theorem cell23_5138202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_5138202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138202 prefixEnd_5138202 := by exact prefixLift 5138202
  have htrace : WordTrace (prefixWord ++ tailWord_5138202) baseStart_5138202 baseEnd_5138202 := by
    simpa [prefixWord, tailWord_5138202, baseEnd_5138202] using wordTrace_append hprefix tailTrace_5138202
  have hstable : (prefixWord ++ tailWord_5138202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138202).length < 2 ^ (prefixWord ++ tailWord_5138202).sum := by decide
  have hdescent : baseEnd_5138202 < baseStart_5138202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138212 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_5138212 : Nat := 118140960795 + 5138212 * 2 ^ 59
def prefixEnd_5138212 : Nat := 4983230072969 + 3 ^ 40 * 5138212 * 2
def baseEnd_5138212 : Nat := 2638372460699755955619799

theorem tailTrace_5138212 : CollatzResearch.WordTrace tailWord_5138212 prefixEnd_5138212 2638372460699755955619799 := by
  unfold tailWord_5138212
  simp only [CollatzResearch.WordTrace]
  refine ⟨93702993830571467795220445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124937325107428623726960593 93702993830571467795220445)
  ·
    refine ⟨35138622686464300423207667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93702993830571467795220445 35138622686464300423207667)
    ·
      refine ⟨52707934029696450634811501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35138622686464300423207667 52707934029696450634811501)
      ·
        refine ⟨19765475261136168988054313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52707934029696450634811501 19765475261136168988054313)
        ·
          refine ⟨14824106445852126741040735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19765475261136168988054313 14824106445852126741040735)
          ·
            refine ⟨22236159668778190111561103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824106445852126741040735 22236159668778190111561103)
            ·
              refine ⟨33354239503167285167341655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236159668778190111561103 33354239503167285167341655)
              ·
                refine ⟨50031359254750927751012483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33354239503167285167341655 50031359254750927751012483)
                ·
                  refine ⟨75047038882126391626518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50031359254750927751012483 75047038882126391626518725)
                  ·
                    refine ⟨14071319790398698429972261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75047038882126391626518725 14071319790398698429972261)
                    ·
                      refine ⟨2638372460699755955619799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14071319790398698429972261 2638372460699755955619799)
                      ·
                        rfl

theorem cell23_5138212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_5138212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138212 prefixEnd_5138212 := by exact prefixLift 5138212
  have htrace : WordTrace (prefixWord ++ tailWord_5138212) baseStart_5138212 baseEnd_5138212 := by
    simpa [prefixWord, tailWord_5138212, baseEnd_5138212] using wordTrace_append hprefix tailTrace_5138212
  have hstable : (prefixWord ++ tailWord_5138212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138212).length < 2 ^ (prefixWord ++ tailWord_5138212).sum := by decide
  have hdescent : baseEnd_5138212 < baseStart_5138212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138216 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_5138216 : Nat := 118140960795 + 5138216 * 2 ^ 59
def prefixEnd_5138216 : Nat := 4983230072969 + 3 ^ 40 * 5138216 * 2
def baseEnd_5138216 : Nat := 2638374514622373939969781

theorem tailTrace_5138216 : CollatzResearch.WordTrace tailWord_5138216 prefixEnd_5138216 2638374514622373939969781 := by
  unfold tailWord_5138216
  simp only [CollatzResearch.WordTrace]
  refine ⟨93703066776564222136793251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124937422368752296182391001 93703066776564222136793251)
  ·
    refine ⟨140554600164846333205189877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93703066776564222136793251 140554600164846333205189877)
    ·
      refine ⟨13176993765454343737986551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140554600164846333205189877 13176993765454343737986551)
      ·
        refine ⟨19765490648181515606979827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13176993765454343737986551 19765490648181515606979827)
        ·
          refine ⟨29648235972272273410469741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19765490648181515606979827 29648235972272273410469741)
          ·
            refine ⟨11118088489602102528926153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29648235972272273410469741 11118088489602102528926153)
            ·
              refine ⟨8338566367201576896694615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11118088489602102528926153 8338566367201576896694615)
              ·
                refine ⟨12507849550802365345041923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8338566367201576896694615 12507849550802365345041923)
                ·
                  refine ⟨18761774326203548017562885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12507849550802365345041923 18761774326203548017562885)
                  ·
                    refine ⟨3517832686163165253293041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18761774326203548017562885 3517832686163165253293041)
                    ·
                      refine ⟨2638374514622373939969781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517832686163165253293041 2638374514622373939969781)
                      ·
                        rfl

theorem cell23_5138216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_5138216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138216 prefixEnd_5138216 := by exact prefixLift 5138216
  have htrace : WordTrace (prefixWord ++ tailWord_5138216) baseStart_5138216 baseEnd_5138216 := by
    simpa [prefixWord, tailWord_5138216, baseEnd_5138216] using wordTrace_append hprefix tailTrace_5138216
  have hstable : (prefixWord ++ tailWord_5138216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138216).length < 2 ^ (prefixWord ++ tailWord_5138216).sum := by decide
  have hdescent : baseEnd_5138216 < baseStart_5138216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138246 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5138246 : Nat := 118140960795 + 5138246 * 2 ^ 59
def prefixEnd_5138246 : Nat := 4983230072969 + 3 ^ 40 * 5138246 * 2
def baseEnd_5138246 : Nat := 2638389919042008822594643

theorem tailTrace_5138246 : CollatzResearch.WordTrace tailWord_5138246 prefixEnd_5138246 2638389919042008822594643 := by
  unfold tailWord_5138246
  simp only [CollatzResearch.WordTrace]
  refine ⟨5856475866969367481161831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 124938151828679839598119061 5856475866969367481161831)
  ·
    refine ⟨8784713800454051221742747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5856475866969367481161831 8784713800454051221742747)
    ·
      refine ⟨13177070700681076832614121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784713800454051221742747 13177070700681076832614121)
      ·
        refine ⟨9882803025510807624460591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13177070700681076832614121 9882803025510807624460591)
        ·
          refine ⟨14824204538266211436690887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9882803025510807624460591 14824204538266211436690887)
          ·
            refine ⟨22236306807399317155036331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824204538266211436690887 22236306807399317155036331)
            ·
              refine ⟨33354460211098975732554497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236306807399317155036331 33354460211098975732554497)
              ·
                refine ⟨25015845158324231799415873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33354460211098975732554497 25015845158324231799415873)
                ·
                  refine ⟨18761883868743173849561905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25015845158324231799415873 18761883868743173849561905)
                  ·
                    refine ⟨14071412901557380387171429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18761883868743173849561905 14071412901557380387171429)
                    ·
                      refine ⟨2638389919042008822594643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14071412901557380387171429 2638389919042008822594643)
                      ·
                        rfl

theorem cell23_5138246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5138246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138246 prefixEnd_5138246 := by exact prefixLift 5138246
  have htrace : WordTrace (prefixWord ++ tailWord_5138246) baseStart_5138246 baseEnd_5138246 := by
    simpa [prefixWord, tailWord_5138246, baseEnd_5138246] using wordTrace_append hprefix tailTrace_5138246
  have hstable : (prefixWord ++ tailWord_5138246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138246).length < 2 ^ (prefixWord ++ tailWord_5138246).sum := by decide
  have hdescent : baseEnd_5138246 < baseStart_5138246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138272 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_5138272 : Nat := 118140960795 + 5138272 * 2 ^ 59
def prefixEnd_5138272 : Nat := 4983230072969 + 3 ^ 40 * 5138272 * 2
def baseEnd_5138272 : Nat := 2638403269539025720869523

theorem tailTrace_5138272 : CollatzResearch.WordTrace tailWord_5138272 prefixEnd_5138272 2638403269539025720869523 := by
  unfold tailWord_5138272
  simp only [CollatzResearch.WordTrace]
  refine ⟨93704088020462782918812535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124938784027283710558416713 93704088020462782918812535)
  ·
    refine ⟨140556132030694174378218803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93704088020462782918812535 140556132030694174378218803)
    ·
      refine ⟨210834198046041261567328205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140556132030694174378218803 210834198046041261567328205)
      ·
        refine ⟨79062824267265473087748077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210834198046041261567328205 79062824267265473087748077)
        ·
          refine ⟨29648559100224552407905529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79062824267265473087748077 29648559100224552407905529)
          ·
            refine ⟨22236419325168414305929147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29648559100224552407905529 22236419325168414305929147)
            ·
              refine ⟨33354628987752621458893721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236419325168414305929147 33354628987752621458893721)
              ·
                refine ⟨25015971740814466094170291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33354628987752621458893721 25015971740814466094170291)
                ·
                  refine ⟨37523957611221699141255437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25015971740814466094170291 37523957611221699141255437)
                  ·
                    refine ⟨14071484104208137177970789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37523957611221699141255437 14071484104208137177970789)
                    ·
                      refine ⟨2638403269539025720869523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14071484104208137177970789 2638403269539025720869523)
                      ·
                        rfl

theorem cell23_5138272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_5138272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138272 prefixEnd_5138272 := by exact prefixLift 5138272
  have htrace : WordTrace (prefixWord ++ tailWord_5138272) baseStart_5138272 baseEnd_5138272 := by
    simpa [prefixWord, tailWord_5138272, baseEnd_5138272] using wordTrace_append hprefix tailTrace_5138272
  have hstable : (prefixWord ++ tailWord_5138272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138272).length < 2 ^ (prefixWord ++ tailWord_5138272).sum := by decide
  have hdescent : baseEnd_5138272 < baseStart_5138272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138309 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_5138309 : Nat := 118140960795 + 5138309 * 2 ^ 59
def prefixEnd_5138309 : Nat := 4983230072969 + 3 ^ 40 * 5138309 * 2
def baseEnd_5138309 : Nat := 2638422268323242076106853

theorem tailTrace_5138309 : CollatzResearch.WordTrace tailWord_5138309 prefixEnd_5138309 2638422268323242076106853 := by
  unfold tailWord_5138309
  simp only [CollatzResearch.WordTrace]
  refine ⟨187409525541791521156721981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124939683694527680771147987 187409525541791521156721981)
  ·
    refine ⟨70278572078171820433770743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187409525541791521156721981 70278572078171820433770743)
    ·
      refine ⟨105417858117257730650656115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70278572078171820433770743 105417858117257730650656115)
      ·
        refine ⟨158126787175886595975984173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105417858117257730650656115 158126787175886595975984173)
        ·
          refine ⟨59297545190957473490994065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158126787175886595975984173 59297545190957473490994065)
          ·
            refine ⟨44473158893218105118245549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59297545190957473490994065 44473158893218105118245549)
            ·
              refine ⟨16677434584956789419342081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44473158893218105118245549 16677434584956789419342081)
              ·
                refine ⟨12508075938717592064506561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16677434584956789419342081 12508075938717592064506561)
                ·
                  refine ⟨9381056954038194048379921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12508075938717592064506561 9381056954038194048379921)
                  ·
                    refine ⟨7035792715528645536284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9381056954038194048379921 7035792715528645536284941)
                    ·
                      refine ⟨2638422268323242076106853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035792715528645536284941 2638422268323242076106853)
                      ·
                        rfl

theorem cell23_5138309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_5138309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138309 prefixEnd_5138309 := by exact prefixLift 5138309
  have htrace : WordTrace (prefixWord ++ tailWord_5138309) baseStart_5138309 baseEnd_5138309 := by
    simpa [prefixWord, tailWord_5138309, baseEnd_5138309] using wordTrace_append hprefix tailTrace_5138309
  have hstable : (prefixWord ++ tailWord_5138309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138309).length < 2 ^ (prefixWord ++ tailWord_5138309).sum := by decide
  have hdescent : baseEnd_5138309 < baseStart_5138309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138329 : List Nat := [1, 2, 1, 2, 1, 3, 6, 1, 6]
def baseStart_5138329 : Nat := 118140960795 + 5138329 * 2 ^ 59
def prefixEnd_5138329 : Nat := 4983230072969 + 3 ^ 40 * 5138329 * 2
def baseEnd_5138329 : Nat := 293159170881814666428529

theorem tailTrace_5138329 : CollatzResearch.WordTrace tailWord_5138329 prefixEnd_5138329 293159170881814666428529 := by
  unfold tailWord_5138329
  simp only [CollatzResearch.WordTrace]
  refine ⟨187410255001719064572450041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124940170001146043048300027 187410255001719064572450041)
  ·
    refine ⟨140557691251289298429337531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187410255001719064572450041 140557691251289298429337531)
    ·
      refine ⟨210836536876933947644006297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140557691251289298429337531 210836536876933947644006297)
      ·
        refine ⟨158127402657700460733004723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210836536876933947644006297 158127402657700460733004723)
        ·
          refine ⟨237191103986550691099507085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158127402657700460733004723 237191103986550691099507085)
          ·
            refine ⟨88946663994956509162315157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237191103986550691099507085 88946663994956509162315157)
            ·
              refine ⟨4169374874763586366983523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88946663994956509162315157 4169374874763586366983523)
              ·
                refine ⟨6254062312145379550475285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169374874763586366983523 6254062312145379550475285)
                ·
                  refine ⟨293159170881814666428529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6254062312145379550475285 293159170881814666428529)
                  ·
                    rfl

theorem cell23_5138329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_5138329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138329 prefixEnd_5138329 := by exact prefixLift 5138329
  have htrace : WordTrace (prefixWord ++ tailWord_5138329) baseStart_5138329 baseEnd_5138329 := by
    simpa [prefixWord, tailWord_5138329, baseEnd_5138329] using wordTrace_append hprefix tailTrace_5138329
  have hstable : (prefixWord ++ tailWord_5138329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138329).length < 2 ^ (prefixWord ++ tailWord_5138329).sum := by decide
  have hdescent : baseEnd_5138329 < baseStart_5138329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138339 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 3]
def baseStart_5138339 : Nat := 118140960795 + 5138339 * 2 ^ 59
def prefixEnd_5138339 : Nat := 4983230072969 + 3 ^ 40 * 5138339 * 2
def baseEnd_5138339 : Nat := 2638437672742876958731715

theorem tailTrace_5138339 : CollatzResearch.WordTrace tailWord_5138339 prefixEnd_5138339 2638437672742876958731715 := by
  unfold tailWord_5138339
  simp only [CollatzResearch.WordTrace]
  refine ⟨187410619731682836280314071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124940413154455224186876047 187410619731682836280314071)
  ·
    refine ⟨281115929597524254420471107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187410619731682836280314071 281115929597524254420471107)
    ·
      refine ⟨421673894396286381630706661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281115929597524254420471107 421673894396286381630706661)
      ·
        refine ⟨79063855199303696555757499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421673894396286381630706661 79063855199303696555757499)
        ·
          refine ⟨118595782798955544833636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79063855199303696555757499 118595782798955544833636249)
          ·
            refine ⟨88946837099216658625227187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118595782798955544833636249 88946837099216658625227187)
            ·
              refine ⟨133420255648824987937840781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88946837099216658625227187 133420255648824987937840781)
              ·
                refine ⟨50032595868309370476690293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133420255648824987937840781 50032595868309370476690293)
                ·
                  refine ⟨4690555862654003482189715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50032595868309370476690293 4690555862654003482189715)
                  ·
                    refine ⟨7035833793981005223284573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690555862654003482189715 7035833793981005223284573)
                    ·
                      refine ⟨2638437672742876958731715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035833793981005223284573 2638437672742876958731715)
                      ·
                        rfl

theorem cell23_5138339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_5138339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138339 prefixEnd_5138339 := by exact prefixLift 5138339
  have htrace : WordTrace (prefixWord ++ tailWord_5138339) baseStart_5138339 baseEnd_5138339 := by
    simpa [prefixWord, tailWord_5138339, baseEnd_5138339] using wordTrace_append hprefix tailTrace_5138339
  have hstable : (prefixWord ++ tailWord_5138339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138339).length < 2 ^ (prefixWord ++ tailWord_5138339).sum := by decide
  have hdescent : baseEnd_5138339 < baseStart_5138339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138389 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_5138389 : Nat := 118140960795 + 5138389 * 2 ^ 59
def prefixEnd_5138389 : Nat := 4983230072969 + 3 ^ 40 * 5138389 * 2
def baseEnd_5138389 : Nat := 879487782258533921035495

theorem tailTrace_5138389 : CollatzResearch.WordTrace tailWord_5138389 prefixEnd_5138389 879487782258533921035495 := by
  unfold tailWord_5138389
  simp only [CollatzResearch.WordTrace]
  refine ⟨187412443381501694819634221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124941628921001129879756147 187412443381501694819634221)
  ·
    refine ⟨70279666268063135557362833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187412443381501694819634221 70279666268063135557362833)
    ·
      refine ⟨52709749701047351668022125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70279666268063135557362833 52709749701047351668022125)
      ·
        refine ⟨19766156137892756875508297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52709749701047351668022125 19766156137892756875508297)
        ·
          refine ⟨14824617103419567656631223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19766156137892756875508297 14824617103419567656631223)
          ·
            refine ⟨22236925655129351484946835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824617103419567656631223 22236925655129351484946835)
            ·
              refine ⟨33355388482694027227420253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22236925655129351484946835 33355388482694027227420253)
              ·
                refine ⟨12508270681010260210282595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33355388482694027227420253 12508270681010260210282595)
                ·
                  refine ⟨18762406021515390315423893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12508270681010260210282595 18762406021515390315423893)
                  ·
                    refine ⟨879487782258533921035495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18762406021515390315423893 879487782258533921035495)
                    ·
                      rfl

theorem cell23_5138389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_5138389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138389 prefixEnd_5138389 := by exact prefixLift 5138389
  have htrace : WordTrace (prefixWord ++ tailWord_5138389) baseStart_5138389 baseEnd_5138389 := by
    simpa [prefixWord, tailWord_5138389, baseEnd_5138389] using wordTrace_append hprefix tailTrace_5138389
  have hstable : (prefixWord ++ tailWord_5138389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138389).length < 2 ^ (prefixWord ++ tailWord_5138389).sum := by decide
  have hdescent : baseEnd_5138389 < baseStart_5138389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138390 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5138390 : Nat := 118140960795 + 5138390 * 2 ^ 59
def prefixEnd_5138390 : Nat := 4983230072969 + 3 ^ 40 * 5138390 * 2
def baseEnd_5138390 : Nat := 2638463860256256259193981

theorem tailTrace_5138390 : CollatzResearch.WordTrace tailWord_5138390 prefixEnd_5138390 2638463860256256259193981 := by
  unfold tailWord_5138390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713279990906129499401289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124941653236332047993613749 11713279990906129499401289)
  ·
    refine ⟨8784959993179597124550967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11713279990906129499401289 8784959993179597124550967)
    ·
      refine ⟨13177439989769395686826451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8784959993179597124550967 13177439989769395686826451)
      ·
        refine ⟨19766159984654093530239677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177439989769395686826451 19766159984654093530239677)
        ·
          refine ⟨7412309994245285073839879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19766159984654093530239677 7412309994245285073839879)
          ·
            refine ⟨11118464991367927610759819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412309994245285073839879 11118464991367927610759819)
            ·
              refine ⟨16677697487051891416139729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11118464991367927610759819 16677697487051891416139729)
              ·
                refine ⟨12508273115288918562104797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16677697487051891416139729 12508273115288918562104797)
                ·
                  refine ⟨4690602418233344460789299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12508273115288918562104797 4690602418233344460789299)
                  ·
                    refine ⟨7035903627350016691183949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690602418233344460789299 7035903627350016691183949)
                    ·
                      refine ⟨2638463860256256259193981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035903627350016691183949 2638463860256256259193981)
                      ·
                        rfl

theorem cell23_5138390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5138390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138390 prefixEnd_5138390 := by exact prefixLift 5138390
  have htrace : WordTrace (prefixWord ++ tailWord_5138390) baseStart_5138390 baseEnd_5138390 := by
    simpa [prefixWord, tailWord_5138390, baseEnd_5138390] using wordTrace_append hprefix tailTrace_5138390
  have hstable : (prefixWord ++ tailWord_5138390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138390).length < 2 ^ (prefixWord ++ tailWord_5138390).sum := by decide
  have hdescent : baseEnd_5138390 < baseStart_5138390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138429 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_5138429 : Nat := 118140960795 + 5138429 * 2 ^ 59
def prefixEnd_5138429 : Nat := 4983230072969 + 3 ^ 40 * 5138429 * 2
def baseEnd_5138429 : Nat := 2638483886001781606606301

theorem tailTrace_5138429 : CollatzResearch.WordTrace tailWord_5138429 prefixEnd_5138429 2638483886001781606606301 := by
  unfold tailWord_5138429
  simp only [CollatzResearch.WordTrace]
  refine ⟨187413902301356781651090341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124942601534237854434060227 187413902301356781651090341)
  ·
    refine ⟨35140106681504396559579439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187413902301356781651090341 35140106681504396559579439)
    ·
      refine ⟨52710160022256594839369159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35140106681504396559579439 52710160022256594839369159)
      ·
        refine ⟨79065240033384892259053739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52710160022256594839369159 79065240033384892259053739)
        ·
          refine ⟨118597860050077338388580609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79065240033384892259053739 118597860050077338388580609)
          ·
            refine ⟨88948395037558003791435457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118597860050077338388580609 88948395037558003791435457)
            ·
              refine ⟨66711296278168502843576593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88948395037558003791435457 66711296278168502843576593)
              ·
                refine ⟨50033472208626377132682445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66711296278168502843576593 50033472208626377132682445)
                ·
                  refine ⟨18762552078234891424755917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50033472208626377132682445 18762552078234891424755917)
                  ·
                    refine ⟨7035957029338084284283469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18762552078234891424755917 7035957029338084284283469)
                    ·
                      refine ⟨2638483886001781606606301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7035957029338084284283469 2638483886001781606606301)
                      ·
                        rfl

theorem cell23_5138429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_5138429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138429 prefixEnd_5138429 := by exact prefixLift 5138429
  have htrace : WordTrace (prefixWord ++ tailWord_5138429) baseStart_5138429 baseEnd_5138429 := by
    simpa [prefixWord, tailWord_5138429, baseEnd_5138429] using wordTrace_append hprefix tailTrace_5138429
  have hstable : (prefixWord ++ tailWord_5138429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138429).length < 2 ^ (prefixWord ++ tailWord_5138429).sum := by decide
  have hdescent : baseEnd_5138429 < baseStart_5138429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138430 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5138430 : Nat := 118140960795 + 5138430 * 2 ^ 59
def prefixEnd_5138430 : Nat := 4983230072969 + 3 ^ 40 * 5138430 * 2
def baseEnd_5138430 : Nat := 2638484399482436102693797

theorem tailTrace_5138430 : CollatzResearch.WordTrace tailWord_5138430 prefixEnd_5138430 2638484399482436102693797 := by
  unfold tailWord_5138430
  simp only [CollatzResearch.WordTrace]
  refine ⟨23426742346794144852734593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124942625849568772547917829 23426742346794144852734593)
  ·
    refine ⟨17570056760095608639550945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23426742346794144852734593 17570056760095608639550945)
    ·
      refine ⟨13177542570071706479663209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17570056760095608639550945 13177542570071706479663209)
      ·
        refine ⟨9883156927553779859747407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13177542570071706479663209 9883156927553779859747407)
        ·
          refine ⟨14824735391330669789621111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883156927553779859747407 14824735391330669789621111)
          ·
            refine ⟨22237103086996004684431667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14824735391330669789621111 22237103086996004684431667)
            ·
              refine ⟨33355654630494007026647501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22237103086996004684431667 33355654630494007026647501)
              ·
                refine ⟨12508370486435252634992813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33355654630494007026647501 12508370486435252634992813)
                ·
                  refine ⟨4690638932413219738122305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12508370486435252634992813 4690638932413219738122305)
                  ·
                    refine ⟨3517979199309914803591729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4690638932413219738122305 3517979199309914803591729)
                    ·
                      refine ⟨2638484399482436102693797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3517979199309914803591729 2638484399482436102693797)
                      ·
                        rfl

theorem cell23_5138430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5138430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138430 prefixEnd_5138430 := by exact prefixLift 5138430
  have htrace : WordTrace (prefixWord ++ tailWord_5138430) baseStart_5138430 baseEnd_5138430 := by
    simpa [prefixWord, tailWord_5138430, baseEnd_5138430] using wordTrace_append hprefix tailTrace_5138430
  have hstable : (prefixWord ++ tailWord_5138430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138430).length < 2 ^ (prefixWord ++ tailWord_5138430).sum := by decide
  have hdescent : baseEnd_5138430 < baseStart_5138430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138432 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 2, 7]
def baseStart_5138432 : Nat := 118140960795 + 5138432 * 2 ^ 59
def prefixEnd_5138432 : Nat := 4983230072969 + 3 ^ 40 * 5138432 * 2
def baseEnd_5138432 : Nat := 879495142147915031622929

theorem tailTrace_5138432 : CollatzResearch.WordTrace tailWord_5138432 prefixEnd_5138432 879495142147915031622929 := by
  unfold tailWord_5138432
  simp only [CollatzResearch.WordTrace]
  refine ⟨93707005860172956581724775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124942674480230608775633033 93707005860172956581724775)
  ·
    refine ⟨140560508790259434872587163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93707005860172956581724775 140560508790259434872587163)
    ·
      refine ⟨210840763185389152308880745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140560508790259434872587163 210840763185389152308880745)
      ·
        refine ⟨158130572389041864231660559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210840763185389152308880745 158130572389041864231660559)
        ·
          refine ⟨237195858583562796347490839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158130572389041864231660559 237195858583562796347490839)
          ·
            refine ⟨355793787875344194521236259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237195858583562796347490839 355793787875344194521236259)
            ·
              refine ⟨533690681813016291781854389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355793787875344194521236259 533690681813016291781854389)
              ·
                refine ⟨50033501419970277354548849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533690681813016291781854389 50033501419970277354548849)
                ·
                  refine ⟨37525126064977708015911637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50033501419970277354548849 37525126064977708015911637)
                  ·
                    refine ⟨879495142147915031622929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37525126064977708015911637 879495142147915031622929)
                    ·
                      rfl

theorem cell23_5138432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_5138432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138432 prefixEnd_5138432 := by exact prefixLift 5138432
  have htrace : WordTrace (prefixWord ++ tailWord_5138432) baseStart_5138432 baseEnd_5138432 := by
    simpa [prefixWord, tailWord_5138432, baseEnd_5138432] using wordTrace_append hprefix tailTrace_5138432
  have hstable : (prefixWord ++ tailWord_5138432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138432).length < 2 ^ (prefixWord ++ tailWord_5138432).sum := by decide
  have hdescent : baseEnd_5138432 < baseStart_5138432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138453 : List Nat := [1, 3, 2, 1, 6, 1, 2, 7]
def baseStart_5138453 : Nat := 118140960795 + 5138453 * 2 ^ 59
def prefixEnd_5138453 : Nat := 4983230072969 + 3 ^ 40 * 5138453 * 2
def baseEnd_5138453 : Nat := 97722081834721833803933

theorem tailTrace_5138453 : CollatzResearch.WordTrace tailWord_5138453 prefixEnd_5138453 97722081834721833803933 := by
  unfold tailWord_5138453
  simp only [CollatzResearch.WordTrace]
  refine ⟨187414777653269833749964013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124943185102179889166642675 187414777653269833749964013)
  ·
    refine ⟨70280541619976187656236505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187414777653269833749964013 70280541619976187656236505)
    ·
      refine ⟨52710406214982140742177379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70280541619976187656236505 52710406214982140742177379)
      ·
        refine ⟨79065609322473211113266069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52710406214982140742177379 79065609322473211113266069)
        ·
          refine ⟨3706200436990931770934347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79065609322473211113266069 3706200436990931770934347)
          ·
            refine ⟨5559300655486397656401521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3706200436990931770934347 5559300655486397656401521)
            ·
              refine ⟨4169475491614798242301141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5559300655486397656401521 4169475491614798242301141)
              ·
                refine ⟨97722081834721833803933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4169475491614798242301141 97722081834721833803933)
                ·
                  rfl

theorem cell23_5138453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 7].length) (baseStart_5138453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138453 prefixEnd_5138453 := by exact prefixLift 5138453
  have htrace : WordTrace (prefixWord ++ tailWord_5138453) baseStart_5138453 baseEnd_5138453 := by
    simpa [prefixWord, tailWord_5138453, baseEnd_5138453] using wordTrace_append hprefix tailTrace_5138453
  have hstable : (prefixWord ++ tailWord_5138453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138453).length < 2 ^ (prefixWord ++ tailWord_5138453).sum := by decide
  have hdescent : baseEnd_5138453 < baseStart_5138453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138486 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5138486 : Nat := 118140960795 + 5138486 * 2 ^ 59
def prefixEnd_5138486 : Nat := 4983230072969 + 3 ^ 40 * 5138486 * 2
def baseEnd_5138486 : Nat := 2638513154399087883593539

theorem tailTrace_5138486 : CollatzResearch.WordTrace tailWord_5138486 prefixEnd_5138486 2638513154399087883593539 := by
  unfold tailWord_5138486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11713498828884392524119707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124943987508100186923943541 11713498828884392524119707)
  ·
    refine ⟨17570248243326588786179561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11713498828884392524119707 17570248243326588786179561)
    ·
      refine ⟨13177686182494941589634671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17570248243326588786179561 13177686182494941589634671)
      ·
        refine ⟨19766529273742412384452007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177686182494941589634671 19766529273742412384452007)
        ·
          refine ⟨29649793910613618576678011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19766529273742412384452007 29649793910613618576678011)
          ·
            refine ⟨44474690865920427865017017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29649793910613618576678011 44474690865920427865017017)
            ·
              refine ⟨33356018149440320898762763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44474690865920427865017017 33356018149440320898762763)
              ·
                refine ⟨50034027224160481348144145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33356018149440320898762763 50034027224160481348144145)
                ·
                  refine ⟨37525520418120361011108109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50034027224160481348144145 37525520418120361011108109)
                  ·
                    refine ⟨14072070156795135379165541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37525520418120361011108109 14072070156795135379165541)
                    ·
                      refine ⟨2638513154399087883593539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14072070156795135379165541 2638513154399087883593539)
                      ·
                        rfl

theorem cell23_5138486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5138486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138486 prefixEnd_5138486 := by exact prefixLift 5138486
  have htrace : WordTrace (prefixWord ++ tailWord_5138486) baseStart_5138486 baseEnd_5138486 := by
    simpa [prefixWord, tailWord_5138486, baseEnd_5138486] using wordTrace_append hprefix tailTrace_5138486
  have hstable : (prefixWord ++ tailWord_5138486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138486).length < 2 ^ (prefixWord ++ tailWord_5138486).sum := by decide
  have hdescent : baseEnd_5138486 < baseStart_5138486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138497 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_5138497 : Nat := 118140960795 + 5138497 * 2 ^ 59
def prefixEnd_5138497 : Nat := 4983230072969 + 3 ^ 40 * 5138497 * 2
def baseEnd_5138497 : Nat := 2638518802686287340555989

theorem tailTrace_5138497 : CollatzResearch.WordTrace tailWord_5138497 prefixEnd_5138497 2638518802686287340555989 := by
  unfold tailWord_5138497
  simp only [CollatzResearch.WordTrace]
  refine ⟨187416382465110429264565745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124944254976740286176377163 187416382465110429264565745)
  ·
    refine ⟨140562286848832821948424309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187416382465110429264565745 140562286848832821948424309)
    ·
      refine ⟨13177714392078077057664779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 140562286848832821948424309 13177714392078077057664779)
      ·
        refine ⟨19766571588117115586497169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13177714392078077057664779 19766571588117115586497169)
        ·
          refine ⟨14824928691087836689872877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19766571588117115586497169 14824928691087836689872877)
          ·
            refine ⟨5559348259157938758702329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14824928691087836689872877 5559348259157938758702329)
            ·
              refine ⟨4169511194368454069026747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5559348259157938758702329 4169511194368454069026747)
              ·
                refine ⟨6254266791552681103540121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169511194368454069026747 6254266791552681103540121)
                ·
                  refine ⟨4690700093664510827655091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254266791552681103540121 4690700093664510827655091)
                  ·
                    refine ⟨7036050140496766241482637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690700093664510827655091 7036050140496766241482637)
                    ·
                      refine ⟨2638518802686287340555989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036050140496766241482637 2638518802686287340555989)
                      ·
                        rfl

theorem cell23_5138497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_5138497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138497 prefixEnd_5138497 := by exact prefixLift 5138497
  have htrace : WordTrace (prefixWord ++ tailWord_5138497) baseStart_5138497 baseEnd_5138497 := by
    simpa [prefixWord, tailWord_5138497, baseEnd_5138497] using wordTrace_append hprefix tailTrace_5138497
  have hstable : (prefixWord ++ tailWord_5138497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138497).length < 2 ^ (prefixWord ++ tailWord_5138497).sum := by decide
  have hdescent : baseEnd_5138497 < baseStart_5138497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138543 : List Nat := [1, 1, 2, 1, 3, 4, 4, 2, 5]
def baseStart_5138543 : Nat := 118140960795 + 5138543 * 2 ^ 59
def prefixEnd_5138543 : Nat := 4983230072969 + 3 ^ 40 * 5138543 * 2
def baseEnd_5138543 : Nat := 293171380310710462286753

theorem tailTrace_5138543 : CollatzResearch.WordTrace tailWord_5138543 prefixEnd_5138543 293171380310710462286753 := by
  unfold tailWord_5138543
  simp only [CollatzResearch.WordTrace]
  refine ⟨187418060222943779120740283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124945373481962519413826855 187418060222943779120740283)
  ·
    refine ⟨281127090334415668681110425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187418060222943779120740283 281127090334415668681110425)
    ·
      refine ⟨210845317750811751510832819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281127090334415668681110425 210845317750811751510832819)
      ·
        refine ⟨316267976626217627266249229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210845317750811751510832819 316267976626217627266249229)
        ·
          refine ⟨118600491234831610224843461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316267976626217627266249229 118600491234831610224843461)
          ·
            refine ⟨22237592106530926917158149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118600491234831610224843461 22237592106530926917158149)
            ·
              refine ⟨4169548519974548796967153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22237592106530926917158149 4169548519974548796967153)
              ·
                refine ⟨3127161389980911597725365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4169548519974548796967153 3127161389980911597725365)
                ·
                  refine ⟨293171380310710462286753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127161389980911597725365 293171380310710462286753)
                  ·
                    rfl

theorem cell23_5138543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 5].length) (baseStart_5138543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138543 prefixEnd_5138543 := by exact prefixLift 5138543
  have htrace : WordTrace (prefixWord ++ tailWord_5138543) baseStart_5138543 baseEnd_5138543 := by
    simpa [prefixWord, tailWord_5138543, baseEnd_5138543] using wordTrace_append hprefix tailTrace_5138543
  have hstable : (prefixWord ++ tailWord_5138543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138543).length < 2 ^ (prefixWord ++ tailWord_5138543).sum := by decide
  have hdescent : baseEnd_5138543 < baseStart_5138543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138576 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2]
def baseStart_5138576 : Nat := 118140960795 + 5138576 * 2 ^ 59
def prefixEnd_5138576 : Nat := 4983230072969 + 3 ^ 40 * 5138576 * 2
def baseEnd_5138576 : Nat := 2638559367657992531468125

theorem tailTrace_5138576 : CollatzResearch.WordTrace tailWord_5138576 prefixEnd_5138576 2638559367657992531468125 := by
  unfold tailWord_5138576
  simp only [CollatzResearch.WordTrace]
  refine ⟨93709631915912112878345791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124946175887882817171127721 93709631915912112878345791)
  ·
    refine ⟨140564447873868169317518687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93709631915912112878345791 140564447873868169317518687)
    ·
      refine ⟨210846671810802253976278031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140564447873868169317518687 210846671810802253976278031)
      ·
        refine ⟨316270007716203380964417047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210846671810802253976278031 316270007716203380964417047)
        ·
          refine ⟨474405011574305071446625571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316270007716203380964417047 474405011574305071446625571)
          ·
            refine ⟨711607517361457607169938357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474405011574305071446625571 711607517361457607169938357)
            ·
              refine ⟨66713204752636650672181721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711607517361457607169938357 66713204752636650672181721)
              ·
                refine ⟨50034903564477488004136291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66713204752636650672181721 50034903564477488004136291)
                ·
                  refine ⟨75052355346716232006204437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50034903564477488004136291 75052355346716232006204437)
                  ·
                    refine ⟨3518079156877323375290833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 75052355346716232006204437 3518079156877323375290833)
                    ·
                      refine ⟨2638559367657992531468125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518079156877323375290833 2638559367657992531468125)
                      ·
                        rfl

theorem cell23_5138576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 1, 6, 2].length) (baseStart_5138576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138576 prefixEnd_5138576 := by exact prefixLift 5138576
  have htrace : WordTrace (prefixWord ++ tailWord_5138576) baseStart_5138576 baseEnd_5138576 := by
    simpa [prefixWord, tailWord_5138576, baseEnd_5138576] using wordTrace_append hprefix tailTrace_5138576
  have hstable : (prefixWord ++ tailWord_5138576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138576).length < 2 ^ (prefixWord ++ tailWord_5138576).sum := by decide
  have hdescent : baseEnd_5138576 < baseStart_5138576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138593 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_5138593 : Nat := 118140960795 + 5138593 * 2 ^ 59
def prefixEnd_5138593 : Nat := 4983230072969 + 3 ^ 40 * 5138593 * 2
def baseEnd_5138593 : Nat := 2638568096829118964955547

theorem tailTrace_5138593 : CollatzResearch.WordTrace tailWord_5138593 prefixEnd_5138593 2638568096829118964955547 := by
  unfold tailWord_5138593
  simp only [CollatzResearch.WordTrace]
  refine ⟨187419883872762637660060433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124946589248508425106706955 187419883872762637660060433)
  ·
    refine ⟨140564912904571978245045325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187419883872762637660060433 140564912904571978245045325)
    ·
      refine ⟨52711842339214491841891997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140564912904571978245045325 52711842339214491841891997)
      ·
        refine ⟨19766940877205434440709499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52711842339214491841891997 19766940877205434440709499)
        ·
          refine ⟨29650411315808151661064249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19766940877205434440709499 29650411315808151661064249)
          ·
            refine ⟨22237808486856113745798187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29650411315808151661064249 22237808486856113745798187)
            ·
              refine ⟨33356712730284170618697281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22237808486856113745798187 33356712730284170618697281)
              ·
                refine ⟨25017534547713127964022961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33356712730284170618697281 25017534547713127964022961)
                ·
                  refine ⟨18763150910784845973017221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25017534547713127964022961 18763150910784845973017221)
                  ·
                    refine ⟨3518090795772158619940729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18763150910784845973017221 3518090795772158619940729)
                    ·
                      refine ⟨2638568096829118964955547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518090795772158619940729 2638568096829118964955547)
                      ·
                        rfl

theorem cell23_5138593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_5138593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138593 prefixEnd_5138593 := by exact prefixLift 5138593
  have htrace : WordTrace (prefixWord ++ tailWord_5138593) baseStart_5138593 baseEnd_5138593 := by
    simpa [prefixWord, tailWord_5138593, baseEnd_5138593] using wordTrace_append hprefix tailTrace_5138593
  have hstable : (prefixWord ++ tailWord_5138593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138593).length < 2 ^ (prefixWord ++ tailWord_5138593).sum := by decide
  have hdescent : baseEnd_5138593 < baseStart_5138593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138619 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6]
def baseStart_5138619 : Nat := 118140960795 + 5138619 * 2 ^ 59
def prefixEnd_5138619 : Nat := 4983230072969 + 3 ^ 40 * 5138619 * 2
def baseEnd_5138619 : Nat := 2638581447326135863230427

theorem tailTrace_5138619 : CollatzResearch.WordTrace tailWord_5138619 prefixEnd_5138619 2638581447326135863230427 := by
  unfold tailWord_5138619
  simp only [CollatzResearch.WordTrace]
  refine ⟨187420832170668444100506911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124947221447112296067004607 187420832170668444100506911)
  ·
    refine ⟨281131248256002666150760367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187420832170668444100506911 281131248256002666150760367)
    ·
      refine ⟨421696872384003999226140551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281131248256002666150760367 421696872384003999226140551)
      ·
        refine ⟨632545308576005998839210827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421696872384003999226140551 632545308576005998839210827)
        ·
          refine ⟨948817962864008998258816241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632545308576005998839210827 948817962864008998258816241)
          ·
            refine ⟨711613472148006748694112181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948817962864008998258816241 711613472148006748694112181)
            ·
              refine ⟨66713763013875632690073017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711613472148006748694112181 66713763013875632690073017)
              ·
                refine ⟨50035322260406724517554763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66713763013875632690073017 50035322260406724517554763)
                ·
                  refine ⟨75052983390610086776332145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50035322260406724517554763 75052983390610086776332145)
                  ·
                    refine ⟨56289737542957565082249109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75052983390610086776332145 56289737542957565082249109)
                    ·
                      refine ⟨2638581447326135863230427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56289737542957565082249109 2638581447326135863230427)
                      ·
                        rfl

theorem cell23_5138619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_5138619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138619 prefixEnd_5138619 := by exact prefixLift 5138619
  have htrace : WordTrace (prefixWord ++ tailWord_5138619) baseStart_5138619 baseEnd_5138619 := by
    simpa [prefixWord, tailWord_5138619, baseEnd_5138619] using wordTrace_append hprefix tailTrace_5138619
  have hstable : (prefixWord ++ tailWord_5138619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138619).length < 2 ^ (prefixWord ++ tailWord_5138619).sum := by decide
  have hdescent : baseEnd_5138619 < baseStart_5138619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138700 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_5138700 : Nat := 118140960795 + 5138700 * 2 ^ 59
def prefixEnd_5138700 : Nat := 4983230072969 + 3 ^ 40 * 5138700 * 2
def baseEnd_5138700 : Nat := 2638623039259150046317555

theorem tailTrace_5138700 : CollatzResearch.WordTrace tailWord_5138700 prefixEnd_5138700 2638623039259150046317555 := by
  unfold tailWord_5138700
  simp only [CollatzResearch.WordTrace]
  refine ⟨93711893241687497467102777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124949190988916663289470369 93711893241687497467102777)
  ·
    refine ⟨70283919931265623100327083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93711893241687497467102777 70283919931265623100327083)
    ·
      refine ⟨105425879896898434650490625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70283919931265623100327083 105425879896898434650490625)
      ·
        refine ⟨79069409922673825987867969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105425879896898434650490625 79069409922673825987867969)
        ·
          refine ⟨59302057442005369490900977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79069409922673825987867969 59302057442005369490900977)
          ·
            refine ⟨44476543081504027118175733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59302057442005369490900977 44476543081504027118175733)
            ·
              refine ⟨4169675913891002542328975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44476543081504027118175733 4169675913891002542328975)
              ·
                refine ⟨6254513870836503813493463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169675913891002542328975 6254513870836503813493463)
                ·
                  refine ⟨9381770806254755720240195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254513870836503813493463 9381770806254755720240195)
                  ·
                    refine ⟨14072656209382133580360293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9381770806254755720240195 14072656209382133580360293)
                    ·
                      refine ⟨2638623039259150046317555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14072656209382133580360293 2638623039259150046317555)
                      ·
                        rfl

theorem cell23_5138700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_5138700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138700 prefixEnd_5138700 := by exact prefixLift 5138700
  have htrace : WordTrace (prefixWord ++ tailWord_5138700) baseStart_5138700 baseEnd_5138700 := by
    simpa [prefixWord, tailWord_5138700, baseEnd_5138700] using wordTrace_append hprefix tailTrace_5138700
  have hstable : (prefixWord ++ tailWord_5138700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138700).length < 2 ^ (prefixWord ++ tailWord_5138700).sum := by decide
  have hdescent : baseEnd_5138700 < baseStart_5138700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138703 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 3]
def baseStart_5138703 : Nat := 118140960795 + 5138703 * 2 ^ 59
def prefixEnd_5138703 : Nat := 4983230072969 + 3 ^ 40 * 5138703 * 2
def baseEnd_5138703 : Nat := 2638624579701113534580041

theorem tailTrace_5138703 : CollatzResearch.WordTrace tailWord_5138703 prefixEnd_5138703 2638624579701113534580041 := by
  unfold tailWord_5138703
  simp only [CollatzResearch.WordTrace]
  refine ⟨187423895902364126446564763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124949263934909417631043175 187423895902364126446564763)
  ·
    refine ⟨281135843853546189669847145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187423895902364126446564763 281135843853546189669847145)
    ·
      refine ⟨210851882890159642252385359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281135843853546189669847145 210851882890159642252385359)
      ·
        refine ⟨316277824335239463378578039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210851882890159642252385359 316277824335239463378578039)
        ·
          refine ⟨474416736502859195067867059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316277824335239463378578039 474416736502859195067867059)
          ·
            refine ⟨711625104754288792601800589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474416736502859195067867059 711625104754288792601800589)
            ·
              refine ⟨266859414282858297225675221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711625104754288792601800589 266859414282858297225675221)
              ·
                refine ⟨6254517522254491341226763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 266859414282858297225675221 6254517522254491341226763)
                ·
                  refine ⟨9381776283381737011840145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254517522254491341226763 9381776283381737011840145)
                  ·
                    refine ⟨7036332212536302758880109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9381776283381737011840145 7036332212536302758880109)
                    ·
                      refine ⟨2638624579701113534580041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036332212536302758880109 2638624579701113534580041)
                      ·
                        rfl

theorem cell23_5138703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_5138703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138703 prefixEnd_5138703 := by exact prefixLift 5138703
  have htrace : WordTrace (prefixWord ++ tailWord_5138703) baseStart_5138703 baseEnd_5138703 := by
    simpa [prefixWord, tailWord_5138703, baseEnd_5138703] using wordTrace_append hprefix tailTrace_5138703
  have hstable : (prefixWord ++ tailWord_5138703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138703).length < 2 ^ (prefixWord ++ tailWord_5138703).sum := by decide
  have hdescent : baseEnd_5138703 < baseStart_5138703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138706 : List Nat := [3, 2, 4, 14]
def baseStart_5138706 : Nat := 118140960795 + 5138706 * 2 ^ 59
def prefixEnd_5138706 : Nat := 4983230072969 + 3 ^ 40 * 5138706 * 2
def baseEnd_5138706 : Nat := 1206504856032499781821

theorem tailTrace_5138706 : CollatzResearch.WordTrace tailWord_5138706 prefixEnd_5138706 1206504856032499781821 := by
  unfold tailWord_5138706
  simp only [CollatzResearch.WordTrace]
  refine ⟨46856001330338314489730993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124949336880902171972615981 46856001330338314489730993)
  ·
    refine ⟨35142000997753735867298245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46856001330338314489730993 35142000997753735867298245)
    ·
      refine ⟨6589125187078825475118421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35142000997753735867298245 6589125187078825475118421)
      ·
        refine ⟨1206504856032499781821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 6589125187078825475118421 1206504856032499781821)
        ·
          rfl

theorem cell23_5138706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 14].length) (baseStart_5138706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138706 prefixEnd_5138706 := by exact prefixLift 5138706
  have htrace : WordTrace (prefixWord ++ tailWord_5138706) baseStart_5138706 baseEnd_5138706 := by
    simpa [prefixWord, tailWord_5138706, baseEnd_5138706] using wordTrace_append hprefix tailTrace_5138706
  have hstable : (prefixWord ++ tailWord_5138706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138706).length < 2 ^ (prefixWord ++ tailWord_5138706).sum := by decide
  have hdescent : baseEnd_5138706 < baseStart_5138706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138740 : List Nat := [2, 5, 1, 1, 1, 3, 3, 7]
def baseStart_5138740 : Nat := 118140960795 + 5138740 * 2 ^ 59
def prefixEnd_5138740 : Nat := 4983230072969 + 3 ^ 40 * 5138740 * 2
def baseEnd_5138740 : Nat := 97727539943901107030273

theorem tailTrace_5138740 : CollatzResearch.WordTrace tailWord_5138740 prefixEnd_5138740 97727539943901107030273 := by
  unfold tailWord_5138740
  simp only [CollatzResearch.WordTrace]
  refine ⟨93712622701615040882830837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124950163602153387843774449 93712622701615040882830837)
  ·
    refine ⟨8785558378276410082765391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 93712622701615040882830837 8785558378276410082765391)
    ·
      refine ⟨13178337567414615124148087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8785558378276410082765391 13178337567414615124148087)
      ·
        refine ⟨19767506351121922686222131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13178337567414615124148087 19767506351121922686222131)
        ·
          refine ⟨29651259526682884029333197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19767506351121922686222131 29651259526682884029333197)
          ·
            refine ⟨11119222322506081510999949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29651259526682884029333197 11119222322506081510999949)
            ·
              refine ⟨4169708370939780566624981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11119222322506081510999949 4169708370939780566624981)
              ·
                refine ⟨97727539943901107030273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4169708370939780566624981 97727539943901107030273)
                ·
                  rfl

theorem cell23_5138740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 7].length) (baseStart_5138740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138740 prefixEnd_5138740 := by exact prefixLift 5138740
  have htrace : WordTrace (prefixWord ++ tailWord_5138740) baseStart_5138740 baseEnd_5138740 := by
    simpa [prefixWord, tailWord_5138740, baseEnd_5138740] using wordTrace_append hprefix tailTrace_5138740
  have hstable : (prefixWord ++ tailWord_5138740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138740).length < 2 ^ (prefixWord ++ tailWord_5138740).sum := by decide
  have hdescent : baseEnd_5138740 < baseStart_5138740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138750 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_5138750 : Nat := 118140960795 + 5138750 * 2 ^ 59
def prefixEnd_5138750 : Nat := 4983230072969 + 3 ^ 40 * 5138750 * 2
def baseEnd_5138750 : Nat := 2638648713291874850692325

theorem tailTrace_5138750 : CollatzResearch.WordTrace tailWord_5138750 prefixEnd_5138750 2638648713291874850692325 := by
  unfold tailWord_5138750
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428201266649231684190713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124950406755462568982350469 23428201266649231684190713)
  ·
    refine ⟨17571150949986923763143035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23428201266649231684190713 17571150949986923763143035)
    ·
      refine ⟨26356726424980385644714553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17571150949986923763143035 26356726424980385644714553)
      ·
        refine ⟨19767544818735289233535915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26356726424980385644714553 19767544818735289233535915)
        ·
          refine ⟨29651317228102933850303873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19767544818735289233535915 29651317228102933850303873)
          ·
            refine ⟨22238487921077200387727905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29651317228102933850303873 22238487921077200387727905)
            ·
              refine ⟨16678865940807900290795929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22238487921077200387727905 16678865940807900290795929)
              ·
                refine ⟨12509149455605925218096947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16678865940807900290795929 12509149455605925218096947)
                ·
                  refine ⟨18763724183408887827145421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12509149455605925218096947 18763724183408887827145421)
                  ·
                    refine ⟨7036396568778332935179533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18763724183408887827145421 7036396568778332935179533)
                    ·
                      refine ⟨2638648713291874850692325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036396568778332935179533 2638648713291874850692325)
                      ·
                        rfl

theorem cell23_5138750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_5138750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138750 prefixEnd_5138750 := by exact prefixLift 5138750
  have htrace : WordTrace (prefixWord ++ tailWord_5138750) baseStart_5138750 baseEnd_5138750 := by
    simpa [prefixWord, tailWord_5138750, baseEnd_5138750] using wordTrace_append hprefix tailTrace_5138750
  have hstable : (prefixWord ++ tailWord_5138750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138750).length < 2 ^ (prefixWord ++ tailWord_5138750).sum := by decide
  have hdescent : baseEnd_5138750 < baseStart_5138750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138776 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_5138776 : Nat := 118140960795 + 5138776 * 2 ^ 59
def prefixEnd_5138776 : Nat := 4983230072969 + 3 ^ 40 * 5138776 * 2
def baseEnd_5138776 : Nat := 2638662063788891748967205

theorem tailTrace_5138776 : CollatzResearch.WordTrace tailWord_5138776 prefixEnd_5138776 2638662063788891748967205 := by
  unfold tailWord_5138776
  simp only [CollatzResearch.WordTrace]
  refine ⟨93713279215549829956986091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124951038954066439942648121 93713279215549829956986091)
  ·
    refine ⟨140569918823324744935479137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93713279215549829956986091 140569918823324744935479137)
    ·
      refine ⟨105427439117493558701609353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140569918823324744935479137 105427439117493558701609353)
      ·
        refine ⟨79070579338120169026207015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105427439117493558701609353 79070579338120169026207015)
        ·
          refine ⟨118605869007180253539310523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79070579338120169026207015 118605869007180253539310523)
          ·
            refine ⟨177908803510770380308965785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118605869007180253539310523 177908803510770380308965785)
            ·
              refine ⟨133431602633077785231724339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177908803510770380308965785 133431602633077785231724339)
              ·
                refine ⟨200147403949616677847586509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133431602633077785231724339 200147403949616677847586509)
                ·
                  refine ⟨75055276481106254192844941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200147403949616677847586509 75055276481106254192844941)
                  ·
                    refine ⟨28145728680414845322316853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75055276481106254192844941 28145728680414845322316853)
                    ·
                      refine ⟨2638662063788891748967205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28145728680414845322316853 2638662063788891748967205)
                      ·
                        rfl

theorem cell23_5138776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_5138776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138776 prefixEnd_5138776 := by exact prefixLift 5138776
  have htrace : WordTrace (prefixWord ++ tailWord_5138776) baseStart_5138776 baseEnd_5138776 := by
    simpa [prefixWord, tailWord_5138776, baseEnd_5138776] using wordTrace_append hprefix tailTrace_5138776
  have hstable : (prefixWord ++ tailWord_5138776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138776).length < 2 ^ (prefixWord ++ tailWord_5138776).sum := by decide
  have hdescent : baseEnd_5138776 < baseStart_5138776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138784 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3]
def baseStart_5138784 : Nat := 118140960795 + 5138784 * 2 ^ 59
def prefixEnd_5138784 : Nat := 4983230072969 + 3 ^ 40 * 5138784 * 2
def baseEnd_5138784 : Nat := 2638666171634127717667169

theorem tailTrace_5138784 : CollatzResearch.WordTrace tailWord_5138784 prefixEnd_5138784 2638666171634127717667169 := by
  unfold tailWord_5138784
  simp only [CollatzResearch.WordTrace]
  refine ⟨93713425107535338640131703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124951233476713784853508937 93713425107535338640131703)
  ·
    refine ⟨140570137661303007960197555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93713425107535338640131703 140570137661303007960197555)
    ·
      refine ⟨210855206491954511940296333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140570137661303007960197555 210855206491954511940296333)
      ·
        refine ⟨79070702434482941977611125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210855206491954511940296333 79070702434482941977611125)
        ·
          refine ⟨7412878353232775810401043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79070702434482941977611125 7412878353232775810401043)
          ·
            refine ⟨11119317529849163715601565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7412878353232775810401043 11119317529849163715601565)
            ·
              refine ⟨4169744073693436393350587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11119317529849163715601565 4169744073693436393350587)
              ·
                refine ⟨6254616110540154590025881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169744073693436393350587 6254616110540154590025881)
                ·
                  refine ⟨4690962082905115942519411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254616110540154590025881 4690962082905115942519411)
                  ·
                    refine ⟨7036443124357673913779117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4690962082905115942519411 7036443124357673913779117)
                    ·
                      refine ⟨2638666171634127717667169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036443124357673913779117 2638666171634127717667169)
                      ·
                        rfl

theorem cell23_5138784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_5138784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138784 prefixEnd_5138784 := by exact prefixLift 5138784
  have htrace : WordTrace (prefixWord ++ tailWord_5138784) baseStart_5138784 baseEnd_5138784 := by
    simpa [prefixWord, tailWord_5138784, baseEnd_5138784] using wordTrace_append hprefix tailTrace_5138784
  have hstable : (prefixWord ++ tailWord_5138784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138784).length < 2 ^ (prefixWord ++ tailWord_5138784).sum := by decide
  have hdescent : baseEnd_5138784 < baseStart_5138784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138794 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_5138794 : Nat := 118140960795 + 5138794 * 2 ^ 59
def prefixEnd_5138794 : Nat := 4983230072969 + 3 ^ 40 * 5138794 * 2
def baseEnd_5138794 : Nat := 2638671306440672678542123

theorem tailTrace_5138794 : CollatzResearch.WordTrace tailWord_5138794 prefixEnd_5138794 2638671306440672678542123 := by
  unfold tailWord_5138794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46856803736258612247031859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124951476630022965992084957 46856803736258612247031859)
  ·
    refine ⟨70285205604387918370547789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46856803736258612247031859 70285205604387918370547789)
    ·
      refine ⟨26356952101645469388955421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70285205604387918370547789 26356952101645469388955421)
      ·
        refine ⟨9883857038117051020858283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26356952101645469388955421 9883857038117051020858283)
        ·
          refine ⟨14825785557175576531287425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883857038117051020858283 14825785557175576531287425)
          ·
            refine ⟨11119339167881682398465569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14825785557175576531287425 11119339167881682398465569)
            ·
              refine ⟨8339504375911261798849177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11119339167881682398465569 8339504375911261798849177)
              ·
                refine ⟨6254628281933446349136883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8339504375911261798849177 6254628281933446349136883)
                ·
                  refine ⟨9381942422900169523705325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254628281933446349136883 9381942422900169523705325)
                  ·
                    refine ⟨3518228408587563571389497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9381942422900169523705325 3518228408587563571389497)
                    ·
                      refine ⟨2638671306440672678542123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518228408587563571389497 2638671306440672678542123)
                      ·
                        rfl

theorem cell23_5138794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_5138794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138794 prefixEnd_5138794 := by exact prefixLift 5138794
  have htrace : WordTrace (prefixWord ++ tailWord_5138794) baseStart_5138794 baseEnd_5138794 := by
    simpa [prefixWord, tailWord_5138794, baseEnd_5138794] using wordTrace_append hprefix tailTrace_5138794
  have hstable : (prefixWord ++ tailWord_5138794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138794).length < 2 ^ (prefixWord ++ tailWord_5138794).sum := by decide
  have hdescent : baseEnd_5138794 < baseStart_5138794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138816 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_5138816 : Nat := 118140960795 + 5138816 * 2 ^ 59
def prefixEnd_5138816 : Nat := 4983230072969 + 3 ^ 40 * 5138816 * 2
def baseEnd_5138816 : Nat := 2638682603015071592467021

theorem tailTrace_5138816 : CollatzResearch.WordTrace tailWord_5138816 prefixEnd_5138816 2638682603015071592467021 := by
  unfold tailWord_5138816
  simp only [CollatzResearch.WordTrace]
  refine ⟨93714008675477373372714151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124952011567303164496952201 93714008675477373372714151)
  ·
    refine ⟨140571013013216060059071227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93714008675477373372714151 140571013013216060059071227)
    ·
      refine ⟨210856519519824090088606841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140571013013216060059071227 210856519519824090088606841)
      ·
        refine ⟨158142389639868067566455131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210856519519824090088606841 158142389639868067566455131)
        ·
          refine ⟨237213584459802101349682697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158142389639868067566455131 237213584459802101349682697)
          ·
            refine ⟨177910188344851576012262023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237213584459802101349682697 177910188344851576012262023)
            ·
              refine ⟨266865282517277364018393035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177910188344851576012262023 266865282517277364018393035)
              ·
                refine ⟨400297923775916046027589553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266865282517277364018393035 400297923775916046027589553)
                ·
                  refine ⟨300223442831937034520692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400297923775916046027589553 300223442831937034520692165)
                  ·
                    refine ⟨56291895530988193972629781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 300223442831937034520692165 56291895530988193972629781)
                    ·
                      refine ⟨2638682603015071592467021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56291895530988193972629781 2638682603015071592467021)
                      ·
                        rfl

theorem cell23_5138816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_5138816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138816 prefixEnd_5138816 := by exact prefixLift 5138816
  have htrace : WordTrace (prefixWord ++ tailWord_5138816) baseStart_5138816 baseEnd_5138816 := by
    simpa [prefixWord, tailWord_5138816, baseEnd_5138816] using wordTrace_append hprefix tailTrace_5138816
  have hstable : (prefixWord ++ tailWord_5138816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138816).length < 2 ^ (prefixWord ++ tailWord_5138816).sum := by decide
  have hdescent : baseEnd_5138816 < baseStart_5138816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138830 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 7]
def baseStart_5138830 : Nat := 118140960795 + 5138830 * 2 ^ 59
def prefixEnd_5138830 : Nat := 4983230072969 + 3 ^ 40 * 5138830 * 2
def baseEnd_5138830 : Nat := 293187754638248281965773

theorem tailTrace_5138830 : CollatzResearch.WordTrace tailWord_5138830 prefixEnd_5138830 293187754638248281965773 := by
  unfold tailWord_5138830
  simp only [CollatzResearch.WordTrace]
  refine ⟨23428565996613003392054743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124952351981936018090958629 23428565996613003392054743)
  ·
    refine ⟨35142848994919505088082115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23428565996613003392054743 35142848994919505088082115)
    ·
      refine ⟨52714273492379257632123173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35142848994919505088082115 52714273492379257632123173)
      ·
        refine ⟨9883926279821110806023095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52714273492379257632123173 9883926279821110806023095)
        ·
          refine ⟨14825889419731666209034643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9883926279821110806023095 14825889419731666209034643)
          ·
            refine ⟨22238834129597499313551965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14825889419731666209034643 22238834129597499313551965)
            ·
              refine ⟨8339562798599062242581987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22238834129597499313551965 8339562798599062242581987)
              ·
                refine ⟨12509344197898593363872981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339562798599062242581987 12509344197898593363872981)
                ·
                  refine ⟨293187754638248281965773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12509344197898593363872981 293187754638248281965773)
                  ·
                    rfl

theorem cell23_5138830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 7].length) (baseStart_5138830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138830 prefixEnd_5138830 := by exact prefixLift 5138830
  have htrace : WordTrace (prefixWord ++ tailWord_5138830) baseStart_5138830 baseEnd_5138830 := by
    simpa [prefixWord, tailWord_5138830, baseEnd_5138830] using wordTrace_append hprefix tailTrace_5138830
  have hstable : (prefixWord ++ tailWord_5138830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138830).length < 2 ^ (prefixWord ++ tailWord_5138830).sum := by decide
  have hdescent : baseEnd_5138830 < baseStart_5138830 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138880 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2]
def baseStart_5138880 : Nat := 118140960795 + 5138880 * 2 ^ 59
def prefixEnd_5138880 : Nat := 4983230072969 + 3 ^ 40 * 5138880 * 2
def baseEnd_5138880 : Nat := 2638715465776959342066727

theorem tailTrace_5138880 : CollatzResearch.WordTrace tailWord_5138880 prefixEnd_5138880 2638715465776959342066727 := by
  unfold tailWord_5138880
  simp only [CollatzResearch.WordTrace]
  refine ⟨93715175811361442837879047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124953567748481923783838729 93715175811361442837879047)
  ·
    refine ⟨140572763717042164256818571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93715175811361442837879047 140572763717042164256818571)
    ·
      refine ⟨210859145575563246385227857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140572763717042164256818571 210859145575563246385227857)
      ·
        refine ⟨158144359181672434788920893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210859145575563246385227857 158144359181672434788920893)
        ·
          refine ⟨59304134693127163045845335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158144359181672434788920893 59304134693127163045845335)
          ·
            refine ⟨88956202039690744568768003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59304134693127163045845335 88956202039690744568768003)
            ·
              refine ⟨133434303059536116853152005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88956202039690744568768003 133434303059536116853152005)
              ·
                refine ⟨25018931823663021909966001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133434303059536116853152005 25018931823663021909966001)
                ·
                  refine ⟨18764198867747266432474501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25018931823663021909966001 18764198867747266432474501)
                  ·
                    refine ⟨3518287287702612456088969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18764198867747266432474501 3518287287702612456088969)
                    ·
                      refine ⟨2638715465776959342066727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518287287702612456088969 2638715465776959342066727)
                      ·
                        rfl

theorem cell23_5138880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_5138880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138880 prefixEnd_5138880 := by exact prefixLift 5138880
  have htrace : WordTrace (prefixWord ++ tailWord_5138880) baseStart_5138880 baseEnd_5138880 := by
    simpa [prefixWord, tailWord_5138880, baseEnd_5138880] using wordTrace_append hprefix tailTrace_5138880
  have hstable : (prefixWord ++ tailWord_5138880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138880).length < 2 ^ (prefixWord ++ tailWord_5138880).sum := by decide
  have hdescent : baseEnd_5138880 < baseStart_5138880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138881 : List Nat := [1, 2, 7, 1, 1, 1, 1, 4, 5]
def baseStart_5138881 : Nat := 118140960795 + 5138881 * 2 ^ 59
def prefixEnd_5138881 : Nat := 4983230072969 + 3 ^ 40 * 5138881 * 2
def baseEnd_5138881 : Nat := 293190664361957093128247

theorem tailTrace_5138881 : CollatzResearch.WordTrace tailWord_5138881 prefixEnd_5138881 293190664361957093128247 := by
  unfold tailWord_5138881
  simp only [CollatzResearch.WordTrace]
  refine ⟨187430388095719262846544497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124953592063812841897696331 187430388095719262846544497)
  ·
    refine ⟨140572791071789447134908373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187430388095719262846544497 140572791071789447134908373)
    ·
      refine ⟨3294674790745065167224415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 140572791071789447134908373 3294674790745065167224415)
      ·
        refine ⟨4942012186117597750836623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3294674790745065167224415 4942012186117597750836623)
        ·
          refine ⟨7413018279176396626254935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942012186117597750836623 7413018279176396626254935)
          ·
            refine ⟨11119527418764594939382403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413018279176396626254935 11119527418764594939382403)
            ·
              refine ⟨16679291128146892409073605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119527418764594939382403 16679291128146892409073605)
              ·
                refine ⟨3127367086527542326701301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16679291128146892409073605 3127367086527542326701301)
                ·
                  refine ⟨293190664361957093128247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3127367086527542326701301 293190664361957093128247)
                  ·
                    rfl

theorem cell23_5138881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 4, 5].length) (baseStart_5138881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138881 prefixEnd_5138881 := by exact prefixLift 5138881
  have htrace : WordTrace (prefixWord ++ tailWord_5138881) baseStart_5138881 baseEnd_5138881 := by
    simpa [prefixWord, tailWord_5138881, baseEnd_5138881] using wordTrace_append hprefix tailTrace_5138881
  have hstable : (prefixWord ++ tailWord_5138881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138881).length < 2 ^ (prefixWord ++ tailWord_5138881).sum := by decide
  have hdescent : baseEnd_5138881 < baseStart_5138881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138883 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3]
def baseStart_5138883 : Nat := 118140960795 + 5138883 * 2 ^ 59
def prefixEnd_5138883 : Nat := 4983230072969 + 3 ^ 40 * 5138883 * 2
def baseEnd_5138883 : Nat := 2638717006218922830329213

theorem tailTrace_5138883 : CollatzResearch.WordTrace tailWord_5138883 prefixEnd_5138883 2638717006218922830329213 := by
  unfold tailWord_5138883
  simp only [CollatzResearch.WordTrace]
  refine ⟨187430461041712017188117303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124953640694474678125411535 187430461041712017188117303)
  ·
    refine ⟨281145691562568025782175955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187430461041712017188117303 281145691562568025782175955)
    ·
      refine ⟨421718537343852038673263933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281145691562568025782175955 421718537343852038673263933)
      ·
        refine ⟨158144451503944514502473975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421718537343852038673263933 158144451503944514502473975)
        ·
          refine ⟨237216677255916771753710963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158144451503944514502473975 237216677255916771753710963)
          ·
            refine ⟨355825015883875157630566445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237216677255916771753710963 355825015883875157630566445)
            ·
              refine ⟨133434380956453184111462417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355825015883875157630566445 133434380956453184111462417)
              ·
                refine ⟨100075785717339888083596813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133434380956453184111462417 100075785717339888083596813)
                ·
                  refine ⟨37528419644002458031348805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100075785717339888083596813 37528419644002458031348805)
                  ·
                    refine ⟨7036578683250460880877901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37528419644002458031348805 7036578683250460880877901)
                    ·
                      refine ⟨2638717006218922830329213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036578683250460880877901 2638717006218922830329213)
                      ·
                        rfl

theorem cell23_5138883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_5138883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138883 prefixEnd_5138883 := by exact prefixLift 5138883
  have htrace : WordTrace (prefixWord ++ tailWord_5138883) baseStart_5138883 baseEnd_5138883 := by
    simpa [prefixWord, tailWord_5138883, baseEnd_5138883] using wordTrace_append hprefix tailTrace_5138883
  have hstable : (prefixWord ++ tailWord_5138883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138883).length < 2 ^ (prefixWord ++ tailWord_5138883).sum := by decide
  have hdescent : baseEnd_5138883 < baseStart_5138883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138890 : List Nat := [3, 1, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_5138890 : Nat := 118140960795 + 5138890 * 2 ^ 59
def prefixEnd_5138890 : Nat := 4983230072969 + 3 ^ 40 * 5138890 * 2
def baseEnd_5138890 : Nat := 879573533527834767647227

theorem tailTrace_5138890 : CollatzResearch.WordTrace tailWord_5138890 prefixEnd_5138890 879573533527834767647227 := by
  unfold tailWord_5138890
  simp only [CollatzResearch.WordTrace]
  refine ⟨46857679088171664345905531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124953810901791104922414749 46857679088171664345905531)
  ·
    refine ⟨70286518632257496518858297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46857679088171664345905531 70286518632257496518858297)
    ·
      refine ⟨52714888974193122389143723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70286518632257496518858297 52714888974193122389143723)
      ·
        refine ⟨79072333461289683583715585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52714888974193122389143723 79072333461289683583715585)
        ·
          refine ⟨59304250095967262687786689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79072333461289683583715585 59304250095967262687786689)
          ·
            refine ⟨44478187571975447015840017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59304250095967262687786689 44478187571975447015840017)
            ·
              refine ⟨33358640678981585261880013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44478187571975447015840017 33358640678981585261880013)
              ·
                refine ⟨12509490254618094473205005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33358640678981585261880013 12509490254618094473205005)
                ·
                  refine ⟨4691058845481785427451877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12509490254618094473205005 4691058845481785427451877)
                  ·
                    refine ⟨879573533527834767647227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691058845481785427451877 879573533527834767647227)
                    ·
                      rfl

theorem cell23_5138890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_5138890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138890 prefixEnd_5138890 := by exact prefixLift 5138890
  have htrace : WordTrace (prefixWord ++ tailWord_5138890) baseStart_5138890 baseEnd_5138890 := by
    simpa [prefixWord, tailWord_5138890, baseEnd_5138890] using wordTrace_append hprefix tailTrace_5138890
  have hstable : (prefixWord ++ tailWord_5138890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138890).length < 2 ^ (prefixWord ++ tailWord_5138890).sum := by decide
  have hdescent : baseEnd_5138890 < baseStart_5138890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138914 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5138914 : Nat := 118140960795 + 5138914 * 2 ^ 59
def prefixEnd_5138914 : Nat := 4983230072969 + 3 ^ 40 * 5138914 * 2
def baseEnd_5138914 : Nat := 2638732924119212209041571

theorem tailTrace_5138914 : CollatzResearch.WordTrace tailWord_5138914 prefixEnd_5138914 2638732924119212209041571 := by
  unfold tailWord_5138914
  simp only [CollatzResearch.WordTrace]
  refine ⟨46857897926149927370623949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124954394469733139654997197 46857897926149927370623949)
  ·
    refine ⟨17571711722306222763983981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46857897926149927370623949 17571711722306222763983981)
    ·
      refine ⟨6589391895864833536493993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17571711722306222763983981 6589391895864833536493993)
      ·
        refine ⟨4942043921898625152370495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6589391895864833536493993 4942043921898625152370495)
        ·
          refine ⟨7413065882847937728555743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942043921898625152370495 7413065882847937728555743)
          ·
            refine ⟨11119598824271906592833615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413065882847937728555743 11119598824271906592833615)
            ·
              refine ⟨16679398236407859889250423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119598824271906592833615 16679398236407859889250423)
              ·
                refine ⟨25019097354611789833875635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16679398236407859889250423 25019097354611789833875635)
                ·
                  refine ⟨37528646031917684750813453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25019097354611789833875635 37528646031917684750813453)
                  ·
                    refine ⟨14073242261969131781555045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37528646031917684750813453 14073242261969131781555045)
                    ·
                      refine ⟨2638732924119212209041571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14073242261969131781555045 2638732924119212209041571)
                      ·
                        rfl

theorem cell23_5138914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5138914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138914 prefixEnd_5138914 := by exact prefixLift 5138914
  have htrace : WordTrace (prefixWord ++ tailWord_5138914) baseStart_5138914 baseEnd_5138914 := by
    simpa [prefixWord, tailWord_5138914, baseEnd_5138914] using wordTrace_append hprefix tailTrace_5138914
  have hstable : (prefixWord ++ tailWord_5138914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138914).length < 2 ^ (prefixWord ++ tailWord_5138914).sum := by decide
  have hdescent : baseEnd_5138914 < baseStart_5138914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138917 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5138917 : Nat := 118140960795 + 5138917 * 2 ^ 59
def prefixEnd_5138917 : Nat := 4983230072969 + 3 ^ 40 * 5138917 * 2
def baseEnd_5138917 : Nat := 2638734464561175697304057

theorem tailTrace_5138917 : CollatzResearch.WordTrace tailWord_5138917 prefixEnd_5138917 2638734464561175697304057 := by
  unfold tailWord_5138917
  simp only [CollatzResearch.WordTrace]
  refine ⟨187431701123588840994855005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124954467415725893996570003 187431701123588840994855005)
  ·
    refine ⟨70286887921345815373070627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187431701123588840994855005 70286887921345815373070627)
    ·
      refine ⟨105430331882018723059605941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70286887921345815373070627 105430331882018723059605941)
      ·
        refine ⟨9884093613939255286838057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105430331882018723059605941 9884093613939255286838057)
        ·
          refine ⟨7413070210454441465128543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9884093613939255286838057 7413070210454441465128543)
          ·
            refine ⟨11119605315681662197692815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413070210454441465128543 11119605315681662197692815)
            ·
              refine ⟨16679407973522493296539223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119605315681662197692815 16679407973522493296539223)
              ·
                refine ⟨25019111960283739944808835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16679407973522493296539223 25019111960283739944808835)
                ·
                  refine ⟨37528667940425609917213253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25019111960283739944808835 37528667940425609917213253)
                  ·
                    refine ⟨7036625238829801859477485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37528667940425609917213253 7036625238829801859477485)
                    ·
                      refine ⟨2638734464561175697304057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036625238829801859477485 2638734464561175697304057)
                      ·
                        rfl

theorem cell23_5138917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5138917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138917 prefixEnd_5138917 := by exact prefixLift 5138917
  have htrace : WordTrace (prefixWord ++ tailWord_5138917) baseStart_5138917 baseEnd_5138917 := by
    simpa [prefixWord, tailWord_5138917, baseEnd_5138917] using wordTrace_append hprefix tailTrace_5138917
  have hstable : (prefixWord ++ tailWord_5138917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138917).length < 2 ^ (prefixWord ++ tailWord_5138917).sum := by decide
  have hdescent : baseEnd_5138917 < baseStart_5138917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138947 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 3]
def baseStart_5138947 : Nat := 118140960795 + 5138947 * 2 ^ 59
def prefixEnd_5138947 : Nat := 4983230072969 + 3 ^ 40 * 5138947 * 2
def baseEnd_5138947 : Nat := 2638749868980810579928919

theorem tailTrace_5138947 : CollatzResearch.WordTrace tailWord_5138947 prefixEnd_5138947 2638749868980810579928919 := by
  unfold tailWord_5138947
  simp only [CollatzResearch.WordTrace]
  refine ⟨187432795313480156118447095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124955196875653437412298063 187432795313480156118447095)
  ·
    refine ⟨281149192970220234177670643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187432795313480156118447095 281149192970220234177670643)
    ·
      refine ⟨421723789455330351266505965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281149192970220234177670643 421723789455330351266505965)
      ·
        refine ⟨158146421045748881724939737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421723789455330351266505965 158146421045748881724939737)
        ·
          refine ⟨118609815784311661293704803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158146421045748881724939737 118609815784311661293704803)
          ·
            refine ⟨177914723676467491940557205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118609815784311661293704803 177914723676467491940557205)
            ·
              refine ⟨8339752672334413684713619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177914723676467491940557205 8339752672334413684713619)
              ·
                refine ⟨12509629008501620527070429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8339752672334413684713619 12509629008501620527070429)
                ·
                  refine ⟨4691110878188107697651411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12509629008501620527070429 4691110878188107697651411)
                  ·
                    refine ⟨7036666317282161546477117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691110878188107697651411 7036666317282161546477117)
                    ·
                      refine ⟨2638749868980810579928919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036666317282161546477117 2638749868980810579928919)
                      ·
                        rfl

theorem cell23_5138947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_5138947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138947 prefixEnd_5138947 := by exact prefixLift 5138947
  have htrace : WordTrace (prefixWord ++ tailWord_5138947) baseStart_5138947 baseEnd_5138947 := by
    simpa [prefixWord, tailWord_5138947, baseEnd_5138947] using wordTrace_append hprefix tailTrace_5138947
  have hstable : (prefixWord ++ tailWord_5138947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138947).length < 2 ^ (prefixWord ++ tailWord_5138947).sum := by decide
  have hdescent : baseEnd_5138947 < baseStart_5138947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138953 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_5138953 : Nat := 118140960795 + 5138953 * 2 ^ 59
def prefixEnd_5138953 : Nat := 4983230072969 + 3 ^ 40 * 5138953 * 2
def baseEnd_5138953 : Nat := 2638752949864737556453891

theorem tailTrace_5138953 : CollatzResearch.WordTrace tailWord_5138953 prefixEnd_5138953 2638752949864737556453891 := by
  unfold tailWord_5138953
  simp only [CollatzResearch.WordTrace]
  refine ⟨187433014151458419143165513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124955342767638946095443675 187433014151458419143165513)
  ·
    refine ⟨140574760613593814357374135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187433014151458419143165513 140574760613593814357374135)
    ·
      refine ⟨210862140920390721536061203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140574760613593814357374135 210862140920390721536061203)
      ·
        refine ⟨316293211380586082304091805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210862140920390721536061203 316293211380586082304091805)
        ·
          refine ⟨118609954267719780864034427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316293211380586082304091805 118609954267719780864034427)
          ·
            refine ⟨177914931401579671296051641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118609954267719780864034427 177914931401579671296051641)
            ·
              refine ⟨133436198551184753472038731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177914931401579671296051641 133436198551184753472038731)
              ·
                refine ⟨200154297826777130208058097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133436198551184753472038731 200154297826777130208058097)
                ·
                  refine ⟨150115723370082847656043573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200154297826777130208058097 150115723370082847656043573)
                  ·
                    refine ⟨14073349065945266967754085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 150115723370082847656043573 14073349065945266967754085)
                    ·
                      refine ⟨2638752949864737556453891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14073349065945266967754085 2638752949864737556453891)
                      ·
                        rfl

theorem cell23_5138953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_5138953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138953 prefixEnd_5138953 := by exact prefixLift 5138953
  have htrace : WordTrace (prefixWord ++ tailWord_5138953) baseStart_5138953 baseEnd_5138953 := by
    simpa [prefixWord, tailWord_5138953, baseEnd_5138953] using wordTrace_append hprefix tailTrace_5138953
  have hstable : (prefixWord ++ tailWord_5138953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138953).length < 2 ^ (prefixWord ++ tailWord_5138953).sum := by decide
  have hdescent : baseEnd_5138953 < baseStart_5138953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138970 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_5138970 : Nat := 118140960795 + 5138970 * 2 ^ 59
def prefixEnd_5138970 : Nat := 4983230072969 + 3 ^ 40 * 5138970 * 2
def baseEnd_5138970 : Nat := 2638761679035863989941313

theorem tailTrace_5138970 : CollatzResearch.WordTrace tailWord_5138970 prefixEnd_5138970 2638761679035863989941313 := by
  unfold tailWord_5138970
  simp only [CollatzResearch.WordTrace]
  refine ⟨46858408548099207761633591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124955756128264554031022909 46858408548099207761633591)
  ·
    refine ⟨70287612822148811642450387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46858408548099207761633591 70287612822148811642450387)
    ·
      refine ⟨105431419233223217463675581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70287612822148811642450387 105431419233223217463675581)
      ·
        refine ⟨39536782212458706548878343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105431419233223217463675581 39536782212458706548878343)
        ·
          refine ⟨59305173318688059823317515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39536782212458706548878343 59305173318688059823317515)
          ·
            refine ⟨88957759978032089734976273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59305173318688059823317515 88957759978032089734976273)
            ·
              refine ⟨66718319983524067301232205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88957759978032089734976273 66718319983524067301232205)
              ·
                refine ⟨25019369993821525237962077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66718319983524067301232205 25019369993821525237962077)
                ·
                  refine ⟨9382263747683071964235779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25019369993821525237962077 9382263747683071964235779)
                  ·
                    refine ⟨14073395621524607946353669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9382263747683071964235779 14073395621524607946353669)
                    ·
                      refine ⟨2638761679035863989941313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14073395621524607946353669 2638761679035863989941313)
                      ·
                        rfl

theorem cell23_5138970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_5138970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138970 prefixEnd_5138970 := by exact prefixLift 5138970
  have htrace : WordTrace (prefixWord ++ tailWord_5138970) baseStart_5138970 baseEnd_5138970 := by
    simpa [prefixWord, tailWord_5138970, baseEnd_5138970] using wordTrace_append hprefix tailTrace_5138970
  have hstable : (prefixWord ++ tailWord_5138970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138970).length < 2 ^ (prefixWord ++ tailWord_5138970).sum := by decide
  have hdescent : baseEnd_5138970 < baseStart_5138970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138987 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 5, 2, 2]
def baseStart_5138987 : Nat := 118140960795 + 5138987 * 2 ^ 59
def prefixEnd_5138987 : Nat := 4983230072969 + 3 ^ 40 * 5138987 * 2
def baseEnd_5138987 : Nat := 2638770408206990423428735

theorem tailTrace_5138987 : CollatzResearch.WordTrace tailWord_5138987 prefixEnd_5138987 2638770408206990423428735 := by
  unfold tailWord_5138987
  simp only [CollatzResearch.WordTrace]
  refine ⟨187434254233335242949903215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124956169488890161966602143 187434254233335242949903215)
  ·
    refine ⟨281151381350002864424854823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187434254233335242949903215 281151381350002864424854823)
    ·
      refine ⟨421727072025004296637282235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281151381350002864424854823 421727072025004296637282235)
      ·
        refine ⟨632590608037506444955923353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421727072025004296637282235 632590608037506444955923353)
        ·
          refine ⟨474442956028129833716942515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632590608037506444955923353 474442956028129833716942515)
          ·
            refine ⟨711664434042194750575413773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474442956028129833716942515 711664434042194750575413773)
            ·
              refine ⟨266874162765823031465780165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711664434042194750575413773 266874162765823031465780165)
              ·
                refine ⟨50038905518591818399833781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266874162765823031465780165 50038905518591818399833781)
                ·
                  refine ⟨4691147392367982974984417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50038905518591818399833781 4691147392367982974984417)
                  ·
                    refine ⟨3518360544275987231238313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691147392367982974984417 3518360544275987231238313)
                    ·
                      refine ⟨2638770408206990423428735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518360544275987231238313 2638770408206990423428735)
                      ·
                        rfl

theorem cell23_5138987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5, 2, 2].length) (baseStart_5138987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138987 prefixEnd_5138987 := by exact prefixLift 5138987
  have htrace : WordTrace (prefixWord ++ tailWord_5138987) baseStart_5138987 baseEnd_5138987 := by
    simpa [prefixWord, tailWord_5138987, baseEnd_5138987] using wordTrace_append hprefix tailTrace_5138987
  have hstable : (prefixWord ++ tailWord_5138987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138987).length < 2 ^ (prefixWord ++ tailWord_5138987).sum := by decide
  have hdescent : baseEnd_5138987 < baseStart_5138987 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138993 : List Nat := [1, 2, 2, 3, 1, 1, 13]
def baseStart_5138993 : Nat := 118140960795 + 5138993 * 2 ^ 59
def prefixEnd_5138993 : Nat := 4983230072969 + 3 ^ 40 * 5138993 * 2
def baseEnd_5138993 : Nat := 32577450482603918517947

theorem tailTrace_5138993 : CollatzResearch.WordTrace tailWord_5138993 prefixEnd_5138993 32577450482603918517947 := by
  unfold tailWord_5138993
  simp only [CollatzResearch.WordTrace]
  refine ⟨187434473071313505974621633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124956315380875670649747755 187434473071313505974621633)
  ·
    refine ⟨140575854803485129480966225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187434473071313505974621633 140575854803485129480966225)
    ·
      refine ⟨105431891102613847110724669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140575854803485129480966225 105431891102613847110724669)
      ·
        refine ⟨39536959163480192666521751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105431891102613847110724669 39536959163480192666521751)
        ·
          refine ⟨59305438745220288999782627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39536959163480192666521751 59305438745220288999782627)
          ·
            refine ⟨88958158117830433499673941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59305438745220288999782627 88958158117830433499673941)
            ·
              refine ⟨32577450482603918517947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 88958158117830433499673941 32577450482603918517947)
              ·
                rfl

theorem cell23_5138993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 13].length) (baseStart_5138993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138993 prefixEnd_5138993 := by exact prefixLift 5138993
  have htrace : WordTrace (prefixWord ++ tailWord_5138993) baseStart_5138993 baseEnd_5138993 := by
    simpa [prefixWord, tailWord_5138993, baseEnd_5138993] using wordTrace_append hprefix tailTrace_5138993
  have hstable : (prefixWord ++ tailWord_5138993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138993).length < 2 ^ (prefixWord ++ tailWord_5138993).sum := by decide
  have hdescent : baseEnd_5138993 < baseStart_5138993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5138997 : List Nat := [1, 3, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_5138997 : Nat := 118140960795 + 5138997 * 2 ^ 59
def prefixEnd_5138997 : Nat := 4983230072969 + 3 ^ 40 * 5138997 * 2
def baseEnd_5138997 : Nat := 879591847671178461434563

theorem tailTrace_5138997 : CollatzResearch.WordTrace tailWord_5138997 prefixEnd_5138997 879591847671178461434563 := by
  unfold tailWord_5138997
  simp only [CollatzResearch.WordTrace]
  refine ⟨187434618963299014657767245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124956412642199343105178163 187434618963299014657767245)
  ·
    refine ⟨70287982111237130496662717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187434618963299014657767245 70287982111237130496662717)
    ·
      refine ⟨26357993291713923936248519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70287982111237130496662717 26357993291713923936248519)
      ·
        refine ⟨39536989937570885904372779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26357993291713923936248519 39536989937570885904372779)
        ·
          refine ⟨59305484906356328856559169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39536989937570885904372779 59305484906356328856559169)
          ·
            refine ⟨44479113679767246642419377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59305484906356328856559169 44479113679767246642419377)
            ·
              refine ⟨33359335259825434981814533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44479113679767246642419377 33359335259825434981814533)
              ·
                refine ⟨6254875361217269059090225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33359335259825434981814533 6254875361217269059090225)
                ·
                  refine ⟨4691156520912951794317669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6254875361217269059090225 4691156520912951794317669)
                  ·
                    refine ⟨879591847671178461434563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691156520912951794317669 879591847671178461434563)
                    ·
                      rfl

theorem cell23_5138997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_5138997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5138997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5138997 prefixEnd_5138997 := by exact prefixLift 5138997
  have htrace : WordTrace (prefixWord ++ tailWord_5138997) baseStart_5138997 baseEnd_5138997 := by
    simpa [prefixWord, tailWord_5138997, baseEnd_5138997] using wordTrace_append hprefix tailTrace_5138997
  have hstable : (prefixWord ++ tailWord_5138997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5138997).length < 2 ^ (prefixWord ++ tailWord_5138997).sum := by decide
  have hdescent : baseEnd_5138997 < baseStart_5138997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5138997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139021 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_5139021 : Nat := 118140960795 + 5139021 * 2 ^ 59
def prefixEnd_5139021 : Nat := 4983230072969 + 3 ^ 40 * 5139021 * 2
def baseEnd_5139021 : Nat := 2638787866549243290403579

theorem tailTrace_5139021 : CollatzResearch.WordTrace tailWord_5139021 prefixEnd_5139021 2638787866549243290403579 := by
  unfold tailWord_5139021
  simp only [CollatzResearch.WordTrace]
  refine ⟨187435494315212066756640917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124956996210141377837760611 187435494315212066756640917)
  ·
    refine ⟨8786038796025565629217543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187435494315212066756640917 8786038796025565629217543)
    ·
      refine ⟨13179058194038348443826315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8786038796025565629217543 13179058194038348443826315)
      ·
        refine ⟨19768587291057522665739473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179058194038348443826315 19768587291057522665739473)
        ·
          refine ⟨14826440468293141999304605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19768587291057522665739473 14826440468293141999304605)
          ·
            refine ⟨5559915175609928249739227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14826440468293141999304605 5559915175609928249739227)
            ·
              refine ⟨8339872763414892374608841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5559915175609928249739227 8339872763414892374608841)
              ·
                refine ⟨6254904572561169280956631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8339872763414892374608841 6254904572561169280956631)
                ·
                  refine ⟨9382356858841753921434947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254904572561169280956631 9382356858841753921434947)
                  ·
                    refine ⟨14073535288262630882152421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9382356858841753921434947 14073535288262630882152421)
                    ·
                      refine ⟨2638787866549243290403579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14073535288262630882152421 2638787866549243290403579)
                      ·
                        rfl

theorem cell23_5139021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_5139021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139021 prefixEnd_5139021 := by exact prefixLift 5139021
  have htrace : WordTrace (prefixWord ++ tailWord_5139021) baseStart_5139021 baseEnd_5139021 := by
    simpa [prefixWord, tailWord_5139021, baseEnd_5139021] using wordTrace_append hprefix tailTrace_5139021
  have hstable : (prefixWord ++ tailWord_5139021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139021).length < 2 ^ (prefixWord ++ tailWord_5139021).sum := by decide
  have hdescent : baseEnd_5139021 < baseStart_5139021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139098 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5139098 : Nat := 118140960795 + 5139098 * 2 ^ 59
def prefixEnd_5139098 : Nat := 4983230072969 + 3 ^ 40 * 5139098 * 2
def baseEnd_5139098 : Nat := 2638827404559639489140725

theorem tailTrace_5139098 : CollatzResearch.WordTrace tailWord_5139098 prefixEnd_5139098 2638827404559639489140725 := by
  unfold tailWord_5139098
  simp only [CollatzResearch.WordTrace]
  refine ⟨46859575683983277226798487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124958868490622072604795965 46859575683983277226798487)
  ·
    refine ⟨70289363525974915840197731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46859575683983277226798487 70289363525974915840197731)
    ·
      refine ⟨105434045288962373760296597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70289363525974915840197731 105434045288962373760296597)
      ·
        refine ⟨4942220872920111270013903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 105434045288962373760296597 4942220872920111270013903)
        ·
          refine ⟨7413331309380166905020855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4942220872920111270013903 7413331309380166905020855)
          ·
            refine ⟨11119996964070250357531283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7413331309380166905020855 11119996964070250357531283)
            ·
              refine ⟨16679995446105375536296925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11119996964070250357531283 16679995446105375536296925)
              ·
                refine ⟨6254998292289515826111347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16679995446105375536296925 6254998292289515826111347)
                ·
                  refine ⟨9382497438434273739167021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6254998292289515826111347 9382497438434273739167021)
                  ·
                    refine ⟨3518436539412852652187633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9382497438434273739167021 3518436539412852652187633)
                    ·
                      refine ⟨2638827404559639489140725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518436539412852652187633 2638827404559639489140725)
                      ·
                        rfl

theorem cell23_5139098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5139098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139098 prefixEnd_5139098 := by exact prefixLift 5139098
  have htrace : WordTrace (prefixWord ++ tailWord_5139098) baseStart_5139098 baseEnd_5139098 := by
    simpa [prefixWord, tailWord_5139098, baseEnd_5139098] using wordTrace_append hprefix tailTrace_5139098
  have hstable : (prefixWord ++ tailWord_5139098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139098).length < 2 ^ (prefixWord ++ tailWord_5139098).sum := by decide
  have hdescent : baseEnd_5139098 < baseStart_5139098 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139117 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 7]
def baseStart_5139117 : Nat := 118140960795 + 5139117 * 2 ^ 59
def prefixEnd_5139117 : Nat := 4983230072969 + 3 ^ 40 * 5139117 * 2
def baseEnd_5139117 : Nat := 293204128965786101644793

theorem tailTrace_5139117 : CollatzResearch.WordTrace tailWord_5139117 prefixEnd_5139117 293204128965786101644793 := by
  unfold tailWord_5139117
  simp only [CollatzResearch.WordTrace]
  refine ⟨187438995722864275152135605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124959330481909516768090403 187438995722864275152135605)
  ·
    refine ⟨17572405849018525795512713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187438995722864275152135605 17572405849018525795512713)
    ·
      refine ⟨13179304386763894346634535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17572405849018525795512713 13179304386763894346634535)
      ·
        refine ⟨19768956580145841519951803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13179304386763894346634535 19768956580145841519951803)
        ·
          refine ⟨29653434870218762279927705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19768956580145841519951803 29653434870218762279927705)
          ·
            refine ⟨22240076152664071709945779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29653434870218762279927705 22240076152664071709945779)
            ·
              refine ⟨33360114228996107564918669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22240076152664071709945779 33360114228996107564918669)
              ·
                refine ⟨12510042835873540336844501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33360114228996107564918669 12510042835873540336844501)
                ·
                  refine ⟨293204128965786101644793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12510042835873540336844501 293204128965786101644793)
                  ·
                    rfl

theorem cell23_5139117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_5139117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139117 prefixEnd_5139117 := by exact prefixLift 5139117
  have htrace : WordTrace (prefixWord ++ tailWord_5139117) baseStart_5139117 baseEnd_5139117 := by
    simpa [prefixWord, tailWord_5139117, baseEnd_5139117] using wordTrace_append hprefix tailTrace_5139117
  have hstable : (prefixWord ++ tailWord_5139117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139117).length < 2 ^ (prefixWord ++ tailWord_5139117).sum := by decide
  have hdescent : baseEnd_5139117 < baseStart_5139117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139130 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_5139130 : Nat := 118140960795 + 5139130 * 2 ^ 59
def prefixEnd_5139130 : Nat := 4983230072969 + 3 ^ 40 * 5139130 * 2
def baseEnd_5139130 : Nat := 879614611980194454646859

theorem tailTrace_5139130 : CollatzResearch.WordTrace tailWord_5139130 prefixEnd_5139130 879614611980194454646859 := by
  unfold tailWord_5139130
  simp only [CollatzResearch.WordTrace]
  refine ⟨46859867467954294593089711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124959646581211452248239229 46859867467954294593089711)
  ·
    refine ⟨70289801201931441889634567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46859867467954294593089711 70289801201931441889634567)
    ·
      refine ⟨105434701802897162834451851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70289801201931441889634567 105434701802897162834451851)
      ·
        refine ⟨158152052704345744251677777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105434701802897162834451851 158152052704345744251677777)
        ·
          refine ⟨118614039528259308188758333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158152052704345744251677777 118614039528259308188758333)
          ·
            refine ⟨44480264823097240570784375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118614039528259308188758333 44480264823097240570784375)
            ·
              refine ⟨66720397234645860856176563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44480264823097240570784375 66720397234645860856176563)
              ·
                refine ⟨100080595851968791284264845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66720397234645860856176563 100080595851968791284264845)
                ·
                  refine ⟨37530223444488296731599317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100080595851968791284264845 37530223444488296731599317)
                  ·
                    refine ⟨879614611980194454646859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 37530223444488296731599317 879614611980194454646859)
                    ·
                      rfl

theorem cell23_5139130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_5139130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139130 prefixEnd_5139130 := by exact prefixLift 5139130
  have htrace : WordTrace (prefixWord ++ tailWord_5139130) baseStart_5139130 baseEnd_5139130 := by
    simpa [prefixWord, tailWord_5139130, baseEnd_5139130] using wordTrace_append hprefix tailTrace_5139130
  have hstable : (prefixWord ++ tailWord_5139130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139130).length < 2 ^ (prefixWord ++ tailWord_5139130).sum := by decide
  have hdescent : baseEnd_5139130 < baseStart_5139130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139164 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5139164 : Nat := 118140960795 + 5139164 * 2 ^ 59
def prefixEnd_5139164 : Nat := 4983230072969 + 3 ^ 40 * 5139164 * 2
def baseEnd_5139164 : Nat := 879620431427612076971807

theorem tailTrace_5139164 : CollatzResearch.WordTrace tailWord_5139164 prefixEnd_5139164 879620431427612076971807 := by
  unfold tailWord_5139164
  simp only [CollatzResearch.WordTrace]
  refine ⟨93720354976847001089548273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124960473302462668119397697 93720354976847001089548273)
  ·
    refine ⟨70290266232635250817161205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93720354976847001089548273 70290266232635250817161205)
    ·
      refine ⟨6589712459309554764108863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70290266232635250817161205 6589712459309554764108863)
      ·
        refine ⟨9884568688964332146163295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6589712459309554764108863 9884568688964332146163295)
        ·
          refine ⟨14826853033446498219244943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9884568688964332146163295 14826853033446498219244943)
          ·
            refine ⟨22240279550169747328867415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14826853033446498219244943 22240279550169747328867415)
            ·
              refine ⟨33360419325254620993301123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22240279550169747328867415 33360419325254620993301123)
              ·
                refine ⟨50040628987881931489951685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33360419325254620993301123 50040628987881931489951685)
                ·
                  refine ⟨9382617935227862154365941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50040628987881931489951685 9382617935227862154365941)
                  ·
                    refine ⟨879620431427612076971807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9382617935227862154365941 879620431427612076971807)
                    ·
                      rfl

theorem cell23_5139164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5139164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139164 prefixEnd_5139164 := by exact prefixLift 5139164
  have htrace : WordTrace (prefixWord ++ tailWord_5139164) baseStart_5139164 baseEnd_5139164 := by
    simpa [prefixWord, tailWord_5139164, baseEnd_5139164] using wordTrace_append hprefix tailTrace_5139164
  have hstable : (prefixWord ++ tailWord_5139164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139164).length < 2 ^ (prefixWord ++ tailWord_5139164).sum := by decide
  have hdescent : baseEnd_5139164 < baseStart_5139164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139167 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4]
def baseStart_5139167 : Nat := 118140960795 + 5139167 * 2 ^ 59
def prefixEnd_5139167 : Nat := 4983230072969 + 3 ^ 40 * 5139167 * 2
def baseEnd_5139167 : Nat := 2638862834724799719177907

theorem tailTrace_5139167 : CollatzResearch.WordTrace tailWord_5139167 prefixEnd_5139167 2638862834724799719177907 := by
  unfold tailWord_5139167
  simp only [CollatzResearch.WordTrace]
  refine ⟨187440819372683133691455755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124960546248455422460970503 187440819372683133691455755)
  ·
    refine ⟨281161229059024700537183633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187440819372683133691455755 281161229059024700537183633)
    ·
      refine ⟨210870921794268525402887725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281161229059024700537183633 210870921794268525402887725)
      ·
        refine ⟨79076595672850697026082897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210870921794268525402887725 79076595672850697026082897)
        ·
          refine ⟨59307446754638022769562173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79076595672850697026082897 59307446754638022769562173)
          ·
            refine ⟨22240292532989258538585815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59307446754638022769562173 22240292532989258538585815)
            ·
              refine ⟨33360438799483887807878723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22240292532989258538585815 33360438799483887807878723)
              ·
                refine ⟨50040658199225831711818085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33360438799483887807878723 50040658199225831711818085)
                ·
                  refine ⟨9382623412354843445965891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50040658199225831711818085 9382623412354843445965891)
                  ·
                    refine ⟨14073935118532265168948837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9382623412354843445965891 14073935118532265168948837)
                    ·
                      refine ⟨2638862834724799719177907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14073935118532265168948837 2638862834724799719177907)
                      ·
                        rfl

theorem cell23_5139167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_5139167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139167 prefixEnd_5139167 := by exact prefixLift 5139167
  have htrace : WordTrace (prefixWord ++ tailWord_5139167) baseStart_5139167 baseEnd_5139167 := by
    simpa [prefixWord, tailWord_5139167, baseEnd_5139167] using wordTrace_append hprefix tailTrace_5139167
  have hstable : (prefixWord ++ tailWord_5139167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139167).length < 2 ^ (prefixWord ++ tailWord_5139167).sum := by decide
  have hdescent : baseEnd_5139167 < baseStart_5139167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139187 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3]
def baseStart_5139187 : Nat := 118140960795 + 5139187 * 2 ^ 59
def prefixEnd_5139187 : Nat := 4983230072969 + 3 ^ 40 * 5139187 * 2
def baseEnd_5139187 : Nat := 2638873104337889640927815

theorem tailTrace_5139187 : CollatzResearch.WordTrace tailWord_5139187 prefixEnd_5139187 2638873104337889640927815 := by
  unfold tailWord_5139187
  simp only [CollatzResearch.WordTrace]
  refine ⟨187441548832610677107183815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124961032555073784738122543 187441548832610677107183815)
  ·
    refine ⟨281162323248916015660775723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187441548832610677107183815 281162323248916015660775723)
    ·
      refine ⟨421743484873374023491163585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281162323248916015660775723 421743484873374023491163585)
      ·
        refine ⟨316307613655030517618372689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421743484873374023491163585 316307613655030517618372689)
        ·
          refine ⟨237230710241272888213779517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316307613655030517618372689 237230710241272888213779517)
          ·
            refine ⟨88961516340477333080167319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237230710241272888213779517 88961516340477333080167319)
            ·
              refine ⟨133442274510715999620250979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88961516340477333080167319 133442274510715999620250979)
              ·
                refine ⟨200163411766073999430376469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133442274510715999620250979 200163411766073999430376469)
                ·
                  refine ⟨9382659926534718723298897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200163411766073999430376469 9382659926534718723298897)
                  ·
                    refine ⟨7036994944901039042474173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9382659926534718723298897 7036994944901039042474173)
                    ·
                      refine ⟨2638873104337889640927815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7036994944901039042474173 2638873104337889640927815)
                      ·
                        rfl

theorem cell23_5139187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 2, 3].length) (baseStart_5139187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139187 prefixEnd_5139187 := by exact prefixLift 5139187
  have htrace : WordTrace (prefixWord ++ tailWord_5139187) baseStart_5139187 baseEnd_5139187 := by
    simpa [prefixWord, tailWord_5139187, baseEnd_5139187] using wordTrace_append hprefix tailTrace_5139187
  have hstable : (prefixWord ++ tailWord_5139187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139187).length < 2 ^ (prefixWord ++ tailWord_5139187).sum := by decide
  have hdescent : baseEnd_5139187 < baseStart_5139187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139200 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_5139200 : Nat := 118140960795 + 5139200 * 2 ^ 59
def prefixEnd_5139200 : Nat := 4983230072969 + 3 ^ 40 * 5139200 * 2
def baseEnd_5139200 : Nat := 2638879779586398090065255

theorem tailTrace_5139200 : CollatzResearch.WordTrace tailWord_5139200 prefixEnd_5139200 2638879779586398090065255 := by
  unfold tailWord_5139200
  simp only [CollatzResearch.WordTrace]
  refine ⟨93721011490781790163703527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124961348654375720218271369 93721011490781790163703527)
  ·
    refine ⟨140581517236172685245555291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93721011490781790163703527 140581517236172685245555291)
    ·
      refine ⟨210872275854259027868332937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140581517236172685245555291 210872275854259027868332937)
      ·
        refine ⟨158154206890694270901249703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210872275854259027868332937 158154206890694270901249703)
        ·
          refine ⟨237231310336041406351874555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158154206890694270901249703 237231310336041406351874555)
          ·
            refine ⟨355846965504062109527811833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237231310336041406351874555 355846965504062109527811833)
            ·
              refine ⟨266885224128046582145858875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355846965504062109527811833 266885224128046582145858875)
              ·
                refine ⟨400327836192069873218788313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266885224128046582145858875 400327836192069873218788313)
                ·
                  refine ⟨300245877144052404914091235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400327836192069873218788313 300245877144052404914091235)
                  ·
                    refine ⟨450368815716078607371136853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 300245877144052404914091235 450368815716078607371136853)
                    ·
                      refine ⟨2638879779586398090065255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 450368815716078607371136853 2638879779586398090065255)
                      ·
                        rfl

theorem cell23_5139200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_5139200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139200 prefixEnd_5139200 := by exact prefixLift 5139200
  have htrace : WordTrace (prefixWord ++ tailWord_5139200) baseStart_5139200 baseEnd_5139200 := by
    simpa [prefixWord, tailWord_5139200, baseEnd_5139200] using wordTrace_append hprefix tailTrace_5139200
  have hstable : (prefixWord ++ tailWord_5139200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139200).length < 2 ^ (prefixWord ++ tailWord_5139200).sum := by decide
  have hdescent : baseEnd_5139200 < baseStart_5139200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139228 : List Nat := [2, 2, 3, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5139228 : Nat := 118140960795 + 5139228 * 2 ^ 59
def prefixEnd_5139228 : Nat := 4983230072969 + 3 ^ 40 * 5139228 * 2
def baseEnd_5139228 : Nat := 879631385681574660171709

theorem tailTrace_5139228 : CollatzResearch.WordTrace tailWord_5139228 prefixEnd_5139228 879631385681574660171709 := by
  unfold tailWord_5139228
  simp only [CollatzResearch.WordTrace]
  refine ⟨93721522112731070554713169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124962029483641427406284225 93721522112731070554713169)
  ·
    refine ⟨70291141584548302916034877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93721522112731070554713169 70291141584548302916034877)
    ·
      refine ⟨26359178094205613593513079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70291141584548302916034877 26359178094205613593513079)
      ·
        refine ⟨39538767141308420390269619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26359178094205613593513079 39538767141308420390269619)
        ·
          refine ⟨59308150711962630585404429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39538767141308420390269619 59308150711962630585404429)
          ·
            refine ⟨22240556516985986469526661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59308150711962630585404429 22240556516985986469526661)
            ·
              refine ⟨4170104346934872463036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22240556516985986469526661 4170104346934872463036249)
              ·
                refine ⟨3127578260201154347277187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4170104346934872463036249 3127578260201154347277187)
                ·
                  refine ⟨4691367390301731520915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127578260201154347277187 4691367390301731520915781)
                  ·
                    refine ⟨879631385681574660171709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691367390301731520915781 879631385681574660171709)
                    ·
                      rfl

theorem cell23_5139228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5139228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139228 prefixEnd_5139228 := by exact prefixLift 5139228
  have htrace : WordTrace (prefixWord ++ tailWord_5139228) baseStart_5139228 baseEnd_5139228 := by
    simpa [prefixWord, tailWord_5139228, baseEnd_5139228] using wordTrace_append hprefix tailTrace_5139228
  have hstable : (prefixWord ++ tailWord_5139228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139228).length < 2 ^ (prefixWord ++ tailWord_5139228).sum := by decide
  have hdescent : baseEnd_5139228 < baseStart_5139228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139237 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_5139237 : Nat := 118140960795 + 5139237 * 2 ^ 59
def prefixEnd_5139237 : Nat := 4983230072969 + 3 ^ 40 * 5139237 * 2
def baseEnd_5139237 : Nat := 879632926123538148434195

theorem tailTrace_5139237 : CollatzResearch.WordTrace tailWord_5139237 prefixEnd_5139237 879632926123538148434195 := by
  unfold tailWord_5139237
  simp only [CollatzResearch.WordTrace]
  refine ⟨187443372482429535646503965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124962248321619690431002643 187443372482429535646503965)
  ·
    refine ⟨70291264680911075867438987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187443372482429535646503965 70291264680911075867438987)
    ·
      refine ⟨105436897021366613801158481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70291264680911075867438987 105436897021366613801158481)
      ·
        refine ⟨79077672766024960350868861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105436897021366613801158481 79077672766024960350868861)
        ·
          refine ⟨29654127287259360131575823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79077672766024960350868861 29654127287259360131575823)
          ·
            refine ⟨44481190930889040197363735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29654127287259360131575823 44481190930889040197363735)
            ·
              refine ⟨66721786396333560296045603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44481190930889040197363735 66721786396333560296045603)
              ·
                refine ⟨100082679594500340444068405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66721786396333560296045603 100082679594500340444068405)
                ·
                  refine ⟨9382751211984406916631413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100082679594500340444068405 9382751211984406916631413)
                  ·
                    refine ⟨879632926123538148434195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9382751211984406916631413 879632926123538148434195)
                    ·
                      rfl

theorem cell23_5139237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_5139237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139237 prefixEnd_5139237 := by exact prefixLift 5139237
  have htrace : WordTrace (prefixWord ++ tailWord_5139237) baseStart_5139237 baseEnd_5139237 := by
    simpa [prefixWord, tailWord_5139237, baseEnd_5139237] using wordTrace_append hprefix tailTrace_5139237
  have hstable : (prefixWord ++ tailWord_5139237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139237).length < 2 ^ (prefixWord ++ tailWord_5139237).sum := by decide
  have hdescent : baseEnd_5139237 < baseStart_5139237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139244 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_5139244 : Nat := 118140960795 + 5139244 * 2 ^ 59
def prefixEnd_5139244 : Nat := 4983230072969 + 3 ^ 40 * 5139244 * 2
def baseEnd_5139244 : Nat := 2638902372735195917915053

theorem tailTrace_5139244 : CollatzResearch.WordTrace tailWord_5139244 prefixEnd_5139244 2638902372735195917915053 := by
  unfold tailWord_5139244
  simp only [CollatzResearch.WordTrace]
  refine ⟨93721813896702087921004393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124962418528936117228005857 93721813896702087921004393)
  ·
    refine ⟨70291360422526565940753295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93721813896702087921004393 70291360422526565940753295)
    ·
      refine ⟨105437040633789848911129943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70291360422526565940753295 105437040633789848911129943)
      ·
        refine ⟨158155560950684773366694915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105437040633789848911129943 158155560950684773366694915)
        ·
          refine ⟨237233341426027160050042373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158155560950684773366694915 237233341426027160050042373)
          ·
            refine ⟨44481251517380092509382945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237233341426027160050042373 44481251517380092509382945)
            ·
              refine ⟨33360938638035069382037209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44481251517380092509382945 33360938638035069382037209)
              ·
                refine ⟨25020703978526302036527907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33360938638035069382037209 25020703978526302036527907)
                ·
                  refine ⟨37531055967789453054791861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25020703978526302036527907 37531055967789453054791861)
                  ·
                    refine ⟨3518536496980261223886737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37531055967789453054791861 3518536496980261223886737)
                    ·
                      refine ⟨2638902372735195917915053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518536496980261223886737 2638902372735195917915053)
                      ·
                        rfl

theorem cell23_5139244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_5139244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139244 prefixEnd_5139244 := by exact prefixLift 5139244
  have htrace : WordTrace (prefixWord ++ tailWord_5139244) baseStart_5139244 baseEnd_5139244 := by
    simpa [prefixWord, tailWord_5139244, baseEnd_5139244] using wordTrace_append hprefix tailTrace_5139244
  have hstable : (prefixWord ++ tailWord_5139244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139244).length < 2 ^ (prefixWord ++ tailWord_5139244).sum := by decide
  have hdescent : baseEnd_5139244 < baseStart_5139244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139251 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 3]
def baseStart_5139251 : Nat := 118140960795 + 5139251 * 2 ^ 59
def prefixEnd_5139251 : Nat := 4983230072969 + 3 ^ 40 * 5139251 * 2
def baseEnd_5139251 : Nat := 2638905967099777390527521

theorem tailTrace_5139251 : CollatzResearch.WordTrace tailWord_5139251 prefixEnd_5139251 2638905967099777390527521 := by
  unfold tailWord_5139251
  simp only [CollatzResearch.WordTrace]
  refine ⟨187443883104378816037513607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124962588736252544025009071 187443883104378816037513607)
  ·
    refine ⟨281165824656568224056270411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187443883104378816037513607 281165824656568224056270411)
    ·
      refine ⟨421748736984852336084405617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281165824656568224056270411 421748736984852336084405617)
      ·
        refine ⟨316311552738639252063304213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421748736984852336084405617 316311552738639252063304213)
        ·
          refine ⟨14827104034623714940467385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 316311552738639252063304213 14827104034623714940467385)
          ·
            refine ⟨11120328025967786205350539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14827104034623714940467385 11120328025967786205350539)
            ·
              refine ⟨16680492038951679308025809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120328025967786205350539 16680492038951679308025809)
              ·
                refine ⟨12510369029213759481019357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16680492038951679308025809 12510369029213759481019357)
                ·
                  refine ⟨4691388385955159805382259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12510369029213759481019357 4691388385955159805382259)
                  ·
                    refine ⟨7037082578932739708073389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691388385955159805382259 7037082578932739708073389)
                    ·
                      refine ⟨2638905967099777390527521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037082578932739708073389 2638905967099777390527521)
                      ·
                        rfl

theorem cell23_5139251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 1, 3].length) (baseStart_5139251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139251 prefixEnd_5139251 := by exact prefixLift 5139251
  have htrace : WordTrace (prefixWord ++ tailWord_5139251) baseStart_5139251 baseEnd_5139251 := by
    simpa [prefixWord, tailWord_5139251, baseEnd_5139251] using wordTrace_append hprefix tailTrace_5139251
  have hstable : (prefixWord ++ tailWord_5139251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139251).length < 2 ^ (prefixWord ++ tailWord_5139251).sum := by decide
  have hdescent : baseEnd_5139251 < baseStart_5139251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139267 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 1, 6]
def baseStart_5139267 : Nat := 118140960795 + 5139267 * 2 ^ 59
def prefixEnd_5139267 : Nat := 4983230072969 + 3 ^ 40 * 5139267 * 2
def baseEnd_5139267 : Nat := 879638060930083109309149

theorem tailTrace_5139267 : CollatzResearch.WordTrace tailWord_5139267 prefixEnd_5139267 879638060930083109309149 := by
  unfold tailWord_5139267
  simp only [CollatzResearch.WordTrace]
  refine ⟨187444466672320850770096055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124962977781547233846730703 187444466672320850770096055)
  ·
    refine ⟨281166700008481276155144083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187444466672320850770096055 281166700008481276155144083)
    ·
      refine ⟨421750050012721914232716125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281166700008481276155144083 421750050012721914232716125)
      ·
        refine ⟨158156268754770717837268547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421750050012721914232716125 158156268754770717837268547)
        ·
          refine ⟨237234403132156076755902821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158156268754770717837268547 237234403132156076755902821)
          ·
            refine ⟨44481450587279264391731779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237234403132156076755902821 44481450587279264391731779)
            ·
              refine ⟨66722175880918896587597669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44481450587279264391731779 66722175880918896587597669)
              ·
                refine ⟨12510407977672293110174563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66722175880918896587597669 12510407977672293110174563)
                ·
                  refine ⟨18765611966508439665261845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12510407977672293110174563 18765611966508439665261845)
                  ·
                    refine ⟨879638060930083109309149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18765611966508439665261845 879638060930083109309149)
                    ·
                      rfl

theorem cell23_5139267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 6].length) (baseStart_5139267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139267 prefixEnd_5139267 := by exact prefixLift 5139267
  have htrace : WordTrace (prefixWord ++ tailWord_5139267) baseStart_5139267 baseEnd_5139267 := by
    simpa [prefixWord, tailWord_5139267, baseEnd_5139267] using wordTrace_append hprefix tailTrace_5139267
  have hstable : (prefixWord ++ tailWord_5139267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139267).length < 2 ^ (prefixWord ++ tailWord_5139267).sum := by decide
  have hdescent : baseEnd_5139267 < baseStart_5139267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139304 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5139304 : Nat := 118140960795 + 5139304 * 2 ^ 59
def prefixEnd_5139304 : Nat := 4983230072969 + 3 ^ 40 * 5139304 * 2
def baseEnd_5139304 : Nat := 2638933181574465683164777

theorem tailTrace_5139304 : CollatzResearch.WordTrace tailWord_5139304 prefixEnd_5139304 2638933181574465683164777 := by
  unfold tailWord_5139304
  simp only [CollatzResearch.WordTrace]
  refine ⟨93722908086593403044596483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124963877448791204059461977 93722908086593403044596483)
  ·
    refine ⟨140584362129890104566894725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93722908086593403044596483 140584362129890104566894725)
    ·
      refine ⟨26359567899354394606292761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140584362129890104566894725 26359567899354394606292761)
      ·
        refine ⟨19769675924515795954719571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26359567899354394606292761 19769675924515795954719571)
        ·
          refine ⟨29654513886773693932079357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19769675924515795954719571 29654513886773693932079357)
          ·
            refine ⟨11120442707540135224529759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29654513886773693932079357 11120442707540135224529759)
            ·
              refine ⟨16680664061310202836794639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120442707540135224529759 16680664061310202836794639)
              ·
                refine ⟨25020996091965304255191959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16680664061310202836794639 25020996091965304255191959)
                ·
                  refine ⟨37531494137947956382787939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25020996091965304255191959 37531494137947956382787939)
                  ·
                    refine ⟨56297241206921934574181909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37531494137947956382787939 56297241206921934574181909)
                    ·
                      refine ⟨2638933181574465683164777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56297241206921934574181909 2638933181574465683164777)
                      ·
                        rfl

theorem cell23_5139304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5139304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139304 prefixEnd_5139304 := by exact prefixLift 5139304
  have htrace : WordTrace (prefixWord ++ tailWord_5139304) baseStart_5139304 baseEnd_5139304 := by
    simpa [prefixWord, tailWord_5139304, baseEnd_5139304] using wordTrace_append hprefix tailTrace_5139304
  have hstable : (prefixWord ++ tailWord_5139304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139304).length < 2 ^ (prefixWord ++ tailWord_5139304).sum := by decide
  have hdescent : baseEnd_5139304 < baseStart_5139304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139314 : List Nat := [3, 2, 1, 2, 1, 1, 6, 7]
def baseStart_5139314 : Nat := 118140960795 + 5139314 * 2 ^ 59
def prefixEnd_5139314 : Nat := 4983230072969 + 3 ^ 40 * 5139314 * 2
def baseEnd_5139314 : Nat := 97738456162259653482953

theorem tailTrace_5139314 : CollatzResearch.WordTrace tailWord_5139314 prefixEnd_5139314 97738456162259653482953 := by
  unfold tailWord_5139314
  simp only [CollatzResearch.WordTrace]
  refine ⟨46861545225787644449264249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124964120602100385198037997 46861545225787644449264249)
  ·
    refine ⟨35146158919340733336948187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46861545225787644449264249 35146158919340733336948187)
    ·
      refine ⟨52719238379011100005422281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35146158919340733336948187 52719238379011100005422281)
      ·
        refine ⟨39539428784258325004066711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52719238379011100005422281 39539428784258325004066711)
        ·
          refine ⟨59309143176387487506100067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39539428784258325004066711 59309143176387487506100067)
          ·
            refine ⟨88963714764581231259150101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59309143176387487506100067 88963714764581231259150101)
            ·
              refine ⟨4170174129589745215272661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88963714764581231259150101 4170174129589745215272661)
              ·
                refine ⟨97738456162259653482953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4170174129589745215272661 97738456162259653482953)
                ·
                  rfl

theorem cell23_5139314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_5139314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139314 prefixEnd_5139314 := by exact prefixLift 5139314
  have htrace : WordTrace (prefixWord ++ tailWord_5139314) baseStart_5139314 baseEnd_5139314 := by
    simpa [prefixWord, tailWord_5139314, baseEnd_5139314] using wordTrace_append hprefix tailTrace_5139314
  have hstable : (prefixWord ++ tailWord_5139314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139314).length < 2 ^ (prefixWord ++ tailWord_5139314).sum := by decide
  have hdescent : baseEnd_5139314 < baseStart_5139314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139324 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_5139324 : Nat := 118140960795 + 5139324 * 2 ^ 59
def prefixEnd_5139324 : Nat := 4983230072969 + 3 ^ 40 * 5139324 * 2
def baseEnd_5139324 : Nat := 2638943451187555604914685

theorem tailTrace_5139324 : CollatzResearch.WordTrace tailWord_5139324 prefixEnd_5139324 2638943451187555604914685 := by
  unfold tailWord_5139324
  simp only [CollatzResearch.WordTrace]
  refine ⟨93723272816557174752460513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124964363755409566336614017 93723272816557174752460513)
  ·
    refine ⟨70292454612417881064345385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93723272816557174752460513 70292454612417881064345385)
    ·
      refine ⟨52719340959313410798259039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70292454612417881064345385 52719340959313410798259039)
      ·
        refine ⟨79079011438970116197388559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52719340959313410798259039 79079011438970116197388559)
        ·
          refine ⟨118618517158455174296082839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79079011438970116197388559 118618517158455174296082839)
          ·
            refine ⟨177927775737682761444124259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118618517158455174296082839 177927775737682761444124259)
            ·
              refine ⟨266891663606524142166186389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177927775737682761444124259 266891663606524142166186389)
              ·
                refine ⟨12510546731555819164039987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 266891663606524142166186389 12510546731555819164039987)
                ·
                  refine ⟨18765820097333728746059981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12510546731555819164039987 18765820097333728746059981)
                  ·
                    refine ⟨7037182536500148279772493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18765820097333728746059981 7037182536500148279772493)
                    ·
                      refine ⟨2638943451187555604914685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037182536500148279772493 2638943451187555604914685)
                      ·
                        rfl

theorem cell23_5139324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_5139324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139324 prefixEnd_5139324 := by exact prefixLift 5139324
  have htrace : WordTrace (prefixWord ++ tailWord_5139324) baseStart_5139324 baseEnd_5139324 := by
    simpa [prefixWord, tailWord_5139324, baseEnd_5139324] using wordTrace_append hprefix tailTrace_5139324
  have hstable : (prefixWord ++ tailWord_5139324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139324).length < 2 ^ (prefixWord ++ tailWord_5139324).sum := by decide
  have hdescent : baseEnd_5139324 < baseStart_5139324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139325 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_5139325 : Nat := 118140960795 + 5139325 * 2 ^ 59
def prefixEnd_5139325 : Nat := 4983230072969 + 3 ^ 40 * 5139325 * 2
def baseEnd_5139325 : Nat := 2638943964668210101002181

theorem tailTrace_5139325 : CollatzResearch.WordTrace tailWord_5139325 prefixEnd_5139325 2638943964668210101002181 := by
  unfold tailWord_5139325
  simp only [CollatzResearch.WordTrace]
  refine ⟨187446582106110726675707429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124964388070740484450471619 187446582106110726675707429)
  ·
    refine ⟨35146234144895761251695143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187446582106110726675707429 35146234144895761251695143)
    ·
      refine ⟨52719351217343641877542715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35146234144895761251695143 52719351217343641877542715)
      ·
        refine ⟨79079026826015462816314073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52719351217343641877542715 79079026826015462816314073)
        ·
          refine ⟨59309270119511597112235555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79079026826015462816314073 59309270119511597112235555)
          ·
            refine ⟨88963905179267395668353333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59309270119511597112235555 88963905179267395668353333)
            ·
              refine ⟨8340366110556318343908125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88963905179267395668353333 8340366110556318343908125)
              ·
                refine ⟨3127637291458619378965547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8340366110556318343908125 3127637291458619378965547)
                ·
                  refine ⟨4691455937187929068448321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127637291458619378965547 4691455937187929068448321)
                  ·
                    refine ⟨3518591952890946801336241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691455937187929068448321 3518591952890946801336241)
                    ·
                      refine ⟨2638943964668210101002181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518591952890946801336241 2638943964668210101002181)
                      ·
                        rfl

theorem cell23_5139325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_5139325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139325 prefixEnd_5139325 := by exact prefixLift 5139325
  have htrace : WordTrace (prefixWord ++ tailWord_5139325) baseStart_5139325 baseEnd_5139325 := by
    simpa [prefixWord, tailWord_5139325, baseEnd_5139325] using wordTrace_append hprefix tailTrace_5139325
  have hstable : (prefixWord ++ tailWord_5139325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139325).length < 2 ^ (prefixWord ++ tailWord_5139325).sum := by decide
  have hdescent : baseEnd_5139325 < baseStart_5139325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139351 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_5139351 : Nat := 118140960795 + 5139351 * 2 ^ 59
def prefixEnd_5139351 : Nat := 4983230072969 + 3 ^ 40 * 5139351 * 2
def baseEnd_5139351 : Nat := 2638957315165226999277061

theorem tailTrace_5139351 : CollatzResearch.WordTrace tailWord_5139351 prefixEnd_5139351 2638957315165226999277061 := by
  unfold tailWord_5139351
  simp only [CollatzResearch.WordTrace]
  refine ⟨187447530404016533116153907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124965020269344355410769271 187447530404016533116153907)
  ·
    refine ⟨281171295606024799674230861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187447530404016533116153907 281171295606024799674230861)
    ·
      refine ⟨105439235852259299877836573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281171295606024799674230861 105439235852259299877836573)
      ·
        refine ⟨39539713444597237454188715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105439235852259299877836573 39539713444597237454188715)
        ·
          refine ⟨59309570166895856181283073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39539713444597237454188715 59309570166895856181283073)
          ·
            refine ⟨44482177625171892135962305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59309570166895856181283073 44482177625171892135962305)
            ·
              refine ⟨33361633218878919101971729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44482177625171892135962305 33361633218878919101971729)
              ·
                refine ⟨25021224914159189326478797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33361633218878919101971729 25021224914159189326478797)
                ·
                  refine ⟨9382959342809695997429549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25021224914159189326478797 9382959342809695997429549)
                  ·
                    refine ⟨3518609753553635999036081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9382959342809695997429549 3518609753553635999036081)
                    ·
                      refine ⟨2638957315165226999277061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518609753553635999036081 2638957315165226999277061)
                      ·
                        rfl

theorem cell23_5139351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_5139351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139351 prefixEnd_5139351 := by exact prefixLift 5139351
  have htrace : WordTrace (prefixWord ++ tailWord_5139351) baseStart_5139351 baseEnd_5139351 := by
    simpa [prefixWord, tailWord_5139351, baseEnd_5139351] using wordTrace_append hprefix tailTrace_5139351
  have hstable : (prefixWord ++ tailWord_5139351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139351).length < 2 ^ (prefixWord ++ tailWord_5139351).sum := by decide
  have hdescent : baseEnd_5139351 < baseStart_5139351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139384 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_5139384 : Nat := 118140960795 + 5139384 * 2 ^ 59
def prefixEnd_5139384 : Nat := 4983230072969 + 3 ^ 40 * 5139384 * 2
def baseEnd_5139384 : Nat := 2638974260026825370164409

theorem tailTrace_5139384 : CollatzResearch.WordTrace tailWord_5139384 prefixEnd_5139384 2638974260026825370164409 := by
  unfold tailWord_5139384
  simp only [CollatzResearch.WordTrace]
  refine ⟨93724367006448489876052603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124965822675264653168070137 93724367006448489876052603)
  ·
    refine ⟨140586550509672734814078905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93724367006448489876052603 140586550509672734814078905)
    ·
      refine ⟨105439912882254551110559179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140586550509672734814078905 105439912882254551110559179)
      ·
        refine ⟨158159869323381826665838769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105439912882254551110559179 158159869323381826665838769)
        ·
          refine ⟨118619901992536369999379077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158159869323381826665838769 118619901992536369999379077)
          ·
            refine ⟨22241231623600569374883577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118619901992536369999379077 22241231623600569374883577)
            ·
              refine ⟨16680923717700427031162683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22241231623600569374883577 16680923717700427031162683)
              ·
                refine ⟨25021385576550640546744025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16680923717700427031162683 25021385576550640546744025)
                ·
                  refine ⟨18766039182412980410058019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25021385576550640546744025 18766039182412980410058019)
                  ·
                    refine ⟨28149058773619470615087029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18766039182412980410058019 28149058773619470615087029)
                    ·
                      refine ⟨2638974260026825370164409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28149058773619470615087029 2638974260026825370164409)
                      ·
                        rfl

theorem cell23_5139384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_5139384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139384 prefixEnd_5139384 := by exact prefixLift 5139384
  have htrace : WordTrace (prefixWord ++ tailWord_5139384) baseStart_5139384 baseEnd_5139384 := by
    simpa [prefixWord, tailWord_5139384, baseEnd_5139384] using wordTrace_append hprefix tailTrace_5139384
  have hstable : (prefixWord ++ tailWord_5139384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139384).length < 2 ^ (prefixWord ++ tailWord_5139384).sum := by decide
  have hdescent : baseEnd_5139384 < baseStart_5139384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139385 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 1, 3, 2]
def baseStart_5139385 : Nat := 118140960795 + 5139385 * 2 ^ 59
def prefixEnd_5139385 : Nat := 4983230072969 + 3 ^ 40 * 5139385 * 2
def baseEnd_5139385 : Nat := 2638974773507479866251905

theorem tailTrace_5139385 : CollatzResearch.WordTrace tailWord_5139385 prefixEnd_5139385 2638974773507479866251905 := by
  unfold tailWord_5139385
  simp only [CollatzResearch.WordTrace]
  refine ⟨187448770485893356922891609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124965846990595571281927739 187448770485893356922891609)
  ·
    refine ⟨140586577864420017692168707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187448770485893356922891609 140586577864420017692168707)
    ·
      refine ⟨210879866796630026538253061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140586577864420017692168707 210879866796630026538253061)
      ·
        refine ⟨39539975024368129975922449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210879866796630026538253061 39539975024368129975922449)
        ·
          refine ⟨29654981268276097481941837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39539975024368129975922449 29654981268276097481941837)
          ·
            refine ⟨11120617975603536555728189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29654981268276097481941837 11120617975603536555728189)
            ·
              refine ⟨4170231740851326208398071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11120617975603536555728189 4170231740851326208398071)
              ·
                refine ⟨6255347611276989312597107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170231740851326208398071 6255347611276989312597107)
                ·
                  refine ⟨9383021416915483968895661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255347611276989312597107 9383021416915483968895661)
                  ·
                    refine ⟨3518633031343306488335873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9383021416915483968895661 3518633031343306488335873)
                    ·
                      refine ⟨2638974773507479866251905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518633031343306488335873 2638974773507479866251905)
                      ·
                        rfl

theorem cell23_5139385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_5139385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139385 prefixEnd_5139385 := by exact prefixLift 5139385
  have htrace : WordTrace (prefixWord ++ tailWord_5139385) baseStart_5139385 baseEnd_5139385 := by
    simpa [prefixWord, tailWord_5139385, baseEnd_5139385] using wordTrace_append hprefix tailTrace_5139385
  have hstable : (prefixWord ++ tailWord_5139385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139385).length < 2 ^ (prefixWord ++ tailWord_5139385).sum := by decide
  have hdescent : baseEnd_5139385 < baseStart_5139385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139404 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 7]
def baseStart_5139404 : Nat := 118140960795 + 5139404 * 2 ^ 59
def prefixEnd_5139404 : Nat := 4983230072969 + 3 ^ 40 * 5139404 * 2
def baseEnd_5139404 : Nat := 293220503293323921323813

theorem tailTrace_5139404 : CollatzResearch.WordTrace tailWord_5139404 prefixEnd_5139404 293220503293323921323813 := by
  unfold tailWord_5139404
  simp only [CollatzResearch.WordTrace]
  refine ⟨93724731736412261583916633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124966308981883015445222177 93724731736412261583916633)
  ·
    refine ⟨70293548802309196187937475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93724731736412261583916633 70293548802309196187937475)
    ·
      refine ⟨105440323203463794281906213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70293548802309196187937475 105440323203463794281906213)
      ·
        refine ⟨19770060600649461427857415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105440323203463794281906213 19770060600649461427857415)
        ·
          refine ⟨29655090900974192141786123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19770060600649461427857415 29655090900974192141786123)
          ·
            refine ⟨44482636351461288212679185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29655090900974192141786123 44482636351461288212679185)
            ·
              refine ⟨33361977263595966159509389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44482636351461288212679185 33361977263595966159509389)
              ·
                refine ⟨12510741473848487309816021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33361977263595966159509389 12510741473848487309816021)
                ·
                  refine ⟨293220503293323921323813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12510741473848487309816021 293220503293323921323813)
                  ·
                    rfl

theorem cell23_5139404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_5139404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139404 prefixEnd_5139404 := by exact prefixLift 5139404
  have htrace : WordTrace (prefixWord ++ tailWord_5139404) baseStart_5139404 baseEnd_5139404 := by
    simpa [prefixWord, tailWord_5139404, baseEnd_5139404] using wordTrace_append hprefix tailTrace_5139404
  have hstable : (prefixWord ++ tailWord_5139404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139404).length < 2 ^ (prefixWord ++ tailWord_5139404).sum := by decide
  have hdescent : baseEnd_5139404 < baseStart_5139404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139421 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 7]
def baseStart_5139421 : Nat := 118140960795 + 5139421 * 2 ^ 59
def prefixEnd_5139421 : Nat := 4983230072969 + 3 ^ 40 * 5139421 * 2
def baseEnd_5139421 : Nat := 293221473201226858377971

theorem tailTrace_5139421 : CollatzResearch.WordTrace tailWord_5139421 prefixEnd_5139421 293221473201226858377971 := by
  unfold tailWord_5139421
  simp only [CollatzResearch.WordTrace]
  refine ⟨187450083513762935071202117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124966722342508623380801411 187450083513762935071202117)
  ·
    refine ⟨35146890658830550325850397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187450083513762935071202117 35146890658830550325850397)
    ·
      refine ⟨13180083997061456372193899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35146890658830550325850397 13180083997061456372193899)
      ·
        refine ⟨19770125995592184558290849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13180083997061456372193899 19770125995592184558290849)
        ·
          refine ⟨14827594496694138418718137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19770125995592184558290849 14827594496694138418718137)
          ·
            refine ⟨11120695872520603814038603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14827594496694138418718137 11120695872520603814038603)
            ·
              refine ⟨16681043808780905721057905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11120695872520603814038603 16681043808780905721057905)
              ·
                refine ⟨12510782856585679290793429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16681043808780905721057905 12510782856585679290793429)
                ·
                  refine ⟨293221473201226858377971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12510782856585679290793429 293221473201226858377971)
                  ·
                    rfl

theorem cell23_5139421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_5139421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139421 prefixEnd_5139421 := by exact prefixLift 5139421
  have htrace : WordTrace (prefixWord ++ tailWord_5139421) baseStart_5139421 baseEnd_5139421 := by
    simpa [prefixWord, tailWord_5139421, baseEnd_5139421] using wordTrace_append hprefix tailTrace_5139421
  have hstable : (prefixWord ++ tailWord_5139421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139421).length < 2 ^ (prefixWord ++ tailWord_5139421).sum := by decide
  have hdescent : baseEnd_5139421 < baseStart_5139421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139481 : List Nat := [1, 2, 1, 2, 1, 1, 6, 2, 3, 4]
def baseStart_5139481 : Nat := 118140960795 + 5139481 * 2 ^ 59
def prefixEnd_5139481 : Nat := 4983230072969 + 3 ^ 40 * 5139481 * 2
def baseEnd_5139481 : Nat := 879674689216770496883821

theorem tailTrace_5139481 : CollatzResearch.WordTrace tailWord_5139481 prefixEnd_5139481 879674689216770496883821 := by
  unfold tailWord_5139481
  simp only [CollatzResearch.WordTrace]
  refine ⟨187452271893545565318386297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124968181262363710212257531 187452271893545565318386297)
  ·
    refine ⟨140589203920159173988789723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187452271893545565318386297 140589203920159173988789723)
    ·
      refine ⟨210883805880238760983184585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140589203920159173988789723 210883805880238760983184585)
      ·
        refine ⟨158162854410179070737388439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210883805880238760983184585 158162854410179070737388439)
        ·
          refine ⟨237244281615268606106082659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158162854410179070737388439 237244281615268606106082659)
          ·
            refine ⟨355866422422902909159123989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237244281615268606106082659 355866422422902909159123989)
            ·
              refine ⟨16681238551073573866833937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 355866422422902909159123989 16681238551073573866833937)
              ·
                refine ⟨12510928913305180400125453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16681238551073573866833937 12510928913305180400125453)
                ·
                  refine ⟨4691598342489442650047045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12510928913305180400125453 4691598342489442650047045)
                  ·
                    refine ⟨879674689216770496883821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691598342489442650047045 879674689216770496883821)
                    ·
                      rfl

theorem cell23_5139481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 4].length) (baseStart_5139481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139481 prefixEnd_5139481 := by exact prefixLift 5139481
  have htrace : WordTrace (prefixWord ++ tailWord_5139481) baseStart_5139481 baseEnd_5139481 := by
    simpa [prefixWord, tailWord_5139481, baseEnd_5139481] using wordTrace_append hprefix tailTrace_5139481
  have hstable : (prefixWord ++ tailWord_5139481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139481).length < 2 ^ (prefixWord ++ tailWord_5139481).sum := by decide
  have hdescent : baseEnd_5139481 < baseStart_5139481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139491 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3]
def baseStart_5139491 : Nat := 118140960795 + 5139491 * 2 ^ 59
def prefixEnd_5139491 : Nat := 4983230072969 + 3 ^ 40 * 5139491 * 2
def baseEnd_5139491 : Nat := 2639029202456856451526417

theorem tailTrace_5139491 : CollatzResearch.WordTrace tailWord_5139491 prefixEnd_5139491 2639029202456856451526417 := by
  unfold tailWord_5139491
  simp only [CollatzResearch.WordTrace]
  refine ⟨187452636623509337026250327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124968424415672891350833551 187452636623509337026250327)
  ·
    refine ⟨281178954935264005539375491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187452636623509337026250327 281178954935264005539375491)
    ·
      refine ⟨421768432402896008309063237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281178954935264005539375491 421768432402896008309063237)
      ·
        refine ⟨79081581075543001557949357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 421768432402896008309063237 79081581075543001557949357)
        ·
          refine ⟨29655592903328625584231009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79081581075543001557949357 29655592903328625584231009)
          ·
            refine ⟨22241694677496469188173257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29655592903328625584231009 22241694677496469188173257)
            ·
              refine ⟨16681271008122351891129943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22241694677496469188173257 16681271008122351891129943)
              ·
                refine ⟨25021906512183527836694915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16681271008122351891129943 25021906512183527836694915)
                ·
                  refine ⟨37532859768275291755042373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25021906512183527836694915 37532859768275291755042373)
                  ·
                    refine ⟨7037411206551617204070445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37532859768275291755042373 7037411206551617204070445)
                    ·
                      refine ⟨2639029202456856451526417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037411206551617204070445 2639029202456856451526417)
                      ·
                        rfl

theorem cell23_5139491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_5139491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139491 prefixEnd_5139491 := by exact prefixLift 5139491
  have htrace : WordTrace (prefixWord ++ tailWord_5139491) baseStart_5139491 baseEnd_5139491 := by
    simpa [prefixWord, tailWord_5139491, baseEnd_5139491] using wordTrace_append hprefix tailTrace_5139491
  have hstable : (prefixWord ++ tailWord_5139491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139491).length < 2 ^ (prefixWord ++ tailWord_5139491).sum := by decide
  have hdescent : baseEnd_5139491 < baseStart_5139491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139514 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_5139514 : Nat := 118140960795 + 5139514 * 2 ^ 59
def prefixEnd_5139514 : Nat := 4983230072969 + 3 ^ 40 * 5139514 * 2
def baseEnd_5139514 : Nat := 2639041012511909861538811

theorem tailTrace_5139514 : CollatzResearch.WordTrace tailWord_5139514 prefixEnd_5139514 2639041012511909861538811 := by
  unfold tailWord_5139514
  simp only [CollatzResearch.WordTrace]
  refine ⟨46863368875606502988584399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124968983668284007969558397 46863368875606502988584399)
  ·
    refine ⟨70295053313409754482876599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46863368875606502988584399 70295053313409754482876599)
    ·
      refine ⟨105442579970114631724314899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70295053313409754482876599 105442579970114631724314899)
      ·
        refine ⟨158163869955171947586472349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105442579970114631724314899 158163869955171947586472349)
        ·
          refine ⟨59311451233189480344927131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158163869955171947586472349 59311451233189480344927131)
          ·
            refine ⟨88967176849784220517390697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59311451233189480344927131 88967176849784220517390697)
            ·
              refine ⟨66725382637338165388043023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88967176849784220517390697 66725382637338165388043023)
              ·
                refine ⟨100088073956007248082064535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66725382637338165388043023 100088073956007248082064535)
                ·
                  refine ⟨150132110934010872123096803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100088073956007248082064535 150132110934010872123096803)
                  ·
                    refine ⟨225198166401016308184645205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 150132110934010872123096803 225198166401016308184645205)
                    ·
                      refine ⟨2639041012511909861538811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 225198166401016308184645205 2639041012511909861538811)
                      ·
                        rfl

theorem cell23_5139514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_5139514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139514 prefixEnd_5139514 := by exact prefixLift 5139514
  have htrace : WordTrace (prefixWord ++ tailWord_5139514) baseStart_5139514 baseEnd_5139514 := by
    simpa [prefixWord, tailWord_5139514, baseEnd_5139514] using wordTrace_append hprefix tailTrace_5139514
  have hstable : (prefixWord ++ tailWord_5139514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139514).length < 2 ^ (prefixWord ++ tailWord_5139514).sum := by decide
  have hdescent : baseEnd_5139514 < baseStart_5139514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139541 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_5139541 : Nat := 118140960795 + 5139541 * 2 ^ 59
def prefixEnd_5139541 : Nat := 4983230072969 + 3 ^ 40 * 5139541 * 2
def baseEnd_5139541 : Nat := 879684958829860418633729

theorem tailTrace_5139541 : CollatzResearch.WordTrace tailWord_5139541 prefixEnd_5139541 879684958829860418633729 := by
  unfold tailWord_5139541
  simp only [CollatzResearch.WordTrace]
  refine ⟨187454460273328195565570477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124969640182218797043713651 187454460273328195565570477)
  ·
    refine ⟨70295422602498073337088929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187454460273328195565570477 70295422602498073337088929)
    ·
      refine ⟨52721566951873555002816697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70295422602498073337088929 52721566951873555002816697)
      ·
        refine ⟨39541175213905166252112523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52721566951873555002816697 39541175213905166252112523)
        ·
          refine ⟨59311762820857749378168785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39541175213905166252112523 59311762820857749378168785)
          ·
            refine ⟨44483822115643312033626589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59311762820857749378168785 44483822115643312033626589)
            ·
              refine ⟨16681433293366242012609971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44483822115643312033626589 16681433293366242012609971)
              ·
                refine ⟨25022149940049363018914957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16681433293366242012609971 25022149940049363018914957)
                ·
                  refine ⟨9383306227518511132093109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25022149940049363018914957 9383306227518511132093109)
                  ·
                    refine ⟨879684958829860418633729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9383306227518511132093109 879684958829860418633729)
                    ·
                      rfl

theorem cell23_5139541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_5139541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139541 prefixEnd_5139541 := by exact prefixLift 5139541
  have htrace : WordTrace (prefixWord ++ tailWord_5139541) baseStart_5139541 baseEnd_5139541 := by
    simpa [prefixWord, tailWord_5139541, baseEnd_5139541] using wordTrace_append hprefix tailTrace_5139541
  have hstable : (prefixWord ++ tailWord_5139541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139541).length < 2 ^ (prefixWord ++ tailWord_5139541).sum := by decide
  have hdescent : baseEnd_5139541 < baseStart_5139541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139555 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 1, 1, 3]
def baseStart_5139555 : Nat := 118140960795 + 5139555 * 2 ^ 59
def prefixEnd_5139555 : Nat := 4983230072969 + 3 ^ 40 * 5139555 * 2
def baseEnd_5139555 : Nat := 2639062065218744201126123

theorem tailTrace_5139555 : CollatzResearch.WordTrace tailWord_5139555 prefixEnd_5139555 2639062065218744201126123 := by
  unfold tailWord_5139555
  simp only [CollatzResearch.WordTrace]
  refine ⟨187454970895277475956580119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124969980596851650637720079 187454970895277475956580119)
  ·
    refine ⟨281182456342916213934870179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187454970895277475956580119 281182456342916213934870179)
    ·
      refine ⟨421773684514374320902305269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281182456342916213934870179 421773684514374320902305269)
      ·
        refine ⟨39541282923222592584591119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 421773684514374320902305269 39541282923222592584591119)
        ·
          refine ⟨59311924384833888876886679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39541282923222592584591119 59311924384833888876886679)
          ·
            refine ⟨88967886577250833315330019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59311924384833888876886679 88967886577250833315330019)
            ·
              refine ⟨133451829865876249972995029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88967886577250833315330019 133451829865876249972995029)
              ·
                refine ⟨3127777262481474608742071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133451829865876249972995029 3127777262481474608742071)
                ·
                  refine ⟨4691665893722211913113107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127777262481474608742071 4691665893722211913113107)
                  ·
                    refine ⟨7037498840583317869669661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691665893722211913113107 7037498840583317869669661)
                    ·
                      refine ⟨2639062065218744201126123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037498840583317869669661 2639062065218744201126123)
                      ·
                        rfl

theorem cell23_5139555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_5139555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139555 prefixEnd_5139555 := by exact prefixLift 5139555
  have htrace : WordTrace (prefixWord ++ tailWord_5139555) baseStart_5139555 baseEnd_5139555 := by
    simpa [prefixWord, tailWord_5139555, baseEnd_5139555] using wordTrace_append hprefix tailTrace_5139555
  have hstable : (prefixWord ++ tailWord_5139555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139555).length < 2 ^ (prefixWord ++ tailWord_5139555).sum := by decide
  have hdescent : baseEnd_5139555 < baseStart_5139555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139565 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_5139565 : Nat := 118140960795 + 5139565 * 2 ^ 59
def prefixEnd_5139565 : Nat := 4983230072969 + 3 ^ 40 * 5139565 * 2
def baseEnd_5139565 : Nat := 2639067200025289162001077

theorem tailTrace_5139565 : CollatzResearch.WordTrace tailWord_5139565 prefixEnd_5139565 2639067200025289162001077 := by
  unfold tailWord_5139565
  simp only [CollatzResearch.WordTrace]
  refine ⟨187455335625241247664444149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124970223750160831776296099 187455335625241247664444149)
  ·
    refine ⟨17573937714866366968541639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187455335625241247664444149 17573937714866366968541639)
    ·
      refine ⟨26360906572299550452812459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17573937714866366968541639 26360906572299550452812459)
      ·
        refine ⟨39541359858449325679218689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26360906572299550452812459 39541359858449325679218689)
        ·
          refine ⟨29656019893836994259414017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39541359858449325679218689 29656019893836994259414017)
          ·
            refine ⟨22242014920377745694560513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29656019893836994259414017 22242014920377745694560513)
            ·
              refine ⟨16681511190283309270920385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22242014920377745694560513 16681511190283309270920385)
              ·
                refine ⟨12511133392712481953190289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16681511190283309270920385 12511133392712481953190289)
                ·
                  refine ⟨9383350044534361464892717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12511133392712481953190289 9383350044534361464892717)
                  ·
                    refine ⟨3518756266700385549334769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9383350044534361464892717 3518756266700385549334769)
                    ·
                      refine ⟨2639067200025289162001077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518756266700385549334769 2639067200025289162001077)
                      ·
                        rfl

theorem cell23_5139565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_5139565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139565 prefixEnd_5139565 := by exact prefixLift 5139565
  have htrace : WordTrace (prefixWord ++ tailWord_5139565) baseStart_5139565 baseEnd_5139565 := by
    simpa [prefixWord, tailWord_5139565, baseEnd_5139565] using wordTrace_append hprefix tailTrace_5139565
  have hstable : (prefixWord ++ tailWord_5139565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139565).length < 2 ^ (prefixWord ++ tailWord_5139565).sum := by decide
  have hdescent : baseEnd_5139565 < baseStart_5139565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139581 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_5139581 : Nat := 118140960795 + 5139581 * 2 ^ 59
def prefixEnd_5139581 : Nat := 4983230072969 + 3 ^ 40 * 5139581 * 2
def baseEnd_5139581 : Nat := 2639075415715761099401003

theorem tailTrace_5139581 : CollatzResearch.WordTrace tailWord_5139581 prefixEnd_5139581 2639075415715761099401003 := by
  unfold tailWord_5139581
  simp only [CollatzResearch.WordTrace]
  refine ⟨187455919193183282397026597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124970612795455521598017731 187455919193183282397026597)
  ·
    refine ⟨35147984848721865449442487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187455919193183282397026597 35147984848721865449442487)
    ·
      refine ⟨52721977273082798174163731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35147984848721865449442487 52721977273082798174163731)
      ·
        refine ⟨79082965909624197261245597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52721977273082798174163731 79082965909624197261245597)
        ·
          refine ⟨29656112216109073972967099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79082965909624197261245597 29656112216109073972967099)
          ·
            refine ⟨44484168324163610959450649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29656112216109073972967099 44484168324163610959450649)
            ·
              refine ⟨33363126243122708219587987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44484168324163610959450649 33363126243122708219587987)
              ·
                refine ⟨50044689364684062329381981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33363126243122708219587987 50044689364684062329381981)
                ·
                  refine ⟨18766758511756523373518243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50044689364684062329381981 18766758511756523373518243)
                  ·
                    refine ⟨28150137767634785060277365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18766758511756523373518243 28150137767634785060277365)
                    ·
                      refine ⟨2639075415715761099401003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28150137767634785060277365 2639075415715761099401003)
                      ·
                        rfl

theorem cell23_5139581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_5139581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139581 prefixEnd_5139581 := by exact prefixLift 5139581
  have htrace : WordTrace (prefixWord ++ tailWord_5139581) baseStart_5139581 baseEnd_5139581 := by
    simpa [prefixWord, tailWord_5139581, baseEnd_5139581] using wordTrace_append hprefix tailTrace_5139581
  have hstable : (prefixWord ++ tailWord_5139581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139581).length < 2 ^ (prefixWord ++ tailWord_5139581).sum := by decide
  have hdescent : baseEnd_5139581 < baseStart_5139581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139588 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 1, 6]
def baseStart_5139588 : Nat := 118140960795 + 5139588 * 2 ^ 59
def prefixEnd_5139588 : Nat := 4983230072969 + 3 ^ 40 * 5139588 * 2
def baseEnd_5139588 : Nat := 879693003360114190671157

theorem tailTrace_5139588 : CollatzResearch.WordTrace tailWord_5139588 prefixEnd_5139588 879693003360114190671157 := by
  unfold tailWord_5139588
  simp only [CollatzResearch.WordTrace]
  refine ⟨93728087252078961296265709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124970783002771948395020945 93728087252078961296265709)
  ·
    refine ⟨35148032719529610486099641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93728087252078961296265709 35148032719529610486099641)
    ·
      refine ⟨26361024539647207864574731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35148032719529610486099641 26361024539647207864574731)
      ·
        refine ⟨39541536809470811796862097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26361024539647207864574731 39541536809470811796862097)
        ·
          refine ⟨29656152607103108847646573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39541536809470811796862097 29656152607103108847646573)
          ·
            refine ⟨11121057227663665817867465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29656152607103108847646573 11121057227663665817867465)
            ·
              refine ⟨8340792920747749363400599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11121057227663665817867465 8340792920747749363400599)
              ·
                refine ⟨12511189381121624045100899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8340792920747749363400599 12511189381121624045100899)
                ·
                  refine ⟨18766784071682436067651349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12511189381121624045100899 18766784071682436067651349)
                  ·
                    refine ⟨879693003360114190671157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18766784071682436067651349 879693003360114190671157)
                    ·
                      rfl

theorem cell23_5139588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_5139588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139588 prefixEnd_5139588 := by exact prefixLift 5139588
  have htrace : WordTrace (prefixWord ++ tailWord_5139588) baseStart_5139588 baseEnd_5139588 := by
    simpa [prefixWord, tailWord_5139588, baseEnd_5139588] using wordTrace_append hprefix tailTrace_5139588
  have hstable : (prefixWord ++ tailWord_5139588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139588).length < 2 ^ (prefixWord ++ tailWord_5139588).sum := by decide
  have hdescent : baseEnd_5139588 < baseStart_5139588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139608 : List Nat := [2, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5139608 : Nat := 118140960795 + 5139608 * 2 ^ 59
def prefixEnd_5139608 : Nat := 4983230072969 + 3 ^ 40 * 5139608 * 2
def baseEnd_5139608 : Nat := 2639089279693432493763379

theorem tailTrace_5139608 : CollatzResearch.WordTrace tailWord_5139608 prefixEnd_5139608 2639089279693432493763379 := by
  unfold tailWord_5139608
  simp only [CollatzResearch.WordTrace]
  refine ⟨93728451982042733004129739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124971269309390310672172985 93728451982042733004129739)
  ·
    refine ⟨140592677973064099506194609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93728451982042733004129739 140592677973064099506194609)
    ·
      refine ⟨105444508479798074629645957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140592677973064099506194609 105444508479798074629645957)
      ·
        refine ⟨19770845339962138993058617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 105444508479798074629645957 19770845339962138993058617)
        ·
          refine ⟨14828134004971604244793963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19770845339962138993058617 14828134004971604244793963)
          ·
            refine ⟨22242201007457406367190945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14828134004971604244793963 22242201007457406367190945)
            ·
              refine ⟨16681650755593054775393209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22242201007457406367190945 16681650755593054775393209)
              ·
                refine ⟨12511238066694791081544907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16681650755593054775393209 12511238066694791081544907)
                ·
                  refine ⟨18766857100042186622317361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12511238066694791081544907 18766857100042186622317361)
                  ·
                    refine ⟨14075142825031639966738021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18766857100042186622317361 14075142825031639966738021)
                    ·
                      refine ⟨2639089279693432493763379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14075142825031639966738021 2639089279693432493763379)
                      ·
                        rfl

theorem cell23_5139608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5139608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139608 prefixEnd_5139608 := by exact prefixLift 5139608
  have htrace : WordTrace (prefixWord ++ tailWord_5139608) baseStart_5139608 baseEnd_5139608 := by
    simpa [prefixWord, tailWord_5139608, baseEnd_5139608] using wordTrace_append hprefix tailTrace_5139608
  have hstable : (prefixWord ++ tailWord_5139608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139608).length < 2 ^ (prefixWord ++ tailWord_5139608).sum := by decide
  have hdescent : baseEnd_5139608 < baseStart_5139608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139612 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_5139612 : Nat := 118140960795 + 5139612 * 2 ^ 59
def prefixEnd_5139612 : Nat := 4983230072969 + 3 ^ 40 * 5139612 * 2
def baseEnd_5139612 : Nat := 2639091333616050478113361

theorem tailTrace_5139612 : CollatzResearch.WordTrace tailWord_5139612 prefixEnd_5139612 2639091333616050478113361 := by
  unfold tailWord_5139612
  simp only [CollatzResearch.WordTrace]
  refine ⟨93728524928035487345702545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124971366570713983127603393 93728524928035487345702545)
  ·
    refine ⟨70296393696026615509276909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93728524928035487345702545 70296393696026615509276909)
    ·
      refine ⟨26361147636009980815978841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70296393696026615509276909 26361147636009980815978841)
      ·
        refine ⟨19770860727007485611984131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26361147636009980815978841 19770860727007485611984131)
        ·
          refine ⟨29656291090511228417976197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19770860727007485611984131 29656291090511228417976197)
          ·
            refine ⟨5560554579470855328370537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29656291090511228417976197 5560554579470855328370537)
            ·
              refine ⟨4170415934603141496277903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5560554579470855328370537 4170415934603141496277903)
              ·
                refine ⟨6255623901904712244416855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4170415934603141496277903 6255623901904712244416855)
                ·
                  refine ⟨9383435852857068366625283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255623901904712244416855 9383435852857068366625283)
                  ·
                    refine ⟨14075153779285602549937925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9383435852857068366625283 14075153779285602549937925)
                    ·
                      refine ⟨2639091333616050478113361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14075153779285602549937925 2639091333616050478113361)
                      ·
                        rfl

theorem cell23_5139612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_5139612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139612 prefixEnd_5139612 := by exact prefixLift 5139612
  have htrace : WordTrace (prefixWord ++ tailWord_5139612) baseStart_5139612 baseEnd_5139612 := by
    simpa [prefixWord, tailWord_5139612, baseEnd_5139612] using wordTrace_append hprefix tailTrace_5139612
  have hstable : (prefixWord ++ tailWord_5139612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139612).length < 2 ^ (prefixWord ++ tailWord_5139612).sum := by decide
  have hdescent : baseEnd_5139612 < baseStart_5139612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139618 : List Nat := [3, 3, 1, 3, 2, 1, 10]
def baseStart_5139618 : Nat := 118140960795 + 5139618 * 2 ^ 59
def prefixEnd_5139618 : Nat := 4983230072969 + 3 ^ 40 * 5139618 * 2
def baseEnd_5139618 : Nat := 32581412524691079686893

theorem tailTrace_5139618 : CollatzResearch.WordTrace tailWord_5139618 prefixEnd_5139618 32581412524691079686893 := by
  unfold tailWord_5139618
  simp only [CollatzResearch.WordTrace]
  refine ⟨46864317173512309429030877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124971512462699491810749005 46864317173512309429030877)
  ·
    refine ⟨17574118940067116035886579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46864317173512309429030877 17574118940067116035886579)
    ·
      refine ⟨26361178410100674053829869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17574118940067116035886579 26361178410100674053829869)
      ·
        refine ⟨9885441903787752770186201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26361178410100674053829869 9885441903787752770186201)
        ·
          refine ⟨7414081427840814577639651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9885441903787752770186201 7414081427840814577639651)
          ·
            refine ⟨11121122141761221866459477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414081427840814577639651 11121122141761221866459477)
            ·
              refine ⟨32581412524691079686893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11121122141761221866459477 32581412524691079686893)
              ·
                rfl

theorem cell23_5139618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 10].length) (baseStart_5139618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139618 prefixEnd_5139618 := by exact prefixLift 5139618
  have htrace : WordTrace (prefixWord ++ tailWord_5139618) baseStart_5139618 baseEnd_5139618 := by
    simpa [prefixWord, tailWord_5139618, baseEnd_5139618] using wordTrace_append hprefix tailTrace_5139618
  have hstable : (prefixWord ++ tailWord_5139618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139618).length < 2 ^ (prefixWord ++ tailWord_5139618).sum := by decide
  have hdescent : baseEnd_5139618 < baseStart_5139618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139629 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_5139629 : Nat := 118140960795 + 5139629 * 2 ^ 59
def prefixEnd_5139629 : Nat := 4983230072969 + 3 ^ 40 * 5139629 * 2
def baseEnd_5139629 : Nat := 2639100062787176911600783

theorem tailTrace_5139629 : CollatzResearch.WordTrace tailWord_5139629 prefixEnd_5139629 2639100062787176911600783 := by
  unfold tailWord_5139629
  simp only [CollatzResearch.WordTrace]
  refine ⟨187457669897009386594773941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124971779931339591063182627 187457669897009386594773941)
  ·
    refine ⟨17574156552844629993260057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187457669897009386594773941 17574156552844629993260057)
    ·
      refine ⟨13180617414633472494945043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17574156552844629993260057 13180617414633472494945043)
      ·
        refine ⟨19770926121950208742417565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13180617414633472494945043 19770926121950208742417565)
        ·
          refine ⟨7414097295731328278406587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19770926121950208742417565 7414097295731328278406587)
          ·
            refine ⟨11121145943596992417609881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414097295731328278406587 11121145943596992417609881)
            ·
              refine ⟨8340859457697744313207411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11121145943596992417609881 8340859457697744313207411)
              ·
                refine ⟨12511289186546616469811117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8340859457697744313207411 12511289186546616469811117)
                ·
                  refine ⟨4691733444954981176179169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12511289186546616469811117 4691733444954981176179169)
                  ·
                    refine ⟨3518800083716235882134377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4691733444954981176179169 3518800083716235882134377)
                    ·
                      refine ⟨2639100062787176911600783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518800083716235882134377 2639100062787176911600783)
                      ·
                        rfl

theorem cell23_5139629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_5139629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139629 prefixEnd_5139629 := by exact prefixLift 5139629
  have htrace : WordTrace (prefixWord ++ tailWord_5139629) baseStart_5139629 baseEnd_5139629 := by
    simpa [prefixWord, tailWord_5139629, baseEnd_5139629] using wordTrace_append hprefix tailTrace_5139629
  have hstable : (prefixWord ++ tailWord_5139629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139629).length < 2 ^ (prefixWord ++ tailWord_5139629).sum := by decide
  have hdescent : baseEnd_5139629 < baseStart_5139629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139645 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_5139645 : Nat := 118140960795 + 5139645 * 2 ^ 59
def prefixEnd_5139645 : Nat := 4983230072969 + 3 ^ 40 * 5139645 * 2
def baseEnd_5139645 : Nat := 2639108278477648849000709

theorem tailTrace_5139645 : CollatzResearch.WordTrace tailWord_5139645 prefixEnd_5139645 2639108278477648849000709 := by
  unfold tailWord_5139645
  simp only [CollatzResearch.WordTrace]
  refine ⟨187458253464951421327356389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124972168976634280884904259 187458253464951421327356389)
  ·
    refine ⟨35148422524678391498879323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187458253464951421327356389 35148422524678391498879323)
    ·
      refine ⟨52722633787017587248318985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35148422524678391498879323 52722633787017587248318985)
      ·
        refine ⟨39541975340263190436239239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52722633787017587248318985 39541975340263190436239239)
        ·
          refine ⟨59312963010394785654358859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39541975340263190436239239 59312963010394785654358859)
          ·
            refine ⟨88969444515592178481538289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59312963010394785654358859 88969444515592178481538289)
            ·
              refine ⟨66727083386694133861153717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88969444515592178481538289 66727083386694133861153717)
              ·
                refine ⟨6255664067502575049483161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66727083386694133861153717 6255664067502575049483161)
                ·
                  refine ⟨4691748050626931287112371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6255664067502575049483161 4691748050626931287112371)
                  ·
                    refine ⟨7037622075940396930668557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4691748050626931287112371 7037622075940396930668557)
                    ·
                      refine ⟨2639108278477648849000709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037622075940396930668557 2639108278477648849000709)
                      ·
                        rfl

theorem cell23_5139645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_5139645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139645 prefixEnd_5139645 := by exact prefixLift 5139645
  have htrace : WordTrace (prefixWord ++ tailWord_5139645) baseStart_5139645 baseEnd_5139645 := by
    simpa [prefixWord, tailWord_5139645, baseEnd_5139645] using wordTrace_append hprefix tailTrace_5139645
  have hstable : (prefixWord ++ tailWord_5139645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139645).length < 2 ^ (prefixWord ++ tailWord_5139645).sum := by decide
  have hdescent : baseEnd_5139645 < baseStart_5139645 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139652 : List Nat := [2, 3, 3, 1, 4, 1, 2, 7]
def baseStart_5139652 : Nat := 118140960795 + 5139652 * 2 ^ 59
def prefixEnd_5139652 : Nat := 4983230072969 + 3 ^ 40 * 5139652 * 2
def baseEnd_5139652 : Nat := 97744884179341863763451

theorem tailTrace_5139652 : CollatzResearch.WordTrace tailWord_5139652 prefixEnd_5139652 97744884179341863763451 := by
  unfold tailWord_5139652
  simp only [CollatzResearch.WordTrace]
  refine ⟨93729254387963030761430605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124972339183950707681907473 93729254387963030761430605)
  ·
    refine ⟨35148470395486136535536477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93729254387963030761430605 35148470395486136535536477)
    ·
      refine ⟨13180676398307301200826179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35148470395486136535536477 13180676398307301200826179)
      ·
        refine ⟨19771014597460951801239269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13180676398307301200826179 19771014597460951801239269)
        ·
          refine ⟨3707065237023928462732363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19771014597460951801239269 3707065237023928462732363)
          ·
            refine ⟨5560597855535892694098545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707065237023928462732363 5560597855535892694098545)
            ·
              refine ⟨4170448391651919520573909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5560597855535892694098545 4170448391651919520573909)
              ·
                refine ⟨97744884179341863763451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4170448391651919520573909 97744884179341863763451)
                ·
                  rfl

theorem cell23_5139652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 7].length) (baseStart_5139652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139652 prefixEnd_5139652 := by exact prefixLift 5139652
  have htrace : WordTrace (prefixWord ++ tailWord_5139652) baseStart_5139652 baseEnd_5139652 := by
    simpa [prefixWord, tailWord_5139652, baseEnd_5139652] using wordTrace_append hprefix tailTrace_5139652
  have hstable : (prefixWord ++ tailWord_5139652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139652).length < 2 ^ (prefixWord ++ tailWord_5139652).sum := by decide
  have hdescent : baseEnd_5139652 < baseStart_5139652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139671 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_5139671 : Nat := 118140960795 + 5139671 * 2 ^ 59
def prefixEnd_5139671 : Nat := 4983230072969 + 3 ^ 40 * 5139671 * 2
def baseEnd_5139671 : Nat := 2639121628974665747275589

theorem tailTrace_5139671 : CollatzResearch.WordTrace tailWord_5139671 prefixEnd_5139671 2639121628974665747275589 := by
  unfold tailWord_5139671
  simp only [CollatzResearch.WordTrace]
  refine ⟨187459201762857227767802867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124972801175238151845201911 187459201762857227767802867)
  ·
    refine ⟨281188802644285841651704301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187459201762857227767802867 281188802644285841651704301)
    ·
      refine ⟨105445800991607190619389113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281188802644285841651704301 105445800991607190619389113)
      ·
        refine ⟨79084350743705392964541835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105445800991607190619389113 79084350743705392964541835)
        ·
          refine ⟨118626526115558089446812753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79084350743705392964541835 118626526115558089446812753)
          ·
            refine ⟨88969894586668567085109565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118626526115558089446812753 88969894586668567085109565)
            ·
              refine ⟨33363710470000712656916087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88969894586668567085109565 33363710470000712656916087)
              ·
                refine ⟨50045565705001068985374131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33363710470000712656916087 50045565705001068985374131)
                ·
                  refine ⟨75068348557501603478061197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50045565705001068985374131 75068348557501603478061197)
                  ·
                    refine ⟨28150630709063101304272949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75068348557501603478061197 28150630709063101304272949)
                    ·
                      refine ⟨2639121628974665747275589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28150630709063101304272949 2639121628974665747275589)
                      ·
                        rfl

theorem cell23_5139671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_5139671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139671 prefixEnd_5139671 := by exact prefixLift 5139671
  have htrace : WordTrace (prefixWord ++ tailWord_5139671) baseStart_5139671 baseEnd_5139671 := by
    simpa [prefixWord, tailWord_5139671, baseEnd_5139671] using wordTrace_append hprefix tailTrace_5139671
  have hstable : (prefixWord ++ tailWord_5139671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139671).length < 2 ^ (prefixWord ++ tailWord_5139671).sum := by decide
  have hdescent : baseEnd_5139671 < baseStart_5139671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139688 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5139688 : Nat := 118140960795 + 5139688 * 2 ^ 59
def prefixEnd_5139688 : Nat := 4983230072969 + 3 ^ 40 * 5139688 * 2
def baseEnd_5139688 : Nat := 2639130358145792180763011

theorem tailTrace_5139688 : CollatzResearch.WordTrace tailWord_5139688 prefixEnd_5139688 2639130358145792180763011 := by
  unfold tailWord_5139688
  simp only [CollatzResearch.WordTrace]
  refine ⟨93729910901897819835585859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124973214535863759780781145 93729910901897819835585859)
  ·
    refine ⟨140594866352846729753378789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93729910901897819835585859 140594866352846729753378789)
    ·
      refine ⟨26361537441158761828758523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 140594866352846729753378789 26361537441158761828758523)
      ·
        refine ⟨39542306161738142743137785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26361537441158761828758523 39542306161738142743137785)
        ·
          refine ⟨29656729621303607057353339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39542306161738142743137785 29656729621303607057353339)
          ·
            refine ⟨44485094431955410586030009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29656729621303607057353339 44485094431955410586030009)
            ·
              refine ⟨33363820823966557939522507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44485094431955410586030009 33363820823966557939522507)
              ·
                refine ⟨50045731235949836909283761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33363820823966557939522507 50045731235949836909283761)
                ·
                  refine ⟨37534298426962377681962821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50045731235949836909283761 37534298426962377681962821)
                  ·
                    refine ⟨7037680955055445815368029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37534298426962377681962821 7037680955055445815368029)
                    ·
                      refine ⟨2639130358145792180763011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7037680955055445815368029 2639130358145792180763011)
                      ·
                        rfl

theorem cell23_5139688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5139688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139688 prefixEnd_5139688 := by exact prefixLift 5139688
  have htrace : WordTrace (prefixWord ++ tailWord_5139688) baseStart_5139688 baseEnd_5139688 := by
    simpa [prefixWord, tailWord_5139688, baseEnd_5139688] using wordTrace_append hprefix tailTrace_5139688
  have hstable : (prefixWord ++ tailWord_5139688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139688).length < 2 ^ (prefixWord ++ tailWord_5139688).sum := by decide
  have hdescent : baseEnd_5139688 < baseStart_5139688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139748 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_5139748 : Nat := 118140960795 + 5139748 * 2 ^ 59
def prefixEnd_5139748 : Nat := 4983230072969 + 3 ^ 40 * 5139748 * 2
def baseEnd_5139748 : Nat := 2639161166985061946012735

theorem tailTrace_5139748 : CollatzResearch.WordTrace tailWord_5139748 prefixEnd_5139748 2639161166985061946012735 := by
  unfold tailWord_5139748
  simp only [CollatzResearch.WordTrace]
  refine ⟨93731005091789134959177949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124974673455718846612237265 93731005091789134959177949)
  ·
    refine ⟨35149126909420925609691731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93731005091789134959177949 35149126909420925609691731)
    ·
      refine ⟨52723690364131388414537597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35149126909420925609691731 52723690364131388414537597)
      ·
        refine ⟨19771383886549270655451599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52723690364131388414537597 19771383886549270655451599)
        ·
          refine ⟨29657075829823905983177399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19771383886549270655451599 29657075829823905983177399)
          ·
            refine ⟨44485613744735858974766099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29657075829823905983177399 44485613744735858974766099)
            ·
              refine ⟨66728420617103788462149149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44485613744735858974766099 66728420617103788462149149)
              ·
                refine ⟨25023157731413920673305931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66728420617103788462149149 25023157731413920673305931)
                ·
                  refine ⟨37534736597120881009958897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25023157731413920673305931 37534736597120881009958897)
                  ·
                    refine ⟨28151052447840660757469173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37534736597120881009958897 28151052447840660757469173)
                    ·
                      refine ⟨2639161166985061946012735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28151052447840660757469173 2639161166985061946012735)
                      ·
                        rfl

theorem cell23_5139748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_5139748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139748 prefixEnd_5139748 := by exact prefixLift 5139748
  have htrace : WordTrace (prefixWord ++ tailWord_5139748) baseStart_5139748 baseEnd_5139748 := by
    simpa [prefixWord, tailWord_5139748, baseEnd_5139748] using wordTrace_append hprefix tailTrace_5139748
  have hstable : (prefixWord ++ tailWord_5139748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139748).length < 2 ^ (prefixWord ++ tailWord_5139748).sum := by decide
  have hdescent : baseEnd_5139748 < baseStart_5139748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139775 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4]
def baseStart_5139775 : Nat := 118140960795 + 5139775 * 2 ^ 59
def prefixEnd_5139775 : Nat := 4983230072969 + 3 ^ 40 * 5139775 * 2
def baseEnd_5139775 : Nat := 2639175030962733340375111

theorem tailTrace_5139775 : CollatzResearch.WordTrace tailWord_5139775 prefixEnd_5139775 2639175030962733340375111 := by
  unfold tailWord_5139775
  simp only [CollatzResearch.WordTrace]
  refine ⟨187462994954480453529588779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124975329969653635686392519 187462994954480453529588779)
  ·
    refine ⟨281194492431720680294383169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187462994954480453529588779 281194492431720680294383169)
    ·
      refine ⟨210895869323790510220787377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281194492431720680294383169 210895869323790510220787377)
      ·
        refine ⟨158171901992842882665590533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210895869323790510220787377 158171901992842882665590533)
        ·
          refine ⟨29657231623658040499798225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158171901992842882665590533 29657231623658040499798225)
          ·
            refine ⟨22242923717743530374848669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29657231623658040499798225 22242923717743530374848669)
            ·
              refine ⟨8341096394153823890568251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22242923717743530374848669 8341096394153823890568251)
              ·
                refine ⟨12511644591230735835852377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341096394153823890568251 12511644591230735835852377)
                ·
                  refine ⟨9383733443423051876889283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12511644591230735835852377 9383733443423051876889283)
                  ·
                    refine ⟨14075600165134577815333925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9383733443423051876889283 14075600165134577815333925)
                    ·
                      refine ⟨2639175030962733340375111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14075600165134577815333925 2639175030962733340375111)
                      ·
                        rfl

theorem cell23_5139775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_5139775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139775 prefixEnd_5139775 := by exact prefixLift 5139775
  have htrace : WordTrace (prefixWord ++ tailWord_5139775) baseStart_5139775 baseEnd_5139775 := by
    simpa [prefixWord, tailWord_5139775, baseEnd_5139775] using wordTrace_append hprefix tailTrace_5139775
  have hstable : (prefixWord ++ tailWord_5139775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139775).length < 2 ^ (prefixWord ++ tailWord_5139775).sum := by decide
  have hdescent : baseEnd_5139775 < baseStart_5139775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139788 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5139788 : Nat := 118140960795 + 5139788 * 2 ^ 59
def prefixEnd_5139788 : Nat := 4983230072969 + 3 ^ 40 * 5139788 * 2
def baseEnd_5139788 : Nat := 2639181706211241789512551

theorem tailTrace_5139788 : CollatzResearch.WordTrace tailWord_5139788 prefixEnd_5139788 2639181706211241789512551 := by
  unfold tailWord_5139788
  simp only [CollatzResearch.WordTrace]
  refine ⟨93731734551716678374906009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124975646068955571166541345 93731734551716678374906009)
  ·
    refine ⟨70298800913787508781179507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93731734551716678374906009 70298800913787508781179507)
    ·
      refine ⟨105448201370681263171769261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70298800913787508781179507 105448201370681263171769261)
      ·
        refine ⟨39543075514005473689413473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105448201370681263171769261 39543075514005473689413473)
        ·
          refine ⟨29657306635504105267060105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39543075514005473689413473 29657306635504105267060105)
          ·
            refine ⟨22242979976628078950295079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29657306635504105267060105 22242979976628078950295079)
            ·
              refine ⟨33364469964942118425442619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22242979976628078950295079 33364469964942118425442619)
              ·
                refine ⟨50046704947413177638163929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33364469964942118425442619 50046704947413177638163929)
                ·
                  refine ⟨37535028710559883228622947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50046704947413177638163929 37535028710559883228622947)
                  ·
                    refine ⟨56302543065839824842934421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37535028710559883228622947 56302543065839824842934421)
                    ·
                      refine ⟨2639181706211241789512551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56302543065839824842934421 2639181706211241789512551)
                      ·
                        rfl

theorem cell23_5139788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5139788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139788 prefixEnd_5139788 := by exact prefixLift 5139788
  have htrace : WordTrace (prefixWord ++ tailWord_5139788) baseStart_5139788 baseEnd_5139788 := by
    simpa [prefixWord, tailWord_5139788, baseEnd_5139788] using wordTrace_append hprefix tailTrace_5139788
  have hstable : (prefixWord ++ tailWord_5139788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139788).length < 2 ^ (prefixWord ++ tailWord_5139788).sum := by decide
  have hdescent : baseEnd_5139788 < baseStart_5139788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139802 : List Nat := [3, 1, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_5139802 : Nat := 118140960795 + 5139802 * 2 ^ 59
def prefixEnd_5139802 : Nat := 4983230072969 + 3 ^ 40 * 5139802 * 2
def baseEnd_5139802 : Nat := 879729631646801578245829

theorem tailTrace_5139802 : CollatzResearch.WordTrace tailWord_5139802 prefixEnd_5139802 879729631646801578245829 := by
  unfold tailWord_5139802
  simp only [CollatzResearch.WordTrace]
  refine ⟨46865994931345659285205415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124975986483588424760547773 46865994931345659285205415)
  ·
    refine ⟨70298992397018488927808123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46865994931345659285205415 70298992397018488927808123)
    ·
      refine ⟨105448488595527733391712185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70298992397018488927808123 105448488595527733391712185)
      ·
        refine ⟨79086366446645800043784139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105448488595527733391712185 79086366446645800043784139)
        ·
          refine ⟨118629549669968700065676209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79086366446645800043784139 118629549669968700065676209)
          ·
            refine ⟨88972162252476525049257157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118629549669968700065676209 88972162252476525049257157)
            ·
              refine ⟨16682280422339348446735717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88972162252476525049257157 16682280422339348446735717)
              ·
                refine ⟨3127927579188627833762947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16682280422339348446735717 3127927579188627833762947)
                ·
                  refine ⟨4691891368782941750644421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3127927579188627833762947 4691891368782941750644421)
                  ·
                    refine ⟨879729631646801578245829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4691891368782941750644421 879729631646801578245829)
                    ·
                      rfl

theorem cell23_5139802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_5139802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139802 prefixEnd_5139802 := by exact prefixLift 5139802
  have htrace : WordTrace (prefixWord ++ tailWord_5139802) baseStart_5139802 baseEnd_5139802 := by
    simpa [prefixWord, tailWord_5139802, baseEnd_5139802] using wordTrace_append hprefix tailTrace_5139802
  have hstable : (prefixWord ++ tailWord_5139802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139802).length < 2 ^ (prefixWord ++ tailWord_5139802).sum := by decide
  have hdescent : baseEnd_5139802 < baseStart_5139802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139835 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 1, 5, 2]
def baseStart_5139835 : Nat := 118140960795 + 5139835 * 2 ^ 59
def prefixEnd_5139835 : Nat := 4983230072969 + 3 ^ 40 * 5139835 * 2
def baseEnd_5139835 : Nat := 2639205839802003105624835

theorem tailTrace_5139835 : CollatzResearch.WordTrace tailWord_5139835 prefixEnd_5139835 2639205839802003105624835 := by
  unfold tailWord_5139835
  simp only [CollatzResearch.WordTrace]
  refine ⟨187465183334263083776772959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124976788889508722517848639 187465183334263083776772959)
  ·
    refine ⟨281197775001394625665159439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187465183334263083776772959 281197775001394625665159439)
    ·
      refine ⟨421796662502091938497739159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281197775001394625665159439 421796662502091938497739159)
      ·
        refine ⟨632694993753137907746608739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421796662502091938497739159 632694993753137907746608739)
        ·
          refine ⟨949042490629706861619913109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632694993753137907746608739 949042490629706861619913109)
          ·
            refine ⟨44486366748267509138433427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 949042490629706861619913109 44486366748267509138433427)
            ·
              refine ⟨66729550122401263707650141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44486366748267509138433427 66729550122401263707650141)
              ·
                refine ⟨25023581295900473890368803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66729550122401263707650141 25023581295900473890368803)
                ·
                  refine ⟨37535371943850710835553205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25023581295900473890368803 37535371943850710835553205)
                  ·
                    refine ⟨3518941119736004140833113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37535371943850710835553205 3518941119736004140833113)
                    ·
                      refine ⟨2639205839802003105624835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518941119736004140833113 2639205839802003105624835)
                      ·
                        rfl

theorem cell23_5139835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 5, 2].length) (baseStart_5139835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139835 prefixEnd_5139835 := by exact prefixLift 5139835
  have htrace : WordTrace (prefixWord ++ tailWord_5139835) baseStart_5139835 baseEnd_5139835 := by
    simpa [prefixWord, tailWord_5139835, baseEnd_5139835] using wordTrace_append hprefix tailTrace_5139835
  have hstable : (prefixWord ++ tailWord_5139835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139835).length < 2 ^ (prefixWord ++ tailWord_5139835).sum := by decide
  have hdescent : baseEnd_5139835 < baseStart_5139835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139845 : List Nat := [1, 3, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_5139845 : Nat := 118140960795 + 5139845 * 2 ^ 59
def prefixEnd_5139845 : Nat := 4983230072969 + 3 ^ 40 * 5139845 * 2
def baseEnd_5139845 : Nat := 879736991536182688833263

theorem tailTrace_5139845 : CollatzResearch.WordTrace tailWord_5139845 prefixEnd_5139845 879736991536182688833263 := by
  unfold tailWord_5139845
  simp only [CollatzResearch.WordTrace]
  refine ⟨187465548064226855484636989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124977032042817903656424659 187465548064226855484636989)
  ·
    refine ⟨70299580524085070806738871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187465548064226855484636989 70299580524085070806738871)
    ·
      refine ⟨105449370786127606210108307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70299580524085070806738871 105449370786127606210108307)
      ·
        refine ⟨158174056179191409315162461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105449370786127606210108307 158174056179191409315162461)
        ·
          refine ⟨59315271067196778493185923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158174056179191409315162461 59315271067196778493185923)
          ·
            refine ⟨88972906600795167739778885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59315271067196778493185923 88972906600795167739778885)
            ·
              refine ⟨16682419987649093951208541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88972906600795167739778885 16682419987649093951208541)
              ·
                refine ⟨6255907495368410231703203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16682419987649093951208541 6255907495368410231703203)
                ·
                  refine ⟨9383861243052615347554805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6255907495368410231703203 9383861243052615347554805)
                  ·
                    refine ⟨879736991536182688833263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9383861243052615347554805 879736991536182688833263)
                    ·
                      rfl

theorem cell23_5139845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_5139845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139845 prefixEnd_5139845 := by exact prefixLift 5139845
  have htrace : WordTrace (prefixWord ++ tailWord_5139845) baseStart_5139845 baseEnd_5139845 := by
    simpa [prefixWord, tailWord_5139845, baseEnd_5139845] using wordTrace_append hprefix tailTrace_5139845
  have hstable : (prefixWord ++ tailWord_5139845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139845).length < 2 ^ (prefixWord ++ tailWord_5139845).sum := by decide
  have hdescent : baseEnd_5139845 < baseStart_5139845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139852 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_5139852 : Nat := 118140960795 + 5139852 * 2 ^ 59
def prefixEnd_5139852 : Nat := 4983230072969 + 3 ^ 40 * 5139852 * 2
def baseEnd_5139852 : Nat := 2639214568973129539112257

theorem tailTrace_5139852 : CollatzResearch.WordTrace tailWord_5139852 prefixEnd_5139852 2639214568973129539112257 := by
  unfold tailWord_5139852
  simp only [CollatzResearch.WordTrace]
  refine ⟨93732901687600747840070905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124977202250134330453427873 93732901687600747840070905)
  ·
    refine ⟨70299676265700560880053179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93732901687600747840070905 70299676265700560880053179)
    ·
      refine ⟨105449514398550841320079769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70299676265700560880053179 105449514398550841320079769)
      ·
        refine ⟨79087135798913130990059827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105449514398550841320079769 79087135798913130990059827)
        ·
          refine ⟨118630703698369696485089741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79087135798913130990059827 118630703698369696485089741)
          ·
            refine ⟨44486513886888636181908653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 118630703698369696485089741 44486513886888636181908653)
            ·
              refine ⟨16682442707583238568215745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44486513886888636181908653 16682442707583238568215745)
              ·
                refine ⟨12511832030687428926161809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16682442707583238568215745 12511832030687428926161809)
                ·
                  refine ⟨9383874023015571694621357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12511832030687428926161809 9383874023015571694621357)
                  ·
                    refine ⟨3518952758630839385483009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9383874023015571694621357 3518952758630839385483009)
                    ·
                      refine ⟨2639214568973129539112257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3518952758630839385483009 2639214568973129539112257)
                      ·
                        rfl

theorem cell23_5139852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_5139852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139852 prefixEnd_5139852 := by exact prefixLift 5139852
  have htrace : WordTrace (prefixWord ++ tailWord_5139852) baseStart_5139852 baseEnd_5139852 := by
    simpa [prefixWord, tailWord_5139852, baseEnd_5139852] using wordTrace_append hprefix tailTrace_5139852
  have hstable : (prefixWord ++ tailWord_5139852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139852).length < 2 ^ (prefixWord ++ tailWord_5139852).sum := by decide
  have hdescent : baseEnd_5139852 < baseStart_5139852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139895 : List Nat := [1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_5139895 : Nat := 118140960795 + 5139895 * 2 ^ 59
def prefixEnd_5139895 : Nat := 4983230072969 + 3 ^ 40 * 5139895 * 2
def baseEnd_5139895 : Nat := 2639236648641272870874559

theorem tailTrace_5139895 : CollatzResearch.WordTrace tailWord_5139895 prefixEnd_5139895 2639236648641272870874559 := by
  unfold tailWord_5139895
  simp only [CollatzResearch.WordTrace]
  refine ⟨187467371714045714023957139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124978247809363809349304759 187467371714045714023957139)
  ·
    refine ⟨281201057571068571035935709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187467371714045714023957139 281201057571068571035935709)
    ·
      refine ⟨105450396589150714138475891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281201057571068571035935709 105450396589150714138475891)
      ·
        refine ⟨158175594883726071207713837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105450396589150714138475891 158175594883726071207713837)
        ·
          refine ⟨59315848081397276702892689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158175594883726071207713837 59315848081397276702892689)
          ·
            refine ⟨44486886061047957527169517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59315848081397276702892689 44486886061047957527169517)
            ·
              refine ⟨16682582272892984072688569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44486886061047957527169517 16682582272892984072688569)
              ·
                refine ⟨12511936704669738054516427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16682582272892984072688569 12511936704669738054516427)
                ·
                  refine ⟨18767905057004607081774641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12511936704669738054516427 18767905057004607081774641)
                  ·
                    refine ⟨14075928792753455311330981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18767905057004607081774641 14075928792753455311330981)
                    ·
                      refine ⟨2639236648641272870874559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14075928792753455311330981 2639236648641272870874559)
                      ·
                        rfl

theorem cell23_5139895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_5139895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139895 prefixEnd_5139895 := by exact prefixLift 5139895
  have htrace : WordTrace (prefixWord ++ tailWord_5139895) baseStart_5139895 baseEnd_5139895 := by
    simpa [prefixWord, tailWord_5139895, baseEnd_5139895] using wordTrace_append hprefix tailTrace_5139895
  have hstable : (prefixWord ++ tailWord_5139895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139895).length < 2 ^ (prefixWord ++ tailWord_5139895).sum := by decide
  have hdescent : baseEnd_5139895 < baseStart_5139895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139905 : List Nat := [1, 2, 7, 13]
def baseStart_5139905 : Nat := 118140960795 + 5139905 * 2 ^ 59
def prefixEnd_5139905 : Nat := 4983230072969 + 3 ^ 40 * 5139905 * 2
def baseEnd_5139905 : Nat := 1206786366459907559099

theorem tailTrace_5139905 : CollatzResearch.WordTrace tailWord_5139905 prefixEnd_5139905 1206786366459907559099 := by
  unfold tailWord_5139905
  simp only [CollatzResearch.WordTrace]
  refine ⟨187467736444009485731821169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124978490962672990487880779 187467736444009485731821169)
  ·
    refine ⟨140600802333007114298865877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187467736444009485731821169 140600802333007114298865877)
    ·
      refine ⟨3295331304679854241379669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 140600802333007114298865877 3295331304679854241379669)
      ·
        refine ⟨1206786366459907559099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3295331304679854241379669 1206786366459907559099)
        ·
          rfl

theorem cell23_5139905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 13].length) (baseStart_5139905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139905 prefixEnd_5139905 := by exact prefixLift 5139905
  have htrace : WordTrace (prefixWord ++ tailWord_5139905) baseStart_5139905 baseEnd_5139905 := by
    simpa [prefixWord, tailWord_5139905, baseEnd_5139905] using wordTrace_append hprefix tailTrace_5139905
  have hstable : (prefixWord ++ tailWord_5139905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139905).length < 2 ^ (prefixWord ++ tailWord_5139905).sum := by decide
  have hdescent : baseEnd_5139905 < baseStart_5139905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139965 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_5139965 : Nat := 118140960795 + 5139965 * 2 ^ 59
def prefixEnd_5139965 : Nat := 4983230072969 + 3 ^ 40 * 5139965 * 2
def baseEnd_5139965 : Nat := 879757530762362532333079

theorem tailTrace_5139965 : CollatzResearch.WordTrace tailWord_5139965 prefixEnd_5139965 879757530762362532333079 := by
  unfold tailWord_5139965
  simp only [CollatzResearch.WordTrace]
  refine ⟨187469924823792115979005349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124979949882528077319336899 187469924823792115979005349)
  ·
    refine ⟨35150610904461021746063503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187469924823792115979005349 35150610904461021746063503)
    ·
      refine ⟨52725916356691532619095255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35150610904461021746063503 52725916356691532619095255)
      ·
        refine ⟨79088874535037298928642883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52725916356691532619095255 79088874535037298928642883)
        ·
          refine ⟨118633311802555948392964325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79088874535037298928642883 118633311802555948392964325)
          ·
            refine ⟨22243745962979240323680811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118633311802555948392964325 22243745962979240323680811)
            ·
              refine ⟨33365618944468860485521217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22243745962979240323680811 33365618944468860485521217)
              ·
                refine ⟨25024214208351645364140913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33365618944468860485521217 25024214208351645364140913)
                ·
                  refine ⟨18768160656263734023105685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25024214208351645364140913 18768160656263734023105685)
                  ·
                    refine ⟨879757530762362532333079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18768160656263734023105685 879757530762362532333079)
                    ·
                      rfl

theorem cell23_5139965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_5139965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139965 prefixEnd_5139965 := by exact prefixLift 5139965
  have htrace : WordTrace (prefixWord ++ tailWord_5139965) baseStart_5139965 baseEnd_5139965 := by
    simpa [prefixWord, tailWord_5139965, baseEnd_5139965] using wordTrace_append hprefix tailTrace_5139965
  have hstable : (prefixWord ++ tailWord_5139965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139965).length < 2 ^ (prefixWord ++ tailWord_5139965).sum := by decide
  have hdescent : baseEnd_5139965 < baseStart_5139965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139985 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_5139985 : Nat := 118140960795 + 5139985 * 2 ^ 59
def prefixEnd_5139985 : Nat := 4983230072969 + 3 ^ 40 * 5139985 * 2
def baseEnd_5139985 : Nat := 2639282861900177518749145

theorem tailTrace_5139985 : CollatzResearch.WordTrace tailWord_5139985 prefixEnd_5139985 2639282861900177518749145 := by
  unfold tailWord_5139985
  simp only [CollatzResearch.WordTrace]
  refine ⟨187470654283719659394733409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124980436189146439596488939 187470654283719659394733409)
  ·
    refine ⟨140602990712789744546050057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187470654283719659394733409 140602990712789744546050057)
    ·
      refine ⟨105452243034592308409537543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140602990712789744546050057 105452243034592308409537543)
      ·
        refine ⟨158178364551888462614306315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105452243034592308409537543 158178364551888462614306315)
        ·
          refine ⟨237267546827832693921459473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158178364551888462614306315 237267546827832693921459473)
          ·
            refine ⟨177950660120874520441094605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237267546827832693921459473 177950660120874520441094605)
            ·
              refine ⟨66731497545327945165410477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177950660120874520441094605 66731497545327945165410477)
              ·
                refine ⟨25024311579497979437028929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66731497545327945165410477 25024311579497979437028929)
                ·
                  refine ⟨18768233684623484577771697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25024311579497979437028929 18768233684623484577771697)
                  ·
                    refine ⟨14076175263467613433328773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18768233684623484577771697 14076175263467613433328773)
                    ·
                      refine ⟨2639282861900177518749145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14076175263467613433328773 2639282861900177518749145)
                      ·
                        rfl

theorem cell23_5139985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_5139985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139985 prefixEnd_5139985 := by exact prefixLift 5139985
  have htrace : WordTrace (prefixWord ++ tailWord_5139985) baseStart_5139985 baseEnd_5139985 := by
    simpa [prefixWord, tailWord_5139985, baseEnd_5139985] using wordTrace_append hprefix tailTrace_5139985
  have hstable : (prefixWord ++ tailWord_5139985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139985).length < 2 ^ (prefixWord ++ tailWord_5139985).sum := by decide
  have hdescent : baseEnd_5139985 < baseStart_5139985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5139989 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_5139989 : Nat := 118140960795 + 5139989 * 2 ^ 59
def prefixEnd_5139989 : Nat := 4983230072969 + 3 ^ 40 * 5139989 * 2
def baseEnd_5139989 : Nat := 2639284915822795503099127

theorem tailTrace_5139989 : CollatzResearch.WordTrace tailWord_5139989 prefixEnd_5139989 2639284915822795503099127 := by
  unfold tailWord_5139989
  simp only [CollatzResearch.WordTrace]
  refine ⟨187470800175705168077879021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124980533450470112051919347 187470800175705168077879021)
  ·
    refine ⟨70301550065889438029204633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187470800175705168077879021 70301550065889438029204633)
    ·
      refine ⟨52726162549417078521903475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70301550065889438029204633 52726162549417078521903475)
      ·
        refine ⟨79089243824125617782855213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52726162549417078521903475 79089243824125617782855213)
        ·
          refine ⟨29658466434047106668570705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79089243824125617782855213 29658466434047106668570705)
          ·
            refine ⟨22243849825535330001428029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29658466434047106668570705 22243849825535330001428029)
            ·
              refine ⟨8341443684575748750535511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22243849825535330001428029 8341443684575748750535511)
              ·
                refine ⟨12512165526863623125803267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341443684575748750535511 12512165526863623125803267)
                ·
                  refine ⟨18768248290295434688704901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12512165526863623125803267 18768248290295434688704901)
                  ·
                    refine ⟨3519046554430394004132169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18768248290295434688704901 3519046554430394004132169)
                    ·
                      refine ⟨2639284915822795503099127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519046554430394004132169 2639284915822795503099127)
                      ·
                        rfl

theorem cell23_5139989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_5139989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5139989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5139989 prefixEnd_5139989 := by exact prefixLift 5139989
  have htrace : WordTrace (prefixWord ++ tailWord_5139989) baseStart_5139989 baseEnd_5139989 := by
    simpa [prefixWord, tailWord_5139989, baseEnd_5139989] using wordTrace_append hprefix tailTrace_5139989
  have hstable : (prefixWord ++ tailWord_5139989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5139989).length < 2 ^ (prefixWord ++ tailWord_5139989).sum := by decide
  have hdescent : baseEnd_5139989 < baseStart_5139989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5139989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140029 : List Nat := [1, 4, 1, 3, 3, 2, 1, 1, 7]
def baseStart_5140029 : Nat := 118140960795 + 5140029 * 2 ^ 59
def prefixEnd_5140029 : Nat := 4983230072969 + 3 ^ 40 * 5140029 * 2
def baseEnd_5140029 : Nat := 293256161672108371844327

theorem tailTrace_5140029 : CollatzResearch.WordTrace tailWord_5140029 prefixEnd_5140029 293256161672108371844327 := by
  unfold tailWord_5140029
  simp only [CollatzResearch.WordTrace]
  refine ⟨187472259095560254909335141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124981506063706836606223427 187472259095560254909335141)
  ·
    refine ⟨35151048580417547795500339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187472259095560254909335141 35151048580417547795500339)
    ·
      refine ⟨52726572870626321693250509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35151048580417547795500339 52726572870626321693250509)
      ·
        refine ⟨19772464826484870634968941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52726572870626321693250509 19772464826484870634968941)
        ·
          refine ⟨7414674309931826488113353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19772464826484870634968941 7414674309931826488113353)
          ·
            refine ⟨5561005732448869866085015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7414674309931826488113353 5561005732448869866085015)
            ·
              refine ⟨8341508598673304799127523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561005732448869866085015 8341508598673304799127523)
              ·
                refine ⟨12512262898009957198691285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8341508598673304799127523 12512262898009957198691285)
                ·
                  refine ⟨293256161672108371844327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12512262898009957198691285 293256161672108371844327)
                  ·
                    rfl

theorem cell23_5140029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_5140029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140029 prefixEnd_5140029 := by exact prefixLift 5140029
  have htrace : WordTrace (prefixWord ++ tailWord_5140029) baseStart_5140029 baseEnd_5140029 := by
    simpa [prefixWord, tailWord_5140029, baseEnd_5140029] using wordTrace_append hprefix tailTrace_5140029
  have hstable : (prefixWord ++ tailWord_5140029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140029).length < 2 ^ (prefixWord ++ tailWord_5140029).sum := by decide
  have hdescent : baseEnd_5140029 < baseStart_5140029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140032 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2]
def baseStart_5140032 : Nat := 118140960795 + 5140032 * 2 ^ 59
def prefixEnd_5140032 : Nat := 4983230072969 + 3 ^ 40 * 5140032 * 2
def baseEnd_5140032 : Nat := 2639306995490938834861429

theorem tailTrace_5140032 : CollatzResearch.WordTrace tailWord_5140032 prefixEnd_5140032 2639306995490938834861429 := by
  unfold tailWord_5140032
  simp only [CollatzResearch.WordTrace]
  refine ⟨93736184257274693210847175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124981579009699590947796233 93736184257274693210847175)
  ·
    refine ⟨140604276385912039816270763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93736184257274693210847175 140604276385912039816270763)
    ·
      refine ⟨210906414578868059724406145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140604276385912039816270763 210906414578868059724406145)
      ·
        refine ⟨158179810934151044793304609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210906414578868059724406145 158179810934151044793304609)
        ·
          refine ⟨118634858200613283594978457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158179810934151044793304609 118634858200613283594978457)
          ·
            refine ⟨88976143650459962696233843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118634858200613283594978457 88976143650459962696233843)
            ·
              refine ⟨133464215475689944044350765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88976143650459962696233843 133464215475689944044350765)
              ·
                refine ⟨50049080803383729016631537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133464215475689944044350765 50049080803383729016631537)
                ·
                  refine ⟨37536810602537796762473653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50049080803383729016631537 37536810602537796762473653)
                  ·
                    refine ⟨3519075993987918446481905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37536810602537796762473653 3519075993987918446481905)
                    ·
                      refine ⟨2639306995490938834861429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519075993987918446481905 2639306995490938834861429)
                      ·
                        rfl

theorem cell23_5140032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_5140032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140032 prefixEnd_5140032 := by exact prefixLift 5140032
  have htrace : WordTrace (prefixWord ++ tailWord_5140032) baseStart_5140032 baseEnd_5140032 := by
    simpa [prefixWord, tailWord_5140032, baseEnd_5140032] using wordTrace_append hprefix tailTrace_5140032
  have hstable : (prefixWord ++ tailWord_5140032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140032).length < 2 ^ (prefixWord ++ tailWord_5140032).sum := by decide
  have hdescent : baseEnd_5140032 < baseStart_5140032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140075 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_5140075 : Nat := 118140960795 + 5140075 * 2 ^ 59
def prefixEnd_5140075 : Nat := 4983230072969 + 3 ^ 40 * 5140075 * 2
def baseEnd_5140075 : Nat := 2639329075159082166623731

theorem tailTrace_5140075 : CollatzResearch.WordTrace tailWord_5140075 prefixEnd_5140075 2639329075159082166623731 := by
  unfold tailWord_5140075
  simp only [CollatzResearch.WordTrace]
  refine ⟨187473936853393604765509679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124982624568929069843673119 187473936853393604765509679)
  ·
    refine ⟨281210905280090407148264519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187473936853393604765509679 281210905280090407148264519)
    ·
      refine ⟨421816357920135610722396779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281210905280090407148264519 421816357920135610722396779)
      ·
        refine ⟨632724536880203416083595169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421816357920135610722396779 632724536880203416083595169)
        ·
          refine ⟨474543402660152562062696377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632724536880203416083595169 474543402660152562062696377)
          ·
            refine ⟨355907551995114421547022283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474543402660152562062696377 355907551995114421547022283)
            ·
              refine ⟨533861327992671632320533425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355907551995114421547022283 533861327992671632320533425)
              ·
                refine ⟨400395995994503724240400069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533861327992671632320533425 400395995994503724240400069)
                ·
                  refine ⟨75074249248969448295075013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400395995994503724240400069 75074249248969448295075013)
                  ·
                    refine ⟨14076421734181771555326565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 75074249248969448295075013 14076421734181771555326565)
                    ·
                      refine ⟨2639329075159082166623731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14076421734181771555326565 2639329075159082166623731)
                      ·
                        rfl

theorem cell23_5140075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_5140075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140075 prefixEnd_5140075 := by exact prefixLift 5140075
  have htrace : WordTrace (prefixWord ++ tailWord_5140075) baseStart_5140075 baseEnd_5140075 := by
    simpa [prefixWord, tailWord_5140075, baseEnd_5140075] using wordTrace_append hprefix tailTrace_5140075
  have hstable : (prefixWord ++ tailWord_5140075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140075).length < 2 ^ (prefixWord ++ tailWord_5140075).sum := by decide
  have hdescent : baseEnd_5140075 < baseStart_5140075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140116 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_5140116 : Nat := 118140960795 + 5140116 * 2 ^ 59
def prefixEnd_5140116 : Nat := 4983230072969 + 3 ^ 40 * 5140116 * 2
def baseEnd_5140116 : Nat := 2639350127865916506211043

theorem tailTrace_5140116 : CollatzResearch.WordTrace tailWord_5140116 prefixEnd_5140116 2639350127865916506211043 := by
  unfold tailWord_5140116
  simp only [CollatzResearch.WordTrace]
  refine ⟨93737716123122534383876101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124983621497496712511834801 93737716123122534383876101)
  ·
    refine ⟨17575821773085475196976769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93737716123122534383876101 17575821773085475196976769)
    ·
      refine ⟨13181866329814106397732577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17575821773085475196976769 13181866329814106397732577)
      ·
        refine ⟨9886399747360579798299433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13181866329814106397732577 9886399747360579798299433)
        ·
          refine ⟨7414799810520434848724575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9886399747360579798299433 7414799810520434848724575)
          ·
            refine ⟨11122199715780652273086863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414799810520434848724575 11122199715780652273086863)
            ·
              refine ⟨16683299573670978409630295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122199715780652273086863 16683299573670978409630295)
              ·
                refine ⟨25024949360506467614445443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16683299573670978409630295 25024949360506467614445443)
                ·
                  refine ⟨37537424040759701421668165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25024949360506467614445443 37537424040759701421668165)
                  ·
                    refine ⟨7038267007642444016562781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37537424040759701421668165 7038267007642444016562781)
                    ·
                      refine ⟨2639350127865916506211043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038267007642444016562781 2639350127865916506211043)
                      ·
                        rfl

theorem cell23_5140116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_5140116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140116 prefixEnd_5140116 := by exact prefixLift 5140116
  have htrace : WordTrace (prefixWord ++ tailWord_5140116) baseStart_5140116 baseEnd_5140116 := by
    simpa [prefixWord, tailWord_5140116, baseEnd_5140116] using wordTrace_append hprefix tailTrace_5140116
  have hstable : (prefixWord ++ tailWord_5140116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140116).length < 2 ^ (prefixWord ++ tailWord_5140116).sum := by decide
  have hdescent : baseEnd_5140116 < baseStart_5140116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140152 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_5140152 : Nat := 118140960795 + 5140152 * 2 ^ 59
def prefixEnd_5140152 : Nat := 4983230072969 + 3 ^ 40 * 5140152 * 2
def baseEnd_5140152 : Nat := 2639368613169478365360877

theorem tailTrace_5140152 : CollatzResearch.WordTrace tailWord_5140152 prefixEnd_5140152 2639368613169478365360877 := by
  unfold tailWord_5140152
  simp only [CollatzResearch.WordTrace]
  refine ⟨93738372637057323458031355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124984496849409764610708473 93738372637057323458031355)
  ·
    refine ⟨140607558955585985187047033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93738372637057323458031355 140607558955585985187047033)
    ·
      refine ⟨105455669216689488890285275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140607558955585985187047033 105455669216689488890285275)
      ·
        refine ⟨158183503825034233335427913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105455669216689488890285275 158183503825034233335427913)
        ·
          refine ⟨118637627868775675001570935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158183503825034233335427913 118637627868775675001570935)
          ·
            refine ⟨177956441803163512502356403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118637627868775675001570935 177956441803163512502356403)
            ·
              refine ⟨266934662704745268753534605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177956441803163512502356403 266934662704745268753534605)
              ·
                refine ⟨100100498514279475782575477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266934662704745268753534605 100100498514279475782575477)
                ·
                  refine ⟨9384421735713700854616451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100100498514279475782575477 9384421735713700854616451)
                  ·
                    refine ⟨14076632603570551281924677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9384421735713700854616451 14076632603570551281924677)
                    ·
                      refine ⟨2639368613169478365360877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14076632603570551281924677 2639368613169478365360877)
                      ·
                        rfl

theorem cell23_5140152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_5140152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140152 prefixEnd_5140152 := by exact prefixLift 5140152
  have htrace : WordTrace (prefixWord ++ tailWord_5140152) baseStart_5140152 baseEnd_5140152 := by
    simpa [prefixWord, tailWord_5140152, baseEnd_5140152] using wordTrace_append hprefix tailTrace_5140152
  have hstable : (prefixWord ++ tailWord_5140152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140152).length < 2 ^ (prefixWord ++ tailWord_5140152).sum := by decide
  have hdescent : baseEnd_5140152 < baseStart_5140152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140173 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5140173 : Nat := 118140960795 + 5140173 * 2 ^ 59
def prefixEnd_5140173 : Nat := 4983230072969 + 3 ^ 40 * 5140173 * 2
def baseEnd_5140173 : Nat := 2639379396263222783198281

theorem tailTrace_5140173 : CollatzResearch.WordTrace tailWord_5140173 prefixEnd_5140173 2639379396263222783198281 := by
  unfold tailWord_5140173
  simp only [CollatzResearch.WordTrace]
  refine ⟨187477511207038567502577173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124985007471359045001718115 187477511207038567502577173)
  ·
    refine ⟨8788008337829932851683305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187477511207038567502577173 8788008337829932851683305)
    ·
      refine ⟨6591006253372449638762479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8788008337829932851683305 6591006253372449638762479)
      ·
        refine ⟨9886509380058674458143719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591006253372449638762479 9886509380058674458143719)
        ·
          refine ⟨14829764070088011687215579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886509380058674458143719 14829764070088011687215579)
          ·
            refine ⟨22244646105132017530823369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14829764070088011687215579 22244646105132017530823369)
            ·
              refine ⟨16683484578849013148117527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22244646105132017530823369 16683484578849013148117527)
              ·
                refine ⟨25025226868273519722176291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16683484578849013148117527 25025226868273519722176291)
                ·
                  refine ⟨37537840302410279583264437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25025226868273519722176291 37537840302410279583264437)
                  ·
                    refine ⟨3519172528350963710931041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37537840302410279583264437 3519172528350963710931041)
                    ·
                      refine ⟨2639379396263222783198281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519172528350963710931041 2639379396263222783198281)
                      ·
                        rfl

theorem cell23_5140173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5140173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140173 prefixEnd_5140173 := by exact prefixLift 5140173
  have htrace : WordTrace (prefixWord ++ tailWord_5140173) baseStart_5140173 baseEnd_5140173 := by
    simpa [prefixWord, tailWord_5140173, baseEnd_5140173] using wordTrace_append hprefix tailTrace_5140173
  have hstable : (prefixWord ++ tailWord_5140173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140173).length < 2 ^ (prefixWord ++ tailWord_5140173).sum := by decide
  have hdescent : baseEnd_5140173 < baseStart_5140173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140180 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5140180 : Nat := 118140960795 + 5140180 * 2 ^ 59
def prefixEnd_5140180 : Nat := 4983230072969 + 3 ^ 40 * 5140180 * 2
def baseEnd_5140180 : Nat := 2639382990627804255810749

theorem tailTrace_5140180 : CollatzResearch.WordTrace tailWord_5140180 prefixEnd_5140180 2639382990627804255810749 := by
  unfold tailWord_5140180
  simp only [CollatzResearch.WordTrace]
  refine ⟨93738883259006603849040997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124985177678675471798721329 93738883259006603849040997)
  ·
    refine ⟨17576040611063738221695187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93738883259006603849040997 17576040611063738221695187)
    ·
      refine ⟨26364060916595607332542781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17576040611063738221695187 26364060916595607332542781)
      ·
        refine ⟨9886522843723352749703543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26364060916595607332542781 9886522843723352749703543)
        ·
          refine ⟨14829784265585029124555315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886522843723352749703543 14829784265585029124555315)
          ·
            refine ⟨22244676398377543686832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14829784265585029124555315 22244676398377543686832973)
            ·
              refine ⟨8341753649391578882562365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22244676398377543686832973 8341753649391578882562365)
              ·
                refine ⟨3128157618521842080960887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8341753649391578882562365 3128157618521842080960887)
                ·
                  refine ⟨4692236427782763121441331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128157618521842080960887 4692236427782763121441331)
                  ·
                    refine ⟨7038354641674144682161997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692236427782763121441331 7038354641674144682161997)
                    ·
                      refine ⟨2639382990627804255810749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038354641674144682161997 2639382990627804255810749)
                      ·
                        rfl

theorem cell23_5140180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5140180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140180 prefixEnd_5140180 := by exact prefixLift 5140180
  have htrace : WordTrace (prefixWord ++ tailWord_5140180) baseStart_5140180 baseEnd_5140180 := by
    simpa [prefixWord, tailWord_5140180, baseEnd_5140180] using wordTrace_append hprefix tailTrace_5140180
  have hstable : (prefixWord ++ tailWord_5140180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140180).length < 2 ^ (prefixWord ++ tailWord_5140180).sum := by decide
  have hdescent : baseEnd_5140180 < baseStart_5140180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140203 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 1, 2, 2]
def baseStart_5140203 : Nat := 118140960795 + 5140203 * 2 ^ 59
def prefixEnd_5140203 : Nat := 4983230072969 + 3 ^ 40 * 5140203 * 2
def baseEnd_5140203 : Nat := 2639394800682857665823143

theorem tailTrace_5140203 : CollatzResearch.WordTrace tailWord_5140203 prefixEnd_5140203 2639394800682857665823143 := by
  unfold tailWord_5140203
  simp only [CollatzResearch.WordTrace]
  refine ⟨187478605396929882626169263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124985736931286588417446175 187478605396929882626169263)
  ·
    refine ⟨281217908095394823939253895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187478605396929882626169263 281217908095394823939253895)
    ·
      refine ⟨421826862143092235908880843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281217908095394823939253895 421826862143092235908880843)
      ·
        refine ⟨632740293214638353863321265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421826862143092235908880843 632740293214638353863321265)
        ·
          refine ⟨474555219910978765397490949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632740293214638353863321265 474555219910978765397490949)
          ·
            refine ⟨88979103733308518512029553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 474555219910978765397490949 88979103733308518512029553)
            ·
              refine ⟨66734327799981388884022165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88979103733308518512029553 66734327799981388884022165)
              ·
                refine ⟨3128171615624127603938539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66734327799981388884022165 3128171615624127603938539)
                ·
                  refine ⟨4692257423436191405907809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128171615624127603938539 4692257423436191405907809)
                  ·
                    refine ⟨3519193067577143554430857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692257423436191405907809 3519193067577143554430857)
                    ·
                      refine ⟨2639394800682857665823143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519193067577143554430857 2639394800682857665823143)
                      ·
                        rfl

theorem cell23_5140203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 1, 2, 2].length) (baseStart_5140203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140203 prefixEnd_5140203 := by exact prefixLift 5140203
  have htrace : WordTrace (prefixWord ++ tailWord_5140203) baseStart_5140203 baseEnd_5140203 := by
    simpa [prefixWord, tailWord_5140203, baseEnd_5140203] using wordTrace_append hprefix tailTrace_5140203
  have hstable : (prefixWord ++ tailWord_5140203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140203).length < 2 ^ (prefixWord ++ tailWord_5140203).sum := by decide
  have hdescent : baseEnd_5140203 < baseStart_5140203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140219 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 3]
def baseStart_5140219 : Nat := 118140960795 + 5140219 * 2 ^ 59
def prefixEnd_5140219 : Nat := 4983230072969 + 3 ^ 40 * 5140219 * 2
def baseEnd_5140219 : Nat := 2639403016373329603223069

theorem tailTrace_5140219 : CollatzResearch.WordTrace tailWord_5140219 prefixEnd_5140219 2639403016373329603223069 := by
  unfold tailWord_5140219
  simp only [CollatzResearch.WordTrace]
  refine ⟨187479188964871917358751711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124986125976581278239167807 187479188964871917358751711)
  ·
    refine ⟨281218783447307876038127567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187479188964871917358751711 281218783447307876038127567)
    ·
      refine ⟨421828175170961814057191351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281218783447307876038127567 421828175170961814057191351)
      ·
        refine ⟨632742262756442721085787027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421828175170961814057191351 632742262756442721085787027)
        ·
          refine ⟨949113394134664081628680541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632742262756442721085787027 949113394134664081628680541)
          ·
            refine ⟨355917522800499030610755203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 949113394134664081628680541 355917522800499030610755203)
            ·
              refine ⟨533876284200748545916132805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355917522800499030610755203 533876284200748545916132805)
              ·
                refine ⟨100101803287640352359274901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533876284200748545916132805 100101803287640352359274901)
                ·
                  refine ⟨4692272029108141516841011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100101803287640352359274901 4692272029108141516841011)
                  ·
                    refine ⟨7038408043662212275261517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692272029108141516841011 7038408043662212275261517)
                    ·
                      refine ⟨2639403016373329603223069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038408043662212275261517 2639403016373329603223069)
                      ·
                        rfl

theorem cell23_5140219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 1, 3].length) (baseStart_5140219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140219 prefixEnd_5140219 := by exact prefixLift 5140219
  have htrace : WordTrace (prefixWord ++ tailWord_5140219) baseStart_5140219 baseEnd_5140219 := by
    simpa [prefixWord, tailWord_5140219, baseEnd_5140219] using wordTrace_append hprefix tailTrace_5140219
  have hstable : (prefixWord ++ tailWord_5140219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140219).length < 2 ^ (prefixWord ++ tailWord_5140219).sum := by decide
  have hdescent : baseEnd_5140219 < baseStart_5140219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140350 : List Nat := [4, 2, 3, 1, 1, 1, 3, 3, 5]
def baseStart_5140350 : Nat := 118140960795 + 5140350 * 2 ^ 59
def prefixEnd_5140350 : Nat := 4983230072969 + 3 ^ 40 * 5140350 * 2
def baseEnd_5140350 : Nat := 293274475815452065631663

theorem tailTrace_5140350 : CollatzResearch.WordTrace tailWord_5140350 prefixEnd_5140350 293274475815452065631663 := by
  unfold tailWord_5140350
  simp only [CollatzResearch.WordTrace]
  refine ⟨23435495865924665841471313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124989311284931551154513669 23435495865924665841471313)
  ·
    refine ⟨17576621899443499381103485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23435495865924665841471313 17576621899443499381103485)
    ·
      refine ⟨6591233212291312267913807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17576621899443499381103485 6591233212291312267913807)
      ·
        refine ⟨9886849818436968401870711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591233212291312267913807 9886849818436968401870711)
        ·
          refine ⟨14830274727655452602806067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9886849818436968401870711 14830274727655452602806067)
          ·
            refine ⟨22245412091483178904209101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14830274727655452602806067 22245412091483178904209101)
            ·
              refine ⟨8342029534306192089078413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22245412091483178904209101 8342029534306192089078413)
              ·
                refine ⟨3128261075364822033404405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8342029534306192089078413 3128261075364822033404405)
                ·
                  refine ⟨293274475815452065631663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3128261075364822033404405 293274475815452065631663)
                  ·
                    rfl

theorem cell23_5140350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_5140350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140350 prefixEnd_5140350 := by exact prefixLift 5140350
  have htrace : WordTrace (prefixWord ++ tailWord_5140350) baseStart_5140350 baseEnd_5140350 := by
    simpa [prefixWord, tailWord_5140350, baseEnd_5140350] using wordTrace_append hprefix tailTrace_5140350
  have hstable : (prefixWord ++ tailWord_5140350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140350).length < 2 ^ (prefixWord ++ tailWord_5140350).sum := by decide
  have hdescent : baseEnd_5140350 < baseStart_5140350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140419 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 7, 5]
def baseStart_5140419 : Nat := 118140960795 + 5140419 * 2 ^ 59
def prefixEnd_5140419 : Nat := 4983230072969 + 3 ^ 40 * 5140419 * 2
def baseEnd_5140419 : Nat := 879835237501409606907383

theorem tailTrace_5140419 : CollatzResearch.WordTrace tailWord_5140419 prefixEnd_5140419 879835237501409606907383 := by
  unfold tailWord_5140419
  simp only [CollatzResearch.WordTrace]
  refine ⟨187486483564147351516032311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124990989042764901010688207 187486483564147351516032311)
  ·
    refine ⟨281229725346221027274048467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187486483564147351516032311 281229725346221027274048467)
    ·
      refine ⟨421844588019331540911072701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281229725346221027274048467 421844588019331540911072701)
      ·
        refine ⟨158191720507249327841652263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421844588019331540911072701 158191720507249327841652263)
        ·
          refine ⟨237287580760873991762478395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158191720507249327841652263 237287580760873991762478395)
          ·
            refine ⟨355931371141310987643717593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237287580760873991762478395 355931371141310987643717593)
            ·
              refine ⟨266948528355983240732788195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355931371141310987643717593 266948528355983240732788195)
              ·
                refine ⟨400422792533974861099182293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266948528355983240732788195 400422792533974861099182293)
                ·
                  refine ⟨9384909200015035807012085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 400422792533974861099182293 9384909200015035807012085)
                  ·
                    refine ⟨879835237501409606907383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9384909200015035807012085 879835237501409606907383)
                    ·
                      rfl

theorem cell23_5140419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 5].length) (baseStart_5140419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140419 prefixEnd_5140419 := by exact prefixLift 5140419
  have htrace : WordTrace (prefixWord ++ tailWord_5140419) baseStart_5140419 baseEnd_5140419 := by
    simpa [prefixWord, tailWord_5140419, baseEnd_5140419] using wordTrace_append hprefix tailTrace_5140419
  have hstable : (prefixWord ++ tailWord_5140419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140419).length < 2 ^ (prefixWord ++ tailWord_5140419).sum := by decide
  have hdescent : baseEnd_5140419 < baseStart_5140419 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140436 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_5140436 : Nat := 118140960795 + 5140436 * 2 ^ 59
def prefixEnd_5140436 : Nat := 4983230072969 + 3 ^ 40 * 5140436 * 2
def baseEnd_5140436 : Nat := 879838147225118418069857

theorem tailTrace_5140436 : CollatzResearch.WordTrace tailWord_5140436 prefixEnd_5140436 879838147225118418069857 := by
  unfold tailWord_5140436
  simp only [CollatzResearch.WordTrace]
  refine ⟨93743551802542881709700581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124991402403390508946267441 93743551802542881709700581)
  ·
    refine ⟨17576915962976790320568859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 93743551802542881709700581 17576915962976790320568859)
    ·
      refine ⟨26365373944465185480853289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17576915962976790320568859 26365373944465185480853289)
      ·
        refine ⟨19774030458348889110639967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26365373944465185480853289 19774030458348889110639967)
        ·
          refine ⟨29661045687523333665959951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19774030458348889110639967 29661045687523333665959951)
          ·
            refine ⟨44491568531285000498939927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29661045687523333665959951 44491568531285000498939927)
            ·
              refine ⟨66737352796927500748409891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44491568531285000498939927 66737352796927500748409891)
              ·
                refine ⟨100106029195391251122614837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66737352796927500748409891 100106029195391251122614837)
                ·
                  refine ⟨9384940237067929792745141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100106029195391251122614837 9384940237067929792745141)
                  ·
                    refine ⟨879838147225118418069857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9384940237067929792745141 879838147225118418069857)
                    ·
                      rfl

theorem cell23_5140436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_5140436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140436 prefixEnd_5140436 := by exact prefixLift 5140436
  have htrace : WordTrace (prefixWord ++ tailWord_5140436) baseStart_5140436 baseEnd_5140436 := by
    simpa [prefixWord, tailWord_5140436, baseEnd_5140436] using wordTrace_append hprefix tailTrace_5140436
  have hstable : (prefixWord ++ tailWord_5140436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140436).length < 2 ^ (prefixWord ++ tailWord_5140436).sum := by decide
  have hdescent : baseEnd_5140436 < baseStart_5140436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140470 : List Nat := [5, 1, 1, 1, 4, 1, 1, 3, 1, 5]
def baseStart_5140470 : Nat := 118140960795 + 5140470 * 2 ^ 59
def prefixEnd_5140470 : Nat := 4983230072969 + 3 ^ 40 * 5140470 * 2
def baseEnd_5140470 : Nat := 879843966672536040394805

theorem tailTrace_5140470 : CollatzResearch.WordTrace tailWord_5140470 prefixEnd_5140470 879843966672536040394805 := by
  unfold tailWord_5140470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11718021480435161701633679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 124992229124641724817425909 11718021480435161701633679)
  ·
    refine ⟨17577032220652742552450519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11718021480435161701633679 17577032220652742552450519)
    ·
      refine ⟨26365548330979113828675779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17577032220652742552450519 26365548330979113828675779)
      ·
        refine ⟨39548322496468670743013669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26365548330979113828675779 39548322496468670743013669)
        ·
          refine ⟨7415310468087875764315063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39548322496468670743013669 7415310468087875764315063)
          ·
            refine ⟨11122965702131813646472595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415310468087875764315063 11122965702131813646472595)
            ·
              refine ⟨16684448553197720469708893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122965702131813646472595 16684448553197720469708893)
              ·
                refine ⟨6256668207449145176140835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16684448553197720469708893 6256668207449145176140835)
                ·
                  refine ⟨9385002311173717764211253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6256668207449145176140835 9385002311173717764211253)
                  ·
                    refine ⟨879843966672536040394805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9385002311173717764211253 879843966672536040394805)
                    ·
                      rfl

theorem cell23_5140470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_5140470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140470 prefixEnd_5140470 := by exact prefixLift 5140470
  have htrace : WordTrace (prefixWord ++ tailWord_5140470) baseStart_5140470 baseEnd_5140470 := by
    simpa [prefixWord, tailWord_5140470, baseEnd_5140470] using wordTrace_append hprefix tailTrace_5140470
  have hstable : (prefixWord ++ tailWord_5140470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140470).length < 2 ^ (prefixWord ++ tailWord_5140470).sum := by decide
  have hdescent : baseEnd_5140470 < baseStart_5140470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140473 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_5140473 : Nat := 118140960795 + 5140473 * 2 ^ 59
def prefixEnd_5140473 : Nat := 4983230072969 + 3 ^ 40 * 5140473 * 2
def baseEnd_5140473 : Nat := 2639533440459571609446901

theorem tailTrace_5140473 : CollatzResearch.WordTrace tailWord_5140473 prefixEnd_5140473 2639533440459571609446901 := by
  unfold tailWord_5140473
  simp only [CollatzResearch.WordTrace]
  refine ⟨187488453105951718738498073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124992302070634479158998715 187488453105951718738498073)
  ·
    refine ⟨140616339829463789053873555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187488453105951718738498073 140616339829463789053873555)
    ·
      refine ⟨210924509744195683580810333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140616339829463789053873555 210924509744195683580810333)
      ·
        refine ⟨79096691154073381342803875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210924509744195683580810333 79096691154073381342803875)
        ·
          refine ⟨118645036731110072014205813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79096691154073381342803875 118645036731110072014205813)
          ·
            refine ⟨11122972193541569251331795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 118645036731110072014205813 11122972193541569251331795)
            ·
              refine ⟨16684458290312353876997693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122972193541569251331795 16684458290312353876997693)
              ·
                refine ⟨6256671858867132703874135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16684458290312353876997693 6256671858867132703874135)
                ·
                  refine ⟨9385007788300699055811203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6256671858867132703874135 9385007788300699055811203)
                  ·
                    refine ⟨14077511682451048583716805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9385007788300699055811203 14077511682451048583716805)
                    ·
                      refine ⟨2639533440459571609446901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14077511682451048583716805 2639533440459571609446901)
                      ·
                        rfl

theorem cell23_5140473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_5140473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140473 prefixEnd_5140473 := by exact prefixLift 5140473
  have htrace : WordTrace (prefixWord ++ tailWord_5140473) baseStart_5140473 baseEnd_5140473 := by
    simpa [prefixWord, tailWord_5140473, baseEnd_5140473] using wordTrace_append hprefix tailTrace_5140473
  have hstable : (prefixWord ++ tailWord_5140473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140473).length < 2 ^ (prefixWord ++ tailWord_5140473).sum := by decide
  have hdescent : baseEnd_5140473 < baseStart_5140473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140476 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_5140476 : Nat := 118140960795 + 5140476 * 2 ^ 59
def prefixEnd_5140476 : Nat := 4983230072969 + 3 ^ 40 * 5140476 * 2
def baseEnd_5140476 : Nat := 2639534980901535097709387

theorem tailTrace_5140476 : CollatzResearch.WordTrace tailWord_5140476 prefixEnd_5140476 2639534980901535097709387 := by
  unfold tailWord_5140476
  simp only [CollatzResearch.WordTrace]
  refine ⟨93744281262470425125428641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124992375016627233500571521 93744281262470425125428641)
  ·
    refine ⟨70308210946852818844071481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93744281262470425125428641 70308210946852818844071481)
    ·
      refine ⟨52731158210139614133053611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70308210946852818844071481 52731158210139614133053611)
      ·
        refine ⟨79096737315209421199580417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52731158210139614133053611 79096737315209421199580417)
        ·
          refine ⟨59322552986407065899685313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79096737315209421199580417 59322552986407065899685313)
          ·
            refine ⟨44491914739805299424763985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59322552986407065899685313 44491914739805299424763985)
            ·
              refine ⟨33368936054853974568572989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44491914739805299424763985 33368936054853974568572989)
              ·
                refine ⟨12513351020570240463214871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33368936054853974568572989 12513351020570240463214871)
                ·
                  refine ⟨18770026530855360694822307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12513351020570240463214871 18770026530855360694822307)
                  ·
                    refine ⟨28155039796283041042233461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18770026530855360694822307 28155039796283041042233461)
                    ·
                      refine ⟨2639534980901535097709387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28155039796283041042233461 2639534980901535097709387)
                      ·
                        rfl

theorem cell23_5140476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_5140476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140476 prefixEnd_5140476 := by exact prefixLift 5140476
  have htrace : WordTrace (prefixWord ++ tailWord_5140476) baseStart_5140476 baseEnd_5140476 := by
    simpa [prefixWord, tailWord_5140476, baseEnd_5140476] using wordTrace_append hprefix tailTrace_5140476
  have hstable : (prefixWord ++ tailWord_5140476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140476).length < 2 ^ (prefixWord ++ tailWord_5140476).sum := by decide
  have hdescent : baseEnd_5140476 < baseStart_5140476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140489 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_5140489 : Nat := 118140960795 + 5140489 * 2 ^ 59
def prefixEnd_5140489 : Nat := 4983230072969 + 3 ^ 40 * 5140489 * 2
def baseEnd_5140489 : Nat := 2639541656150043546846827

theorem tailTrace_5140489 : CollatzResearch.WordTrace tailWord_5140489 prefixEnd_5140489 2639541656150043546846827 := by
  unfold tailWord_5140489
  simp only [CollatzResearch.WordTrace]
  refine ⟨187489036673893753471080521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124992691115929168980720347 187489036673893753471080521)
  ·
    refine ⟨140616777505420315103310391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187489036673893753471080521 140616777505420315103310391)
    ·
      refine ⟨210925166258130472654965587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140616777505420315103310391 210925166258130472654965587)
      ·
        refine ⟨316387749387195708982448381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210925166258130472654965587 316387749387195708982448381)
        ·
          refine ⟨118645406020198390868418143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 316387749387195708982448381 118645406020198390868418143)
          ·
            refine ⟨177968109030297586302627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118645406020198390868418143 177968109030297586302627215)
            ·
              refine ⟨266952163545446379453940823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177968109030297586302627215 266952163545446379453940823)
              ·
                refine ⟨400428245318169569180911235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266952163545446379453940823 400428245318169569180911235)
                ·
                  refine ⟨600642367977254353771366853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400428245318169569180911235 600642367977254353771366853)
                  ·
                    refine ⟨112620443995735191332131285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600642367977254353771366853 112620443995735191332131285)
                    ·
                      refine ⟨2639541656150043546846827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112620443995735191332131285 2639541656150043546846827)
                      ·
                        rfl

theorem cell23_5140489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_5140489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140489 prefixEnd_5140489 := by exact prefixLift 5140489
  have htrace : WordTrace (prefixWord ++ tailWord_5140489) baseStart_5140489 baseEnd_5140489 := by
    simpa [prefixWord, tailWord_5140489, baseEnd_5140489] using wordTrace_append hprefix tailTrace_5140489
  have hstable : (prefixWord ++ tailWord_5140489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140489).length < 2 ^ (prefixWord ++ tailWord_5140489).sum := by decide
  have hdescent : baseEnd_5140489 < baseStart_5140489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140503 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_5140503 : Nat := 118140960795 + 5140503 * 2 ^ 59
def prefixEnd_5140503 : Nat := 4983230072969 + 3 ^ 40 * 5140503 * 2
def baseEnd_5140503 : Nat := 2639548844879206492071763

theorem tailTrace_5140503 : CollatzResearch.WordTrace tailWord_5140503 prefixEnd_5140503 2639548844879206492071763 := by
  unfold tailWord_5140503
  simp only [CollatzResearch.WordTrace]
  refine ⟨187489547295843033862090163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124993031530562022574726775 187489547295843033862090163)
  ·
    refine ⟨281234320943764550793135245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187489547295843033862090163 281234320943764550793135245)
    ·
      refine ⟨105462870353911706547425717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281234320943764550793135245 105462870353911706547425717)
      ·
        refine ⟨9887144095679222488821161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105462870353911706547425717 9887144095679222488821161)
        ·
          refine ⟨7415358071759416866615871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9887144095679222488821161 7415358071759416866615871)
          ·
            refine ⟨11123037107639125299923807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415358071759416866615871 11123037107639125299923807)
            ·
              refine ⟨16684555661458687949885711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11123037107639125299923807 16684555661458687949885711)
              ·
                refine ⟨25026833492188031924828567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16684555661458687949885711 25026833492188031924828567)
                ·
                  refine ⟨37540250238282047887242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25026833492188031924828567 37540250238282047887242851)
                  ·
                    refine ⟨56310375357423071830864277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37540250238282047887242851 56310375357423071830864277)
                    ·
                      refine ⟨2639548844879206492071763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56310375357423071830864277 2639548844879206492071763)
                      ·
                        rfl

theorem cell23_5140503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_5140503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140503 prefixEnd_5140503 := by exact prefixLift 5140503
  have htrace : WordTrace (prefixWord ++ tailWord_5140503) baseStart_5140503 baseEnd_5140503 := by
    simpa [prefixWord, tailWord_5140503, baseEnd_5140503] using wordTrace_append hprefix tailTrace_5140503
  have hstable : (prefixWord ++ tailWord_5140503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140503).length < 2 ^ (prefixWord ++ tailWord_5140503).sum := by decide
  have hdescent : baseEnd_5140503 < baseStart_5140503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140540 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_5140540 : Nat := 118140960795 + 5140540 * 2 ^ 59
def prefixEnd_5140540 : Nat := 4983230072969 + 3 ^ 40 * 5140540 * 2
def baseEnd_5140540 : Nat := 2639567843663422847309093

theorem tailTrace_5140540 : CollatzResearch.WordTrace tailWord_5140540 prefixEnd_5140540 2639567843663422847309093 := by
  unfold tailWord_5140540
  simp only [CollatzResearch.WordTrace]
  refine ⟨93745448398354494590593537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124993931197805992787458049 93745448398354494590593537)
  ·
    refine ⟨70309086298765870942945153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93745448398354494590593537 70309086298765870942945153)
    ·
      refine ⟨52731814724074403207208865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70309086298765870942945153 52731814724074403207208865)
      ·
        refine ⟨39548861043055802405406649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52731814724074403207208865 39548861043055802405406649)
        ·
          refine ⟨29661645782291851804054987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39548861043055802405406649 29661645782291851804054987)
          ·
            refine ⟨44492468673437777706082481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29661645782291851804054987 44492468673437777706082481)
            ·
              refine ⟨33369351505078333279561861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44492468673437777706082481 33369351505078333279561861)
              ·
                refine ⟨6256753407202187489917849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33369351505078333279561861 6256753407202187489917849)
                ·
                  refine ⟨4692565055401640617438387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6256753407202187489917849 4692565055401640617438387)
                  ·
                    refine ⟨7038847583102460926157581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692565055401640617438387 7038847583102460926157581)
                    ·
                      refine ⟨2639567843663422847309093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038847583102460926157581 2639567843663422847309093)
                      ·
                        rfl

theorem cell23_5140540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_5140540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140540 prefixEnd_5140540 := by exact prefixLift 5140540
  have htrace : WordTrace (prefixWord ++ tailWord_5140540) baseStart_5140540 baseEnd_5140540 := by
    simpa [prefixWord, tailWord_5140540, baseEnd_5140540] using wordTrace_append hprefix tailTrace_5140540
  have hstable : (prefixWord ++ tailWord_5140540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140540).length < 2 ^ (prefixWord ++ tailWord_5140540).sum := by decide
  have hdescent : baseEnd_5140540 < baseStart_5140540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140556 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_5140556 : Nat := 118140960795 + 5140556 * 2 ^ 59
def prefixEnd_5140556 : Nat := 4983230072969 + 3 ^ 40 * 5140556 * 2
def baseEnd_5140556 : Nat := 879858686451298261569673

theorem tailTrace_5140556 : CollatzResearch.WordTrace tailWord_5140556 prefixEnd_5140556 879858686451298261569673 := by
  unfold tailWord_5140556
  simp only [CollatzResearch.WordTrace]
  refine ⟨93745740182325511956884761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124994320243100682609179681 93745740182325511956884761)
  ·
    refine ⟨70309305136744133967663571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93745740182325511956884761 70309305136744133967663571)
    ·
      refine ⟨105463957705116200951495357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70309305136744133967663571 105463957705116200951495357)
      ·
        refine ⟨39548984139418575356810759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105463957705116200951495357 39548984139418575356810759)
        ·
          refine ⟨59323476209127863035216139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39548984139418575356810759 59323476209127863035216139)
          ·
            refine ⟨88985214313691794552824209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59323476209127863035216139 88985214313691794552824209)
            ·
              refine ⟨66738910735268845914618157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88985214313691794552824209 66738910735268845914618157)
              ·
                refine ⟨25027091525725817217981809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66738910735268845914618157 25027091525725817217981809)
                ·
                  refine ⟨18770318644294362913486357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25027091525725817217981809 18770318644294362913486357)
                  ·
                    refine ⟨879858686451298261569673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18770318644294362913486357 879858686451298261569673)
                    ·
                      rfl

theorem cell23_5140556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_5140556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140556 prefixEnd_5140556 := by exact prefixLift 5140556
  have htrace : WordTrace (prefixWord ++ tailWord_5140556) baseStart_5140556 baseEnd_5140556 := by
    simpa [prefixWord, tailWord_5140556, baseEnd_5140556] using wordTrace_append hprefix tailTrace_5140556
  have hstable : (prefixWord ++ tailWord_5140556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140556).length < 2 ^ (prefixWord ++ tailWord_5140556).sum := by decide
  have hdescent : baseEnd_5140556 < baseStart_5140556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140557 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_5140557 : Nat := 118140960795 + 5140557 * 2 ^ 59
def prefixEnd_5140557 : Nat := 4983230072969 + 3 ^ 40 * 5140557 * 2
def baseEnd_5140557 : Nat := 2639576572834549280796515

theorem tailTrace_5140557 : CollatzResearch.WordTrace tailWord_5140557 prefixEnd_5140557 2639576572834549280796515 := by
  unfold tailWord_5140557
  simp only [CollatzResearch.WordTrace]
  refine ⟨187491516837647401084555925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124994344558431600723037283 187491516837647401084555925)
  ·
    refine ⟨8788664851764721925838559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 187491516837647401084555925 8788664851764721925838559)
    ·
      refine ⟨13182997277647082888757839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8788664851764721925838559 13182997277647082888757839)
      ·
        refine ⟨19774495916470624333136759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13182997277647082888757839 19774495916470624333136759)
        ·
          refine ⟨29661743874705936499705139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19774495916470624333136759 29661743874705936499705139)
          ·
            refine ⟨44492615812058904749557709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29661743874705936499705139 44492615812058904749557709)
            ·
              refine ⟨16684730929522089281084141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44492615812058904749557709 16684730929522089281084141)
              ·
                refine ⟨6256774098570783480406553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16684730929522089281084141 6256774098570783480406553)
                ·
                  refine ⟨4692580573928087610304915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6256774098570783480406553 4692580573928087610304915)
                  ·
                    refine ⟨7038870860892131415457373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4692580573928087610304915 7038870860892131415457373)
                    ·
                      refine ⟨2639576572834549280796515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038870860892131415457373 2639576572834549280796515)
                      ·
                        rfl

theorem cell23_5140557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_5140557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140557 prefixEnd_5140557 := by exact prefixLift 5140557
  have htrace : WordTrace (prefixWord ++ tailWord_5140557) baseStart_5140557 baseEnd_5140557 := by
    simpa [prefixWord, tailWord_5140557, baseEnd_5140557] using wordTrace_append hprefix tailTrace_5140557
  have hstable : (prefixWord ++ tailWord_5140557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140557).length < 2 ^ (prefixWord ++ tailWord_5140557).sum := by decide
  have hdescent : baseEnd_5140557 < baseStart_5140557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140574 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_5140574 : Nat := 118140960795 + 5140574 * 2 ^ 59
def prefixEnd_5140574 : Nat := 4983230072969 + 3 ^ 40 * 5140574 * 2
def baseEnd_5140574 : Nat := 2639585302005675714283937

theorem tailTrace_5140574 : CollatzResearch.WordTrace tailWord_5140574 prefixEnd_5140574 2639585302005675714283937 := by
  unfold tailWord_5140574
  simp only [CollatzResearch.WordTrace]
  refine ⟨23436517109823226623490597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 124994757919057208658616517 23436517109823226623490597)
  ·
    refine ⟨4394346958091854991904487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23436517109823226623490597 4394346958091854991904487)
    ·
      refine ⟨6591520437137782487856731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4394346958091854991904487 6591520437137782487856731)
      ·
        refine ⟨9887280655706673731785097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6591520437137782487856731 9887280655706673731785097)
        ·
          refine ⟨7415460491780005298838823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9887280655706673731785097 7415460491780005298838823)
          ·
            refine ⟨11123190737670007948258235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415460491780005298838823 11123190737670007948258235)
            ·
              refine ⟨16684786106505011922387353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11123190737670007948258235 16684786106505011922387353)
              ·
                refine ⟨12513589579878758941790515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16684786106505011922387353 12513589579878758941790515)
                ·
                  refine ⟨18770384369818138412685773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12513589579878758941790515 18770384369818138412685773)
                  ·
                    refine ⟨7038894138681801904757165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18770384369818138412685773 7038894138681801904757165)
                    ·
                      refine ⟨2639585302005675714283937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038894138681801904757165 2639585302005675714283937)
                      ·
                        rfl

theorem cell23_5140574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_5140574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140574 prefixEnd_5140574 := by exact prefixLift 5140574
  have htrace : WordTrace (prefixWord ++ tailWord_5140574) baseStart_5140574 baseEnd_5140574 := by
    simpa [prefixWord, tailWord_5140574, baseEnd_5140574] using wordTrace_append hprefix tailTrace_5140574
  have hstable : (prefixWord ++ tailWord_5140574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140574).length < 2 ^ (prefixWord ++ tailWord_5140574).sum := by decide
  have hdescent : baseEnd_5140574 < baseStart_5140574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140580 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 6, 2, 2]
def baseStart_5140580 : Nat := 118140960795 + 5140580 * 2 ^ 59
def prefixEnd_5140580 : Nat := 4983230072969 + 3 ^ 40 * 5140580 * 2
def baseEnd_5140580 : Nat := 2639588382889602690808909

theorem tailTrace_5140580 : CollatzResearch.WordTrace tailWord_5140580 prefixEnd_5140580 2639588382889602690808909 := by
  unfold tailWord_5140580
  simp only [CollatzResearch.WordTrace]
  refine ⟨93746177858282038006321597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124994903811042717341762129 93746177858282038006321597)
  ·
    refine ⟨35154816696855764252370599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93746177858282038006321597 35154816696855764252370599)
    ·
      refine ⟨52732225045283646378555899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35154816696855764252370599 52732225045283646378555899)
      ·
        refine ⟨79098337567925469567833849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52732225045283646378555899 79098337567925469567833849)
        ·
          refine ⟨59323753175944102175875387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79098337567925469567833849 59323753175944102175875387)
          ·
            refine ⟨88985629763916153263813081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59323753175944102175875387 88985629763916153263813081)
            ·
              refine ⟨66739222322937114947859811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88985629763916153263813081 66739222322937114947859811)
              ·
                refine ⟨100108833484405672421789717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66739222322937114947859811 100108833484405672421789717)
                ·
                  refine ⟨4692601569581515894771393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100108833484405672421789717 4692601569581515894771393)
                  ·
                    refine ⟨3519451177186136921078545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692601569581515894771393 3519451177186136921078545)
                    ·
                      refine ⟨2639588382889602690808909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519451177186136921078545 2639588382889602690808909)
                      ·
                        rfl

theorem cell23_5140580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_5140580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140580 prefixEnd_5140580 := by exact prefixLift 5140580
  have htrace : WordTrace (prefixWord ++ tailWord_5140580) baseStart_5140580 baseEnd_5140580 := by
    simpa [prefixWord, tailWord_5140580, baseEnd_5140580] using wordTrace_append hprefix tailTrace_5140580
  have hstable : (prefixWord ++ tailWord_5140580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140580).length < 2 ^ (prefixWord ++ tailWord_5140580).sum := by decide
  have hdescent : baseEnd_5140580 < baseStart_5140580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140613 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_5140613 : Nat := 118140960795 + 5140613 * 2 ^ 59
def prefixEnd_5140613 : Nat := 4983230072969 + 3 ^ 40 * 5140613 * 2
def baseEnd_5140613 : Nat := 2639605327751201061696257

theorem tailTrace_5140613 : CollatzResearch.WordTrace tailWord_5140613 prefixEnd_5140613 2639605327751201061696257 := by
  unfold tailWord_5140613
  simp only [CollatzResearch.WordTrace]
  refine ⟨187493559325444522648594493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124995706216963015099062995 187493559325444522648594493)
  ·
    refine ⟨70310084747041695993222935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187493559325444522648594493 70310084747041695993222935)
    ·
      refine ⟨105465127120562543989834403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70310084747041695993222935 105465127120562543989834403)
      ·
        refine ⟨158197690680843815984751605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105465127120562543989834403 158197690680843815984751605)
        ·
          refine ⟨14831033501329107748570463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158197690680843815984751605 14831033501329107748570463)
          ·
            refine ⟨22246550251993661622855695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14831033501329107748570463 22246550251993661622855695)
            ·
              refine ⟨33369825377990492434283543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22246550251993661622855695 33369825377990492434283543)
              ·
                refine ⟨50054738066985738651425315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33369825377990492434283543 50054738066985738651425315)
                ·
                  refine ⟨75082107100478607977137973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50054738066985738651425315 75082107100478607977137973)
                  ·
                    refine ⟨7038947540669869497856685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 75082107100478607977137973 7038947540669869497856685)
                    ·
                      refine ⟨2639605327751201061696257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7038947540669869497856685 2639605327751201061696257)
                      ·
                        rfl

theorem cell23_5140613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_5140613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140613 prefixEnd_5140613 := by exact prefixLift 5140613
  have htrace : WordTrace (prefixWord ++ tailWord_5140613) baseStart_5140613 baseEnd_5140613 := by
    simpa [prefixWord, tailWord_5140613, baseEnd_5140613] using wordTrace_append hprefix tailTrace_5140613
  have hstable : (prefixWord ++ tailWord_5140613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140613).length < 2 ^ (prefixWord ++ tailWord_5140613).sum := by decide
  have hdescent : baseEnd_5140613 < baseStart_5140613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140690 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_5140690 : Nat := 118140960795 + 5140690 * 2 ^ 59
def prefixEnd_5140690 : Nat := 4983230072969 + 3 ^ 40 * 5140690 * 2
def baseEnd_5140690 : Nat := 2639644865761597260433403

theorem tailTrace_5140690 : CollatzResearch.WordTrace tailWord_5140690 prefixEnd_5140690 2639644865761597260433403 := by
  unfold tailWord_5140690
  simp only [CollatzResearch.WordTrace]
  refine ⟨46874091936541391199786881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124997578497443709866098349 46874091936541391199786881)
  ·
    refine ⟨35155568952406043399840161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46874091936541391199786881 35155568952406043399840161)
    ·
      refine ⟨26366676714304532549880121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35155568952406043399840161 26366676714304532549880121)
      ·
        refine ⟨19775007535728399412410091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26366676714304532549880121 19775007535728399412410091)
        ·
          refine ⟨29662511303592599118615137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19775007535728399412410091 29662511303592599118615137)
          ·
            refine ⟨22246883477694449338961353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29662511303592599118615137 22246883477694449338961353)
            ·
              refine ⟨16685162608270837004221015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22246883477694449338961353 16685162608270837004221015)
              ·
                refine ⟨25027743912406255506331523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16685162608270837004221015 25027743912406255506331523)
                ·
                  refine ⟨37541615868609383259497285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25027743912406255506331523 37541615868609383259497285)
                  ·
                    refine ⟨7039052975364259361155741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37541615868609383259497285 7039052975364259361155741)
                    ·
                      refine ⟨2639644865761597260433403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039052975364259361155741 2639644865761597260433403)
                      ·
                        rfl

theorem cell23_5140690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_5140690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140690 prefixEnd_5140690 := by exact prefixLift 5140690
  have htrace : WordTrace (prefixWord ++ tailWord_5140690) baseStart_5140690 baseEnd_5140690 := by
    simpa [prefixWord, tailWord_5140690, baseEnd_5140690] using wordTrace_append hprefix tailTrace_5140690
  have hstable : (prefixWord ++ tailWord_5140690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140690).length < 2 ^ (prefixWord ++ tailWord_5140690).sum := by decide
  have hdescent : baseEnd_5140690 < baseStart_5140690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140697 : List Nat := [1, 2, 1, 2, 3, 1, 5, 3, 1, 4]
def baseStart_5140697 : Nat := 118140960795 + 5140697 * 2 ^ 59
def prefixEnd_5140697 : Nat := 4983230072969 + 3 ^ 40 * 5140697 * 2
def baseEnd_5140697 : Nat := 879882820042059577681957

theorem tailTrace_5140697 : CollatzResearch.WordTrace tailWord_5140697 prefixEnd_5140697 879882820042059577681957 := by
  unfold tailWord_5140697
  simp only [CollatzResearch.WordTrace]
  refine ⟨187496623057140204994652345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124997748704760136663101563 187496623057140204994652345)
  ·
    refine ⟨140622467292855153745989259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187496623057140204994652345 140622467292855153745989259)
    ·
      refine ⟨210933700939282730618983889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140622467292855153745989259 210933700939282730618983889)
      ·
        refine ⟨158200275704462047964237917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210933700939282730618983889 158200275704462047964237917)
        ·
          refine ⟨59325103389173267986589219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158200275704462047964237917 59325103389173267986589219)
          ·
            refine ⟨88987655083759901979883829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59325103389173267986589219 88987655083759901979883829)
            ·
              refine ⟨8342592664102490810614109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88987655083759901979883829 8342592664102490810614109)
              ·
                refine ⟨3128472249038434053980291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8342592664102490810614109 3128472249038434053980291)
                ·
                  refine ⟨4692708373557651080970437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128472249038434053980291 4692708373557651080970437)
                  ·
                    refine ⟨879882820042059577681957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692708373557651080970437 879882820042059577681957)
                    ·
                      rfl

theorem cell23_5140697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 1, 4].length) (baseStart_5140697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140697 prefixEnd_5140697 := by exact prefixLift 5140697
  have htrace : WordTrace (prefixWord ++ tailWord_5140697) baseStart_5140697 baseEnd_5140697 := by
    simpa [prefixWord, tailWord_5140697, baseEnd_5140697] using wordTrace_append hprefix tailTrace_5140697
  have hstable : (prefixWord ++ tailWord_5140697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140697).length < 2 ^ (prefixWord ++ tailWord_5140697).sum := by decide
  have hdescent : baseEnd_5140697 < baseStart_5140697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140714 : List Nat := [3, 1, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_5140714 : Nat := 118140960795 + 5140714 * 2 ^ 59
def prefixEnd_5140714 : Nat := 4983230072969 + 3 ^ 40 * 5140714 * 2
def baseEnd_5140714 : Nat := 879885729765768388844431

theorem tailTrace_5140714 : CollatzResearch.WordTrace tailWord_5140714 prefixEnd_5140714 879885729765768388844431 := by
  unfold tailWord_5140714
  simp only [CollatzResearch.WordTrace]
  refine ⟨46874310774519654224505299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 124998162065385744598680797 46874310774519654224505299)
  ·
    refine ⟨70311466161779481336757949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46874310774519654224505299 70311466161779481336757949)
    ·
      refine ⟨26366799810667305501284231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70311466161779481336757949 26366799810667305501284231)
      ·
        refine ⟨39550199716000958251926347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26366799810667305501284231 39550199716000958251926347)
        ·
          refine ⟨59325299574001437377889521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39550199716000958251926347 59325299574001437377889521)
          ·
            refine ⟨44493974680501078033417141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59325299574001437377889521 44493974680501078033417141)
            ·
              refine ⟨4171310126296976065632857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44493974680501078033417141 4171310126296976065632857)
              ·
                refine ⟨3128482594722732049224643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171310126296976065632857 3128482594722732049224643)
                ·
                  refine ⟨4692723892084098073836965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128482594722732049224643 4692723892084098073836965)
                  ·
                    refine ⟨879885729765768388844431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692723892084098073836965 879885729765768388844431)
                    ·
                      rfl

theorem cell23_5140714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_5140714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140714 prefixEnd_5140714 := by exact prefixLift 5140714
  have htrace : WordTrace (prefixWord ++ tailWord_5140714) baseStart_5140714 baseEnd_5140714 := by
    simpa [prefixWord, tailWord_5140714, baseEnd_5140714] using wordTrace_append hprefix tailTrace_5140714
  have hstable : (prefixWord ++ tailWord_5140714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140714).length < 2 ^ (prefixWord ++ tailWord_5140714).sum := by decide
  have hdescent : baseEnd_5140714 < baseStart_5140714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140723 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 3, 5]
def baseStart_5140723 : Nat := 118140960795 + 5140723 * 2 ^ 59
def prefixEnd_5140723 : Nat := 4983230072969 + 3 ^ 40 * 5140723 * 2
def baseEnd_5140723 : Nat := 879887270207731877106917

theorem tailTrace_5140723 : CollatzResearch.WordTrace tailWord_5140723 prefixEnd_5140723 879887270207731877106917 := by
  unfold tailWord_5140723
  simp only [CollatzResearch.WordTrace]
  refine ⟨187497571355046011435098823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124998380903364007623399215 187497571355046011435098823)
  ·
    refine ⟨281246357032569017152648235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187497571355046011435098823 281246357032569017152648235)
    ·
      refine ⟨421869535548853525728972353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281246357032569017152648235 421869535548853525728972353)
      ·
        refine ⟨316402151661640144296729265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421869535548853525728972353 316402151661640144296729265)
        ·
          refine ⟨237301613746230108222546949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316402151661640144296729265 237301613746230108222546949)
          ·
            refine ⟨44494052577418145291727553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 237301613746230108222546949 44494052577418145291727553)
            ·
              refine ⟨33370539433063608968795665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44494052577418145291727553 33370539433063608968795665)
              ·
                refine ⟨25027904574797706726596749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33370539433063608968795665 25027904574797706726596749)
                ·
                  refine ⟨9385464215549140022473781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25027904574797706726596749 9385464215549140022473781)
                  ·
                    refine ⟨879887270207731877106917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9385464215549140022473781 879887270207731877106917)
                    ·
                      rfl

theorem cell23_5140723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 5].length) (baseStart_5140723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140723 prefixEnd_5140723 := by exact prefixLift 5140723
  have htrace : WordTrace (prefixWord ++ tailWord_5140723) baseStart_5140723 baseEnd_5140723 := by
    simpa [prefixWord, tailWord_5140723, baseEnd_5140723] using wordTrace_append hprefix tailTrace_5140723
  have hstable : (prefixWord ++ tailWord_5140723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140723).length < 2 ^ (prefixWord ++ tailWord_5140723).sum := by decide
  have hdescent : baseEnd_5140723 < baseStart_5140723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140747 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 2, 3, 2]
def baseStart_5140747 : Nat := 118140960795 + 5140747 * 2 ^ 59
def prefixEnd_5140747 : Nat := 4983230072969 + 3 ^ 40 * 5140747 * 2
def baseEnd_5140747 : Nat := 2639674134158903537420641

theorem tailTrace_5140747 : CollatzResearch.WordTrace tailWord_5140747 prefixEnd_5140747 2639674134158903537420641 := by
  unfold tailWord_5140747
  simp only [CollatzResearch.WordTrace]
  refine ⟨187498446706959063533972495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124998964471306042355981663 187498446706959063533972495)
  ·
    refine ⟨281247670060438595300958743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187498446706959063533972495 281247670060438595300958743)
    ·
      refine ⟨421871505090657892951438115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281247670060438595300958743 421871505090657892951438115)
      ·
        refine ⟨632807257635986839427157173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421871505090657892951438115 632807257635986839427157173)
        ·
          refine ⟨59325680403373766196295985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 632807257635986839427157173 59325680403373766196295985)
          ·
            refine ⟨44494260302530324647221989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59325680403373766196295985 44494260302530324647221989)
            ·
              refine ⟨8342673806724435871354123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44494260302530324647221989 8342673806724435871354123)
              ·
                refine ⟨12514010710086653807031185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342673806724435871354123 12514010710086653807031185)
                ·
                  refine ⟨9385508032564990355273389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12514010710086653807031185 9385508032564990355273389)
                  ·
                    refine ⟨3519565512211871383227521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9385508032564990355273389 3519565512211871383227521)
                    ·
                      refine ⟨2639674134158903537420641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519565512211871383227521 2639674134158903537420641)
                      ·
                        rfl

theorem cell23_5140747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 3, 2].length) (baseStart_5140747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140747 prefixEnd_5140747 := by exact prefixLift 5140747
  have htrace : WordTrace (prefixWord ++ tailWord_5140747) baseStart_5140747 baseEnd_5140747 := by
    simpa [prefixWord, tailWord_5140747, baseEnd_5140747] using wordTrace_append hprefix tailTrace_5140747
  have hstable : (prefixWord ++ tailWord_5140747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140747).length < 2 ^ (prefixWord ++ tailWord_5140747).sum := by decide
  have hdescent : baseEnd_5140747 < baseStart_5140747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140753 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_5140753 : Nat := 118140960795 + 5140753 * 2 ^ 59
def prefixEnd_5140753 : Nat := 4983230072969 + 3 ^ 40 * 5140753 * 2
def baseEnd_5140753 : Nat := 879892405014276837981871

theorem tailTrace_5140753 : CollatzResearch.WordTrace tailWord_5140753 prefixEnd_5140753 879892405014276837981871 := by
  unfold tailWord_5140753
  simp only [CollatzResearch.WordTrace]
  refine ⟨187498665544937326558690913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124999110363291551039127275 187498665544937326558690913)
  ·
    refine ⟨140623999158702994919018185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187498665544937326558690913 140623999158702994919018185)
    ·
      refine ⟨105467999369027246189263639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140623999158702994919018185 105467999369027246189263639)
      ·
        refine ⟨158201999053540869283895459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105467999369027246189263639 158201999053540869283895459)
        ·
          refine ⟨237302998580311303925843189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158201999053540869283895459 237302998580311303925843189)
          ·
            refine ⟨22247156116904184743047799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 237302998580311303925843189 22247156116904184743047799)
            ·
              refine ⟨33370734175356277114571699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22247156116904184743047799 33370734175356277114571699)
              ·
                refine ⟨50056101263034415671857549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33370734175356277114571699 50056101263034415671857549)
                ·
                  refine ⟨18771037973637905876946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50056101263034415671857549 18771037973637905876946581)
                  ·
                    refine ⟨879892405014276837981871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18771037973637905876946581 879892405014276837981871)
                    ·
                      rfl

theorem cell23_5140753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_5140753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140753 prefixEnd_5140753 := by exact prefixLift 5140753
  have htrace : WordTrace (prefixWord ++ tailWord_5140753) baseStart_5140753 baseEnd_5140753 := by
    simpa [prefixWord, tailWord_5140753, baseEnd_5140753] using wordTrace_append hprefix tailTrace_5140753
  have hstable : (prefixWord ++ tailWord_5140753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140753).length < 2 ^ (prefixWord ++ tailWord_5140753).sum := by decide
  have hdescent : baseEnd_5140753 < baseStart_5140753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140780 : List Nat := [2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_5140780 : Nat := 118140960795 + 5140780 * 2 ^ 59
def prefixEnd_5140780 : Nat := 4983230072969 + 3 ^ 40 * 5140780 * 2
def baseEnd_5140780 : Nat := 2639691079020501908307989

theorem tailTrace_5140780 : CollatzResearch.WordTrace tailWord_5140780 prefixEnd_5140780 2639691079020501908307989 := by
  unfold tailWord_5140780
  simp only [CollatzResearch.WordTrace]
  refine ⟨93749825157919755084961897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 124999766877226340113282529 93749825157919755084961897)
  ·
    refine ⟨70312368868439816313721423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93749825157919755084961897 70312368868439816313721423)
    ·
      refine ⟨105468553302659724470582135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70312368868439816313721423 105468553302659724470582135)
      ·
        refine ⟨158202829953989586705873203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105468553302659724470582135 158202829953989586705873203)
        ·
          refine ⟨237304244930984380058809805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158202829953989586705873203 237304244930984380058809805)
          ·
            refine ⟨88989091849119142522053677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237304244930984380058809805 88989091849119142522053677)
            ·
              refine ⟨33370909443419678445770129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88989091849119142522053677 33370909443419678445770129)
              ·
                refine ⟨25028182082564758834327597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33370909443419678445770129 25028182082564758834327597)
                ·
                  refine ⟨9385568280961784562872849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25028182082564758834327597 9385568280961784562872849)
                  ·
                    refine ⟨7039176210721338422154637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9385568280961784562872849 7039176210721338422154637)
                    ·
                      refine ⟨2639691079020501908307989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039176210721338422154637 2639691079020501908307989)
                      ·
                        rfl

theorem cell23_5140780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_5140780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140780 prefixEnd_5140780 := by exact prefixLift 5140780
  have htrace : WordTrace (prefixWord ++ tailWord_5140780) baseStart_5140780 baseEnd_5140780 := by
    simpa [prefixWord, tailWord_5140780, baseEnd_5140780] using wordTrace_append hprefix tailTrace_5140780
  have hstable : (prefixWord ++ tailWord_5140780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140780).length < 2 ^ (prefixWord ++ tailWord_5140780).sum := by decide
  have hdescent : baseEnd_5140780 < baseStart_5140780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140783 : List Nat := [1, 1, 2, 1, 2, 1, 7, 8]
def baseStart_5140783 : Nat := 118140960795 + 5140783 * 2 ^ 59
def prefixEnd_5140783 : Nat := 4983230072969 + 3 ^ 40 * 5140783 * 2
def baseEnd_5140783 : Nat := 97766393313424644317425

theorem tailTrace_5140783 : CollatzResearch.WordTrace tailWord_5140783 prefixEnd_5140783 97766393313424644317425 := by
  unfold tailWord_5140783
  simp only [CollatzResearch.WordTrace]
  refine ⟨187499759734828641682283003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 124999839823219094454855335 187499759734828641682283003)
  ·
    refine ⟨281249639602242962523424505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187499759734828641682283003 281249639602242962523424505)
    ·
      refine ⟨210937229701682221892568379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281249639602242962523424505 210937229701682221892568379)
      ·
        refine ⟨316405844552523332838852569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210937229701682221892568379 316405844552523332838852569)
        ·
          refine ⟨237304383414392499629139427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316405844552523332838852569 237304383414392499629139427)
          ·
            refine ⟨355956575121588749443709141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237304383414392499629139427 355956575121588749443709141)
            ·
              refine ⟨8342732229412236315086933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 355956575121588749443709141 8342732229412236315086933)
              ·
                refine ⟨97766393313424644317425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8342732229412236315086933 97766393313424644317425)
                ·
                  rfl

theorem cell23_5140783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 8].length) (baseStart_5140783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140783 prefixEnd_5140783 := by exact prefixLift 5140783
  have htrace : WordTrace (prefixWord ++ tailWord_5140783) baseStart_5140783 baseEnd_5140783 := by
    simpa [prefixWord, tailWord_5140783, baseEnd_5140783] using wordTrace_append hprefix tailTrace_5140783
  have hstable : (prefixWord ++ tailWord_5140783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140783).length < 2 ^ (prefixWord ++ tailWord_5140783).sum := by decide
  have hdescent : baseEnd_5140783 < baseStart_5140783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140794 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_5140794 : Nat := 118140960795 + 5140794 * 2 ^ 59
def prefixEnd_5140794 : Nat := 4983230072969 + 3 ^ 40 * 5140794 * 2
def baseEnd_5140794 : Nat := 2639698267749664853532925

theorem tailTrace_5140794 : CollatzResearch.WordTrace tailWord_5140794 prefixEnd_5140794 2639698267749664853532925 := by
  unfold tailWord_5140794
  simp only [CollatzResearch.WordTrace]
  refine ⟨46875040234447197640233359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125000107291859193707288957 46875040234447197640233359)
  ·
    refine ⟨70312560351670796460350039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46875040234447197640233359 70312560351670796460350039)
    ·
      refine ⟨105468840527506194690525059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70312560351670796460350039 105468840527506194690525059)
      ·
        refine ⟨158203260791259292035787589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105468840527506194690525059 158203260791259292035787589)
        ·
          refine ⟨29663111398361117256710173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158203260791259292035787589 29663111398361117256710173)
          ·
            refine ⟨11123666774385418971266315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29663111398361117256710173 11123666774385418971266315)
            ·
              refine ⟨16685500161578128456899473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11123666774385418971266315 16685500161578128456899473)
              ·
                refine ⟨12514125121183596342674605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16685500161578128456899473 12514125121183596342674605)
                ·
                  refine ⟨4692796920443848628502977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12514125121183596342674605 4692796920443848628502977)
                  ·
                    refine ⟨3519597690332886471377233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692796920443848628502977 3519597690332886471377233)
                    ·
                      refine ⟨2639698267749664853532925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519597690332886471377233 2639698267749664853532925)
                      ·
                        rfl

theorem cell23_5140794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_5140794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140794 prefixEnd_5140794 := by exact prefixLift 5140794
  have htrace : WordTrace (prefixWord ++ tailWord_5140794) baseStart_5140794 baseEnd_5140794 := by
    simpa [prefixWord, tailWord_5140794, baseEnd_5140794] using wordTrace_append hprefix tailTrace_5140794
  have hstable : (prefixWord ++ tailWord_5140794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140794).length < 2 ^ (prefixWord ++ tailWord_5140794).sum := by decide
  have hdescent : baseEnd_5140794 < baseStart_5140794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140821 : List Nat := [1, 3, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_5140821 : Nat := 118140960795 + 5140821 * 2 ^ 59
def prefixEnd_5140821 : Nat := 4983230072969 + 3 ^ 40 * 5140821 * 2
def baseEnd_5140821 : Nat := 879904043909112082631767

theorem tailTrace_5140821 : CollatzResearch.WordTrace tailWord_5140821 prefixEnd_5140821 879904043909112082631767 := by
  unfold tailWord_5140821
  simp only [CollatzResearch.WordTrace]
  refine ⟨187501145708690974172166317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125000763805793982781444211 187501145708690974172166317)
  ·
    refine ⟨70312929640759115314562369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187501145708690974172166317 70312929640759115314562369)
    ·
      refine ⟨52734697230569336485921777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70312929640759115314562369 52734697230569336485921777)
      ·
        refine ⟨39551022922927002364441333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52734697230569336485921777 39551022922927002364441333)
        ·
          refine ⟨3707908399024406471666375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39551022922927002364441333 3707908399024406471666375)
          ·
            refine ⟨5561862598536609707499563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3707908399024406471666375 5561862598536609707499563)
            ·
              refine ⟨8342793897804914561249345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561862598536609707499563 8342793897804914561249345)
              ·
                refine ⟨6257095423353685920937009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8342793897804914561249345 6257095423353685920937009)
                ·
                  refine ⟨4692821567515264440702757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6257095423353685920937009 4692821567515264440702757)
                  ·
                    refine ⟨879904043909112082631767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4692821567515264440702757 879904043909112082631767)
                    ·
                      rfl

theorem cell23_5140821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_5140821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140821 prefixEnd_5140821 := by exact prefixLift 5140821
  have htrace : WordTrace (prefixWord ++ tailWord_5140821) baseStart_5140821 baseEnd_5140821 := by
    simpa [prefixWord, tailWord_5140821, baseEnd_5140821] using wordTrace_append hprefix tailTrace_5140821
  have hstable : (prefixWord ++ tailWord_5140821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140821).length < 2 ^ (prefixWord ++ tailWord_5140821).sum := by decide
  have hdescent : baseEnd_5140821 < baseStart_5140821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140828 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_5140828 : Nat := 118140960795 + 5140828 * 2 ^ 59
def prefixEnd_5140828 : Nat := 4983230072969 + 3 ^ 40 * 5140828 * 2
def baseEnd_5140828 : Nat := 2639715726091917720507769

theorem tailTrace_5140828 : CollatzResearch.WordTrace tailWord_5140828 prefixEnd_5140828 2639715726091917720507769 := by
  unfold tailWord_5140828
  simp only [CollatzResearch.WordTrace]
  refine ⟨93750700509832807183835569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125000934013110409578447425 93750700509832807183835569)
  ·
    refine ⟨70313025382374605387876677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93750700509832807183835569 70313025382374605387876677)
    ·
      refine ⟨13183692259195238510226877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70313025382374605387876677 13183692259195238510226877)
      ·
        refine ⟨4943884597198214441335079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13183692259195238510226877 4943884597198214441335079)
        ·
          refine ⟨7415826895797321662002619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943884597198214441335079 7415826895797321662002619)
          ·
            refine ⟨11123740343695982493003929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7415826895797321662002619 11123740343695982493003929)
            ·
              refine ⟨8342805257771986869752947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11123740343695982493003929 8342805257771986869752947)
              ·
                refine ⟨12514207886657980304629421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342805257771986869752947 12514207886657980304629421)
                ·
                  refine ⟨4692827957496742614236033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12514207886657980304629421 4692827957496742614236033)
                  ·
                    refine ⟨3519620968122556960677025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4692827957496742614236033 3519620968122556960677025)
                    ·
                      refine ⟨2639715726091917720507769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519620968122556960677025 2639715726091917720507769)
                      ·
                        rfl

theorem cell23_5140828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_5140828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140828 prefixEnd_5140828 := by exact prefixLift 5140828
  have htrace : WordTrace (prefixWord ++ tailWord_5140828) baseStart_5140828 baseEnd_5140828 := by
    simpa [prefixWord, tailWord_5140828, baseEnd_5140828] using wordTrace_append hprefix tailTrace_5140828
  have hstable : (prefixWord ++ tailWord_5140828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140828).length < 2 ^ (prefixWord ++ tailWord_5140828).sum := by decide
  have hdescent : baseEnd_5140828 < baseStart_5140828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140844 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_5140844 : Nat := 118140960795 + 5140844 * 2 ^ 59
def prefixEnd_5140844 : Nat := 4983230072969 + 3 ^ 40 * 5140844 * 2
def baseEnd_5140844 : Nat := 2639723941782389657907695

theorem tailTrace_5140844 : CollatzResearch.WordTrace tailWord_5140844 prefixEnd_5140844 2639723941782389657907695 := by
  unfold tailWord_5140844
  simp only [CollatzResearch.WordTrace]
  refine ⟨93750992293803824550126793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125001323058405099400169057 93750992293803824550126793)
  ·
    refine ⟨70313244220352868412595095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93750992293803824550126793 70313244220352868412595095)
    ·
      refine ⟨105469866330529302618892643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70313244220352868412595095 105469866330529302618892643)
      ·
        refine ⟨158204799495793953928338965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105469866330529302618892643 158204799495793953928338965)
        ·
          refine ⟨7415849976365341590390889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 158204799495793953928338965 7415849976365341590390889)
          ·
            refine ⟨5561887482274006192793167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7415849976365341590390889 5561887482274006192793167)
            ·
              refine ⟨8342831223411009289189751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5561887482274006192793167 8342831223411009289189751)
              ·
                refine ⟨12514246835116513933784627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8342831223411009289189751 12514246835116513933784627)
                ·
                  refine ⟨18771370252674770900676941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12514246835116513933784627 18771370252674770900676941)
                  ·
                    refine ⟨7039263844753039087753853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18771370252674770900676941 7039263844753039087753853)
                    ·
                      refine ⟨2639723941782389657907695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039263844753039087753853 2639723941782389657907695)
                      ·
                        rfl

theorem cell23_5140844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_5140844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140844 prefixEnd_5140844 := by exact prefixLift 5140844
  have htrace : WordTrace (prefixWord ++ tailWord_5140844) baseStart_5140844 baseEnd_5140844 := by
    simpa [prefixWord, tailWord_5140844, baseEnd_5140844] using wordTrace_append hprefix tailTrace_5140844
  have hstable : (prefixWord ++ tailWord_5140844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140844).length < 2 ^ (prefixWord ++ tailWord_5140844).sum := by decide
  have hdescent : baseEnd_5140844 < baseStart_5140844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140957 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_5140957 : Nat := 118140960795 + 5140957 * 2 ^ 59
def prefixEnd_5140957 : Nat := 4983230072969 + 3 ^ 40 * 5140957 * 2
def baseEnd_5140957 : Nat := 2639781965096347715794675

theorem tailTrace_5140957 : CollatzResearch.WordTrace tailWord_5140957 prefixEnd_5140957 2639781965096347715794675 := by
  unfold tailWord_5140957
  simp only [CollatzResearch.WordTrace]
  refine ⟨187506106036198269399117125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125004070690798846266078083 187506106036198269399117125)
  ·
    refine ⟨35157394881787175512334461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187506106036198269399117125 35157394881787175512334461)
    ·
      refine ⟨13184023080670190817125423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35157394881787175512334461 13184023080670190817125423)
      ·
        refine ⟨19776034621005286225688135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184023080670190817125423 19776034621005286225688135)
        ·
          refine ⟨29664051931507929338532203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19776034621005286225688135 29664051931507929338532203)
          ·
            refine ⟨44496077897261894007798305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29664051931507929338532203 44496077897261894007798305)
            ·
              refine ⟨33372058422946420505848729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44496077897261894007798305 33372058422946420505848729)
              ·
                refine ⟨25029043817209815379386547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33372058422946420505848729 25029043817209815379386547)
                ·
                  refine ⟨37543565725814723069079821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25029043817209815379386547 37543565725814723069079821)
                  ·
                    refine ⟨14078837147180521150904933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37543565725814723069079821 14078837147180521150904933)
                    ·
                      refine ⟨2639781965096347715794675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14078837147180521150904933 2639781965096347715794675)
                      ·
                        rfl

theorem cell23_5140957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_5140957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140957 prefixEnd_5140957 := by exact prefixLift 5140957
  have htrace : WordTrace (prefixWord ++ tailWord_5140957) baseStart_5140957 baseEnd_5140957 := by
    simpa [prefixWord, tailWord_5140957, baseEnd_5140957] using wordTrace_append hprefix tailTrace_5140957
  have hstable : (prefixWord ++ tailWord_5140957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140957).length < 2 ^ (prefixWord ++ tailWord_5140957).sum := by decide
  have hdescent : baseEnd_5140957 < baseStart_5140957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140974 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4]
def baseStart_5140974 : Nat := 118140960795 + 5140974 * 2 ^ 59
def prefixEnd_5140974 : Nat := 4983230072969 + 3 ^ 40 * 5140974 * 2
def baseEnd_5140974 : Nat := 2639790694267474149282097

theorem tailTrace_5140974 : CollatzResearch.WordTrace tailWord_5140974 prefixEnd_5140974 2639790694267474149282097 := by
  unfold tailWord_5140974
  simp only [CollatzResearch.WordTrace]
  refine ⟨23438340759642085162810747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 125004484051424454201657317 23438340759642085162810747)
  ·
    refine ⟨35157511139463127744216121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23438340759642085162810747 35157511139463127744216121)
    ·
      refine ⟨26368133354597345808162091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35157511139463127744216121 26368133354597345808162091)
      ·
        refine ⟨39552200031896018712243137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26368133354597345808162091 39552200031896018712243137)
        ·
          refine ⟨29664150023922014034182353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39552200031896018712243137 29664150023922014034182353)
          ·
            refine ⟨22248112517941510525636765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29664150023922014034182353 22248112517941510525636765)
            ·
              refine ⟨8343042194228066447113787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22248112517941510525636765 8343042194228066447113787)
              ·
                refine ⟨12514563291342099670670681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343042194228066447113787 12514563291342099670670681)
                ·
                  refine ⟨9385922468506574753003011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12514563291342099670670681 9385922468506574753003011)
                  ·
                    refine ⟨14078883702759862129504517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9385922468506574753003011 14078883702759862129504517)
                    ·
                      refine ⟨2639790694267474149282097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14078883702759862129504517 2639790694267474149282097)
                      ·
                        rfl

theorem cell23_5140974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_5140974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140974 prefixEnd_5140974 := by exact prefixLift 5140974
  have htrace : WordTrace (prefixWord ++ tailWord_5140974) baseStart_5140974 baseEnd_5140974 := by
    simpa [prefixWord, tailWord_5140974, baseEnd_5140974] using wordTrace_append hprefix tailTrace_5140974
  have hstable : (prefixWord ++ tailWord_5140974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140974).length < 2 ^ (prefixWord ++ tailWord_5140974).sum := by decide
  have hdescent : baseEnd_5140974 < baseStart_5140974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140977 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_5140977 : Nat := 118140960795 + 5140977 * 2 ^ 59
def prefixEnd_5140977 : Nat := 4983230072969 + 3 ^ 40 * 5140977 * 2
def baseEnd_5140977 : Nat := 2639792234709437637544583

theorem tailTrace_5140977 : CollatzResearch.WordTrace tailWord_5140977 prefixEnd_5140977 2639792234709437637544583 := by
  unfold tailWord_5140977
  simp only [CollatzResearch.WordTrace]
  refine ⟨187506835496125812814845185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125004556997417208543230123 187506835496125812814845185)
  ·
    refine ⟨140630126622094359611133889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187506835496125812814845185 140630126622094359611133889)
    ·
      refine ⟨105472594966570769708350417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140630126622094359611133889 105472594966570769708350417)
      ·
        refine ⟨79104446224928077281262813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105472594966570769708350417 79104446224928077281262813)
        ·
          refine ⟨29664167334348028980473555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79104446224928077281262813 29664167334348028980473555)
          ·
            refine ⟨44496251001522043470710333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29664167334348028980473555 44496251001522043470710333)
            ·
              refine ⟨16686094125570766301516375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44496251001522043470710333 16686094125570766301516375)
              ·
                refine ⟨25029141188356149452274563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16686094125570766301516375 25029141188356149452274563)
                ·
                  refine ⟨37543711782534224178411845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25029141188356149452274563 37543711782534224178411845)
                  ·
                    refine ⟨7039445959225167033452221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37543711782534224178411845 7039445959225167033452221)
                    ·
                      refine ⟨2639792234709437637544583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039445959225167033452221 2639792234709437637544583)
                      ·
                        rfl

theorem cell23_5140977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_5140977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140977 prefixEnd_5140977 := by exact prefixLift 5140977
  have htrace : WordTrace (prefixWord ++ tailWord_5140977) baseStart_5140977 baseEnd_5140977 := by
    simpa [prefixWord, tailWord_5140977, baseEnd_5140977] using wordTrace_append hprefix tailTrace_5140977
  have hstable : (prefixWord ++ tailWord_5140977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140977).length < 2 ^ (prefixWord ++ tailWord_5140977).sum := by decide
  have hdescent : baseEnd_5140977 < baseStart_5140977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5140997 : List Nat := [1, 3, 1, 1, 2, 2, 5, 2, 6]
def baseStart_5140997 : Nat := 118140960795 + 5140997 * 2 ^ 59
def prefixEnd_5140997 : Nat := 4983230072969 + 3 ^ 40 * 5140997 * 2
def baseEnd_5140997 : Nat := 293311389369169728810499

theorem tailTrace_5140997 : CollatzResearch.WordTrace tailWord_5140997 prefixEnd_5140997 293311389369169728810499 := by
  unfold tailWord_5140997
  simp only [CollatzResearch.WordTrace]
  refine ⟨187507564956053356230573245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125005043304035570820382163 187507564956053356230573245)
  ·
    refine ⟨70315336858520008586464967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187507564956053356230573245 70315336858520008586464967)
    ·
      refine ⟨105473005287780012879697451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70315336858520008586464967 105473005287780012879697451)
      ·
        refine ⟨158209507931670019319546177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105473005287780012879697451 158209507931670019319546177)
        ·
          refine ⟨118657130948752514489659633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158209507931670019319546177 118657130948752514489659633)
          ·
            refine ⟨88992848211564385867244725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118657130948752514489659633 88992848211564385867244725)
            ·
              refine ⟨8343079519834161175054193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88992848211564385867244725 8343079519834161175054193)
              ·
                refine ⟨6257309639875620881290645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8343079519834161175054193 6257309639875620881290645)
                ·
                  refine ⟨293311389369169728810499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6257309639875620881290645 293311389369169728810499)
                  ·
                    rfl

theorem cell23_5140997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_5140997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5140997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5140997 prefixEnd_5140997 := by exact prefixLift 5140997
  have htrace : WordTrace (prefixWord ++ tailWord_5140997) baseStart_5140997 baseEnd_5140997 := by
    simpa [prefixWord, tailWord_5140997, baseEnd_5140997] using wordTrace_append hprefix tailTrace_5140997
  have hstable : (prefixWord ++ tailWord_5140997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5140997).length < 2 ^ (prefixWord ++ tailWord_5140997).sum := by decide
  have hdescent : baseEnd_5140997 < baseStart_5140997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5140997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141067 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_5141067 : Nat := 118140960795 + 5141067 * 2 ^ 59
def prefixEnd_5141067 : Nat := 4983230072969 + 3 ^ 40 * 5141067 * 2
def baseEnd_5141067 : Nat := 2639838447968342285419169

theorem tailTrace_5141067 : CollatzResearch.WordTrace tailWord_5141067 prefixEnd_5141067 2639838447968342285419169 := by
  unfold tailWord_5141067
  simp only [CollatzResearch.WordTrace]
  refine ⟨187510118065799758185621455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125006745377199838790414303 187510118065799758185621455)
  ·
    refine ⟨281265177098699637278432183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187510118065799758185621455 281265177098699637278432183)
    ·
      refine ⟨421897765648049455917648275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281265177098699637278432183 421897765648049455917648275)
      ·
        refine ⟨632846648472074183876472413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421897765648049455917648275 632846648472074183876472413)
        ·
          refine ⟨237317493177027818953677155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 632846648472074183876472413 237317493177027818953677155)
          ·
            refine ⟨355976239765541728430515733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237317493177027818953677155 355976239765541728430515733)
            ·
              refine ⟨16686386239009768520180425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 355976239765541728430515733 16686386239009768520180425)
              ·
                refine ⟨12514789679257326390135319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16686386239009768520180425 12514789679257326390135319)
                ·
                  refine ⟨18772184518885989585202979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12514789679257326390135319 18772184518885989585202979)
                  ·
                    refine ⟨28158276778328984377804469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18772184518885989585202979 28158276778328984377804469)
                    ·
                      refine ⟨2639838447968342285419169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28158276778328984377804469 2639838447968342285419169)
                      ·
                        rfl

theorem cell23_5141067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_5141067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141067 prefixEnd_5141067 := by exact prefixLift 5141067
  have htrace : WordTrace (prefixWord ++ tailWord_5141067) baseStart_5141067 baseEnd_5141067 := by
    simpa [prefixWord, tailWord_5141067, baseEnd_5141067] using wordTrace_append hprefix tailTrace_5141067
  have hstable : (prefixWord ++ tailWord_5141067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141067).length < 2 ^ (prefixWord ++ tailWord_5141067).sum := by decide
  have hdescent : baseEnd_5141067 < baseStart_5141067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141077 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_5141077 : Nat := 118140960795 + 5141077 * 2 ^ 59
def prefixEnd_5141077 : Nat := 4983230072969 + 3 ^ 40 * 5141077 * 2
def baseEnd_5141077 : Nat := 2639843582774887246294123

theorem tailTrace_5141077 : CollatzResearch.WordTrace tailWord_5141077 prefixEnd_5141077 2639843582774887246294123 := by
  unfold tailWord_5141077
  simp only [CollatzResearch.WordTrace]
  refine ⟨187510482795763529893485485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125006988530509019928990323 187510482795763529893485485)
  ·
    refine ⟨70316431048411323710057057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187510482795763529893485485 70316431048411323710057057)
    ·
      refine ⟨52737323286308492782542793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70316431048411323710057057 52737323286308492782542793)
      ·
        refine ⟨39552992464731369586907095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52737323286308492782542793 39552992464731369586907095)
        ·
          refine ⟨59329488697097054380360643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39552992464731369586907095 59329488697097054380360643)
          ·
            refine ⟨88994233045645581570540965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59329488697097054380360643 88994233045645581570540965)
            ·
              refine ⟨16686418696058546544476431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88994233045645581570540965 16686418696058546544476431)
              ·
                refine ⟨25029628044087819816714647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16686418696058546544476431 25029628044087819816714647)
                ·
                  refine ⟨37544442066131729725071971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25029628044087819816714647 37544442066131729725071971)
                  ·
                    refine ⟨56316663099197594587607957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37544442066131729725071971 56316663099197594587607957)
                    ·
                      refine ⟨2639843582774887246294123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56316663099197594587607957 2639843582774887246294123)
                      ·
                        rfl

theorem cell23_5141077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_5141077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141077 prefixEnd_5141077 := by exact prefixLift 5141077
  have htrace : WordTrace (prefixWord ++ tailWord_5141077) baseStart_5141077 baseEnd_5141077 := by
    simpa [prefixWord, tailWord_5141077, baseEnd_5141077] using wordTrace_append hprefix tailTrace_5141077
  have hstable : (prefixWord ++ tailWord_5141077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141077).length < 2 ^ (prefixWord ++ tailWord_5141077).sum := by decide
  have hdescent : baseEnd_5141077 < baseStart_5141077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141101 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_5141101 : Nat := 118140960795 + 5141101 * 2 ^ 59
def prefixEnd_5141101 : Nat := 4983230072969 + 3 ^ 40 * 5141101 * 2
def baseEnd_5141101 : Nat := 2639855906310595152394013

theorem tailTrace_5141101 : CollatzResearch.WordTrace tailWord_5141101 prefixEnd_5141101 2639855906310595152394013 := by
  unfold tailWord_5141101
  simp only [CollatzResearch.WordTrace]
  refine ⟨187511358147676581992359157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125007572098451054661572771 187511358147676581992359157)
  ·
    refine ⟨17579189826344679561783671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187511358147676581992359157 17579189826344679561783671)
    ·
      refine ⟨26368784739517019342675507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17579189826344679561783671 26368784739517019342675507)
      ·
        refine ⟨39553177109275529014013261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26368784739517019342675507 39553177109275529014013261)
        ·
          refine ⟨14832441415978323380254973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39553177109275529014013261 14832441415978323380254973)
          ·
            refine ⟨5562165530991871267595615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14832441415978323380254973 5562165530991871267595615)
            ·
              refine ⟨8343248296487806901393423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562165530991871267595615 8343248296487806901393423)
              ·
                refine ⟨12514872444731710352090135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343248296487806901393423 12514872444731710352090135)
                ·
                  refine ⟨18772308667097565528135203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12514872444731710352090135 18772308667097565528135203)
                  ·
                    refine ⟨28158463000646348292202805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18772308667097565528135203 28158463000646348292202805)
                    ·
                      refine ⟨2639855906310595152394013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28158463000646348292202805 2639855906310595152394013)
                      ·
                        rfl

theorem cell23_5141101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_5141101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141101 prefixEnd_5141101 := by exact prefixLift 5141101
  have htrace : WordTrace (prefixWord ++ tailWord_5141101) baseStart_5141101 baseEnd_5141101 := by
    simpa [prefixWord, tailWord_5141101, baseEnd_5141101] using wordTrace_append hprefix tailTrace_5141101
  have hstable : (prefixWord ++ tailWord_5141101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141101).length < 2 ^ (prefixWord ++ tailWord_5141101).sum := by decide
  have hdescent : baseEnd_5141101 < baseStart_5141101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141109 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_5141109 : Nat := 118140960795 + 5141109 * 2 ^ 59
def prefixEnd_5141109 : Nat := 4983230072969 + 3 ^ 40 * 5141109 * 2
def baseEnd_5141109 : Nat := 2639860014155831121093977

theorem tailTrace_5141109 : CollatzResearch.WordTrace tailWord_5141109 prefixEnd_5141109 2639860014155831121093977 := by
  unfold tailWord_5141109
  simp only [CollatzResearch.WordTrace]
  refine ⟨187511649931647599358650381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125007766621098399572433587 187511649931647599358650381)
  ·
    refine ⟨70316868724367849759493893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187511649931647599358650381 70316868724367849759493893)
    ·
      refine ⟨13184412885818971829905105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70316868724367849759493893 13184412885818971829905105)
      ·
        refine ⟨9888309664364228872428829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13184412885818971829905105 9888309664364228872428829)
        ·
          refine ⟨3708116124136585827160811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9888309664364228872428829 3708116124136585827160811)
          ·
            refine ⟨5562174186204878740741217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708116124136585827160811 5562174186204878740741217)
            ·
              refine ⟨4171630639653659055555913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5562174186204878740741217 4171630639653659055555913)
              ·
                refine ⟨3128722979740244291666935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4171630639653659055555913 3128722979740244291666935)
                ·
                  refine ⟨4693084469610366437500403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3128722979740244291666935 4693084469610366437500403)
                  ·
                    refine ⟨7039626704415549656250605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4693084469610366437500403 7039626704415549656250605)
                    ·
                      refine ⟨2639860014155831121093977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039626704415549656250605 2639860014155831121093977)
                      ·
                        rfl

theorem cell23_5141109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_5141109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141109 prefixEnd_5141109 := by exact prefixLift 5141109
  have htrace : WordTrace (prefixWord ++ tailWord_5141109) baseStart_5141109 baseEnd_5141109 := by
    simpa [prefixWord, tailWord_5141109, baseEnd_5141109] using wordTrace_append hprefix tailTrace_5141109
  have hstable : (prefixWord ++ tailWord_5141109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141109).length < 2 ^ (prefixWord ++ tailWord_5141109).sum := by decide
  have hdescent : baseEnd_5141109 < baseStart_5141109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141114 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_5141114 : Nat := 118140960795 + 5141114 * 2 ^ 59
def prefixEnd_5141114 : Nat := 4983230072969 + 3 ^ 40 * 5141114 * 2
def baseEnd_5141114 : Nat := 2639862581559103601531453

theorem tailTrace_5141114 : CollatzResearch.WordTrace tailWord_5141114 prefixEnd_5141114 2639862581559103601531453 := by
  unfold tailWord_5141114
  simp only [CollatzResearch.WordTrace]
  refine ⟨46877958074157371303145599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125007888197752990141721597 46877958074157371303145599)
  ·
    refine ⟨70316937111236056954718399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46877958074157371303145599 70316937111236056954718399)
    ·
      refine ⟨105475405666854085432077599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70316937111236056954718399 105475405666854085432077599)
      ·
        refine ⟨158213108500281128148116399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105475405666854085432077599 158213108500281128148116399)
        ·
          refine ⟨237319662750421692222174599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158213108500281128148116399 237319662750421692222174599)
          ·
            refine ⟨355979494125632538333261899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237319662750421692222174599 355979494125632538333261899)
            ·
              refine ⟨533969241188448807499892849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355979494125632538333261899 533969241188448807499892849)
              ·
                refine ⟨400476930891336605624919637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533969241188448807499892849 400476930891336605624919637)
                ·
                  refine ⟨4693089033882850847167027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 400476930891336605624919637 4693089033882850847167027)
                  ·
                    refine ⟨7039633550824276270750541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4693089033882850847167027 7039633550824276270750541)
                    ·
                      refine ⟨2639862581559103601531453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039633550824276270750541 2639862581559103601531453)
                      ·
                        rfl

theorem cell23_5141114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_5141114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141114 prefixEnd_5141114 := by exact prefixLift 5141114
  have htrace : WordTrace (prefixWord ++ tailWord_5141114) baseStart_5141114 baseEnd_5141114 := by
    simpa [prefixWord, tailWord_5141114, baseEnd_5141114] using wordTrace_append hprefix tailTrace_5141114
  have hstable : (prefixWord ++ tailWord_5141114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141114).length < 2 ^ (prefixWord ++ tailWord_5141114).sum := by decide
  have hdescent : baseEnd_5141114 < baseStart_5141114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141157 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_5141157 : Nat := 118140960795 + 5141157 * 2 ^ 59
def prefixEnd_5141157 : Nat := 4983230072969 + 3 ^ 40 * 5141157 * 2
def baseEnd_5141157 : Nat := 2639884661227246933293755

theorem tailTrace_5141157 : CollatzResearch.WordTrace tailWord_5141157 prefixEnd_5141157 2639884661227246933293755 := by
  unfold tailWord_5141157
  simp only [CollatzResearch.WordTrace]
  refine ⟨187513400635473703556397725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125008933756982469037598483 187513400635473703556397725)
  ·
    refine ⟨70317525238302638833649147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187513400635473703556397725 70317525238302638833649147)
    ·
      refine ⟨105476287857453958250473721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70317525238302638833649147 105476287857453958250473721)
      ·
        refine ⟨79107215893090468687855291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105476287857453958250473721 79107215893090468687855291)
        ·
          refine ⟨118660823839635703031782937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79107215893090468687855291 118660823839635703031782937)
          ·
            refine ⟨88995617879726777273837203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118660823839635703031782937 88995617879726777273837203)
            ·
              refine ⟨133493426819590165910755805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88995617879726777273837203 133493426819590165910755805)
              ·
                refine ⟨50060035057346312216533427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133493426819590165910755805 50060035057346312216533427)
                ·
                  refine ⟨75090052586019468324800141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50060035057346312216533427 75090052586019468324800141)
                  ·
                    refine ⟨28158769719757300621800053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75090052586019468324800141 28158769719757300621800053)
                    ·
                      refine ⟨2639884661227246933293755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28158769719757300621800053 2639884661227246933293755)
                      ·
                        rfl

theorem cell23_5141157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_5141157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141157 prefixEnd_5141157 := by exact prefixLift 5141157
  have htrace : WordTrace (prefixWord ++ tailWord_5141157) baseStart_5141157 baseEnd_5141157 := by
    simpa [prefixWord, tailWord_5141157, baseEnd_5141157] using wordTrace_append hprefix tailTrace_5141157
  have hstable : (prefixWord ++ tailWord_5141157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141157).length < 2 ^ (prefixWord ++ tailWord_5141157).sum := by decide
  have hdescent : baseEnd_5141157 < baseStart_5141157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141165 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_5141165 : Nat := 118140960795 + 5141165 * 2 ^ 59
def prefixEnd_5141165 : Nat := 4983230072969 + 3 ^ 40 * 5141165 * 2
def baseEnd_5141165 : Nat := 2639888769072482901993719

theorem tailTrace_5141165 : CollatzResearch.WordTrace tailWord_5141165 prefixEnd_5141165 2639888769072482901993719 := by
  unfold tailWord_5141165
  simp only [CollatzResearch.WordTrace]
  refine ⟨187513692419444720922688949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125009128279629813948459299 187513692419444720922688949)
  ·
    refine ⟨17579408664322942586502089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187513692419444720922688949 17579408664322942586502089)
    ·
      refine ⟨13184556498242206939876567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17579408664322942586502089 13184556498242206939876567)
      ·
        refine ⟨19776834747363310409814851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184556498242206939876567 19776834747363310409814851)
        ·
          refine ⟨29665252121044965614722277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19776834747363310409814851 29665252121044965614722277)
          ·
            refine ⟨5562234772695931052760427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29665252121044965614722277 5562234772695931052760427)
            ·
              refine ⟨8343352159043896579140641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5562234772695931052760427 8343352159043896579140641)
              ·
                refine ⟨6257514119282922434355481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8343352159043896579140641 6257514119282922434355481)
                ·
                  refine ⟨4693135589462191825766611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6257514119282922434355481 4693135589462191825766611)
                  ·
                    refine ⟨7039703384193287738649917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4693135589462191825766611 7039703384193287738649917)
                    ·
                      refine ⟨2639888769072482901993719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039703384193287738649917 2639888769072482901993719)
                      ·
                        rfl

theorem cell23_5141165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_5141165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141165 prefixEnd_5141165 := by exact prefixLift 5141165
  have htrace : WordTrace (prefixWord ++ tailWord_5141165) baseStart_5141165 baseEnd_5141165 := by
    simpa [prefixWord, tailWord_5141165, baseEnd_5141165] using wordTrace_append hprefix tailTrace_5141165
  have hstable : (prefixWord ++ tailWord_5141165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141165).length < 2 ^ (prefixWord ++ tailWord_5141165).sum := by decide
  have hdescent : baseEnd_5141165 < baseStart_5141165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141184 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4]
def baseStart_5141184 : Nat := 118140960795 + 5141184 * 2 ^ 59
def prefixEnd_5141184 : Nat := 4983230072969 + 3 ^ 40 * 5141184 * 2
def baseEnd_5141184 : Nat := 2639898525204918327656131

theorem tailTrace_5141184 : CollatzResearch.WordTrace tailWord_5141184 prefixEnd_5141184 2639898525204918327656131 := by
  unfold tailWord_5141184
  simp only [CollatzResearch.WordTrace]
  refine ⟨93757192703187943583815303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125009590270917258111753737 93757192703187943583815303)
  ·
    refine ⟨140635789054781915375722955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93757192703187943583815303 140635789054781915375722955)
    ·
      refine ⟨210953683582172873063584433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140635789054781915375722955 210953683582172873063584433)
      ·
        refine ⟨158215262686629654797688325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210953683582172873063584433 158215262686629654797688325)
        ·
          refine ⟨29665361753743060274566561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 158215262686629654797688325 29665361753743060274566561)
          ·
            refine ⟨22249021315307295205924921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29665361753743060274566561 22249021315307295205924921)
            ·
              refine ⟨16686765986480471404443691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22249021315307295205924921 16686765986480471404443691)
              ·
                refine ⟨25030148979720707106665537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16686765986480471404443691 25030148979720707106665537)
                ·
                  refine ⟨18772611734790530329999153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25030148979720707106665537 18772611734790530329999153)
                  ·
                    refine ⟨14079458801092897747499365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18772611734790530329999153 14079458801092897747499365)
                    ·
                      refine ⟨2639898525204918327656131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14079458801092897747499365 2639898525204918327656131)
                      ·
                        rfl

theorem cell23_5141184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_5141184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141184 prefixEnd_5141184 := by exact prefixLift 5141184
  have htrace : WordTrace (prefixWord ++ tailWord_5141184) baseStart_5141184 baseEnd_5141184 := by
    simpa [prefixWord, tailWord_5141184, baseEnd_5141184] using wordTrace_append hprefix tailTrace_5141184
  have hstable : (prefixWord ++ tailWord_5141184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141184).length < 2 ^ (prefixWord ++ tailWord_5141184).sum := by decide
  have hdescent : baseEnd_5141184 < baseStart_5141184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141188 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_5141188 : Nat := 118140960795 + 5141188 * 2 ^ 59
def prefixEnd_5141188 : Nat := 4983230072969 + 3 ^ 40 * 5141188 * 2
def baseEnd_5141188 : Nat := 2639900579127536312006113

theorem tailTrace_5141188 : CollatzResearch.WordTrace tailWord_5141188 prefixEnd_5141188 2639900579127536312006113 := by
  unfold tailWord_5141188
  simp only [CollatzResearch.WordTrace]
  refine ⟨93757265649180697925388109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125009687532240930567184145 93757265649180697925388109)
  ·
    refine ⟨35158974618442761722020541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93757265649180697925388109 35158974618442761722020541)
    ·
      refine ⟨13184615481916035645757703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35158974618442761722020541 13184615481916035645757703)
      ·
        refine ⟨19776923222874053468636555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13184615481916035645757703 19776923222874053468636555)
        ·
          refine ⟨29665384834311080202954833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19776923222874053468636555 29665384834311080202954833)
          ·
            refine ⟨22249038625733310152216125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29665384834311080202954833 22249038625733310152216125)
            ·
              refine ⟨8343389484649991307081047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22249038625733310152216125 8343389484649991307081047)
              ·
                refine ⟨12515084226974986960621571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343389484649991307081047 12515084226974986960621571)
                ·
                  refine ⟨18772626340462480440932357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12515084226974986960621571 18772626340462480440932357)
                  ·
                    refine ⟨3519867438836715082674817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18772626340462480440932357 3519867438836715082674817)
                    ·
                      refine ⟨2639900579127536312006113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519867438836715082674817 2639900579127536312006113)
                      ·
                        rfl

theorem cell23_5141188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_5141188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141188 prefixEnd_5141188 := by exact prefixLift 5141188
  have htrace : WordTrace (prefixWord ++ tailWord_5141188) baseStart_5141188 baseEnd_5141188 := by
    simpa [prefixWord, tailWord_5141188, baseEnd_5141188] using wordTrace_append hprefix tailTrace_5141188
  have hstable : (prefixWord ++ tailWord_5141188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141188).length < 2 ^ (prefixWord ++ tailWord_5141188).sum := by decide
  have hdescent : baseEnd_5141188 < baseStart_5141188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141194 : List Nat := [3, 1, 2, 1, 4, 1, 2, 2, 7]
def baseStart_5141194 : Nat := 118140960795 + 5141194 * 2 ^ 59
def prefixEnd_5141194 : Nat := 4983230072969 + 3 ^ 40 * 5141194 * 2
def baseEnd_5141194 : Nat := 293322628890162587614565

theorem tailTrace_5141194 : CollatzResearch.WordTrace tailWord_5141194 prefixEnd_5141194 293322628890162587614565 := by
  unfold tailWord_5141194
  simp only [CollatzResearch.WordTrace]
  refine ⟨46878687534084914718873659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125009833424226439250329757 46878687534084914718873659)
  ·
    refine ⟨70318031301127372078310489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46878687534084914718873659 70318031301127372078310489)
    ·
      refine ⟨52738523475845529058732867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70318031301127372078310489 52738523475845529058732867)
      ·
        refine ⟨79107785213768293588099301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52738523475845529058732867 79107785213768293588099301)
        ·
          refine ⟨14832709727581555047768619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79107785213768293588099301 14832709727581555047768619)
          ·
            refine ⟨22249064591372332571652929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14832709727581555047768619 22249064591372332571652929)
            ·
              refine ⟨16686798443529249428739697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22249064591372332571652929 16686798443529249428739697)
              ·
                refine ⟨12515098832646937071554773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16686798443529249428739697 12515098832646937071554773)
                ·
                  refine ⟨293322628890162587614565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12515098832646937071554773 293322628890162587614565)
                  ·
                    rfl

theorem cell23_5141194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 2, 7].length) (baseStart_5141194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141194 prefixEnd_5141194 := by exact prefixLift 5141194
  have htrace : WordTrace (prefixWord ++ tailWord_5141194) baseStart_5141194 baseEnd_5141194 := by
    simpa [prefixWord, tailWord_5141194, baseEnd_5141194] using wordTrace_append hprefix tailTrace_5141194
  have hstable : (prefixWord ++ tailWord_5141194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141194).length < 2 ^ (prefixWord ++ tailWord_5141194).sum := by decide
  have hdescent : baseEnd_5141194 < baseStart_5141194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141234 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_5141234 : Nat := 118140960795 + 5141234 * 2 ^ 59
def prefixEnd_5141234 : Nat := 4983230072969 + 3 ^ 40 * 5141234 * 2
def baseEnd_5141234 : Nat := 2639924199237643132030901

theorem tailTrace_5141234 : CollatzResearch.WordTrace tailWord_5141234 prefixEnd_5141234 2639924199237643132030901 := by
  unfold tailWord_5141234
  simp only [CollatzResearch.WordTrace]
  refine ⟨46879052264048686426737689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125010806037463163804633837 46879052264048686426737689)
  ·
    refine ⟨35159289198036514820053267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46879052264048686426737689 35159289198036514820053267)
    ·
      refine ⟨52738933797054772230079901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35159289198036514820053267 52738933797054772230079901)
      ·
        refine ⟨19777100173895539586279963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52738933797054772230079901 19777100173895539586279963)
        ·
          refine ⟨29665650260843309379419945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19777100173895539586279963 29665650260843309379419945)
          ·
            refine ⟨22249237695632482034564959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29665650260843309379419945 22249237695632482034564959)
            ·
              refine ⟨33373856543448723051847439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22249237695632482034564959 33373856543448723051847439)
              ·
                refine ⟨50060784815173084577771159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33373856543448723051847439 50060784815173084577771159)
                ·
                  refine ⟨75091177222759626866656739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50060784815173084577771159 75091177222759626866656739)
                  ·
                    refine ⟨112636765834139440299985109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75091177222759626866656739 112636765834139440299985109)
                    ·
                      refine ⟨2639924199237643132030901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112636765834139440299985109 2639924199237643132030901)
                      ·
                        rfl

theorem cell23_5141234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_5141234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141234 prefixEnd_5141234 := by exact prefixLift 5141234
  have htrace : WordTrace (prefixWord ++ tailWord_5141234) baseStart_5141234 baseEnd_5141234 := by
    simpa [prefixWord, tailWord_5141234, baseEnd_5141234] using wordTrace_append hprefix tailTrace_5141234
  have hstable : (prefixWord ++ tailWord_5141234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141234).length < 2 ^ (prefixWord ++ tailWord_5141234).sum := by decide
  have hdescent : baseEnd_5141234 < baseStart_5141234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141274 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_5141274 : Nat := 118140960795 + 5141274 * 2 ^ 59
def prefixEnd_5141274 : Nat := 4983230072969 + 3 ^ 40 * 5141274 * 2
def baseEnd_5141274 : Nat := 2639944738463822975530717

theorem tailTrace_5141274 : CollatzResearch.WordTrace tailWord_5141274 prefixEnd_5141274 2639944738463822975530717 := by
  unfold tailWord_5141274
  simp only [CollatzResearch.WordTrace]
  refine ⟨46879416994012458134601719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125011778650699888358937917 46879416994012458134601719)
  ·
    refine ⟨70319125491018687201902579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46879416994012458134601719 70319125491018687201902579)
    ·
      refine ⟨105478688236528030802853869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70319125491018687201902579 105478688236528030802853869)
      ·
        refine ⟨39554508088698011551070201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105478688236528030802853869 39554508088698011551070201)
        ·
          refine ⟨29665881066523508663302651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39554508088698011551070201 29665881066523508663302651)
          ·
            refine ⟨44498821599785262994953977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29665881066523508663302651 44498821599785262994953977)
            ·
              refine ⟨33374116199838947246215483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44498821599785262994953977 33374116199838947246215483)
              ·
                refine ⟨50061174299758420869323225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33374116199838947246215483 50061174299758420869323225)
                ·
                  refine ⟨37545880724818815651992419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50061174299758420869323225 37545880724818815651992419)
                  ·
                    refine ⟨56318821087228223477988629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37545880724818815651992419 56318821087228223477988629)
                    ·
                      refine ⟨2639944738463822975530717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56318821087228223477988629 2639944738463822975530717)
                      ·
                        rfl

theorem cell23_5141274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_5141274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141274 prefixEnd_5141274 := by exact prefixLift 5141274
  have htrace : WordTrace (prefixWord ++ tailWord_5141274) baseStart_5141274 baseEnd_5141274 := by
    simpa [prefixWord, tailWord_5141274, baseEnd_5141274] using wordTrace_append hprefix tailTrace_5141274
  have hstable : (prefixWord ++ tailWord_5141274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141274).length < 2 ^ (prefixWord ++ tailWord_5141274).sum := by decide
  have hdescent : baseEnd_5141274 < baseStart_5141274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141281 : List Nat := [1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_5141281 : Nat := 118140960795 + 5141281 * 2 ^ 59
def prefixEnd_5141281 : Nat := 4983230072969 + 3 ^ 40 * 5141281 * 2
def baseEnd_5141281 : Nat := 2639948332828404448143185

theorem tailTrace_5141281 : CollatzResearch.WordTrace tailWord_5141281 prefixEnd_5141281 2639948332828404448143185 := by
  unfold tailWord_5141281
  simp only [CollatzResearch.WordTrace]
  refine ⟨187517923287024472733911697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125011948858016315155941131 187517923287024472733911697)
  ·
    refine ⟨140638442465268354550433773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187517923287024472733911697 140638442465268354550433773)
    ·
      refine ⟨52739415924475632956412665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140638442465268354550433773 52739415924475632956412665)
      ·
        refine ⟨39554561943356724717309499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52739415924475632956412665 39554561943356724717309499)
        ·
          refine ⟨59331842915035087075964249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39554561943356724717309499 59331842915035087075964249)
          ·
            refine ⟨44498882186276315306973187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59331842915035087075964249 44498882186276315306973187)
            ·
              refine ⟨66748323279414472960459781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44498882186276315306973187 66748323279414472960459781)
              ·
                refine ⟨12515310614890213680086209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66748323279414472960459781 12515310614890213680086209)
                ·
                  refine ⟨9386482961167660260064657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12515310614890213680086209 9386482961167660260064657)
                  ·
                    refine ⟨7039862220875745195048493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9386482961167660260064657 7039862220875745195048493)
                    ·
                      refine ⟨2639948332828404448143185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039862220875745195048493 2639948332828404448143185)
                      ·
                        rfl

theorem cell23_5141281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_5141281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141281 prefixEnd_5141281 := by exact prefixLift 5141281
  have htrace : WordTrace (prefixWord ++ tailWord_5141281) baseStart_5141281 baseEnd_5141281 := by
    simpa [prefixWord, tailWord_5141281, baseEnd_5141281] using wordTrace_append hprefix tailTrace_5141281
  have hstable : (prefixWord ++ tailWord_5141281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141281).length < 2 ^ (prefixWord ++ tailWord_5141281).sum := by decide
  have hdescent : baseEnd_5141281 < baseStart_5141281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141301 : List Nat := [1, 3, 3, 1, 3, 1, 2, 3, 6]
def baseStart_5141301 : Nat := 118140960795 + 5141301 * 2 ^ 59
def prefixEnd_5141301 : Nat := 4983230072969 + 3 ^ 40 * 5141301 * 2
def baseEnd_5141301 : Nat := 293328733604610485543677

theorem tailTrace_5141301 : CollatzResearch.WordTrace tailWord_5141301 prefixEnd_5141301 293328733604610485543677 := by
  unfold tailWord_5141301
  simp only [CollatzResearch.WordTrace]
  refine ⟨187518652746952016149639757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125012435164634677433093171 187518652746952016149639757)
  ·
    refine ⟨70319494780107006056114909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187518652746952016149639757 70319494780107006056114909)
    ·
      refine ⟨26369810542540127271043091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70319494780107006056114909 26369810542540127271043091)
      ·
        refine ⟨39554715813810190906564637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26369810542540127271043091 39554715813810190906564637)
        ·
          refine ⟨14833018430178821589961739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39554715813810190906564637 14833018430178821589961739)
          ·
            refine ⟨22249527645268232384942609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833018430178821589961739 22249527645268232384942609)
            ·
              refine ⟨16687145733951174288706957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22249527645268232384942609 16687145733951174288706957)
              ·
                refine ⟨6257679650231690358265109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16687145733951174288706957 6257679650231690358265109)
                ·
                  refine ⟨293328733604610485543677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6257679650231690358265109 293328733604610485543677)
                  ·
                    rfl

theorem cell23_5141301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_5141301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141301 prefixEnd_5141301 := by exact prefixLift 5141301
  have htrace : WordTrace (prefixWord ++ tailWord_5141301) baseStart_5141301 baseEnd_5141301 := by
    simpa [prefixWord, tailWord_5141301, baseEnd_5141301] using wordTrace_append hprefix tailTrace_5141301
  have hstable : (prefixWord ++ tailWord_5141301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141301).length < 2 ^ (prefixWord ++ tailWord_5141301).sum := by decide
  have hdescent : baseEnd_5141301 < baseStart_5141301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141361 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_5141361 : Nat := 118140960795 + 5141361 * 2 ^ 59
def prefixEnd_5141361 : Nat := 4983230072969 + 3 ^ 40 * 5141361 * 2
def baseEnd_5141361 : Nat := 879996470426921378380939

theorem tailTrace_5141361 : CollatzResearch.WordTrace tailWord_5141361 prefixEnd_5141361 879996470426921378380939 := by
  unfold tailWord_5141361
  simp only [CollatzResearch.WordTrace]
  refine ⟨187520841126734646396823937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125013894084489764264549291 187520841126734646396823937)
  ·
    refine ⟨140640630845050984797617953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187520841126734646396823937 140640630845050984797617953)
    ·
      refine ⟨105480473133788238598213465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140640630845050984797617953 105480473133788238598213465)
      ·
        refine ⟨79110354850341178948660099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105480473133788238598213465 79110354850341178948660099)
        ·
          refine ⟨118665532275511768422990149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79110354850341178948660099 118665532275511768422990149)
          ·
            refine ⟨22249787301658456579310653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118665532275511768422990149 22249787301658456579310653)
            ·
              refine ⟨8343670238121921217241495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22249787301658456579310653 8343670238121921217241495)
              ·
                refine ⟨12515505357182881825862243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343670238121921217241495 12515505357182881825862243)
                ·
                  refine ⟨18773258035774322738793365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12515505357182881825862243 18773258035774322738793365)
                  ·
                    refine ⟨879996470426921378380939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18773258035774322738793365 879996470426921378380939)
                    ·
                      rfl

theorem cell23_5141361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_5141361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141361 prefixEnd_5141361 := by exact prefixLift 5141361
  have htrace : WordTrace (prefixWord ++ tailWord_5141361) baseStart_5141361 baseEnd_5141361 := by
    simpa [prefixWord, tailWord_5141361, baseEnd_5141361] using wordTrace_append hprefix tailTrace_5141361
  have hstable : (prefixWord ++ tailWord_5141361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141361).length < 2 ^ (prefixWord ++ tailWord_5141361).sum := by decide
  have hdescent : baseEnd_5141361 < baseStart_5141361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141368 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2]
def baseStart_5141368 : Nat := 118140960795 + 5141368 * 2 ^ 59
def prefixEnd_5141368 : Nat := 4983230072969 + 3 ^ 40 * 5141368 * 2
def baseEnd_5141368 : Nat := 2639993005645345607755285

theorem tailTrace_5141368 : CollatzResearch.WordTrace tailWord_5141368 prefixEnd_5141368 2639993005645345607755285 := by
  unfold tailWord_5141368
  simp only [CollatzResearch.WordTrace]
  refine ⟨93760548218854643296164379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125014064291806191061552505 93760548218854643296164379)
  ·
    refine ⟨140640822328281964944246569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93760548218854643296164379 140640822328281964944246569)
    ·
      refine ⟨105480616746211473708184927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140640822328281964944246569 105480616746211473708184927)
      ·
        refine ⟨158220925119317210562277391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105480616746211473708184927 158220925119317210562277391)
        ·
          refine ⟨237331387678975815843416087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158220925119317210562277391 237331387678975815843416087)
          ·
            refine ⟨355997081518463723765124131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237331387678975815843416087 355997081518463723765124131)
            ·
              refine ⟨533995622277695585647686197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355997081518463723765124131 533995622277695585647686197)
              ·
                refine ⟨50062089588533961154470581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 533995622277695585647686197 50062089588533961154470581)
                ·
                  refine ⟨4693320898925058858231617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50062089588533961154470581 4693320898925058858231617)
                  ·
                    refine ⟨3519990674193794143673713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4693320898925058858231617 3519990674193794143673713)
                    ·
                      refine ⟨2639993005645345607755285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3519990674193794143673713 2639993005645345607755285)
                      ·
                        rfl

theorem cell23_5141368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 2, 2].length) (baseStart_5141368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141368 prefixEnd_5141368 := by exact prefixLift 5141368
  have htrace : WordTrace (prefixWord ++ tailWord_5141368) baseStart_5141368 baseEnd_5141368 := by
    simpa [prefixWord, tailWord_5141368, baseEnd_5141368] using wordTrace_append hprefix tailTrace_5141368
  have hstable : (prefixWord ++ tailWord_5141368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141368).length < 2 ^ (prefixWord ++ tailWord_5141368).sum := by decide
  have hdescent : baseEnd_5141368 < baseStart_5141368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141371 : List Nat := [1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3]
def baseStart_5141371 : Nat := 118140960795 + 5141371 * 2 ^ 59
def prefixEnd_5141371 : Nat := 4983230072969 + 3 ^ 40 * 5141371 * 2
def baseEnd_5141371 : Nat := 2639994546087309096017771

theorem tailTrace_5141371 : CollatzResearch.WordTrace tailWord_5141371 prefixEnd_5141371 2639994546087309096017771 := by
  unfold tailWord_5141371
  simp only [CollatzResearch.WordTrace]
  refine ⟨187521205856698418104687967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125014137237798945403125311 187521205856698418104687967)
  ·
    refine ⟨281281808785047627157031951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187521205856698418104687967 281281808785047627157031951)
    ·
      refine ⟨421922713177571440735547927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281281808785047627157031951 421922713177571440735547927)
      ·
        refine ⟨632884069766357161103321891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421922713177571440735547927 632884069766357161103321891)
        ·
          refine ⟨949326104649535741654982837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632884069766357161103321891 949326104649535741654982837)
          ·
            refine ⟨88999322310893975780154641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 949326104649535741654982837 88999322310893975780154641)
            ·
              refine ⟨66749491733170481835115981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88999322310893975780154641 66749491733170481835115981)
              ·
                refine ⟨25031059399938930688168493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66749491733170481835115981 25031059399938930688168493)
                ·
                  refine ⟨9386647274977099008063185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25031059399938930688168493 9386647274977099008063185)
                  ·
                    refine ⟨7039985456232824256047389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9386647274977099008063185 7039985456232824256047389)
                    ·
                      refine ⟨2639994546087309096017771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7039985456232824256047389 2639994546087309096017771)
                      ·
                        rfl

theorem cell23_5141371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 3].length) (baseStart_5141371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141371 prefixEnd_5141371 := by exact prefixLift 5141371
  have htrace : WordTrace (prefixWord ++ tailWord_5141371) baseStart_5141371 baseEnd_5141371 := by
    simpa [prefixWord, tailWord_5141371, baseEnd_5141371] using wordTrace_append hprefix tailTrace_5141371
  have hstable : (prefixWord ++ tailWord_5141371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141371).length < 2 ^ (prefixWord ++ tailWord_5141371).sum := by decide
  have hdescent : baseEnd_5141371 < baseStart_5141371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141388 : List Nat := [2, 2, 1, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_5141388 : Nat := 118140960795 + 5141388 * 2 ^ 59
def prefixEnd_5141388 : Nat := 4983230072969 + 3 ^ 40 * 5141388 * 2
def baseEnd_5141388 : Nat := 2640003275258435529505193

theorem tailTrace_5141388 : CollatzResearch.WordTrace tailWord_5141388 prefixEnd_5141388 2640003275258435529505193 := by
  unfold tailWord_5141388
  simp only [CollatzResearch.WordTrace]
  refine ⟨93760912948818415004028409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125014550598424553338704545 93760912948818415004028409)
  ·
    refine ⟨70320684711613811253021307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93760912948818415004028409 70320684711613811253021307)
    ·
      refine ⟨105481027067420716879531961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70320684711613811253021307 105481027067420716879531961)
      ·
        refine ⟨79110770300565537659648971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105481027067420716879531961 79110770300565537659648971)
        ·
          refine ⟨118666155450848306489473457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79110770300565537659648971 118666155450848306489473457)
          ·
            refine ⟨88999616588136229867105093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118666155450848306489473457 88999616588136229867105093)
            ·
              refine ⟨16687428110275543100082205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88999616588136229867105093 16687428110275543100082205)
              ·
                refine ⟨6257785541353328662530827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16687428110275543100082205 6257785541353328662530827)
                ·
                  refine ⟨9386678312029992993796241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6257785541353328662530827 9386678312029992993796241)
                  ·
                    refine ⟨7040008734022494745347181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9386678312029992993796241 7040008734022494745347181)
                    ·
                      refine ⟨2640003275258435529505193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7040008734022494745347181 2640003275258435529505193)
                      ·
                        rfl

theorem cell23_5141388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_5141388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141388 prefixEnd_5141388 := by exact prefixLift 5141388
  have htrace : WordTrace (prefixWord ++ tailWord_5141388) baseStart_5141388 baseEnd_5141388 := by
    simpa [prefixWord, tailWord_5141388, baseEnd_5141388] using wordTrace_append hprefix tailTrace_5141388
  have hstable : (prefixWord ++ tailWord_5141388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141388).length < 2 ^ (prefixWord ++ tailWord_5141388).sum := by decide
  have hdescent : baseEnd_5141388 < baseStart_5141388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141458 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_5141458 : Nat := 118140960795 + 5141458 * 2 ^ 59
def prefixEnd_5141458 : Nat := 4983230072969 + 3 ^ 40 * 5141458 * 2
def baseEnd_5141458 : Nat := 2640039218904250255629871

theorem tailTrace_5141458 : CollatzResearch.WordTrace tailWord_5141458 prefixEnd_5141458 2640039218904250255629871 := by
  unfold tailWord_5141458
  simp only [CollatzResearch.WordTrace]
  refine ⟨46881094751845807990776257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125016252671588821308736685 46881094751845807990776257)
  ·
    refine ⟨35160821063884355993082193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46881094751845807990776257 35160821063884355993082193)
    ·
      refine ⟨26370615797913266994811645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35160821063884355993082193 26370615797913266994811645)
      ·
        refine ⟨9888980924217475123054367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26370615797913266994811645 9888980924217475123054367)
        ·
          refine ⟨14833471386326212684581551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9888980924217475123054367 14833471386326212684581551)
          ·
            refine ⟨22250207079489319026872327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833471386326212684581551 22250207079489319026872327)
            ·
              refine ⟨33375310619233978540308491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22250207079489319026872327 33375310619233978540308491)
              ·
                refine ⟨50062965928850967810462737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33375310619233978540308491 50062965928850967810462737)
                ·
                  refine ⟨37547224446638225857847053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50062965928850967810462737 37547224446638225857847053)
                  ·
                    refine ⟨14080209167489334696692645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37547224446638225857847053 14080209167489334696692645)
                    ·
                      refine ⟨2640039218904250255629871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14080209167489334696692645 2640039218904250255629871)
                      ·
                        rfl

theorem cell23_5141458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_5141458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141458 prefixEnd_5141458 := by exact prefixLift 5141458
  have htrace : WordTrace (prefixWord ++ tailWord_5141458) baseStart_5141458 baseEnd_5141458 := by
    simpa [prefixWord, tailWord_5141458, baseEnd_5141458] using wordTrace_append hprefix tailTrace_5141458
  have hstable : (prefixWord ++ tailWord_5141458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141458).length < 2 ^ (prefixWord ++ tailWord_5141458).sum := by decide
  have hdescent : baseEnd_5141458 < baseStart_5141458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141462 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5141462 : Nat := 118140960795 + 5141462 * 2 ^ 59
def prefixEnd_5141462 : Nat := 4983230072969 + 3 ^ 40 * 5141462 * 2
def baseEnd_5141462 : Nat := 2640041272826868239979853

theorem tailTrace_5141462 : CollatzResearch.WordTrace tailWord_5141462 prefixEnd_5141462 2640041272826868239979853 := by
  unfold tailWord_5141462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11720282806210546290390665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 125016349932912493764167093 11720282806210546290390665)
  ·
    refine ⟨8790212104657909717792999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11720282806210546290390665 8790212104657909717792999)
    ·
      refine ⟨13185318156986864576689499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8790212104657909717792999 13185318156986864576689499)
      ·
        refine ⟨19777977235480296865034249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13185318156986864576689499 19777977235480296865034249)
        ·
          refine ⟨14833482926610222648775687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19777977235480296865034249 14833482926610222648775687)
          ·
            refine ⟨22250224389915333973163531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833482926610222648775687 22250224389915333973163531)
            ·
              refine ⟨33375336584873000959745297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22250224389915333973163531 33375336584873000959745297)
              ·
                refine ⟨25031502438654750719808973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33375336584873000959745297 25031502438654750719808973)
                ·
                  refine ⟨9386813414495531519928365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25031502438654750719808973 9386813414495531519928365)
                  ·
                    refine ⟨3520055030435824319973137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9386813414495531519928365 3520055030435824319973137)
                    ·
                      refine ⟨2640041272826868239979853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520055030435824319973137 2640041272826868239979853)
                      ·
                        rfl

theorem cell23_5141462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5141462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141462 prefixEnd_5141462 := by exact prefixLift 5141462
  have htrace : WordTrace (prefixWord ++ tailWord_5141462) baseStart_5141462 baseEnd_5141462 := by
    simpa [prefixWord, tailWord_5141462, baseEnd_5141462] using wordTrace_append hprefix tailTrace_5141462
  have hstable : (prefixWord ++ tailWord_5141462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141462).length < 2 ^ (prefixWord ++ tailWord_5141462).sum := by decide
  have hdescent : baseEnd_5141462 < baseStart_5141462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141475 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5141475 : Nat := 118140960795 + 5141475 * 2 ^ 59
def prefixEnd_5141475 : Nat := 4983230072969 + 3 ^ 40 * 5141475 * 2
def baseEnd_5141475 : Nat := 2640047948075376689117293

theorem tailTrace_5141475 : CollatzResearch.WordTrace tailWord_5141475 prefixEnd_5141475 2640047948075376689117293 := by
  unfold tailWord_5141475
  simp only [CollatzResearch.WordTrace]
  refine ⟨187524999048321643866473879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125016666032214429244315919 187524999048321643866473879)
  ·
    refine ⟨281287498572482465799710819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187524999048321643866473879 281287498572482465799710819)
    ·
      refine ⟨421931247858723698699566229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281287498572482465799710819 421931247858723698699566229)
      ·
        refine ⟨19778027243377673376542167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 421931247858723698699566229 19778027243377673376542167)
        ·
          refine ⟨29667040865066510064813251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19778027243377673376542167 29667040865066510064813251)
          ·
            refine ⟨44500561297599765097219877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29667040865066510064813251 44500561297599765097219877)
            ·
              refine ⟨8343855243299955955728727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44500561297599765097219877 8343855243299955955728727)
              ·
                refine ⟨12515782864949933933593091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8343855243299955955728727 12515782864949933933593091)
                ·
                  refine ⟨18773674297424900900389637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12515782864949933933593091 18773674297424900900389637)
                  ·
                    refine ⟨3520063930767168918823057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18773674297424900900389637 3520063930767168918823057)
                    ·
                      refine ⟨2640047948075376689117293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520063930767168918823057 2640047948075376689117293)
                      ·
                        rfl

theorem cell23_5141475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5141475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141475 prefixEnd_5141475 := by exact prefixLift 5141475
  have htrace : WordTrace (prefixWord ++ tailWord_5141475) baseStart_5141475 baseEnd_5141475 := by
    simpa [prefixWord, tailWord_5141475, baseEnd_5141475] using wordTrace_append hprefix tailTrace_5141475
  have hstable : (prefixWord ++ tailWord_5141475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141475).length < 2 ^ (prefixWord ++ tailWord_5141475).sum := by decide
  have hdescent : baseEnd_5141475 < baseStart_5141475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141521 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_5141521 : Nat := 118140960795 + 5141521 * 2 ^ 59
def prefixEnd_5141521 : Nat := 4983230072969 + 3 ^ 40 * 5141521 * 2
def baseEnd_5141521 : Nat := 2640071568185483509142081

theorem tailTrace_5141521 : CollatzResearch.WordTrace tailWord_5141521 prefixEnd_5141521 2640071568185483509142081 := by
  unfold tailWord_5141521
  simp only [CollatzResearch.WordTrace]
  refine ⟨187526676806154993722648417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125017784537436662481765611 187526676806154993722648417)
  ·
    refine ⟨140645007604616245291986313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187526676806154993722648417 140645007604616245291986313)
    ·
      refine ⟨105483755703462183968989735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140645007604616245291986313 105483755703462183968989735)
      ·
        refine ⟨158225633555193275953484603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105483755703462183968989735 158225633555193275953484603)
        ·
          refine ⟨237338450332789913930226905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158225633555193275953484603 237338450332789913930226905)
          ·
            refine ⟨178003837749592435447670179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237338450332789913930226905 178003837749592435447670179)
            ·
              refine ⟨267005756624388653171505269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178003837749592435447670179 267005756624388653171505269)
              ·
                refine ⟨25031789683536436234828619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267005756624388653171505269 25031789683536436234828619)
                ·
                  refine ⟨37547684525304654352242929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25031789683536436234828619 37547684525304654352242929)
                  ·
                    refine ⟨28160763393978490764182197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37547684525304654352242929 28160763393978490764182197)
                    ·
                      refine ⟨2640071568185483509142081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28160763393978490764182197 2640071568185483509142081)
                      ·
                        rfl

theorem cell23_5141521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_5141521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141521 prefixEnd_5141521 := by exact prefixLift 5141521
  have htrace : WordTrace (prefixWord ++ tailWord_5141521) baseStart_5141521 baseEnd_5141521 := by
    simpa [prefixWord, tailWord_5141521, baseEnd_5141521] using wordTrace_append hprefix tailTrace_5141521
  have hstable : (prefixWord ++ tailWord_5141521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141521).length < 2 ^ (prefixWord ++ tailWord_5141521).sum := by decide
  have hdescent : baseEnd_5141521 < baseStart_5141521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141541 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_5141541 : Nat := 118140960795 + 5141541 * 2 ^ 59
def prefixEnd_5141541 : Nat := 4983230072969 + 3 ^ 40 * 5141541 * 2
def baseEnd_5141541 : Nat := 880027279266191143630663

theorem tailTrace_5141541 : CollatzResearch.WordTrace tailWord_5141541 prefixEnd_5141541 880027279266191143630663 := by
  unfold tailWord_5141541
  simp only [CollatzResearch.WordTrace]
  refine ⟨187527406266082537138376477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125018270844055024758917651 187527406266082537138376477)
  ·
    refine ⟨70322777349780951426891179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187527406266082537138376477 70322777349780951426891179)
    ·
      refine ⟨105484166024671427140336769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70322777349780951426891179 105484166024671427140336769)
      ·
        refine ⟨79113124518503570355252577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105484166024671427140336769 79113124518503570355252577)
        ·
          refine ⟨59334843388877677766439433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79113124518503570355252577 59334843388877677766439433)
          ·
            refine ⟨44501132541658258324829575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59334843388877677766439433 44501132541658258324829575)
            ·
              refine ⟨66751698812487387487244363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44501132541658258324829575 66751698812487387487244363)
              ·
                refine ⟨100127548218731081230866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66751698812487387487244363 100127548218731081230866545)
                ·
                  refine ⟨75095661164048310923149909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100127548218731081230866545 75095661164048310923149909)
                  ·
                    refine ⟨880027279266191143630663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 75095661164048310923149909 880027279266191143630663)
                    ·
                      rfl

theorem cell23_5141541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_5141541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141541 prefixEnd_5141541 := by exact prefixLift 5141541
  have htrace : WordTrace (prefixWord ++ tailWord_5141541) baseStart_5141541 baseEnd_5141541 := by
    simpa [prefixWord, tailWord_5141541, baseEnd_5141541] using wordTrace_append hprefix tailTrace_5141541
  have hstable : (prefixWord ++ tailWord_5141541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141541).length < 2 ^ (prefixWord ++ tailWord_5141541).sum := by decide
  have hdescent : baseEnd_5141541 < baseStart_5141541 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141548 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_5141548 : Nat := 118140960795 + 5141548 * 2 ^ 59
def prefixEnd_5141548 : Nat := 4983230072969 + 3 ^ 40 * 5141548 * 2
def baseEnd_5141548 : Nat := 2640085432163154903504457

theorem tailTrace_5141548 : CollatzResearch.WordTrace tailWord_5141548 prefixEnd_5141548 2640085432163154903504457 := by
  unfold tailWord_5141548
  simp only [CollatzResearch.WordTrace]
  refine ⟨93763830788528588666940649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125018441051371451555920865 93763830788528588666940649)
  ·
    refine ⟨70322873091396441500205487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93763830788528588666940649 70322873091396441500205487)
    ·
      refine ⟨105484309637094662250308231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70322873091396441500205487 105484309637094662250308231)
      ·
        refine ⟨158226464455641993375462347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105484309637094662250308231 158226464455641993375462347)
        ·
          refine ⟨237339696683462990063193521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158226464455641993375462347 237339696683462990063193521)
          ·
            refine ⟨178004772512597242547395141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237339696683462990063193521 178004772512597242547395141)
            ·
              refine ⟨33375894846111982977636589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 178004772512597242547395141 33375894846111982977636589)
              ·
                refine ⟨12515960567291993616613721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33375894846111982977636589 12515960567291993616613721)
                ·
                  refine ⟨9386970425468995212460291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12515960567291993616613721 9386970425468995212460291)
                  ·
                    refine ⟨14080455638203492818690437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9386970425468995212460291 14080455638203492818690437)
                    ·
                      refine ⟨2640085432163154903504457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14080455638203492818690437 2640085432163154903504457)
                      ·
                        rfl

theorem cell23_5141548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_5141548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141548 prefixEnd_5141548 := by exact prefixLift 5141548
  have htrace : WordTrace (prefixWord ++ tailWord_5141548) baseStart_5141548 baseEnd_5141548 := by
    simpa [prefixWord, tailWord_5141548, baseEnd_5141548] using wordTrace_append hprefix tailTrace_5141548
  have hstable : (prefixWord ++ tailWord_5141548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141548).length < 2 ^ (prefixWord ++ tailWord_5141548).sum := by decide
  have hdescent : baseEnd_5141548 < baseStart_5141548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141565 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_5141565 : Nat := 118140960795 + 5141565 * 2 ^ 59
def prefixEnd_5141565 : Nat := 4983230072969 + 3 ^ 40 * 5141565 * 2
def baseEnd_5141565 : Nat := 2640094161334281336991879

theorem tailTrace_5141565 : CollatzResearch.WordTrace tailWord_5141565 prefixEnd_5141565 2640094161334281336991879 := by
  unfold tailWord_5141565
  simp only [CollatzResearch.WordTrace]
  refine ⟨187528281617995589237250149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125018854411997059491500099 187528281617995589237250149)
  ·
    refine ⟨35161552803374172981984403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187528281617995589237250149 35161552803374172981984403)
    ·
      refine ⟨52742329205061259472976605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35161552803374172981984403 52742329205061259472976605)
      ·
        refine ⟨19778373451897972302366227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52742329205061259472976605 19778373451897972302366227)
        ·
          refine ⟨29667560177846958453549341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19778373451897972302366227 29667560177846958453549341)
          ·
            refine ⟨11125335066692609420081003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29667560177846958453549341 11125335066692609420081003)
            ·
              refine ⟨16688002600038914130121505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11125335066692609420081003 16688002600038914130121505)
              ·
                refine ⟨12516001950029185597591129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16688002600038914130121505 12516001950029185597591129)
                ·
                  refine ⟨9387001462521889198193347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12516001950029185597591129 9387001462521889198193347)
                  ·
                    refine ⟨14080502193782833797290021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9387001462521889198193347 14080502193782833797290021)
                    ·
                      refine ⟨2640094161334281336991879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14080502193782833797290021 2640094161334281336991879)
                      ·
                        rfl

theorem cell23_5141565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_5141565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141565 prefixEnd_5141565 := by exact prefixLift 5141565
  have htrace : WordTrace (prefixWord ++ tailWord_5141565) baseStart_5141565 baseEnd_5141565 := by
    simpa [prefixWord, tailWord_5141565, baseEnd_5141565] using wordTrace_append hprefix tailTrace_5141565
  have hstable : (prefixWord ++ tailWord_5141565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141565).length < 2 ^ (prefixWord ++ tailWord_5141565).sum := by decide
  have hdescent : baseEnd_5141565 < baseStart_5141565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141571 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 8]
def baseStart_5141571 : Nat := 118140960795 + 5141571 * 2 ^ 59
def prefixEnd_5141571 : Nat := 4983230072969 + 3 ^ 40 * 5141571 * 2
def baseEnd_5141571 : Nat := 293344138024245368168539

theorem tailTrace_5141571 : CollatzResearch.WordTrace tailWord_5141571 prefixEnd_5141571 293344138024245368168539 := by
  unfold tailWord_5141571
  simp only [CollatzResearch.WordTrace]
  refine ⟨187528500455973852261968567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125019000303982568174645711 187528500455973852261968567)
  ·
    refine ⟨281292750683960778392952851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187528500455973852261968567 281292750683960778392952851)
    ·
      refine ⟨421939126025941167589429277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281292750683960778392952851 421939126025941167589429277)
      ·
        refine ⟨158227172259727937846035979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421939126025941167589429277 158227172259727937846035979)
        ·
          refine ⟨237340758389591906769053969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158227172259727937846035979 237340758389591906769053969)
          ·
            refine ⟨178005568792193930076790477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237340758389591906769053969 178005568792193930076790477)
            ·
              refine ⟨66752088297072723778796429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178005568792193930076790477 66752088297072723778796429)
              ·
                refine ⟨25032033111402271417048661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66752088297072723778796429 25032033111402271417048661)
                ·
                  refine ⟨293344138024245368168539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25032033111402271417048661 293344138024245368168539)
                  ·
                    rfl

theorem cell23_5141571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 8].length) (baseStart_5141571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141571 prefixEnd_5141571 := by exact prefixLift 5141571
  have htrace : WordTrace (prefixWord ++ tailWord_5141571) baseStart_5141571 baseEnd_5141571 := by
    simpa [prefixWord, tailWord_5141571, baseEnd_5141571] using wordTrace_append hprefix tailTrace_5141571
  have hstable : (prefixWord ++ tailWord_5141571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141571).length < 2 ^ (prefixWord ++ tailWord_5141571).sum := by decide
  have hdescent : baseEnd_5141571 < baseStart_5141571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141575 : List Nat := [1, 1, 4, 1, 3, 2, 3, 1, 3, 4]
def baseStart_5141575 : Nat := 118140960795 + 5141575 * 2 ^ 59
def prefixEnd_5141575 : Nat := 4983230072969 + 3 ^ 40 * 5141575 * 2
def baseEnd_5141575 : Nat := 880033098713608765955611

theorem tailTrace_5141575 : CollatzResearch.WordTrace tailWord_5141575 prefixEnd_5141575 880033098713608765955611 := by
  unfold tailWord_5141575
  simp only [CollatzResearch.WordTrace]
  refine ⟨187528646347959360945114179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125019097565306240630076119 187528646347959360945114179)
  ·
    refine ⟨281292969521939041417671269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187528646347959360945114179 281292969521939041417671269)
    ·
      refine ⟨52742431785363570265813363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 281292969521939041417671269 52742431785363570265813363)
      ·
        refine ⟨79113647678045355398720045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52742431785363570265813363 79113647678045355398720045)
        ·
          refine ⟨29667617879267008274520017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79113647678045355398720045 29667617879267008274520017)
          ·
            refine ⟨22250713409450256205890013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29667617879267008274520017 22250713409450256205890013)
            ·
              refine ⟨8344017528543846077208755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22250713409450256205890013 8344017528543846077208755)
              ·
                refine ⟨12516026292815769115813133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8344017528543846077208755 12516026292815769115813133)
                ·
                  refine ⟨4693509859805913418429925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12516026292815769115813133 4693509859805913418429925)
                  ·
                    refine ⟨880033098713608765955611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693509859805913418429925 880033098713608765955611)
                    ·
                      rfl

theorem cell23_5141575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_5141575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141575 prefixEnd_5141575 := by exact prefixLift 5141575
  have htrace : WordTrace (prefixWord ++ tailWord_5141575) baseStart_5141575 baseEnd_5141575 := by
    simpa [prefixWord, tailWord_5141575, baseEnd_5141575] using wordTrace_append hprefix tailTrace_5141575
  have hstable : (prefixWord ++ tailWord_5141575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141575).length < 2 ^ (prefixWord ++ tailWord_5141575).sum := by decide
  have hdescent : baseEnd_5141575 < baseStart_5141575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141602 : List Nat := [3, 3, 2, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5141602 : Nat := 118140960795 + 5141602 * 2 ^ 59
def prefixEnd_5141602 : Nat := 4983230072969 + 3 ^ 40 * 5141602 * 2
def baseEnd_5141602 : Nat := 2640113160118497692229209

theorem tailTrace_5141602 : CollatzResearch.WordTrace tailWord_5141602 prefixEnd_5141602 2640113160118497692229209 := by
  unfold tailWord_5141602
  simp only [CollatzResearch.WordTrace]
  refine ⟨46882407779715386139086765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125019754079241029704231373 46882407779715386139086765)
  ·
    refine ⟨17580902917393269802157537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46882407779715386139086765 17580902917393269802157537)
    ·
      refine ⟨13185677188044952351618153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17580902917393269802157537 13185677188044952351618153)
      ·
        refine ⟨9889257891033714263713615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13185677188044952351618153 9889257891033714263713615)
        ·
          refine ⟨14833886836550571395570423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889257891033714263713615 14833886836550571395570423)
          ·
            refine ⟨22250830254825857093355635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14833886836550571395570423 22250830254825857093355635)
            ·
              refine ⟨33376245382238785640033453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22250830254825857093355635 33376245382238785640033453)
              ·
                refine ⟨12516092018339544615012545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33376245382238785640033453 12516092018339544615012545)
                ·
                  refine ⟨9387069013754658461259409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12516092018339544615012545 9387069013754658461259409)
                  ·
                    refine ⟨7040301760315993845944557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9387069013754658461259409 7040301760315993845944557)
                    ·
                      refine ⟨2640113160118497692229209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7040301760315993845944557 2640113160118497692229209)
                      ·
                        rfl

theorem cell23_5141602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5141602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141602 prefixEnd_5141602 := by exact prefixLift 5141602
  have htrace : WordTrace (prefixWord ++ tailWord_5141602) baseStart_5141602 baseEnd_5141602 := by
    simpa [prefixWord, tailWord_5141602, baseEnd_5141602] using wordTrace_append hprefix tailTrace_5141602
  have hstable : (prefixWord ++ tailWord_5141602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141602).length < 2 ^ (prefixWord ++ tailWord_5141602).sum := by decide
  have hdescent : baseEnd_5141602 < baseStart_5141602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_5141611 : Nat := 118140960795 + 5141611 * 2 ^ 59
def prefixEnd_5141611 : Nat := 4983230072969 + 3 ^ 40 * 5141611 * 2
def baseEnd_5141611 : Nat := 2640117781444388157016667

theorem tailTrace_5141611 : CollatzResearch.WordTrace tailWord_5141611 prefixEnd_5141611 2640117781444388157016667 := by
  unfold tailWord_5141611
  simp only [CollatzResearch.WordTrace]
  refine ⟨187529959375828939093424687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125019972917219292728949791 187529959375828939093424687)
  ·
    refine ⟨281294939063743408640137031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187529959375828939093424687 281294939063743408640137031)
    ·
      refine ⟨421942408595615112960205547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281294939063743408640137031 421942408595615112960205547)
      ·
        refine ⟨632913612893422669440308321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421942408595615112960205547 632913612893422669440308321)
        ·
          refine ⟨474685209670067002080231241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 632913612893422669440308321 474685209670067002080231241)
          ·
            refine ⟨356013907252550251560173431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474685209670067002080231241 356013907252550251560173431)
            ·
              refine ⟨534020860878825377340260147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356013907252550251560173431 534020860878825377340260147)
              ·
                refine ⟨801031291318238066010390221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534020860878825377340260147 801031291318238066010390221)
                ·
                  refine ⟨300386734244339274753896333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801031291318238066010390221 300386734244339274753896333)
                  ·
                    refine ⟨112645025341627228032711125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 300386734244339274753896333 112645025341627228032711125)
                    ·
                      refine ⟨2640117781444388157016667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112645025341627228032711125 2640117781444388157016667)
                      ·
                        rfl

theorem cell23_5141611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_5141611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141611 prefixEnd_5141611 := by exact prefixLift 5141611
  have htrace : WordTrace (prefixWord ++ tailWord_5141611) baseStart_5141611 baseEnd_5141611 := by
    simpa [prefixWord, tailWord_5141611, baseEnd_5141611] using wordTrace_append hprefix tailTrace_5141611
  have hstable : (prefixWord ++ tailWord_5141611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141611).length < 2 ^ (prefixWord ++ tailWord_5141611).sum := by decide
  have hdescent : baseEnd_5141611 < baseStart_5141611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141655 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5141655 : Nat := 118140960795 + 5141655 * 2 ^ 59
def prefixEnd_5141655 : Nat := 4983230072969 + 3 ^ 40 * 5141655 * 2
def baseEnd_5141655 : Nat := 2640140374593185984866465

theorem tailTrace_5141655 : CollatzResearch.WordTrace tailWord_5141655 prefixEnd_5141655 2640140374593185984866465 := by
  unfold tailWord_5141655
  simp only [CollatzResearch.WordTrace]
  refine ⟨187531564187669534608026419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125021042791779689738684279 187531564187669534608026419)
  ·
    refine ⟨281297346281504301912039629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187531564187669534608026419 281297346281504301912039629)
    ·
      refine ⟨105486504855564113217014861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281297346281504301912039629 105486504855564113217014861)
      ·
        refine ⟨39557439320836542456380573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105486504855564113217014861 39557439320836542456380573)
        ·
          refine ⟨14834039745313703421142715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39557439320836542456380573 14834039745313703421142715)
          ·
            refine ⟨22251059617970555131714073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14834039745313703421142715 22251059617970555131714073)
            ·
              refine ⟨16688294713477916348785555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22251059617970555131714073 16688294713477916348785555)
              ·
                refine ⟨25032442070216874523178333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16688294713477916348785555 25032442070216874523178333)
                ·
                  refine ⟨9387165776331327946191875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25032442070216874523178333 9387165776331327946191875)
                  ·
                    refine ⟨14080748664496991919287813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9387165776331327946191875 14080748664496991919287813)
                    ·
                      refine ⟨2640140374593185984866465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14080748664496991919287813 2640140374593185984866465)
                      ·
                        rfl

theorem cell23_5141655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5141655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141655 prefixEnd_5141655 := by exact prefixLift 5141655
  have htrace : WordTrace (prefixWord ++ tailWord_5141655) baseStart_5141655 baseEnd_5141655 := by
    simpa [prefixWord, tailWord_5141655, baseEnd_5141655] using wordTrace_append hprefix tailTrace_5141655
  have hstable : (prefixWord ++ tailWord_5141655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141655).length < 2 ^ (prefixWord ++ tailWord_5141655).sum := by decide
  have hdescent : baseEnd_5141655 < baseStart_5141655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141665 : List Nat := [1, 2, 3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_5141665 : Nat := 118140960795 + 5141665 * 2 ^ 59
def prefixEnd_5141665 : Nat := 4983230072969 + 3 ^ 40 * 5141665 * 2
def baseEnd_5141665 : Nat := 880048503133243648580473

theorem tailTrace_5141665 : CollatzResearch.WordTrace tailWord_5141665 prefixEnd_5141665 880048503133243648580473 := by
  unfold tailWord_5141665
  simp only [CollatzResearch.WordTrace]
  refine ⟨187531928917633306315890449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125021285945088870877260299 187531928917633306315890449)
  ·
    refine ⟨140648946688224979736917837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187531928917633306315890449 140648946688224979736917837)
    ·
      refine ⟨52743355008084367401344189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140648946688224979736917837 52743355008084367401344189)
      ·
        refine ⟨19778758128031637775504071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52743355008084367401344189 19778758128031637775504071)
        ·
          refine ⟨29668137192047456663256107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19778758128031637775504071 29668137192047456663256107)
          ·
            refine ⟨44502205788071184994884161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29668137192047456663256107 44502205788071184994884161)
            ·
              refine ⟨33376654341053388746163121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44502205788071184994884161 33376654341053388746163121)
              ·
                refine ⟨25032490755790041559622341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33376654341053388746163121 25032490755790041559622341)
                ·
                  refine ⟨4693592016710632792429189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25032490755790041559622341 4693592016710632792429189)
                  ·
                    refine ⟨880048503133243648580473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693592016710632792429189 880048503133243648580473)
                    ·
                      rfl

theorem cell23_5141665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_5141665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141665 prefixEnd_5141665 := by exact prefixLift 5141665
  have htrace : WordTrace (prefixWord ++ tailWord_5141665) baseStart_5141665 baseEnd_5141665 := by
    simpa [prefixWord, tailWord_5141665, baseEnd_5141665] using wordTrace_append hprefix tailTrace_5141665
  have hstable : (prefixWord ++ tailWord_5141665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141665).length < 2 ^ (prefixWord ++ tailWord_5141665).sum := by decide
  have hdescent : baseEnd_5141665 < baseStart_5141665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141682 : List Nat := [3, 2, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_5141682 : Nat := 118140960795 + 5141682 * 2 ^ 59
def prefixEnd_5141682 : Nat := 4983230072969 + 3 ^ 40 * 5141682 * 2
def baseEnd_5141682 : Nat := 880051412856952459742947

theorem tailTrace_5141682 : CollatzResearch.WordTrace tailWord_5141682 prefixEnd_5141682 880051412856952459742947 := by
  unfold tailWord_5141682
  simp only [CollatzResearch.WordTrace]
  refine ⟨46883137239642929554814825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125021699305714478812839533 46883137239642929554814825)
  ·
    refine ⟨35162352929732197166111119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46883137239642929554814825 35162352929732197166111119)
    ·
      refine ⟨52743529394598295749166679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35162352929732197166111119 52743529394598295749166679)
      ·
        refine ⟨79115294091897443623750019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52743529394598295749166679 79115294091897443623750019)
        ·
          refine ⟨118672941137846165435625029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79115294091897443623750019 118672941137846165435625029)
          ·
            refine ⟨22251176463346156019179693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 118672941137846165435625029 22251176463346156019179693)
            ·
              refine ⟨8344191173754808507192385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22251176463346156019179693 8344191173754808507192385)
              ·
                refine ⟨6258143380316106380394289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344191173754808507192385 6258143380316106380394289)
                ·
                  refine ⟨4693607535237079785295717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258143380316106380394289 4693607535237079785295717)
                  ·
                    refine ⟨880051412856952459742947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693607535237079785295717 880051412856952459742947)
                    ·
                      rfl

theorem cell23_5141682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_5141682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141682 prefixEnd_5141682 := by exact prefixLift 5141682
  have htrace : WordTrace (prefixWord ++ tailWord_5141682) baseStart_5141682 baseEnd_5141682 := by
    simpa [prefixWord, tailWord_5141682, baseEnd_5141682] using wordTrace_append hprefix tailTrace_5141682
  have hstable : (prefixWord ++ tailWord_5141682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141682).length < 2 ^ (prefixWord ++ tailWord_5141682).sum := by decide
  have hdescent : baseEnd_5141682 < baseStart_5141682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141689 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 3, 2, 2]
def baseStart_5141689 : Nat := 118140960795 + 5141689 * 2 ^ 59
def prefixEnd_5141689 : Nat := 4983230072969 + 3 ^ 40 * 5141689 * 2
def baseEnd_5141689 : Nat := 2640157832935438851841309

theorem tailTrace_5141689 : CollatzResearch.WordTrace tailWord_5141689 prefixEnd_5141689 2640157832935438851841309 := by
  unfold tailWord_5141689
  simp only [CollatzResearch.WordTrace]
  refine ⟨187532804269546358414764121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125021869513030905609842747 187532804269546358414764121)
  ·
    refine ⟨140649603202159768811073091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187532804269546358414764121 140649603202159768811073091)
    ·
      refine ⟨210974404803239653216609637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140649603202159768811073091 210974404803239653216609637)
      ·
        refine ⟨39557700900607434978114307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210974404803239653216609637 39557700900607434978114307)
        ·
          refine ⟨59336551350911152467171461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39557700900607434978114307 59336551350911152467171461)
          ·
            refine ⟨11125603378295841087594649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59336551350911152467171461 11125603378295841087594649)
            ·
              refine ⟨8344202533721880815695987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11125603378295841087594649 8344202533721880815695987)
              ·
                refine ⟨12516303800582821223543981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8344202533721880815695987 12516303800582821223543981)
                ·
                  refine ⟨4693613925218557958828993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12516303800582821223543981 4693613925218557958828993)
                  ·
                    refine ⟨3520210443913918469121745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4693613925218557958828993 3520210443913918469121745)
                    ·
                      refine ⟨2640157832935438851841309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520210443913918469121745 2640157832935438851841309)
                      ·
                        rfl

theorem cell23_5141689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_5141689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141689 prefixEnd_5141689 := by exact prefixLift 5141689
  have htrace : WordTrace (prefixWord ++ tailWord_5141689) baseStart_5141689 baseEnd_5141689 := by
    simpa [prefixWord, tailWord_5141689, baseEnd_5141689] using wordTrace_append hprefix tailTrace_5141689
  have hstable : (prefixWord ++ tailWord_5141689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141689).length < 2 ^ (prefixWord ++ tailWord_5141689).sum := by decide
  have hdescent : baseEnd_5141689 < baseStart_5141689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141796 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 2, 2, 2]
def baseStart_5141796 : Nat := 118140960795 + 5141796 * 2 ^ 59
def prefixEnd_5141796 : Nat := 4983230072969 + 3 ^ 40 * 5141796 * 2
def baseEnd_5141796 : Nat := 2640212775365469933203317

theorem tailTrace_5141796 : CollatzResearch.WordTrace tailWord_5141796 prefixEnd_5141796 2640212775365469933203317 := by
  unfold tailWord_5141796
  simp only [CollatzResearch.WordTrace]
  refine ⟨93768353440079357844454621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125024471253439143792606161 93768353440079357844454621)
  ·
    refine ⟨35163132540029759191670483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93768353440079357844454621 35163132540029759191670483)
    ·
      refine ⟨52744698810044638787505725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35163132540029759191670483 52744698810044638787505725)
      ·
        refine ⟨19779262053766739545314647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52744698810044638787505725 19779262053766739545314647)
        ·
          refine ⟨29668893080650109317971971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19779262053766739545314647 29668893080650109317971971)
          ·
            refine ⟨44503339620975163976957957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29668893080650109317971971 44503339620975163976957957)
            ·
              refine ⟨8344376178932843245679617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44503339620975163976957957 8344376178932843245679617)
              ·
                refine ⟨6258282134199632434259713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344376178932843245679617 6258282134199632434259713)
                ·
                  refine ⟨4693711600649724325694785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258282134199632434259713 4693711600649724325694785)
                  ·
                    refine ⟨3520283700487293244271089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4693711600649724325694785 3520283700487293244271089)
                    ·
                      refine ⟨2640212775365469933203317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520283700487293244271089 2640212775365469933203317)
                      ·
                        rfl

theorem cell23_5141796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_5141796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141796 prefixEnd_5141796 := by exact prefixLift 5141796
  have htrace : WordTrace (prefixWord ++ tailWord_5141796) baseStart_5141796 baseEnd_5141796 := by
    simpa [prefixWord, tailWord_5141796, baseEnd_5141796] using wordTrace_append hprefix tailTrace_5141796
  have hstable : (prefixWord ++ tailWord_5141796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141796).length < 2 ^ (prefixWord ++ tailWord_5141796).sum := by decide
  have hdescent : baseEnd_5141796 < baseStart_5141796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141869 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_5141869 : Nat := 118140960795 + 5141869 * 2 ^ 59
def prefixEnd_5141869 : Nat := 4983230072969 + 3 ^ 40 * 5141869 * 2
def baseEnd_5141869 : Nat := 2640250259453248147590481

theorem tailTrace_5141869 : CollatzResearch.WordTrace tailWord_5141869 prefixEnd_5141869 2640250259453248147590481 := by
  unfold tailWord_5141869
  simp only [CollatzResearch.WordTrace]
  refine ⟨187539369408894249156316661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125026246272596166104211107 187539369408894249156316661)
  ·
    refine ⟨17581815882083835858404687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 187539369408894249156316661 17581815882083835858404687)
    ·
      refine ⟨26372723823125753787607031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17581815882083835858404687 26372723823125753787607031)
      ·
        refine ⟨39559085734688630681410547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26372723823125753787607031 39559085734688630681410547)
        ·
          refine ⟨59338628602032946022115821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39559085734688630681410547 59338628602032946022115821)
          ·
            refine ⟨22251985725762354758293433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59338628602032946022115821 22251985725762354758293433)
            ·
              refine ⟨16688989294321766068720075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22251985725762354758293433 16688989294321766068720075)
              ·
                refine ⟨25033483941482649103080113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16688989294321766068720075 25033483941482649103080113)
                ·
                  refine ⟨18775112956111986827310085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25033483941482649103080113 18775112956111986827310085)
                  ·
                    refine ⟨3520333679270997530120641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18775112956111986827310085 3520333679270997530120641)
                    ·
                      refine ⟨2640250259453248147590481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520333679270997530120641 2640250259453248147590481)
                      ·
                        rfl

theorem cell23_5141869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_5141869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141869 prefixEnd_5141869 := by exact prefixLift 5141869
  have htrace : WordTrace (prefixWord ++ tailWord_5141869) baseStart_5141869 baseEnd_5141869 := by
    simpa [prefixWord, tailWord_5141869, baseEnd_5141869] using wordTrace_append hprefix tailTrace_5141869
  have hstable : (prefixWord ++ tailWord_5141869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141869).length < 2 ^ (prefixWord ++ tailWord_5141869).sum := by decide
  have hdescent : baseEnd_5141869 < baseStart_5141869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141896 : List Nat := [2, 1, 3, 3, 1, 2, 3, 3, 1, 4]
def baseStart_5141896 : Nat := 118140960795 + 5141896 * 2 ^ 59
def prefixEnd_5141896 : Nat := 4983230072969 + 3 ^ 40 * 5141896 * 2
def baseEnd_5141896 : Nat := 880088041143639847317619

theorem tailTrace_5141896 : CollatzResearch.WordTrace tailWord_5141896 prefixEnd_5141896 880088041143639847317619 := by
  unfold tailWord_5141896
  simp only [CollatzResearch.WordTrace]
  refine ⟨93770177089898216383774771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125026902786530955178366361 93770177089898216383774771)
  ·
    refine ⟨140655265634847324575662157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93770177089898216383774771 140655265634847324575662157)
    ·
      refine ⟨52745724613067746715873309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140655265634847324575662157 52745724613067746715873309)
      ·
        refine ⟨19779646729900405018452491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52745724613067746715873309 19779646729900405018452491)
        ·
          refine ⟨29669470094850607527678737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19779646729900405018452491 29669470094850607527678737)
          ·
            refine ⟨22252102571137955645759053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29669470094850607527678737 22252102571137955645759053)
            ·
              refine ⟨8344538464176733367159645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22252102571137955645759053 8344538464176733367159645)
              ·
                refine ⟨3129201924066275012684867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8344538464176733367159645 3129201924066275012684867)
                ·
                  refine ⟨4693802886099412519027301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129201924066275012684867 4693802886099412519027301)
                  ·
                    refine ⟨880088041143639847317619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693802886099412519027301 880088041143639847317619)
                    ·
                      rfl

theorem cell23_5141896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_5141896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141896 prefixEnd_5141896 := by exact prefixLift 5141896
  have htrace : WordTrace (prefixWord ++ tailWord_5141896) baseStart_5141896 baseEnd_5141896 := by
    simpa [prefixWord, tailWord_5141896, baseEnd_5141896] using wordTrace_append hprefix tailTrace_5141896
  have hstable : (prefixWord ++ tailWord_5141896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141896).length < 2 ^ (prefixWord ++ tailWord_5141896).sum := by decide
  have hdescent : baseEnd_5141896 < baseStart_5141896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141935 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 5, 6]
def baseStart_5141935 : Nat := 118140960795 + 5141935 * 2 ^ 59
def prefixEnd_5141935 : Nat := 4983230072969 + 3 ^ 40 * 5141935 * 2
def baseEnd_5141935 : Nat := 880094716392148296455059

theorem tailTrace_5141935 : CollatzResearch.WordTrace tailWord_5141935 prefixEnd_5141935 880094716392148296455059 := by
  unfold tailWord_5141935
  simp only [CollatzResearch.WordTrace]
  refine ⟨187541776626655142428219259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125027851084436761618812839 187541776626655142428219259)
  ·
    refine ⟨281312664939982713642328889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187541776626655142428219259 281312664939982713642328889)
    ·
      refine ⟨210984498704987035231746667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281312664939982713642328889 210984498704987035231746667)
      ·
        refine ⟨316476748057480552847620001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210984498704987035231746667 316476748057480552847620001)
        ·
          refine ⟨237357561043110414635715001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316476748057480552847620001 237357561043110414635715001)
          ·
            refine ⟨178018170782332810976786251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237357561043110414635715001 178018170782332810976786251)
            ·
              refine ⟨267027256173499216465179377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178018170782332810976786251 267027256173499216465179377)
              ·
                refine ⟨200270442130124412348884533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267027256173499216465179377 200270442130124412348884533)
                ·
                  refine ⟨18775353949699163657707925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200270442130124412348884533 18775353949699163657707925)
                  ·
                    refine ⟨880094716392148296455059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18775353949699163657707925 880094716392148296455059)
                    ·
                      rfl

theorem cell23_5141935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 6].length) (baseStart_5141935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141935 prefixEnd_5141935 := by exact prefixLift 5141935
  have htrace : WordTrace (prefixWord ++ tailWord_5141935) baseStart_5141935 baseEnd_5141935 := by
    simpa [prefixWord, tailWord_5141935, baseEnd_5141935] using wordTrace_append hprefix tailTrace_5141935
  have hstable : (prefixWord ++ tailWord_5141935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141935).length < 2 ^ (prefixWord ++ tailWord_5141935).sum := by decide
  have hdescent : baseEnd_5141935 < baseStart_5141935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141952 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 6, 4]
def baseStart_5141952 : Nat := 118140960795 + 5141952 * 2 ^ 59
def prefixEnd_5141952 : Nat := 4983230072969 + 3 ^ 40 * 5141952 * 2
def baseEnd_5141952 : Nat := 880097626115857107617533

theorem tailTrace_5141952 : CollatzResearch.WordTrace tailWord_5141952 prefixEnd_5141952 880097626115857107617533 := by
  unfold tailWord_5141952
  simp only [CollatzResearch.WordTrace]
  refine ⟨93771198333796777165794055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125028264445062369554392073 93771198333796777165794055)
  ·
    refine ⟨140656797500695165748691083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93771198333796777165794055 140656797500695165748691083)
    ·
      refine ⟨210985196251042748623036625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140656797500695165748691083 210985196251042748623036625)
      ·
        refine ⟨158238897188282061467277469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210985196251042748623036625 158238897188282061467277469)
        ·
          refine ⟨59339586445605773050229051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158238897188282061467277469 59339586445605773050229051)
          ·
            refine ⟨89009379668408659575343577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59339586445605773050229051 89009379668408659575343577)
            ·
              refine ⟨66757034751306494681507683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89009379668408659575343577 66757034751306494681507683)
              ·
                refine ⟨100135552126959742022261525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66757034751306494681507683 100135552126959742022261525)
                ·
                  refine ⟨4693854005951237907293509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 100135552126959742022261525 4693854005951237907293509)
                  ·
                    refine ⟨880097626115857107617533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693854005951237907293509 880097626115857107617533)
                    ·
                      rfl

theorem cell23_5141952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 4].length) (baseStart_5141952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141952 prefixEnd_5141952 := by exact prefixLift 5141952
  have htrace : WordTrace (prefixWord ++ tailWord_5141952) baseStart_5141952 baseEnd_5141952 := by
    simpa [prefixWord, tailWord_5141952, baseEnd_5141952] using wordTrace_append hprefix tailTrace_5141952
  have hstable : (prefixWord ++ tailWord_5141952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141952).length < 2 ^ (prefixWord ++ tailWord_5141952).sum := by decide
  have hdescent : baseEnd_5141952 < baseStart_5141952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5141989 : List Nat := [1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_5141989 : Nat := 118140960795 + 5141989 * 2 ^ 59
def prefixEnd_5141989 : Nat := 4983230072969 + 3 ^ 40 * 5141989 * 2
def baseEnd_5141989 : Nat := 2640311877131787678089929

theorem tailTrace_5141989 : CollatzResearch.WordTrace tailWord_5141989 prefixEnd_5141989 2640311877131787678089929 := by
  unfold tailWord_5141989
  simp only [CollatzResearch.WordTrace]
  refine ⟨187543746168459509650685021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125029164112306339767123347 187543746168459509650685021)
  ·
    refine ⟨70328904813172316119006883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187543746168459509650685021 70328904813172316119006883)
    ·
      refine ⟨105493357219758474178510325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70328904813172316119006883 105493357219758474178510325)
      ·
        refine ⟨9890002239352356954235343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 105493357219758474178510325 9890002239352356954235343)
        ·
          refine ⟨14835003359028535431353015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9890002239352356954235343 14835003359028535431353015)
          ·
            refine ⟨22252505038542803147029523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14835003359028535431353015 22252505038542803147029523)
            ·
              refine ⟨33378757557814204720544285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22252505038542803147029523 33378757557814204720544285)
              ·
                refine ⟨12517034084180326770204107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33378757557814204720544285 12517034084180326770204107)
                ·
                  refine ⟨18775551126270490155306161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12517034084180326770204107 18775551126270490155306161)
                  ·
                    refine ⟨14081663344702867616479621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18775551126270490155306161 14081663344702867616479621)
                    ·
                      refine ⟨2640311877131787678089929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14081663344702867616479621 2640311877131787678089929)
                      ·
                        rfl

theorem cell23_5141989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_5141989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5141989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5141989 prefixEnd_5141989 := by exact prefixLift 5141989
  have htrace : WordTrace (prefixWord ++ tailWord_5141989) baseStart_5141989 baseEnd_5141989 := by
    simpa [prefixWord, tailWord_5141989, baseEnd_5141989] using wordTrace_append hprefix tailTrace_5141989
  have hstable : (prefixWord ++ tailWord_5141989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5141989).length < 2 ^ (prefixWord ++ tailWord_5141989).sum := by decide
  have hdescent : baseEnd_5141989 < baseStart_5141989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5141989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142009 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_5142009 : Nat := 118140960795 + 5142009 * 2 ^ 59
def prefixEnd_5142009 : Nat := 4983230072969 + 3 ^ 40 * 5142009 * 2
def baseEnd_5142009 : Nat := 2640322146744877599839837

theorem tailTrace_5142009 : CollatzResearch.WordTrace tailWord_5142009 prefixEnd_5142009 2640322146744877599839837 := by
  unfold tailWord_5142009
  simp only [CollatzResearch.WordTrace]
  refine ⟨187544475628387053066413081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125029650418924702044275387 187544475628387053066413081)
  ·
    refine ⟨140658356721290289799809811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187544475628387053066413081 140658356721290289799809811)
    ·
      refine ⟨210987535081935434699714717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140658356721290289799809811 210987535081935434699714717)
      ·
        refine ⟨79120325655725788012393019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210987535081935434699714717 79120325655725788012393019)
        ·
          refine ⟨118680488483588682018589529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79120325655725788012393019 118680488483588682018589529)
          ·
            refine ⟨89010366362691511513942147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118680488483588682018589529 89010366362691511513942147)
            ·
              refine ⟨133515549544037267270913221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89010366362691511513942147 133515549544037267270913221)
              ·
                refine ⟨25034165539506987613296229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133515549544037267270913221 25034165539506987613296229)
                ·
                  refine ⟨4693906038657560177493043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25034165539506987613296229 4693906038657560177493043)
                  ·
                    refine ⟨7040859057986340266239565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4693906038657560177493043 7040859057986340266239565)
                    ·
                      refine ⟨2640322146744877599839837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7040859057986340266239565 2640322146744877599839837)
                      ·
                        rfl

theorem cell23_5142009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_5142009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142009 prefixEnd_5142009 := by exact prefixLift 5142009
  have htrace : WordTrace (prefixWord ++ tailWord_5142009) baseStart_5142009 baseEnd_5142009 := by
    simpa [prefixWord, tailWord_5142009, baseEnd_5142009] using wordTrace_append hprefix tailTrace_5142009
  have hstable : (prefixWord ++ tailWord_5142009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142009).length < 2 ^ (prefixWord ++ tailWord_5142009).sum := by decide
  have hdescent : baseEnd_5142009 < baseStart_5142009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142013 : List Nat := [1, 4, 1, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_5142013 : Nat := 118140960795 + 5142013 * 2 ^ 59
def prefixEnd_5142013 : Nat := 4983230072969 + 3 ^ 40 * 5142013 * 2
def baseEnd_5142013 : Nat := 2640324200667495584189819

theorem tailTrace_5142013 : CollatzResearch.WordTrace tailWord_5142013 prefixEnd_5142013 2640324200667495584189819 := by
  unfold tailWord_5142013
  simp only [CollatzResearch.WordTrace]
  refine ⟨187544621520372561749558693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125029747680248374499705795 187544621520372561749558693)
  ·
    refine ⟨35164616535069855328042255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187544621520372561749558693 35164616535069855328042255)
    ·
      refine ⟨52746924802604782992063383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35164616535069855328042255 52746924802604782992063383)
      ·
        refine ⟨79120387203907174488095075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52746924802604782992063383 79120387203907174488095075)
        ·
          refine ⟨118680580805860761732142613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79120387203907174488095075 118680580805860761732142613)
          ·
            refine ⟨5563152225274723206194185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 118680580805860761732142613 5563152225274723206194185)
            ·
              refine ⟨4172364168956042404645639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5563152225274723206194185 4172364168956042404645639)
              ·
                refine ⟨6258546253434063606968459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172364168956042404645639 6258546253434063606968459)
                ·
                  refine ⟨9387819380151095410452689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258546253434063606968459 9387819380151095410452689)
                  ·
                    refine ⟨7040864535113321557839517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9387819380151095410452689 7040864535113321557839517)
                    ·
                      refine ⟨2640324200667495584189819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7040864535113321557839517 2640324200667495584189819)
                      ·
                        rfl

theorem cell23_5142013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_5142013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142013 prefixEnd_5142013 := by exact prefixLift 5142013
  have htrace : WordTrace (prefixWord ++ tailWord_5142013) baseStart_5142013 baseEnd_5142013 := by
    simpa [prefixWord, tailWord_5142013, baseEnd_5142013] using wordTrace_append hprefix tailTrace_5142013
  have hstable : (prefixWord ++ tailWord_5142013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142013).length < 2 ^ (prefixWord ++ tailWord_5142013).sum := by decide
  have hdescent : baseEnd_5142013 < baseStart_5142013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142019 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 5, 3, 2]
def baseStart_5142019 : Nat := 118140960795 + 5142019 * 2 ^ 59
def prefixEnd_5142019 : Nat := 4983230072969 + 3 ^ 40 * 5142019 * 2
def baseEnd_5142019 : Nat := 2640327281551422560714791

theorem tailTrace_5142019 : CollatzResearch.WordTrace tailWord_5142019 prefixEnd_5142019 2640327281551422560714791 := by
  unfold tailWord_5142019
  simp only [CollatzResearch.WordTrace]
  refine ⟨187544840358350824774277111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125029893572233883182851407 187544840358350824774277111)
  ·
    refine ⟨281317260537526237161415667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187544840358350824774277111 281317260537526237161415667)
    ·
      refine ⟨421975890806289355742123501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281317260537526237161415667 421975890806289355742123501)
      ·
        refine ⟨158240959052358508403296313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421975890806289355742123501 158240959052358508403296313)
        ·
          refine ⟨118680719289268881302472235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158240959052358508403296313 118680719289268881302472235)
          ·
            refine ⟨178021078933903321953708353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118680719289268881302472235 178021078933903321953708353)
            ·
              refine ⟨133515809200427491465281265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178021078933903321953708353 133515809200427491465281265)
              ·
                refine ⟨100136856900320618598960949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133515809200427491465281265 100136856900320618598960949)
                ·
                  refine ⟨9387830334405057993652589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100136856900320618598960949 9387830334405057993652589)
                  ·
                    refine ⟨3520436375401896747619721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9387830334405057993652589 3520436375401896747619721)
                    ·
                      refine ⟨2640327281551422560714791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520436375401896747619721 2640327281551422560714791)
                      ·
                        rfl

theorem cell23_5142019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_5142019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142019 prefixEnd_5142019 := by exact prefixLift 5142019
  have htrace : WordTrace (prefixWord ++ tailWord_5142019) baseStart_5142019 baseEnd_5142019 := by
    simpa [prefixWord, tailWord_5142019, baseEnd_5142019] using wordTrace_append hprefix tailTrace_5142019
  have hstable : (prefixWord ++ tailWord_5142019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142019).length < 2 ^ (prefixWord ++ tailWord_5142019).sum := by decide
  have hdescent : baseEnd_5142019 < baseStart_5142019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142020 : List Nat := [2, 3, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_5142020 : Nat := 118140960795 + 5142020 * 2 ^ 59
def prefixEnd_5142020 : Nat := 4983230072969 + 3 ^ 40 * 5142020 * 2
def baseEnd_5142020 : Nat := 880109265010692352267429

theorem tailTrace_5142020 : CollatzResearch.WordTrace tailWord_5142020 prefixEnd_5142020 880109265010692352267429 := by
  unfold tailWord_5142020
  simp only [CollatzResearch.WordTrace]
  refine ⟨93772438415673600972531757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125029917887564801296709009 93772438415673600972531757)
  ·
    refine ⟨35164664405877600364699409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93772438415673600972531757 35164664405877600364699409)
    ·
      refine ⟨26373498304408200273524557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35164664405877600364699409 26373498304408200273524557)
      ·
        refine ⟨9890061864153075102571709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26373498304408200273524557 9890061864153075102571709)
        ·
          refine ⟨3708773199057403163464391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9890061864153075102571709 3708773199057403163464391)
          ·
            refine ⟨5563159798586104745196587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3708773199057403163464391 5563159798586104745196587)
            ·
              refine ⟨8344739697879157117794881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563159798586104745196587 8344739697879157117794881)
              ·
                refine ⟨6258554773409367838346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8344739697879157117794881 6258554773409367838346161)
                ·
                  refine ⟨4693916080057025878759621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258554773409367838346161 4693916080057025878759621)
                  ·
                    refine ⟨880109265010692352267429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4693916080057025878759621 880109265010692352267429)
                    ·
                      rfl

theorem cell23_5142020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_5142020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142020 prefixEnd_5142020 := by exact prefixLift 5142020
  have htrace : WordTrace (prefixWord ++ tailWord_5142020) baseStart_5142020 baseEnd_5142020 := by
    simpa [prefixWord, tailWord_5142020, baseEnd_5142020] using wordTrace_append hprefix tailTrace_5142020
  have hstable : (prefixWord ++ tailWord_5142020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142020).length < 2 ^ (prefixWord ++ tailWord_5142020).sum := by decide
  have hdescent : baseEnd_5142020 < baseStart_5142020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142026 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_5142026 : Nat := 118140960795 + 5142026 * 2 ^ 59
def prefixEnd_5142026 : Nat := 4983230072969 + 3 ^ 40 * 5142026 * 2
def baseEnd_5142026 : Nat := 2640330875916004033327259

theorem tailTrace_5142026 : CollatzResearch.WordTrace tailWord_5142026 prefixEnd_5142026 2640330875916004033327259 := by
  unfold tailWord_5142026
  simp only [CollatzResearch.WordTrace]
  refine ⟨46886273917331366242445483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125030063779550309979854621 46886273917331366242445483)
  ·
    refine ⟨70329410875997049363668225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46886273917331366242445483 70329410875997049363668225)
    ·
      refine ⟨52747058156997787022751169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70329410875997049363668225 52747058156997787022751169)
      ·
        refine ⟨39560293617748340267063377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52747058156997787022751169 39560293617748340267063377)
        ·
          refine ⟨29670220213311255200297533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39560293617748340267063377 29670220213311255200297533)
          ·
            refine ⟨11126332579991720700111575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29670220213311255200297533 11126332579991720700111575)
            ·
              refine ⟨16689498869987581050167363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126332579991720700111575 16689498869987581050167363)
              ·
                refine ⟨25034248304981371575251045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16689498869987581050167363 25034248304981371575251045)
                ·
                  refine ⟨4693921557184007170359571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25034248304981371575251045 4693921557184007170359571)
                  ·
                    refine ⟨7040882335776010755539357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4693921557184007170359571 7040882335776010755539357)
                    ·
                      refine ⟨2640330875916004033327259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7040882335776010755539357 2640330875916004033327259)
                      ·
                        rfl

theorem cell23_5142026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_5142026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142026 prefixEnd_5142026 := by exact prefixLift 5142026
  have htrace : WordTrace (prefixWord ++ tailWord_5142026) baseStart_5142026 baseEnd_5142026 := by
    simpa [prefixWord, tailWord_5142026, baseEnd_5142026] using wordTrace_append hprefix tailTrace_5142026
  have hstable : (prefixWord ++ tailWord_5142026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142026).length < 2 ^ (prefixWord ++ tailWord_5142026).sum := by decide
  have hdescent : baseEnd_5142026 < baseStart_5142026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142069 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_5142069 : Nat := 118140960795 + 5142069 * 2 ^ 59
def prefixEnd_5142069 : Nat := 4983230072969 + 3 ^ 40 * 5142069 * 2
def baseEnd_5142069 : Nat := 2640352955584147365089561

theorem tailTrace_5142069 : CollatzResearch.WordTrace tailWord_5142069 prefixEnd_5142069 2640352955584147365089561 := by
  unfold tailWord_5142069
  simp only [CollatzResearch.WordTrace]
  refine ⟨187546664008169683313597261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125031109338779788875731507 187546664008169683313597261)
  ·
    refine ⟨70329999003063631242598973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187546664008169683313597261 70329999003063631242598973)
    ·
      refine ⟨26373749626148861715974615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70329999003063631242598973 26373749626148861715974615)
      ·
        refine ⟨39560624439223292573961923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26373749626148861715974615 39560624439223292573961923)
        ·
          refine ⟨59340936658834938860942885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39560624439223292573961923 59340936658834938860942885)
          ·
            refine ⟨11126425623531551036426791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59340936658834938860942885 11126425623531551036426791)
            ·
              refine ⟨16689638435297326554640187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126425623531551036426791 16689638435297326554640187)
              ·
                refine ⟨25034457652945989831960281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16689638435297326554640187 25034457652945989831960281)
                ·
                  refine ⟨18775843239709492373970211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25034457652945989831960281 18775843239709492373970211)
                  ·
                    refine ⟨28163764859564238560955317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18775843239709492373970211 28163764859564238560955317)
                    ·
                      refine ⟨2640352955584147365089561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 28163764859564238560955317 2640352955584147365089561)
                      ·
                        rfl

theorem cell23_5142069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_5142069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142069 prefixEnd_5142069 := by exact prefixLift 5142069
  have htrace : WordTrace (prefixWord ++ tailWord_5142069) baseStart_5142069 baseEnd_5142069 := by
    simpa [prefixWord, tailWord_5142069, baseEnd_5142069] using wordTrace_append hprefix tailTrace_5142069
  have hstable : (prefixWord ++ tailWord_5142069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142069).length < 2 ^ (prefixWord ++ tailWord_5142069).sum := by decide
  have hdescent : baseEnd_5142069 < baseStart_5142069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142089 : List Nat := [1, 2, 1, 1, 2, 2, 1, 8, 5]
def baseStart_5142089 : Nat := 118140960795 + 5142089 * 2 ^ 59
def prefixEnd_5142089 : Nat := 4983230072969 + 3 ^ 40 * 5142089 * 2
def baseEnd_5142089 : Nat := 293373691688581920759941

theorem tailTrace_5142089 : CollatzResearch.WordTrace tailWord_5142089 prefixEnd_5142089 293373691688581920759941 := by
  unfold tailWord_5142089
  simp only [CollatzResearch.WordTrace]
  refine ⟨187547393468097226729325321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125031595645398151152883547 187547393468097226729325321)
  ·
    refine ⟨140660545101072920046993991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187547393468097226729325321 140660545101072920046993991)
    ·
      refine ⟨210990817651609380070490987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140660545101072920046993991 210990817651609380070490987)
      ·
        refine ⟨316486226477414070105736481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210990817651609380070490987 316486226477414070105736481)
        ·
          refine ⟨237364669858060552579302361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316486226477414070105736481 237364669858060552579302361)
          ·
            refine ⟨178023502393545414434476771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237364669858060552579302361 178023502393545414434476771)
            ·
              refine ⟨267035253590318121651715157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178023502393545414434476771 267035253590318121651715157)
              ·
                refine ⟨3129319378011540488106037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 267035253590318121651715157 3129319378011540488106037)
                ·
                  refine ⟨293373691688581920759941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129319378011540488106037 293373691688581920759941)
                  ·
                    rfl

theorem cell23_5142089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 5].length) (baseStart_5142089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142089 prefixEnd_5142089 := by exact prefixLift 5142089
  have htrace : WordTrace (prefixWord ++ tailWord_5142089) baseStart_5142089 baseEnd_5142089 := by
    simpa [prefixWord, tailWord_5142089, baseEnd_5142089] using wordTrace_append hprefix tailTrace_5142089
  have hstable : (prefixWord ++ tailWord_5142089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142089).length < 2 ^ (prefixWord ++ tailWord_5142089).sum := by decide
  have hdescent : baseEnd_5142089 < baseStart_5142089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142112 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7]
def baseStart_5142112 : Nat := 118140960795 + 5142112 * 2 ^ 59
def prefixEnd_5142112 : Nat := 4983230072969 + 3 ^ 40 * 5142112 * 2
def baseEnd_5142112 : Nat := 2640375035252290696851863

theorem tailTrace_5142112 : CollatzResearch.WordTrace tailWord_5142112 prefixEnd_5142112 2640375035252290696851863 := by
  unfold tailWord_5142112
  simp only [CollatzResearch.WordTrace]
  refine ⟨93774116173506950828706295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125032154898009267771608393 93774116173506950828706295)
  ·
    refine ⟨140661174260260426243059443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93774116173506950828706295 140661174260260426243059443)
    ·
      refine ⟨210991761390390639364589165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140661174260260426243059443 210991761390390639364589165)
      ·
        refine ⟨79121910521396489761720937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210991761390390639364589165 79121910521396489761720937)
        ·
          refine ⟨59341432891047367321290703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79121910521396489761720937 59341432891047367321290703)
          ·
            refine ⟨89012149336571050981936055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59341432891047367321290703 89012149336571050981936055)
            ·
              refine ⟨133518224004856576472904083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89012149336571050981936055 133518224004856576472904083)
              ·
                refine ⟨200277336007284864709356125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133518224004856576472904083 200277336007284864709356125)
                ·
                  refine ⟨75104001002731824266008547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200277336007284864709356125 75104001002731824266008547)
                  ·
                    refine ⟨112656001504097736399012821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 75104001002731824266008547 112656001504097736399012821)
                    ·
                      refine ⟨2640375035252290696851863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 112656001504097736399012821 2640375035252290696851863)
                      ·
                        rfl

theorem cell23_5142112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_5142112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142112 prefixEnd_5142112 := by exact prefixLift 5142112
  have htrace : WordTrace (prefixWord ++ tailWord_5142112) baseStart_5142112 baseEnd_5142112 := by
    simpa [prefixWord, tailWord_5142112, baseEnd_5142112] using wordTrace_append hprefix tailTrace_5142112
  have hstable : (prefixWord ++ tailWord_5142112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142112).length < 2 ^ (prefixWord ++ tailWord_5142112).sum := by decide
  have hdescent : baseEnd_5142112 < baseStart_5142112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142119 : List Nat := [1, 1, 5, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5142119 : Nat := 118140960795 + 5142119 * 2 ^ 59
def prefixEnd_5142119 : Nat := 4983230072969 + 3 ^ 40 * 5142119 * 2
def baseEnd_5142119 : Nat := 880126209872290723154777

theorem tailTrace_5142119 : CollatzResearch.WordTrace tailWord_5142119 prefixEnd_5142119 880126209872290723154777 := by
  unfold tailWord_5142119
  simp only [CollatzResearch.WordTrace]
  refine ⟨187548487657988541852917411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125032325105325694568611607 187548487657988541852917411)
  ·
    refine ⟨281322731486982812779376117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187548487657988541852917411 281322731486982812779376117)
    ·
      refine ⟨26374006076904638698066511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 281322731486982812779376117 26374006076904638698066511)
      ·
        refine ⟨39561009115356958047099767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26374006076904638698066511 39561009115356958047099767)
        ·
          refine ⟨59341513673035437070649651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39561009115356958047099767 59341513673035437070649651)
          ·
            refine ⟨89012270509553155605974477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59341513673035437070649651 89012270509553155605974477)
            ·
              refine ⟨33379601441082433352240429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89012270509553155605974477 33379601441082433352240429)
              ·
                refine ⟨12517350540405912507090161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33379601441082433352240429 12517350540405912507090161)
                ·
                  refine ⟨9388012905304434380317621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12517350540405912507090161 9388012905304434380317621)
                  ·
                    refine ⟨880126209872290723154777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9388012905304434380317621 880126209872290723154777)
                    ·
                      rfl

theorem cell23_5142119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5142119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142119 prefixEnd_5142119 := by exact prefixLift 5142119
  have htrace : WordTrace (prefixWord ++ tailWord_5142119) baseStart_5142119 baseEnd_5142119 := by
    simpa [prefixWord, tailWord_5142119, baseEnd_5142119] using wordTrace_append hprefix tailTrace_5142119
  have hstable : (prefixWord ++ tailWord_5142119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142119).length < 2 ^ (prefixWord ++ tailWord_5142119).sum := by decide
  have hdescent : baseEnd_5142119 < baseStart_5142119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142139 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4]
def baseStart_5142139 : Nat := 118140960795 + 5142139 * 2 ^ 59
def prefixEnd_5142139 : Nat := 4983230072969 + 3 ^ 40 * 5142139 * 2
def baseEnd_5142139 : Nat := 2640388899229962091214239

theorem tailTrace_5142139 : CollatzResearch.WordTrace tailWord_5142139 prefixEnd_5142139 2640388899229962091214239 := by
  unfold tailWord_5142139
  simp only [CollatzResearch.WordTrace]
  refine ⟨187549217117916085268645471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125032811411944056845763647 187549217117916085268645471)
  ·
    refine ⟨281323825676874127902968207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187549217117916085268645471 281323825676874127902968207)
    ·
      refine ⟨421985738515311191854452311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281323825676874127902968207 421985738515311191854452311)
      ·
        refine ⟨632978607772966787781678467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421985738515311191854452311 632978607772966787781678467)
        ·
          refine ⟨949467911659450181672517701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632978607772966787781678467 949467911659450181672517701)
          ·
            refine ⟨178025233436146909063597069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 949467911659450181672517701 178025233436146909063597069)
            ·
              refine ⟨66759462538555090898848901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178025233436146909063597069 66759462538555090898848901)
              ·
                refine ⟨12517399225979079543534169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66759462538555090898848901 12517399225979079543534169)
                ·
                  refine ⟨9388049419484309657650627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12517399225979079543534169 9388049419484309657650627)
                  ·
                    refine ⟨14082074129226464486475941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9388049419484309657650627 14082074129226464486475941)
                    ·
                      refine ⟨2640388899229962091214239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14082074129226464486475941 2640388899229962091214239)
                      ·
                        rfl

theorem cell23_5142139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 4].length) (baseStart_5142139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142139 prefixEnd_5142139 := by exact prefixLift 5142139
  have htrace : WordTrace (prefixWord ++ tailWord_5142139) baseStart_5142139 baseEnd_5142139 := by
    simpa [prefixWord, tailWord_5142139, baseEnd_5142139] using wordTrace_append hprefix tailTrace_5142139
  have hstable : (prefixWord ++ tailWord_5142139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142139).length < 2 ^ (prefixWord ++ tailWord_5142139).sum := by decide
  have hdescent : baseEnd_5142139 < baseStart_5142139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142156 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_5142156 : Nat := 118140960795 + 5142156 * 2 ^ 59
def prefixEnd_5142156 : Nat := 4983230072969 + 3 ^ 40 * 5142156 * 2
def baseEnd_5142156 : Nat := 2640397628401088524701661

theorem tailTrace_5142156 : CollatzResearch.WordTrace tailWord_5142156 prefixEnd_5142156 2640397628401088524701661 := by
  unfold tailWord_5142156
  simp only [CollatzResearch.WordTrace]
  refine ⟨93774918579427248586007161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125033224772569664781342881 93774918579427248586007161)
  ·
    refine ⟨70331188934570436439505371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93774918579427248586007161 70331188934570436439505371)
    ·
      refine ⟨105496783401855654659258057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70331188934570436439505371 105496783401855654659258057)
      ·
        refine ⟨79122587551391740994443543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105496783401855654659258057 79122587551391740994443543)
        ·
          refine ⟨118683881327087611491665315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79122587551391740994443543 118683881327087611491665315)
          ·
            refine ⟨178025821990631417237497973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118683881327087611491665315 178025821990631417237497973)
            ·
              refine ⟨16689920811621695366015435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178025821990631417237497973 16689920811621695366015435)
              ·
                refine ⟨25034881217432543049023153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16689920811621695366015435 25034881217432543049023153)
                ·
                  refine ⟨18776160913074407286767365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25034881217432543049023153 18776160913074407286767365)
                  ·
                    refine ⟨3520530171201451366268881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18776160913074407286767365 3520530171201451366268881)
                    ·
                      refine ⟨2640397628401088524701661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520530171201451366268881 2640397628401088524701661)
                      ·
                        rfl

theorem cell23_5142156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_5142156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142156 prefixEnd_5142156 := by exact prefixLift 5142156
  have htrace : WordTrace (prefixWord ++ tailWord_5142156) baseStart_5142156 baseEnd_5142156 := by
    simpa [prefixWord, tailWord_5142156, baseEnd_5142156] using wordTrace_append hprefix tailTrace_5142156
  have hstable : (prefixWord ++ tailWord_5142156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142156).length < 2 ^ (prefixWord ++ tailWord_5142156).sum := by decide
  have hdescent : baseEnd_5142156 < baseStart_5142156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142176 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3]
def baseStart_5142176 : Nat := 118140960795 + 5142176 * 2 ^ 59
def prefixEnd_5142176 : Nat := 4983230072969 + 3 ^ 40 * 5142176 * 2
def baseEnd_5142176 : Nat := 2640407898014178446451569

theorem tailTrace_5142176 : CollatzResearch.WordTrace tailWord_5142176 prefixEnd_5142176 2640407898014178446451569 := by
  unfold tailWord_5142176
  simp only [CollatzResearch.WordTrace]
  refine ⟨93775283309391020293871191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125033711079188027058494921 93775283309391020293871191)
  ·
    refine ⟨140662924964086530440806787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93775283309391020293871191 140662924964086530440806787)
    ·
      refine ⟨210994387446129795661210181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140662924964086530440806787 210994387446129795661210181)
      ·
        refine ⟨39561447646149336686476909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 210994387446129795661210181 39561447646149336686476909)
        ·
          refine ⟨14835542867306001257428841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39561447646149336686476909 14835542867306001257428841)
          ·
            refine ⟨11126657150479500943071631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14835542867306001257428841 11126657150479500943071631)
            ·
              refine ⟨16689985725719251414607447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11126657150479500943071631 16689985725719251414607447)
              ·
                refine ⟨25034978588578877121911171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16689985725719251414607447 25034978588578877121911171)
                ·
                  refine ⟨37552467882868315682866757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25034978588578877121911171 37552467882868315682866757)
                  ·
                    refine ⟨7041087728037809190537517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37552467882868315682866757 7041087728037809190537517)
                    ·
                      refine ⟨2640407898014178446451569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041087728037809190537517 2640407898014178446451569)
                      ·
                        rfl

theorem cell23_5142176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_5142176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142176 prefixEnd_5142176 := by exact prefixLift 5142176
  have htrace : WordTrace (prefixWord ++ tailWord_5142176) baseStart_5142176 baseEnd_5142176 := by
    simpa [prefixWord, tailWord_5142176, baseEnd_5142176] using wordTrace_append hprefix tailTrace_5142176
  have hstable : (prefixWord ++ tailWord_5142176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142176).length < 2 ^ (prefixWord ++ tailWord_5142176).sum := by decide
  have hdescent : baseEnd_5142176 < baseStart_5142176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142199 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_5142199 : Nat := 118140960795 + 5142199 * 2 ^ 59
def prefixEnd_5142199 : Nat := 4983230072969 + 3 ^ 40 * 5142199 * 2
def baseEnd_5142199 : Nat := 2640419708069231856463963

theorem tailTrace_5142199 : CollatzResearch.WordTrace tailWord_5142199 prefixEnd_5142199 2640419708069231856463963 := by
  unfold tailWord_5142199
  simp only [CollatzResearch.WordTrace]
  refine ⟨187551405497698715515829651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125034270331799143677219767 187551405497698715515829651)
  ·
    refine ⟨281327108246548073273744477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187551405497698715515829651 281327108246548073273744477)
    ·
      refine ⟨105497665592455527477654179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281327108246548073273744477 105497665592455527477654179)
      ·
        refine ⟨158246498388683291216481269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105497665592455527477654179 158246498388683291216481269)
        ·
          refine ⟨14835609223939058551545119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158246498388683291216481269 14835609223939058551545119)
          ·
            refine ⟨22253413835908587827317679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14835609223939058551545119 22253413835908587827317679)
            ·
              refine ⟨33380120753862881740976519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22253413835908587827317679 33380120753862881740976519)
              ·
                refine ⟨50070181130794322611464779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33380120753862881740976519 50070181130794322611464779)
                ·
                  refine ⟨75105271696191483917197169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50070181130794322611464779 75105271696191483917197169)
                  ·
                    refine ⟨56328953772143612937897877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 75105271696191483917197169 56328953772143612937897877)
                    ·
                      refine ⟨2640419708069231856463963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56328953772143612937897877 2640419708069231856463963)
                      ·
                        rfl

theorem cell23_5142199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_5142199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142199 prefixEnd_5142199 := by exact prefixLift 5142199
  have htrace : WordTrace (prefixWord ++ tailWord_5142199) baseStart_5142199 baseEnd_5142199 := by
    simpa [prefixWord, tailWord_5142199, baseEnd_5142199] using wordTrace_append hprefix tailTrace_5142199
  have hstable : (prefixWord ++ tailWord_5142199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142199).length < 2 ^ (prefixWord ++ tailWord_5142199).sum := by decide
  have hdescent : baseEnd_5142199 < baseStart_5142199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142216 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_5142216 : Nat := 118140960795 + 5142216 * 2 ^ 59
def prefixEnd_5142216 : Nat := 4983230072969 + 3 ^ 40 * 5142216 * 2
def baseEnd_5142216 : Nat := 2640428437240358289951385

theorem tailTrace_5142216 : CollatzResearch.WordTrace tailWord_5142216 prefixEnd_5142216 2640428437240358289951385 := by
  unfold tailWord_5142216
  simp only [CollatzResearch.WordTrace]
  refine ⟨93776012769318563709599251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125034683692424751612799001 93776012769318563709599251)
  ·
    refine ⟨140664019153977845564398877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93776012769318563709599251 140664019153977845564398877)
    ·
      refine ⟨52749007182741692086649579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 140664019153977845564398877 52749007182741692086649579)
      ·
        refine ⟨79123510774112538129974369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52749007182741692086649579 79123510774112538129974369)
        ·
          refine ⟨59342633080584403597480777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79123510774112538129974369 59342633080584403597480777)
          ·
            refine ⟨44506974810438302698110583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59342633080584403597480777 44506974810438302698110583)
            ·
              refine ⟨66760462215657454047165875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44506974810438302698110583 66760462215657454047165875)
              ·
                refine ⟨100140693323486181070748813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66760462215657454047165875 100140693323486181070748813)
                ·
                  refine ⟨37552759996307317901530805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100140693323486181070748813 37552759996307317901530805)
                  ·
                    refine ⟨3520571249653811053268513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37552759996307317901530805 3520571249653811053268513)
                    ·
                      refine ⟨2640428437240358289951385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520571249653811053268513 2640428437240358289951385)
                      ·
                        rfl

theorem cell23_5142216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_5142216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142216 prefixEnd_5142216 := by exact prefixLift 5142216
  have htrace : WordTrace (prefixWord ++ tailWord_5142216) baseStart_5142216 baseEnd_5142216 := by
    simpa [prefixWord, tailWord_5142216, baseEnd_5142216] using wordTrace_append hprefix tailTrace_5142216
  have hstable : (prefixWord ++ tailWord_5142216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142216).length < 2 ^ (prefixWord ++ tailWord_5142216).sum := by decide
  have hdescent : baseEnd_5142216 < baseStart_5142216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142239 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 3, 6]
def baseStart_5142239 : Nat := 118140960795 + 5142239 * 2 ^ 59
def prefixEnd_5142239 : Nat := 4983230072969 + 3 ^ 40 * 5142239 * 2
def baseEnd_5142239 : Nat := 880146749098470566654593

theorem tailTrace_5142239 : CollatzResearch.WordTrace tailWord_5142239 prefixEnd_5142239 880146749098470566654593 := by
  unfold tailWord_5142239
  simp only [CollatzResearch.WordTrace]
  refine ⟨187552864417553802347285771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125035242945035868231523847 187552864417553802347285771)
  ·
    refine ⟨281329296626330703520928657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187552864417553802347285771 281329296626330703520928657)
    ·
      refine ⟨210996972469748027640696493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281329296626330703520928657 210996972469748027640696493)
      ·
        refine ⟨79123864676155510365261185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210996972469748027640696493 79123864676155510365261185)
        ·
          refine ⟨59342898507116632773945889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79123864676155510365261185 59342898507116632773945889)
          ·
            refine ⟨44507173880337474580459417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59342898507116632773945889 44507173880337474580459417)
            ·
              refine ⟨33380380410253105935344563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44507173880337474580459417 33380380410253105935344563)
              ·
                refine ⟨50070570615379658903016845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33380380410253105935344563 50070570615379658903016845)
                ·
                  refine ⟨18776463980767372088631317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50070570615379658903016845 18776463980767372088631317)
                  ·
                    refine ⟨880146749098470566654593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18776463980767372088631317 880146749098470566654593)
                    ·
                      rfl

theorem cell23_5142239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 6].length) (baseStart_5142239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142239 prefixEnd_5142239 := by exact prefixLift 5142239
  have htrace : WordTrace (prefixWord ++ tailWord_5142239) baseStart_5142239 baseEnd_5142239 := by
    simpa [prefixWord, tailWord_5142239, baseEnd_5142239] using wordTrace_append hprefix tailTrace_5142239
  have hstable : (prefixWord ++ tailWord_5142239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142239).length < 2 ^ (prefixWord ++ tailWord_5142239).sum := by decide
  have hdescent : baseEnd_5142239 < baseStart_5142239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142240 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 1, 1, 3]
def baseStart_5142240 : Nat := 118140960795 + 5142240 * 2 ^ 59
def prefixEnd_5142240 : Nat := 4983230072969 + 3 ^ 40 * 5142240 * 2
def baseEnd_5142240 : Nat := 2640440760776066196051275

theorem tailTrace_5142240 : CollatzResearch.WordTrace tailWord_5142240 prefixEnd_5142240 2640440760776066196051275 := by
  unfold tailWord_5142240
  simp only [CollatzResearch.WordTrace]
  refine ⟨93776450445275089759036087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125035267260366786345381449 93776450445275089759036087)
  ·
    refine ⟨140664675667912634638554131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93776450445275089759036087 140664675667912634638554131)
    ·
      refine ⟨210997013501868951957831197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140664675667912634638554131 210997013501868951957831197)
      ·
        refine ⟨79123880063200856984186699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 210997013501868951957831197 79123880063200856984186699)
        ·
          refine ⟨118685820094801285476280049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79123880063200856984186699 118685820094801285476280049)
          ·
            refine ⟨89014365071100964107210037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118685820094801285476280049 89014365071100964107210037)
            ·
              refine ⟨8345096725415715385050941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89014365071100964107210037 8345096725415715385050941)
              ·
                refine ⟨3129411272030893269394103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8345096725415715385050941 3129411272030893269394103)
                ·
                  refine ⟨4694116908046339904091155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129411272030893269394103 4694116908046339904091155)
                  ·
                    refine ⟨7041175362069509856136733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694116908046339904091155 7041175362069509856136733)
                    ·
                      refine ⟨2640440760776066196051275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041175362069509856136733 2640440760776066196051275)
                      ·
                        rfl

theorem cell23_5142240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_5142240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142240 prefixEnd_5142240 := by exact prefixLift 5142240
  have htrace : WordTrace (prefixWord ++ tailWord_5142240) baseStart_5142240 baseEnd_5142240 := by
    simpa [prefixWord, tailWord_5142240, baseEnd_5142240] using wordTrace_append hprefix tailTrace_5142240
  have hstable : (prefixWord ++ tailWord_5142240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142240).length < 2 ^ (prefixWord ++ tailWord_5142240).sum := by decide
  have hdescent : baseEnd_5142240 < baseStart_5142240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142257 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 1, 1, 3]
def baseStart_5142257 : Nat := 118140960795 + 5142257 * 2 ^ 59
def prefixEnd_5142257 : Nat := 4983230072969 + 3 ^ 40 * 5142257 * 2
def baseEnd_5142257 : Nat := 2640449489947192629538697

theorem tailTrace_5142257 : CollatzResearch.WordTrace tailWord_5142257 prefixEnd_5142257 2640449489947192629538697 := by
  unfold tailWord_5142257
  simp only [CollatzResearch.WordTrace]
  refine ⟨187553520931488591421441025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125035680620992394280960683 187553520931488591421441025)
  ·
    refine ⟨140665140698616443566080769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187553520931488591421441025 140665140698616443566080769)
    ·
      refine ⟨105498855523962332674560577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140665140698616443566080769 105498855523962332674560577)
      ·
        refine ⟨79124141642971749505920433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105498855523962332674560577 79124141642971749505920433)
        ·
          refine ⟨59343106232228812129440325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79124141642971749505920433 59343106232228812129440325)
          ·
            refine ⟨11126832418542902274270061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59343106232228812129440325 11126832418542902274270061)
            ·
              refine ⟨4172562156953588352851273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11126832418542902274270061 4172562156953588352851273)
              ·
                refine ⟨3129421617715191264638455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172562156953588352851273 3129421617715191264638455)
                ·
                  refine ⟨4694132426572786896957683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129421617715191264638455 4694132426572786896957683)
                  ·
                    refine ⟨7041198639859180345436525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694132426572786896957683 7041198639859180345436525)
                    ·
                      refine ⟨2640449489947192629538697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041198639859180345436525 2640449489947192629538697)
                      ·
                        rfl

theorem cell23_5142257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_5142257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142257 prefixEnd_5142257 := by exact prefixLift 5142257
  have htrace : WordTrace (prefixWord ++ tailWord_5142257) baseStart_5142257 baseEnd_5142257 := by
    simpa [prefixWord, tailWord_5142257, baseEnd_5142257] using wordTrace_append hprefix tailTrace_5142257
  have hstable : (prefixWord ++ tailWord_5142257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142257).length < 2 ^ (prefixWord ++ tailWord_5142257).sum := by decide
  have hdescent : baseEnd_5142257 < baseStart_5142257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142259 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6]
def baseStart_5142259 : Nat := 118140960795 + 5142259 * 2 ^ 59
def prefixEnd_5142259 : Nat := 4983230072969 + 3 ^ 40 * 5142259 * 2
def baseEnd_5142259 : Nat := 2640450516908501621713687

theorem tailTrace_5142259 : CollatzResearch.WordTrace tailWord_5142259 prefixEnd_5142259 2640450516908501621713687 := by
  unfold tailWord_5142259
  simp only [CollatzResearch.WordTrace]
  refine ⟨187553593877481345763013831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125035729251654230508675887 187553593877481345763013831)
  ·
    refine ⟨281330390816222018644520747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187553593877481345763013831 281330390816222018644520747)
    ·
      refine ⟨421995586224333027966781121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281330390816222018644520747 421995586224333027966781121)
      ·
        refine ⟨316496689668249770975085841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421995586224333027966781121 316496689668249770975085841)
        ·
          refine ⟨237372517251187328231314381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316496689668249770975085841 237372517251187328231314381)
          ·
            refine ⟨89014693969195248086742893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237372517251187328231314381 89014693969195248086742893)
            ·
              refine ⟨33380510238448218032528585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89014693969195248086742893 33380510238448218032528585)
              ·
                refine ⟨25035382678836163524396439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33380510238448218032528585 25035382678836163524396439)
                ·
                  refine ⟨37553074018254245286594659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25035382678836163524396439 37553074018254245286594659)
                  ·
                    refine ⟨56329611027381367929891989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37553074018254245286594659 56329611027381367929891989)
                    ·
                      refine ⟨2640450516908501621713687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56329611027381367929891989 2640450516908501621713687)
                      ·
                        rfl

theorem cell23_5142259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 6].length) (baseStart_5142259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142259 prefixEnd_5142259 := by exact prefixLift 5142259
  have htrace : WordTrace (prefixWord ++ tailWord_5142259) baseStart_5142259 baseEnd_5142259 := by
    simpa [prefixWord, tailWord_5142259, baseEnd_5142259] using wordTrace_append hprefix tailTrace_5142259
  have hstable : (prefixWord ++ tailWord_5142259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142259).length < 2 ^ (prefixWord ++ tailWord_5142259).sum := by decide
  have hdescent : baseEnd_5142259 < baseStart_5142259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142266 : List Nat := [3, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_5142266 : Nat := 118140960795 + 5142266 * 2 ^ 59
def prefixEnd_5142266 : Nat := 4983230072969 + 3 ^ 40 * 5142266 * 2
def baseEnd_5142266 : Nat := 2640454111273083094326155

theorem tailTrace_5142266 : CollatzResearch.WordTrace tailWord_5142266 prefixEnd_5142266 2640454111273083094326155 := by
  unfold tailWord_5142266
  simp only [CollatzResearch.WordTrace]
  refine ⟨46888462297113996489629663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125035899458970657305679101 46888462297113996489629663)
  ·
    refine ⟨70332693445670994734444495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46888462297113996489629663 70332693445670994734444495)
    ·
      refine ⟨105499040168506492101666743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70332693445670994734444495 105499040168506492101666743)
      ·
        refine ⟨158248560252759738152500115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105499040168506492101666743 158248560252759738152500115)
        ·
          refine ⟨237372840379139607228750173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158248560252759738152500115 237372840379139607228750173)
          ·
            refine ⟨89014815142177352710781315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 237372840379139607228750173 89014815142177352710781315)
            ·
              refine ⟨133522222713266029066171973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89014815142177352710781315 133522222713266029066171973)
              ·
                refine ⟨25035416758737380449907245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133522222713266029066171973 25035416758737380449907245)
                ·
                  refine ⟨9388281284526517668715217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25035416758737380449907245 9388281284526517668715217)
                  ·
                    refine ⟨7041210963394888251536413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9388281284526517668715217 7041210963394888251536413)
                    ·
                      refine ⟨2640454111273083094326155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041210963394888251536413 2640454111273083094326155)
                      ·
                        rfl

theorem cell23_5142266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_5142266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142266 prefixEnd_5142266 := by exact prefixLift 5142266
  have htrace : WordTrace (prefixWord ++ tailWord_5142266) baseStart_5142266 baseEnd_5142266 := by
    simpa [prefixWord, tailWord_5142266, baseEnd_5142266] using wordTrace_append hprefix tailTrace_5142266
  have hstable : (prefixWord ++ tailWord_5142266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142266).length < 2 ^ (prefixWord ++ tailWord_5142266).sum := by decide
  have hdescent : baseEnd_5142266 < baseStart_5142266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142276 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_5142276 : Nat := 118140960795 + 5142276 * 2 ^ 59
def prefixEnd_5142276 : Nat := 4983230072969 + 3 ^ 40 * 5142276 * 2
def baseEnd_5142276 : Nat := 2640459246079628055201109

theorem tailTrace_5142276 : CollatzResearch.WordTrace tailWord_5142276 prefixEnd_5142276 2640459246079628055201109 := by
  unfold tailWord_5142276
  simp only [CollatzResearch.WordTrace]
  refine ⟨93777106959209878833191341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125036142612279838444255121 93777106959209878833191341)
  ·
    refine ⟨35166415109703704562446753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93777106959209878833191341 35166415109703704562446753)
    ·
      refine ⟨26374811332277778421835065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35166415109703704562446753 26374811332277778421835065)
      ·
        refine ⟨19781108499208333816376299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26374811332277778421835065 19781108499208333816376299)
        ·
          refine ⟨29671662748812500724564449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19781108499208333816376299 29671662748812500724564449)
          ·
            refine ⟨22253747061609375543423337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29671662748812500724564449 22253747061609375543423337)
            ·
              refine ⟨16690310296207031657567503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22253747061609375543423337 16690310296207031657567503)
              ·
                refine ⟨25035465444310547486351255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16690310296207031657567503 25035465444310547486351255)
                ·
                  refine ⟨37553198166465821229526883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25035465444310547486351255 37553198166465821229526883)
                  ·
                    refine ⟨56329797249698731844290325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37553198166465821229526883 56329797249698731844290325)
                    ·
                      refine ⟨2640459246079628055201109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56329797249698731844290325 2640459246079628055201109)
                      ·
                        rfl

theorem cell23_5142276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_5142276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142276 prefixEnd_5142276 := by exact prefixLift 5142276
  have htrace : WordTrace (prefixWord ++ tailWord_5142276) baseStart_5142276 baseEnd_5142276 := by
    simpa [prefixWord, tailWord_5142276, baseEnd_5142276] using wordTrace_append hprefix tailTrace_5142276
  have hstable : (prefixWord ++ tailWord_5142276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142276).length < 2 ^ (prefixWord ++ tailWord_5142276).sum := by decide
  have hdescent : baseEnd_5142276 < baseStart_5142276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142283 : List Nat := [1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 3]
def baseStart_5142283 : Nat := 118140960795 + 5142283 * 2 ^ 59
def prefixEnd_5142283 : Nat := 4983230072969 + 3 ^ 40 * 5142283 * 2
def baseEnd_5142283 : Nat := 2640462840444209527813577

theorem tailTrace_5142283 : CollatzResearch.WordTrace tailWord_5142283 prefixEnd_5142283 2640462840444209527813577 := by
  unfold tailWord_5142283
  simp only [CollatzResearch.WordTrace]
  refine ⟨187554469229394397861887503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125036312819596265241258335 187554469229394397861887503)
  ·
    refine ⟨281331703844091596792831255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187554469229394397861887503 281331703844091596792831255)
    ·
      refine ⟨421997555766137395189246883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281331703844091596792831255 421997555766137395189246883)
      ·
        refine ⟨632996333649206092783870325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421997555766137395189246883 632996333649206092783870325)
        ·
          refine ⟨59343406279613071198487843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 632996333649206092783870325 59343406279613071198487843)
          ·
            refine ⟨89015109419419606797731765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59343406279613071198487843 89015109419419606797731765)
            ·
              refine ⟨8345166508070588137287353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 89015109419419606797731765 8345166508070588137287353)
              ·
                refine ⟨6258874881052941102965515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8345166508070588137287353 6258874881052941102965515)
                ·
                  refine ⟨9388312321579411654448273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258874881052941102965515 9388312321579411654448273)
                  ·
                    refine ⟨7041234241184558740836205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9388312321579411654448273 7041234241184558740836205)
                    ·
                      refine ⟨2640462840444209527813577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041234241184558740836205 2640462840444209527813577)
                      ·
                        rfl

theorem cell23_5142283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 2, 3].length) (baseStart_5142283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142283 prefixEnd_5142283 := by exact prefixLift 5142283
  have htrace : WordTrace (prefixWord ++ tailWord_5142283) baseStart_5142283 baseEnd_5142283 := by
    simpa [prefixWord, tailWord_5142283, baseEnd_5142283] using wordTrace_append hprefix tailTrace_5142283
  have hstable : (prefixWord ++ tailWord_5142283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142283).length < 2 ^ (prefixWord ++ tailWord_5142283).sum := by decide
  have hdescent : baseEnd_5142283 < baseStart_5142283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142296 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3]
def baseStart_5142296 : Nat := 118140960795 + 5142296 * 2 ^ 59
def prefixEnd_5142296 : Nat := 4983230072969 + 3 ^ 40 * 5142296 * 2
def baseEnd_5142296 : Nat := 2640469515692717976951017

theorem tailTrace_5142296 : CollatzResearch.WordTrace tailWord_5142296 prefixEnd_5142296 2640469515692717976951017 := by
  unfold tailWord_5142296
  simp only [CollatzResearch.WordTrace]
  refine ⟨93777471689173650541055371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125036628918898200721407161 93777471689173650541055371)
  ·
    refine ⟨140666207533760475811583057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93777471689173650541055371 140666207533760475811583057)
    ·
      refine ⟨105499655650320356858687293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140666207533760475811583057 105499655650320356858687293)
      ·
        refine ⟨39562370868870133822007735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105499655650320356858687293 39562370868870133822007735)
        ·
          refine ⟨59343556303305200733011603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39562370868870133822007735 59343556303305200733011603)
          ·
            refine ⟨89015334454957801099517405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59343556303305200733011603 89015334454957801099517405)
            ·
              refine ⟨33380750420609175412319027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89015334454957801099517405 33380750420609175412319027)
              ·
                refine ⟨50071125630913763118478541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33380750420609175412319027 50071125630913763118478541)
                ·
                  refine ⟨18776672111592661169429453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50071125630913763118478541 18776672111592661169429453)
                  ·
                    refine ⟨7041252041847247938536045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18776672111592661169429453 7041252041847247938536045)
                    ·
                      refine ⟨2640469515692717976951017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041252041847247938536045 2640469515692717976951017)
                      ·
                        rfl

theorem cell23_5142296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_5142296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142296 prefixEnd_5142296 := by exact prefixLift 5142296
  have htrace : WordTrace (prefixWord ++ tailWord_5142296) baseStart_5142296 baseEnd_5142296 := by
    simpa [prefixWord, tailWord_5142296, baseEnd_5142296] using wordTrace_append hprefix tailTrace_5142296
  have hstable : (prefixWord ++ tailWord_5142296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142296).length < 2 ^ (prefixWord ++ tailWord_5142296).sum := by decide
  have hdescent : baseEnd_5142296 < baseStart_5142296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142300 : List Nat := [2, 2, 3, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_5142300 : Nat := 118140960795 + 5142300 * 2 ^ 59
def prefixEnd_5142300 : Nat := 4983230072969 + 3 ^ 40 * 5142300 * 2
def baseEnd_5142300 : Nat := 2640471569615335961300999

theorem tailTrace_5142300 : CollatzResearch.WordTrace tailWord_5142300 prefixEnd_5142300 2640471569615335961300999 := by
  unfold tailWord_5142300
  simp only [CollatzResearch.WordTrace]
  refine ⟨93777544635166404882628177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125036726180221873176837569 93777544635166404882628177)
  ·
    refine ⟨70333158476374803661971133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93777544635166404882628177 70333158476374803661971133)
    ·
      refine ⟨26374934428640551373239175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70333158476374803661971133 26374934428640551373239175)
      ·
        refine ⟨39562401642960827059858763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26374934428640551373239175 39562401642960827059858763)
        ·
          refine ⟨59343602464441240589788145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39562401642960827059858763 59343602464441240589788145)
          ·
            refine ⟨44507701848330930442341109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59343602464441240589788145 44507701848330930442341109)
            ·
              refine ⟨4172597048281024728969479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44507701848330930442341109 4172597048281024728969479)
              ·
                refine ⟨6258895572421537093454219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172597048281024728969479 6258895572421537093454219)
                ·
                  refine ⟨9388343358632305640181329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258895572421537093454219 9388343358632305640181329)
                  ·
                    refine ⟨7041257518974229230135997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9388343358632305640181329 7041257518974229230135997)
                    ·
                      refine ⟨2640471569615335961300999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041257518974229230135997 2640471569615335961300999)
                      ·
                        rfl

theorem cell23_5142300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_5142300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142300 prefixEnd_5142300 := by exact prefixLift 5142300
  have htrace : WordTrace (prefixWord ++ tailWord_5142300) baseStart_5142300 baseEnd_5142300 := by
    simpa [prefixWord, tailWord_5142300, baseEnd_5142300] using wordTrace_append hprefix tailTrace_5142300
  have hstable : (prefixWord ++ tailWord_5142300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142300).length < 2 ^ (prefixWord ++ tailWord_5142300).sum := by decide
  have hdescent : baseEnd_5142300 < baseStart_5142300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142330 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_5142330 : Nat := 118140960795 + 5142330 * 2 ^ 59
def prefixEnd_5142330 : Nat := 4983230072969 + 3 ^ 40 * 5142330 * 2
def baseEnd_5142330 : Nat := 2640486974034970843925861

theorem tailTrace_5142330 : CollatzResearch.WordTrace tailWord_5142330 prefixEnd_5142330 2640486974034970843925861 := by
  unfold tailWord_5142330
  simp only [CollatzResearch.WordTrace]
  refine ⟨46889045865056031222212111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125037455640149416592565629 46889045865056031222212111)
  ·
    refine ⟨70333568797584046833318167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46889045865056031222212111 70333568797584046833318167)
    ·
      refine ⟨105500353196376070249977251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70333568797584046833318167 105500353196376070249977251)
      ·
        refine ⟨158250529794564105374965877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105500353196376070249977251 158250529794564105374965877)
        ·
          refine ⟨14835987168240384878903051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 158250529794564105374965877 14835987168240384878903051)
          ·
            refine ⟨22253980752360577318354577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14835987168240384878903051 22253980752360577318354577)
            ·
              refine ⟨16690485564270432988765933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22253980752360577318354577 16690485564270432988765933)
              ·
                refine ⟨6258932086601412370787225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16690485564270432988765933 6258932086601412370787225)
                ·
                  refine ⟨4694199064951059278090419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258932086601412370787225 4694199064951059278090419)
                  ·
                    refine ⟨7041298597426588917135629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694199064951059278090419 7041298597426588917135629)
                    ·
                      refine ⟨2640486974034970843925861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041298597426588917135629 2640486974034970843925861)
                      ·
                        rfl

theorem cell23_5142330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_5142330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142330 prefixEnd_5142330 := by exact prefixLift 5142330
  have htrace : WordTrace (prefixWord ++ tailWord_5142330) baseStart_5142330 baseEnd_5142330 := by
    simpa [prefixWord, tailWord_5142330, baseEnd_5142330] using wordTrace_append hprefix tailTrace_5142330
  have hstable : (prefixWord ++ tailWord_5142330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142330).length < 2 ^ (prefixWord ++ tailWord_5142330).sum := by decide
  have hdescent : baseEnd_5142330 < baseStart_5142330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142357 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_5142357 : Nat := 118140960795 + 5142357 * 2 ^ 59
def prefixEnd_5142357 : Nat := 4983230072969 + 3 ^ 40 * 5142357 * 2
def baseEnd_5142357 : Nat := 2640500838012642238288237

theorem tailTrace_5142357 : CollatzResearch.WordTrace tailWord_5142357 prefixEnd_5142357 2640500838012642238288237 := by
  unfold tailWord_5142357
  simp only [CollatzResearch.WordTrace]
  refine ⟨187557168231126308500081325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125038112154084205666720883 187557168231126308500081325)
  ·
    refine ⟨70333938086672365687530497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187557168231126308500081325 70333938086672365687530497)
    ·
      refine ⟨52750453565004274265647873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70333938086672365687530497 52750453565004274265647873)
      ·
        refine ⟨39562840173753205699235905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52750453565004274265647873 39562840173753205699235905)
        ·
          refine ⟨29672130130314904274426929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39562840173753205699235905 29672130130314904274426929)
          ·
            refine ⟨22254097597736178205820197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29672130130314904274426929 22254097597736178205820197)
            ·
              refine ⟨4172643299575533413591287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22254097597736178205820197 4172643299575533413591287)
              ·
                refine ⟨6258964949363300120386931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172643299575533413591287 6258964949363300120386931)
                ·
                  refine ⟨9388447424044950180580397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6258964949363300120386931 9388447424044950180580397)
                  ·
                    refine ⟨3520667784016856317717649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9388447424044950180580397 3520667784016856317717649)
                    ·
                      refine ⟨2640500838012642238288237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520667784016856317717649 2640500838012642238288237)
                      ·
                        rfl

theorem cell23_5142357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_5142357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142357 prefixEnd_5142357 := by exact prefixLift 5142357
  have htrace : WordTrace (prefixWord ++ tailWord_5142357) baseStart_5142357 baseEnd_5142357 := by
    simpa [prefixWord, tailWord_5142357, baseEnd_5142357] using wordTrace_append hprefix tailTrace_5142357
  have hstable : (prefixWord ++ tailWord_5142357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142357).length < 2 ^ (prefixWord ++ tailWord_5142357).sum := by decide
  have hdescent : baseEnd_5142357 < baseStart_5142357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142364 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_5142364 : Nat := 118140960795 + 5142364 * 2 ^ 59
def prefixEnd_5142364 : Nat := 4983230072969 + 3 ^ 40 * 5142364 * 2
def baseEnd_5142364 : Nat := 2640504432377223710900705

theorem tailTrace_5142364 : CollatzResearch.WordTrace tailWord_5142364 prefixEnd_5142364 2640504432377223710900705 := by
  unfold tailWord_5142364
  simp only [CollatzResearch.WordTrace]
  refine ⟨93778711771050474347793073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125038282361400632463724097 93778711771050474347793073)
  ·
    refine ⟨70334033828287855760844805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93778711771050474347793073 70334033828287855760844805)
    ·
      refine ⟨13187631342803972955158401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70334033828287855760844805 13187631342803972955158401)
      ·
        refine ⟨9890723507102979716368801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13187631342803972955158401 9890723507102979716368801)
        ·
          refine ⟨7418042630327234787276601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9890723507102979716368801 7418042630327234787276601)
          ·
            refine ⟨5563531972745426090457451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418042630327234787276601 5563531972745426090457451)
            ·
              refine ⟨8345297959118139135686177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563531972745426090457451 8345297959118139135686177)
              ·
                refine ⟨6258973469338604351764633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8345297959118139135686177 6258973469338604351764633)
                ·
                  refine ⟨4694230102003953263823475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6258973469338604351764633 4694230102003953263823475)
                  ·
                    refine ⟨7041345153005929895735213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694230102003953263823475 7041345153005929895735213)
                    ·
                      refine ⟨2640504432377223710900705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041345153005929895735213 2640504432377223710900705)
                      ·
                        rfl

theorem cell23_5142364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_5142364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142364 prefixEnd_5142364 := by exact prefixLift 5142364
  have htrace : WordTrace (prefixWord ++ tailWord_5142364) baseStart_5142364 baseEnd_5142364 := by
    simpa [prefixWord, tailWord_5142364, baseEnd_5142364] using wordTrace_append hprefix tailTrace_5142364
  have hstable : (prefixWord ++ tailWord_5142364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142364).length < 2 ^ (prefixWord ++ tailWord_5142364).sum := by decide
  have hdescent : baseEnd_5142364 < baseStart_5142364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142423 : List Nat := [1, 1, 3, 3, 1, 4, 1, 2, 2, 5]
def baseStart_5142423 : Nat := 118140960795 + 5142423 * 2 ^ 59
def prefixEnd_5142423 : Nat := 4983230072969 + 3 ^ 40 * 5142423 * 2
def baseEnd_5142423 : Nat := 880178242578612993354311

theorem tailTrace_5142423 : CollatzResearch.WordTrace tailWord_5142423 prefixEnd_5142423 880178242578612993354311 := by
  unfold tailWord_5142423
  simp only [CollatzResearch.WordTrace]
  refine ⟨187559575448887201771983923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125039716965924801181322615 187559575448887201771983923)
  ·
    refine ⟨281339363173330802657975885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187559575448887201771983923 281339363173330802657975885)
    ·
      refine ⟨105502261189999050996740957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281339363173330802657975885 105502261189999050996740957)
      ·
        refine ⟨39563347946249644123777859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 105502261189999050996740957 39563347946249644123777859)
        ·
          refine ⟨59345021919374466185666789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39563347946249644123777859 59345021919374466185666789)
          ·
            refine ⟨11127191609882712409812523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 59345021919374466185666789 11127191609882712409812523)
            ·
              refine ⟨16690787414824068614718785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11127191609882712409812523 16690787414824068614718785)
              ·
                refine ⟨12518090561118051461039089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16690787414824068614718785 12518090561118051461039089)
                ·
                  refine ⟨9388567920838538595779317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12518090561118051461039089 9388567920838538595779317)
                  ·
                    refine ⟨880178242578612993354311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9388567920838538595779317 880178242578612993354311)
                    ·
                      rfl

theorem cell23_5142423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_5142423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142423 prefixEnd_5142423 := by exact prefixLift 5142423
  have htrace : WordTrace (prefixWord ++ tailWord_5142423) baseStart_5142423 baseEnd_5142423 := by
    simpa [prefixWord, tailWord_5142423, baseEnd_5142423] using wordTrace_append hprefix tailTrace_5142423
  have hstable : (prefixWord ++ tailWord_5142423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142423).length < 2 ^ (prefixWord ++ tailWord_5142423).sum := by decide
  have hdescent : baseEnd_5142423 < baseStart_5142423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142563 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6]
def baseStart_5142563 : Nat := 118140960795 + 5142563 * 2 ^ 59
def prefixEnd_5142563 : Nat := 4983230072969 + 3 ^ 40 * 5142563 * 2
def baseEnd_5142563 : Nat := 2640606615027468432312289

theorem tailTrace_5142563 : CollatzResearch.WordTrace tailWord_5142563 prefixEnd_5142563 2640606615027468432312289 := by
  unfold tailWord_5142563
  simp only [CollatzResearch.WordTrace]
  refine ⟨187564681668380005682080343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125043121112253337121386895 187564681668380005682080343)
  ·
    refine ⟨281347022502570008523120515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187564681668380005682080343 281347022502570008523120515)
    ·
      refine ⟨422020533753855012784680773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 281347022502570008523120515 422020533753855012784680773)
      ·
        refine ⟨79128850078847814897127645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 422020533753855012784680773 79128850078847814897127645)
        ·
          refine ⟨29673318779567930586422867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79128850078847814897127645 29673318779567930586422867)
          ·
            refine ⟨44509978169351895879634301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29673318779567930586422867 44509978169351895879634301)
            ·
              refine ⟨16691241813506960954862863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44509978169351895879634301 16691241813506960954862863)
              ·
                refine ⟨25036862720260441432294295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16691241813506960954862863 25036862720260441432294295)
                ·
                  refine ⟨37555294080390662148441443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25036862720260441432294295 37555294080390662148441443)
                  ·
                    refine ⟨56332941120585993222662165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37555294080390662148441443 56332941120585993222662165)
                    ·
                      refine ⟨2640606615027468432312289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 56332941120585993222662165 2640606615027468432312289)
                      ·
                        rfl

theorem cell23_5142563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_5142563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142563 prefixEnd_5142563 := by exact prefixLift 5142563
  have htrace : WordTrace (prefixWord ++ tailWord_5142563) baseStart_5142563 baseEnd_5142563 := by
    simpa [prefixWord, tailWord_5142563, baseEnd_5142563] using wordTrace_append hprefix tailTrace_5142563
  have hstable : (prefixWord ++ tailWord_5142563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142563).length < 2 ^ (prefixWord ++ tailWord_5142563).sum := by decide
  have hdescent : baseEnd_5142563 < baseStart_5142563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142601 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 1, 2, 2]
def baseStart_5142601 : Nat := 118140960795 + 5142601 * 2 ^ 59
def prefixEnd_5142601 : Nat := 4983230072969 + 3 ^ 40 * 5142601 * 2
def baseEnd_5142601 : Nat := 2640626127292339283637115

theorem tailTrace_5142601 : CollatzResearch.WordTrace tailWord_5142601 prefixEnd_5142601 2640626127292339283637115 := by
  unfold tailWord_5142601
  simp only [CollatzResearch.WordTrace]
  refine ⟨187566067642242338171963657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125044045094828225447975771 187566067642242338171963657)
  ·
    refine ⟨140674550731681753628972743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187566067642242338171963657 140674550731681753628972743)
    ·
      refine ⟨211011826097522630443459115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140674550731681753628972743 211011826097522630443459115)
      ·
        refine ⟨316517739146283945665188673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211011826097522630443459115 316517739146283945665188673)
        ·
          refine ⟨237388304359712959248891505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316517739146283945665188673 237388304359712959248891505)
          ·
            refine ⟨178041228269784719436668629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237388304359712959248891505 178041228269784719436668629)
            ·
              refine ⟨4172841287573079361796921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 178041228269784719436668629 4172841287573079361796921)
              ·
                refine ⟨3129630965679809521347691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4172841287573079361796921 3129630965679809521347691)
                ·
                  refine ⟨4694446448519714282021537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3129630965679809521347691 4694446448519714282021537)
                  ·
                    refine ⟨3520834836389785711516153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4694446448519714282021537 3520834836389785711516153)
                    ·
                      refine ⟨2640626127292339283637115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520834836389785711516153 2640626127292339283637115)
                      ·
                        rfl

theorem cell23_5142601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 2, 2].length) (baseStart_5142601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142601 prefixEnd_5142601 := by exact prefixLift 5142601
  have htrace : WordTrace (prefixWord ++ tailWord_5142601) baseStart_5142601 baseEnd_5142601 := by
    simpa [prefixWord, tailWord_5142601, baseEnd_5142601] using wordTrace_append hprefix tailTrace_5142601
  have hstable : (prefixWord ++ tailWord_5142601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142601).length < 2 ^ (prefixWord ++ tailWord_5142601).sum := by decide
  have hdescent : baseEnd_5142601 < baseStart_5142601 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142617 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_5142617 : Nat := 118140960795 + 5142617 * 2 ^ 59
def prefixEnd_5142617 : Nat := 4983230072969 + 3 ^ 40 * 5142617 * 2
def baseEnd_5142617 : Nat := 2640634342982811221037041

theorem tailTrace_5142617 : CollatzResearch.WordTrace tailWord_5142617 prefixEnd_5142617 2640634342982811221037041 := by
  unfold tailWord_5142617
  simp only [CollatzResearch.WordTrace]
  refine ⟨187566651210184372904546105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125044434140122915269697403 187566651210184372904546105)
  ·
    refine ⟨140674988407638279678409579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187566651210184372904546105 140674988407638279678409579)
    ·
      refine ⟨211012482611457419517614369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140674988407638279678409579 211012482611457419517614369)
      ·
        refine ⟨158259361958593064638210777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 211012482611457419517614369 158259361958593064638210777)
        ·
          refine ⟨118694521468944798478658083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158259361958593064638210777 118694521468944798478658083)
          ·
            refine ⟨178041782203417197717987125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118694521468944798478658083 178041782203417197717987125)
            ·
              refine ⟨16691417081570362286061293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 178041782203417197717987125 16691417081570362286061293)
              ·
                refine ⟨6259281405588885857272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16691417081570362286061293 6259281405588885857272985)
                ·
                  refine ⟨4694461054191664392954739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6259281405588885857272985 4694461054191664392954739)
                  ·
                    refine ⟨7041691581287496589432109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4694461054191664392954739 7041691581287496589432109)
                    ·
                      refine ⟨2640634342982811221037041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041691581287496589432109 2640634342982811221037041)
                      ·
                        rfl

theorem cell23_5142617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_5142617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142617 prefixEnd_5142617 := by exact prefixLift 5142617
  have htrace : WordTrace (prefixWord ++ tailWord_5142617) baseStart_5142617 baseEnd_5142617 := by
    simpa [prefixWord, tailWord_5142617, baseEnd_5142617] using wordTrace_append hprefix tailTrace_5142617
  have hstable : (prefixWord ++ tailWord_5142617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142617).length < 2 ^ (prefixWord ++ tailWord_5142617).sum := by decide
  have hdescent : baseEnd_5142617 < baseStart_5142617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142621 : List Nat := [1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_5142621 : Nat := 118140960795 + 5142621 * 2 ^ 59
def prefixEnd_5142621 : Nat := 4983230072969 + 3 ^ 40 * 5142621 * 2
def baseEnd_5142621 : Nat := 2640636396905429205387023

theorem tailTrace_5142621 : CollatzResearch.WordTrace tailWord_5142621 prefixEnd_5142621 2640636396905429205387023 := by
  unfold tailWord_5142621
  simp only [CollatzResearch.WordTrace]
  refine ⟨187566797102169881587691717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125044531401446587725127811 187566797102169881587691717)
  ·
    refine ⟨35168774456656852797692197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 187566797102169881587691717 35168774456656852797692197)
    ·
      refine ⟨6594145210623159899567287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35168774456656852797692197 6594145210623159899567287)
      ·
        refine ⟨9891217815934739849350931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594145210623159899567287 9891217815934739849350931)
        ·
          refine ⟨14836826723902109774026397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9891217815934739849350931 14836826723902109774026397)
          ·
            refine ⟨5563810021463291165259899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14836826723902109774026397 5563810021463291165259899)
            ·
              refine ⟨8345715032194936747889849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563810021463291165259899 8345715032194936747889849)
              ·
                refine ⟨6259286274146202560917387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8345715032194936747889849 6259286274146202560917387)
                ·
                  refine ⟨9388929411219303841376081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259286274146202560917387 9388929411219303841376081)
                  ·
                    refine ⟨7041697058414477881032061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9388929411219303841376081 7041697058414477881032061)
                    ·
                      refine ⟨2640636396905429205387023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041697058414477881032061 2640636396905429205387023)
                      ·
                        rfl

theorem cell23_5142621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_5142621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142621 prefixEnd_5142621 := by exact prefixLift 5142621
  have htrace : WordTrace (prefixWord ++ tailWord_5142621) baseStart_5142621 baseEnd_5142621 := by
    simpa [prefixWord, tailWord_5142621, baseEnd_5142621] using wordTrace_append hprefix tailTrace_5142621
  have hstable : (prefixWord ++ tailWord_5142621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142621).length < 2 ^ (prefixWord ++ tailWord_5142621).sum := by decide
  have hdescent : baseEnd_5142621 < baseStart_5142621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142623 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4]
def baseStart_5142623 : Nat := 118140960795 + 5142623 * 2 ^ 59
def prefixEnd_5142623 : Nat := 4983230072969 + 3 ^ 40 * 5142623 * 2
def baseEnd_5142623 : Nat := 2640637423866738197562013

theorem tailTrace_5142623 : CollatzResearch.WordTrace tailWord_5142623 prefixEnd_5142623 2640637423866738197562013 := by
  unfold tailWord_5142623
  simp only [CollatzResearch.WordTrace]
  refine ⟨187566870048162635929264523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125044580032108423952843015 187566870048162635929264523)
  ·
    refine ⟨281350305072243953893896785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187566870048162635929264523 281350305072243953893896785)
    ·
      refine ⟨211012728804182965420422589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281350305072243953893896785 211012728804182965420422589)
      ·
        refine ⟨79129773301568612032658471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 211012728804182965420422589 79129773301568612032658471)
        ·
          refine ⟨118694659952352918048987707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79129773301568612032658471 118694659952352918048987707)
          ·
            refine ⟨178041989928529377073481561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118694659952352918048987707 178041989928529377073481561)
            ·
              refine ⟨133531492446397032805111171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178041989928529377073481561 133531492446397032805111171)
              ·
                refine ⟨200297238669595549207666757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133531492446397032805111171 200297238669595549207666757)
                ·
                  refine ⟨37555732250549165476437517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200297238669595549207666757 37555732250549165476437517)
                  ·
                    refine ⟨14083399593955937053664069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37555732250549165476437517 14083399593955937053664069)
                    ·
                      refine ⟨2640637423866738197562013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14083399593955937053664069 2640637423866738197562013)
                      ·
                        rfl

theorem cell23_5142623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_5142623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142623 prefixEnd_5142623 := by exact prefixLift 5142623
  have htrace : WordTrace (prefixWord ++ tailWord_5142623) baseStart_5142623 baseEnd_5142623 := by
    simpa [prefixWord, tailWord_5142623, baseEnd_5142623] using wordTrace_append hprefix tailTrace_5142623
  have hstable : (prefixWord ++ tailWord_5142623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142623).length < 2 ^ (prefixWord ++ tailWord_5142623).sum := by decide
  have hdescent : baseEnd_5142623 < baseStart_5142623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142660 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_5142660 : Nat := 118140960795 + 5142660 * 2 ^ 59
def prefixEnd_5142660 : Nat := 4983230072969 + 3 ^ 40 * 5142660 * 2
def baseEnd_5142660 : Nat := 2640656422650954552799343

theorem tailTrace_5142660 : CollatzResearch.WordTrace tailWord_5142660 prefixEnd_5142660 2640656422650954552799343 := by
  unfold tailWord_5142660
  simp only [CollatzResearch.WordTrace]
  refine ⟨93784109774514295624180717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125045479699352394165574289 93784109774514295624180717)
  ·
    refine ⟨35169041165442860859067769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 93784109774514295624180717 35169041165442860859067769)
    ·
      refine ⟨26376780874082145644300827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35169041165442860859067769 26376780874082145644300827)
      ·
        refine ⟨39565171311123218466451241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26376780874082145644300827 39565171311123218466451241)
        ·
          refine ⟨29673878483342413849838431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39565171311123218466451241 29673878483342413849838431)
          ·
            refine ⟨44510817725013620774757647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29673878483342413849838431 44510817725013620774757647)
            ·
              refine ⟨66766226587520431162136471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44510817725013620774757647 66766226587520431162136471)
              ·
                refine ⟨100149339881280646743204707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66766226587520431162136471 100149339881280646743204707)
                ·
                  refine ⟨150224009821920970114807061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100149339881280646743204707 150224009821920970114807061)
                  ·
                    refine ⟨7041750460402545474131581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 150224009821920970114807061 7041750460402545474131581)
                    ·
                      refine ⟨2640656422650954552799343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041750460402545474131581 2640656422650954552799343)
                      ·
                        rfl

theorem cell23_5142660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_5142660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142660 prefixEnd_5142660 := by exact prefixLift 5142660
  have htrace : WordTrace (prefixWord ++ tailWord_5142660) baseStart_5142660 baseEnd_5142660 := by
    simpa [prefixWord, tailWord_5142660, baseEnd_5142660] using wordTrace_append hprefix tailTrace_5142660
  have hstable : (prefixWord ++ tailWord_5142660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142660).length < 2 ^ (prefixWord ++ tailWord_5142660).sum := by decide
  have hdescent : baseEnd_5142660 < baseStart_5142660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142674 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_5142674 : Nat := 118140960795 + 5142674 * 2 ^ 59
def prefixEnd_5142674 : Nat := 4983230072969 + 3 ^ 40 * 5142674 * 2
def baseEnd_5142674 : Nat := 2640663611380117498024279

theorem tailTrace_5142674 : CollatzResearch.WordTrace tailWord_5142674 prefixEnd_5142674 2640663611380117498024279 := by
  unfold tailWord_5142674
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892182542744467909842769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125045820113985247759580717 46892182542744467909842769)
  ·
    refine ⟨35169136907058350932382077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46892182542744467909842769 35169136907058350932382077)
    ·
      refine ⟨13188426340146881599643279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35169136907058350932382077 13188426340146881599643279)
      ·
        refine ⟨19782639510220322399464919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13188426340146881599643279 19782639510220322399464919)
        ·
          refine ⟨29673959265330483599197379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19782639510220322399464919 29673959265330483599197379)
          ·
            refine ⟨44510938897995725398796069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29673959265330483599197379 44510938897995725398796069)
            ·
              refine ⟨8345801043374198512274263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44510938897995725398796069 8345801043374198512274263)
              ·
                refine ⟨12518701565061297768411395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8345801043374198512274263 12518701565061297768411395)
                ·
                  refine ⟨18778052347591946652617093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12518701565061297768411395 18778052347591946652617093)
                  ·
                    refine ⟨3520884815173489997365705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18778052347591946652617093 3520884815173489997365705)
                    ·
                      refine ⟨2640663611380117498024279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520884815173489997365705 2640663611380117498024279)
                      ·
                        rfl

theorem cell23_5142674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_5142674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142674 prefixEnd_5142674 := by exact prefixLift 5142674
  have htrace : WordTrace (prefixWord ++ tailWord_5142674) baseStart_5142674 baseEnd_5142674 := by
    simpa [prefixWord, tailWord_5142674, baseEnd_5142674] using wordTrace_append hprefix tailTrace_5142674
  have hstable : (prefixWord ++ tailWord_5142674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142674).length < 2 ^ (prefixWord ++ tailWord_5142674).sum := by decide
  have hdescent : baseEnd_5142674 < baseStart_5142674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142695 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_5142695 : Nat := 118140960795 + 5142695 * 2 ^ 59
def prefixEnd_5142695 : Nat := 4983230072969 + 3 ^ 40 * 5142695 * 2
def baseEnd_5142695 : Nat := 2640674394473861915861683

theorem tailTrace_5142695 : CollatzResearch.WordTrace tailWord_5142695 prefixEnd_5142695 2640674394473861915861683 := by
  unfold tailWord_5142695
  simp only [CollatzResearch.WordTrace]
  refine ⟨187569496103901792225885539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125046330735934528150590359 187569496103901792225885539)
  ·
    refine ⟨281354244155852688338828309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187569496103901792225885539 281354244155852688338828309)
    ·
      refine ⟨13188480194805594765882577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 281354244155852688338828309 13188480194805594765882577)
      ·
        refine ⟨9891360146104196074411933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13188480194805594765882577 9891360146104196074411933)
        ·
          refine ⟨3709260054789073527904475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9891360146104196074411933 3709260054789073527904475)
          ·
            refine ⟨5563890082183610291856713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3709260054789073527904475 5563890082183610291856713)
            ·
              refine ⟨4172917561637707718892535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5563890082183610291856713 4172917561637707718892535)
              ·
                refine ⟨6259376342456561578338803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4172917561637707718892535 6259376342456561578338803)
                ·
                  refine ⟨9389064513684842367508205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6259376342456561578338803 9389064513684842367508205)
                  ·
                    refine ⟨3520899192631815887815577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9389064513684842367508205 3520899192631815887815577)
                    ·
                      refine ⟨2640674394473861915861683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3520899192631815887815577 2640674394473861915861683)
                      ·
                        rfl

theorem cell23_5142695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_5142695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142695 prefixEnd_5142695 := by exact prefixLift 5142695
  have htrace : WordTrace (prefixWord ++ tailWord_5142695) baseStart_5142695 baseEnd_5142695 := by
    simpa [prefixWord, tailWord_5142695, baseEnd_5142695] using wordTrace_append hprefix tailTrace_5142695
  have hstable : (prefixWord ++ tailWord_5142695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142695).length < 2 ^ (prefixWord ++ tailWord_5142695).sum := by decide
  have hdescent : baseEnd_5142695 < baseStart_5142695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142730 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_5142730 : Nat := 118140960795 + 5142730 * 2 ^ 59
def prefixEnd_5142730 : Nat := 4983230072969 + 3 ^ 40 * 5142730 * 2
def baseEnd_5142730 : Nat := 2640692366296769278924021

theorem tailTrace_5142730 : CollatzResearch.WordTrace tailWord_5142730 prefixEnd_5142730 2640692366296769278924021 := by
  unfold tailWord_5142730
  simp only [CollatzResearch.WordTrace]
  refine ⟨46892693164693748300852411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 125047181772516662135606429 46892693164693748300852411)
  ·
    refine ⟨70339039747040622451278617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46892693164693748300852411 70339039747040622451278617)
    ·
      refine ⟨52754279810280466838458963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70339039747040622451278617 52754279810280466838458963)
      ·
        refine ⟨79131419715420700257688445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52754279810280466838458963 79131419715420700257688445)
        ·
          refine ⟨29674282393282762596633167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 79131419715420700257688445 29674282393282762596633167)
          ·
            refine ⟨44511423589924143894949751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29674282393282762596633167 44511423589924143894949751)
            ·
              refine ⟨66767135384886215842424627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44511423589924143894949751 66767135384886215842424627)
              ·
                refine ⟨100150703077329323763636941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66767135384886215842424627 100150703077329323763636941)
                ·
                  refine ⟨37556513653998496411363853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100150703077329323763636941 37556513653998496411363853)
                  ·
                    refine ⟨14083692620249436154261445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37556513653998496411363853 14083692620249436154261445)
                    ·
                      refine ⟨2640692366296769278924021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14083692620249436154261445 2640692366296769278924021)
                      ·
                        rfl

theorem cell23_5142730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_5142730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142730 prefixEnd_5142730 := by exact prefixLift 5142730
  have htrace : WordTrace (prefixWord ++ tailWord_5142730) baseStart_5142730 baseEnd_5142730 := by
    simpa [prefixWord, tailWord_5142730, baseEnd_5142730] using wordTrace_append hprefix tailTrace_5142730
  have hstable : (prefixWord ++ tailWord_5142730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142730).length < 2 ^ (prefixWord ++ tailWord_5142730).sum := by decide
  have hdescent : baseEnd_5142730 < baseStart_5142730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142748 : List Nat := [2, 2, 5, 2, 1, 2, 1, 3, 5]
def baseStart_5142748 : Nat := 118140960795 + 5142748 * 2 ^ 59
def prefixEnd_5142748 : Nat := 4983230072969 + 3 ^ 40 * 5142748 * 2
def baseEnd_5142748 : Nat := 293411289883172245388771

theorem tailTrace_5142748 : CollatzResearch.WordTrace tailWord_5142748 prefixEnd_5142748 293411289883172245388771 := by
  unfold tailWord_5142748
  simp only [CollatzResearch.WordTrace]
  refine ⟨93785714586354891138782449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 125047619448473188185043265 93785714586354891138782449)
  ·
    refine ⟨70339285939766168354086837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93785714586354891138782449 70339285939766168354086837)
    ·
      refine ⟨6594308056853078283195641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70339285939766168354086837 6594308056853078283195641)
      ·
        refine ⟨4945731042639808712396731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6594308056853078283195641 4945731042639808712396731)
        ·
          refine ⟨7418596563959713068595097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4945731042639808712396731 7418596563959713068595097)
          ·
            refine ⟨5563947422969784801446323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7418596563959713068595097 5563947422969784801446323)
            ·
              refine ⟨8345921134454677202169485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5563947422969784801446323 8345921134454677202169485)
              ·
                refine ⟨3129720425420503950813557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8345921134454677202169485 3129720425420503950813557)
                ·
                  refine ⟨293411289883172245388771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3129720425420503950813557 293411289883172245388771)
                  ·
                    rfl

theorem cell23_5142748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_5142748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142748 prefixEnd_5142748 := by exact prefixLift 5142748
  have htrace : WordTrace (prefixWord ++ tailWord_5142748) baseStart_5142748 baseEnd_5142748 := by
    simpa [prefixWord, tailWord_5142748, baseEnd_5142748] using wordTrace_append hprefix tailTrace_5142748
  have hstable : (prefixWord ++ tailWord_5142748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142748).length < 2 ^ (prefixWord ++ tailWord_5142748).sum := by decide
  have hdescent : baseEnd_5142748 < baseStart_5142748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5142767 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3]
def baseStart_5142767 : Nat := 118140960795 + 5142767 * 2 ^ 59
def prefixEnd_5142767 : Nat := 4983230072969 + 3 ^ 40 * 5142767 * 2
def baseEnd_5142767 : Nat := 2640711365080985634161351

theorem tailTrace_5142767 : CollatzResearch.WordTrace tailWord_5142767 prefixEnd_5142767 2640711365080985634161351 := by
  unfold tailWord_5142767
  simp only [CollatzResearch.WordTrace]
  refine ⟨187572122159640948522506555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 125048081439760632348337703 187572122159640948522506555)
  ·
    refine ⟨281358183239461422783759833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 187572122159640948522506555 281358183239461422783759833)
    ·
      refine ⟨211018637429596067087819875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 281358183239461422783759833 211018637429596067087819875)
      ·
        refine ⟨316527956144394100631729813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211018637429596067087819875 316527956144394100631729813)
        ·
          refine ⟨14837247944268473467112335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 316527956144394100631729813 14837247944268473467112335)
          ·
            refine ⟨22255871916402710200668503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14837247944268473467112335 22255871916402710200668503)
            ·
              refine ⟨33383807874604065301002755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22255871916402710200668503 33383807874604065301002755)
              ·
                refine ⟨50075711811906097951504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33383807874604065301002755 50075711811906097951504133)
                ·
                  refine ⟨9389195964732393365907025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50075711811906097951504133 9389195964732393365907025)
                  ·
                    refine ⟨7041896973549295024430269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9389195964732393365907025 7041896973549295024430269)
                    ·
                      refine ⟨2640711365080985634161351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7041896973549295024430269 2640711365080985634161351)
                      ·
                        rfl

theorem cell23_5142767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 3].length) (baseStart_5142767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5142767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5142767 prefixEnd_5142767 := by exact prefixLift 5142767
  have htrace : WordTrace (prefixWord ++ tailWord_5142767) baseStart_5142767 baseEnd_5142767 := by
    simpa [prefixWord, tailWord_5142767, baseEnd_5142767] using wordTrace_append hprefix tailTrace_5142767
  have hstable : (prefixWord ++ tailWord_5142767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5142767).length < 2 ^ (prefixWord ++ tailWord_5142767).sum := by decide
  have hdescent : baseEnd_5142767 < baseStart_5142767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5142767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
