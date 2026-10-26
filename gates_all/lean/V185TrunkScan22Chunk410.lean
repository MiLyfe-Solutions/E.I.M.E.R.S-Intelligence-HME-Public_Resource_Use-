import V185TrunkScan22Chunk409

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3655877 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 5]
def baseStart_3655877 : Nat := 118140960795 + 3655877 * 2 ^ 59
def prefixEnd_3655877 : Nat := 4983230072969 + 3 ^ 40 * 3655877 * 2
def baseEnd_3655877 : Nat := 417160469937177355138763

theorem tailTrace_3655877 : CollatzResearch.WordTrace tailWord_3655877 prefixEnd_3655877 417160469937177355138763 := by
  unfold tailWord_3655877
  simp only [CollatzResearch.WordTrace]
  refine ⟨133340788576389477927749885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88893859050926318618499923 133340788576389477927749885)
  ·
    refine ⟨50002795716146054222906207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133340788576389477927749885 50002795716146054222906207)
    ·
      refine ⟨75004193574219081334359311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50002795716146054222906207 75004193574219081334359311)
      ·
        refine ⟨112506290361328622001538967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75004193574219081334359311 112506290361328622001538967)
        ·
          refine ⟨168759435541992933002308451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112506290361328622001538967 168759435541992933002308451)
          ·
            refine ⟨253139153312989399503462677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168759435541992933002308451 253139153312989399503462677)
            ·
              refine ⟨11865897811546378101724813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253139153312989399503462677 11865897811546378101724813)
              ·
                refine ⟨4449711679329891788146805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11865897811546378101724813 4449711679329891788146805)
                ·
                  refine ⟨417160469937177355138763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449711679329891788146805 417160469937177355138763)
                  ·
                    rfl

theorem cell22_3655877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_3655877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655877 prefixEnd_3655877 := by exact prefixLift 3655877
  have htrace : WordTrace (prefixWord ++ tailWord_3655877) baseStart_3655877 baseEnd_3655877 := by
    simpa [prefixWord, tailWord_3655877, baseEnd_3655877] using wordTrace_append hprefix tailTrace_3655877
  have hstable : (prefixWord ++ tailWord_3655877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655877).length < 2 ^ (prefixWord ++ tailWord_3655877).sum := by decide
  have hdescent : baseEnd_3655877 < baseStart_3655877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655911 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 5]
def baseStart_3655911 : Nat := 118140960795 + 3655911 * 2 ^ 59
def prefixEnd_3655911 : Nat := 4983230072969 + 3 ^ 40 * 3655911 * 2
def baseEnd_3655911 : Nat := 417164349568789103355395

theorem tailTrace_3655911 : CollatzResearch.WordTrace tailWord_3655911 prefixEnd_3655911 417164349568789103355395 := by
  unfold tailWord_3655911
  simp only [CollatzResearch.WordTrace]
  refine ⟨133342028658266301734487587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88894685772177534489658391 133342028658266301734487587)
  ·
    refine ⟨200013042987399452601731381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133342028658266301734487587 200013042987399452601731381)
    ·
      refine ⟨18751222780068698681412317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200013042987399452601731381 18751222780068698681412317)
      ·
        refine ⟨7031708542525762005529619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18751222780068698681412317 7031708542525762005529619)
        ·
          refine ⟨10547562813788643008294429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7031708542525762005529619 10547562813788643008294429)
          ·
            refine ⟨3955336055170741128110411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10547562813788643008294429 3955336055170741128110411)
            ·
              refine ⟨5933004082756111692165617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955336055170741128110411 5933004082756111692165617)
              ·
                refine ⟨4449753062067083769124213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5933004082756111692165617 4449753062067083769124213)
                ·
                  refine ⟨417164349568789103355395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4449753062067083769124213 417164349568789103355395)
                  ·
                    rfl

theorem cell22_3655911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 5].length) (baseStart_3655911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655911 prefixEnd_3655911 := by exact prefixLift 3655911
  have htrace : WordTrace (prefixWord ++ tailWord_3655911) baseStart_3655911 baseEnd_3655911 := by
    simpa [prefixWord, tailWord_3655911, baseEnd_3655911] using wordTrace_append hprefix tailTrace_3655911
  have hstable : (prefixWord ++ tailWord_3655911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655911).length < 2 ^ (prefixWord ++ tailWord_3655911).sum := by decide
  have hdescent : baseEnd_3655911 < baseStart_3655911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655967 : List Nat := [1, 1, 2, 4, 3, 1, 10]
def baseStart_3655967 : Nat := 118140960795 + 3655967 * 2 ^ 59
def prefixEnd_3655967 : Nat := 4983230072969 + 3 ^ 40 * 3655967 * 2
def baseEnd_3655967 : Nat := 46352304394474141876519

theorem tailTrace_3655967 : CollatzResearch.WordTrace tailWord_3655967 prefixEnd_3655967 46352304394474141876519 := by
  unfold tailWord_3655967
  simp only [CollatzResearch.WordTrace]
  refine ⟨133344071146063423298526155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88896047430708948865684103 133344071146063423298526155)
  ·
    refine ⟨200016106719095134947789233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133344071146063423298526155 200016106719095134947789233)
    ·
      refine ⟨150012080039321351210841925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200016106719095134947789233 150012080039321351210841925)
      ·
        refine ⟨28127265007372753352032861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150012080039321351210841925 28127265007372753352032861)
        ·
          refine ⟨10547724377764782507012323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28127265007372753352032861 10547724377764782507012323)
          ·
            refine ⟨15821586566647173760518485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10547724377764782507012323 15821586566647173760518485)
            ·
              refine ⟨46352304394474141876519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15821586566647173760518485 46352304394474141876519)
              ·
                rfl

theorem cell22_3655967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 10].length) (baseStart_3655967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655967 prefixEnd_3655967 := by exact prefixLift 3655967
  have htrace : WordTrace (prefixWord ++ tailWord_3655967) baseStart_3655967 baseEnd_3655967 := by
    simpa [prefixWord, tailWord_3655967, baseEnd_3655967] using wordTrace_append hprefix tailTrace_3655967
  have hstable : (prefixWord ++ tailWord_3655967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655967).length < 2 ^ (prefixWord ++ tailWord_3655967).sum := by decide
  have hdescent : baseEnd_3655967 < baseStart_3655967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655973 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 4]
def baseStart_3655973 : Nat := 118140960795 + 3655973 * 2 ^ 59
def prefixEnd_3655973 : Nat := 4983230072969 + 3 ^ 40 * 3655973 * 2
def baseEnd_3655973 : Nat := 417171424191139938338665

theorem tailTrace_3655973 : CollatzResearch.WordTrace tailWord_3655973 prefixEnd_3655973 417171424191139938338665 := by
  unfold tailWord_3655973
  simp only [CollatzResearch.WordTrace]
  refine ⟨133344289984041686323244573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88896193322694457548829715 133344289984041686323244573)
  ·
    refine ⟨50004108744015632371216715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133344289984041686323244573 50004108744015632371216715)
    ·
      refine ⟨75006163116023448556825073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50004108744015632371216715 75006163116023448556825073)
      ·
        refine ⟨56254622337017586417618805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75006163116023448556825073 56254622337017586417618805)
        ·
          refine ⟨5273870844095398726651763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56254622337017586417618805 5273870844095398726651763)
          ·
            refine ⟨7910806266143098089977645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5273870844095398726651763 7910806266143098089977645)
            ·
              refine ⟨2966552349803661783741617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7910806266143098089977645 2966552349803661783741617)
              ·
                refine ⟨2224914262352746337806213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2966552349803661783741617 2224914262352746337806213)
                ·
                  refine ⟨417171424191139938338665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2224914262352746337806213 417171424191139938338665)
                  ·
                    rfl

theorem cell22_3655973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_3655973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655973 prefixEnd_3655973 := by exact prefixLift 3655973
  have htrace : WordTrace (prefixWord ++ tailWord_3655973) baseStart_3655973 baseEnd_3655973 := by
    simpa [prefixWord, tailWord_3655973, baseEnd_3655973] using wordTrace_append hprefix tailTrace_3655973
  have hstable : (prefixWord ++ tailWord_3655973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655973).length < 2 ^ (prefixWord ++ tailWord_3655973).sum := by decide
  have hdescent : baseEnd_3655973 < baseStart_3655973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655988 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_3655988 : Nat := 118140960795 + 3655988 * 2 ^ 59
def prefixEnd_3655988 : Nat := 4983230072969 + 3 ^ 40 * 3655988 * 2
def baseEnd_3655988 : Nat := 1251519407379964775890949

theorem tailTrace_3655988 : CollatzResearch.WordTrace tailWord_3655988 prefixEnd_3655988 1251519407379964775890949 := by
  unfold tailWord_3655988
  simp only [CollatzResearch.WordTrace]
  refine ⟨66672418539493671942520309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88896558052658229256693745 66672418539493671942520309)
  ·
    refine ⟨6250539238077531744611279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66672418539493671942520309 6250539238077531744611279)
    ·
      refine ⟨9375808857116297616916919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6250539238077531744611279 9375808857116297616916919)
      ·
        refine ⟨14063713285674446425375379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9375808857116297616916919 14063713285674446425375379)
        ·
          refine ⟨21095569928511669638063069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14063713285674446425375379 21095569928511669638063069)
          ·
            refine ⟨7910838723191876114273651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21095569928511669638063069 7910838723191876114273651)
            ·
              refine ⟨11866258084787814171410477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7910838723191876114273651 11866258084787814171410477)
              ·
                refine ⟨4449846781795430314278929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11866258084787814171410477 4449846781795430314278929)
                ·
                  refine ⟨3337385086346572735709197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4449846781795430314278929 3337385086346572735709197)
                  ·
                    refine ⟨1251519407379964775890949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337385086346572735709197 1251519407379964775890949)
                    ·
                      rfl

theorem cell22_3655988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_3655988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655988 prefixEnd_3655988 := by exact prefixLift 3655988
  have htrace : WordTrace (prefixWord ++ tailWord_3655988) baseStart_3655988 baseEnd_3655988 := by
    simpa [prefixWord, tailWord_3655988, baseEnd_3655988] using wordTrace_append hprefix tailTrace_3655988
  have hstable : (prefixWord ++ tailWord_3655988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655988).length < 2 ^ (prefixWord ++ tailWord_3655988).sum := by decide
  have hdescent : baseEnd_3655988 < baseStart_3655988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3655999 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 5, 3]
def baseStart_3655999 : Nat := 118140960795 + 3655999 * 2 ^ 59
def prefixEnd_3655999 : Nat := 4983230072969 + 3 ^ 40 * 3655999 * 2
def baseEnd_3655999 : Nat := 1251523172904764413865915

theorem tailTrace_3655999 : CollatzResearch.WordTrace tailWord_3655999 prefixEnd_3655999 1251523172904764413865915 := by
  unfold tailWord_3655999
  simp only [CollatzResearch.WordTrace]
  refine ⟨133345238281947492763691051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88896825521298328509127367 133345238281947492763691051)
  ·
    refine ⟨200017857422921239145536577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133345238281947492763691051 200017857422921239145536577)
    ·
      refine ⟨150013393067190929359152433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200017857422921239145536577 150013393067190929359152433)
      ·
        refine ⟨112510044800393197019364325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150013393067190929359152433 112510044800393197019364325)
        ·
          refine ⟨21095633400073724441130811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112510044800393197019364325 21095633400073724441130811)
          ·
            refine ⟨31643450100110586661696217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21095633400073724441130811 31643450100110586661696217)
            ·
              refine ⟨23732587575082939996272163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31643450100110586661696217 23732587575082939996272163)
              ·
                refine ⟨35598881362624409994408245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23732587575082939996272163 35598881362624409994408245)
                ·
                  refine ⟨3337395127746038436975773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35598881362624409994408245 3337395127746038436975773)
                  ·
                    refine ⟨1251523172904764413865915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337395127746038436975773 1251523172904764413865915)
                    ·
                      rfl

theorem cell22_3655999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_3655999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3655999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3655999 prefixEnd_3655999 := by exact prefixLift 3655999
  have htrace : WordTrace (prefixWord ++ tailWord_3655999) baseStart_3655999 baseEnd_3655999 := by
    simpa [prefixWord, tailWord_3655999, baseEnd_3655999] using wordTrace_append hprefix tailTrace_3655999
  have hstable : (prefixWord ++ tailWord_3655999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3655999).length < 2 ^ (prefixWord ++ tailWord_3655999).sum := by decide
  have hdescent : baseEnd_3655999 < baseStart_3655999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3655999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656059 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 3, 4]
def baseStart_3656059 : Nat := 118140960795 + 3656059 * 2 ^ 59
def prefixEnd_3656059 : Nat := 4983230072969 + 3 ^ 40 * 3656059 * 2
def baseEnd_3656059 : Nat := 1251543712130944257365731

theorem tailTrace_3656059 : CollatzResearch.WordTrace tailWord_3656059 prefixEnd_3656059 1251543712130944257365731 := by
  unfold tailWord_3656059
  simp only [CollatzResearch.WordTrace]
  refine ⟨133347426661730123010875231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88898284441153415340583487 133347426661730123010875231)
  ·
    refine ⟨200021139992595184516312847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133347426661730123010875231 200021139992595184516312847)
    ·
      refine ⟨300031709988892776774469271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200021139992595184516312847 300031709988892776774469271)
      ·
        refine ⟨450047564983339165161703907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300031709988892776774469271 450047564983339165161703907)
        ·
          refine ⟨675071347475008747742555861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450047564983339165161703907 675071347475008747742555861)
          ·
            refine ⟨15821984706445517525216153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 675071347475008747742555861 15821984706445517525216153)
            ·
              refine ⟨11866488529834138143912115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15821984706445517525216153 11866488529834138143912115)
              ·
                refine ⟨17799732794751207215868173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11866488529834138143912115 17799732794751207215868173)
                ·
                  refine ⟨6674899798031702705950565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17799732794751207215868173 6674899798031702705950565)
                  ·
                    refine ⟨1251543712130944257365731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674899798031702705950565 1251543712130944257365731)
                    ·
                      rfl

theorem cell22_3656059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 4].length) (baseStart_3656059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656059 prefixEnd_3656059 := by exact prefixLift 3656059
  have htrace : WordTrace (prefixWord ++ tailWord_3656059) baseStart_3656059 baseEnd_3656059 := by
    simpa [prefixWord, tailWord_3656059, baseEnd_3656059] using wordTrace_append hprefix tailTrace_3656059
  have hstable : (prefixWord ++ tailWord_3656059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656059).length < 2 ^ (prefixWord ++ tailWord_3656059).sum := by decide
  have hdescent : baseEnd_3656059 < baseStart_3656059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656076 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_3656076 : Nat := 118140960795 + 3656076 * 2 ^ 59
def prefixEnd_3656076 : Nat := 4983230072969 + 3 ^ 40 * 3656076 * 2
def baseEnd_3656076 : Nat := 1251549531578361879690679

theorem tailTrace_3656076 : CollatzResearch.WordTrace tailWord_3656076 prefixEnd_3656076 1251549531578361879690679 := by
  unfold tailWord_3656076
  simp only [CollatzResearch.WordTrace]
  refine ⟨66674023351334267457122041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88898697801779023276162721 66674023351334267457122041)
  ·
    refine ⟨50005517513500700592841531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66674023351334267457122041 50005517513500700592841531)
    ·
      refine ⟨75008276270251050889262297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50005517513500700592841531 75008276270251050889262297)
      ·
        refine ⟨56256207202688288166946723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75008276270251050889262297 56256207202688288166946723)
        ·
          refine ⟨84384310804032432250420085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56256207202688288166946723 84384310804032432250420085)
          ·
            refine ⟨7911029137878040523476883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84384310804032432250420085 7911029137878040523476883)
            ·
              refine ⟨11866543706817060785215325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911029137878040523476883 11866543706817060785215325)
              ·
                refine ⟨4449953890056397794455747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11866543706817060785215325 4449953890056397794455747)
                ·
                  refine ⟨6674930835084596691683621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4449953890056397794455747 6674930835084596691683621)
                  ·
                    refine ⟨1251549531578361879690679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6674930835084596691683621 1251549531578361879690679)
                    ·
                      rfl

theorem cell22_3656076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_3656076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656076 prefixEnd_3656076 := by exact prefixLift 3656076
  have htrace : WordTrace (prefixWord ++ tailWord_3656076) baseStart_3656076 baseEnd_3656076 := by
    simpa [prefixWord, tailWord_3656076, baseEnd_3656076] using wordTrace_append hprefix tailTrace_3656076
  have hstable : (prefixWord ++ tailWord_3656076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656076).length < 2 ^ (prefixWord ++ tailWord_3656076).sum := by decide
  have hdescent : baseEnd_3656076 < baseStart_3656076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656119 : List Nat := [1, 1, 3, 1, 3, 4, 1, 8]
def baseStart_3656119 : Nat := 118140960795 + 3656119 * 2 ^ 59
def prefixEnd_3656119 : Nat := 4983230072969 + 3 ^ 40 * 3656119 * 2
def baseEnd_3656119 : Nat := 139062694595236011207283

theorem tailTrace_3656119 : CollatzResearch.WordTrace tailWord_3656119 prefixEnd_3656119 139062694595236011207283 := by
  unfold tailWord_3656119
  simp only [CollatzResearch.WordTrace]
  refine ⟨133349615041512753258059411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88899743361008502172039607 133349615041512753258059411)
  ·
    refine ⟨200024422562269129887089117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133349615041512753258059411 200024422562269129887089117)
    ·
      refine ⟨75009158460850923707658419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200024422562269129887089117 75009158460850923707658419)
      ·
        refine ⟨112513737691276385561487629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75009158460850923707658419 112513737691276385561487629)
        ·
          refine ⟨42192651634228644585557861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112513737691276385561487629 42192651634228644585557861)
          ·
            refine ⟨7911122181417870859792099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42192651634228644585557861 7911122181417870859792099)
            ·
              refine ⟨11866683272126806289688149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911122181417870859792099 11866683272126806289688149)
              ·
                refine ⟨139062694595236011207283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11866683272126806289688149 139062694595236011207283)
                ·
                  rfl

theorem cell22_3656119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 8].length) (baseStart_3656119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656119 prefixEnd_3656119 := by exact prefixLift 3656119
  have htrace : WordTrace (prefixWord ++ tailWord_3656119) baseStart_3656119 baseEnd_3656119 := by
    simpa [prefixWord, tailWord_3656119, baseEnd_3656119] using wordTrace_append hprefix tailTrace_3656119
  have hstable : (prefixWord ++ tailWord_3656119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656119).length < 2 ^ (prefixWord ++ tailWord_3656119).sum := by decide
  have hdescent : baseEnd_3656119 < baseStart_3656119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656241 : List Nat := [1, 2, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3656241 : Nat := 118140960795 + 3656241 * 2 ^ 59
def prefixEnd_3656241 : Nat := 4983230072969 + 3 ^ 40 * 3656241 * 2
def baseEnd_3656241 : Nat := 1251606014450356449315173

theorem tailTrace_3656241 : CollatzResearch.WordTrace tailWord_3656241 prefixEnd_3656241 1251606014450356449315173 := by
  unfold tailWord_3656241
  simp only [CollatzResearch.WordTrace]
  refine ⟨133354064747070768094000577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88902709831380512062667051 133354064747070768094000577)
  ·
    refine ⟨100015548560303076070500433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133354064747070768094000577 100015548560303076070500433)
    ·
      refine ⟨75011661420227307052875325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100015548560303076070500433 75011661420227307052875325)
      ·
        refine ⟨28129373032585240144828247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75011661420227307052875325 28129373032585240144828247)
        ·
          refine ⟨42194059548877860217242371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28129373032585240144828247 42194059548877860217242371)
          ·
            refine ⟨63291089323316790325863557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42194059548877860217242371 63291089323316790325863557)
            ·
              refine ⟨11867079248121898186099417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63291089323316790325863557 11867079248121898186099417)
              ·
                refine ⟨8900309436091423639574563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11867079248121898186099417 8900309436091423639574563)
                ·
                  refine ⟨13350464154137135459361845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8900309436091423639574563 13350464154137135459361845)
                  ·
                    refine ⟨1251606014450356449315173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13350464154137135459361845 1251606014450356449315173)
                    ·
                      rfl

theorem cell22_3656241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3656241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656241 prefixEnd_3656241 := by exact prefixLift 3656241
  have htrace : WordTrace (prefixWord ++ tailWord_3656241) baseStart_3656241 baseEnd_3656241 := by
    simpa [prefixWord, tailWord_3656241, baseEnd_3656241] using wordTrace_append hprefix tailTrace_3656241
  have hstable : (prefixWord ++ tailWord_3656241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656241).length < 2 ^ (prefixWord ++ tailWord_3656241).sum := by decide
  have hdescent : baseEnd_3656241 < baseStart_3656241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656243 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 4]
def baseStart_3656243 : Nat := 118140960795 + 3656243 * 2 ^ 59
def prefixEnd_3656243 : Nat := 4983230072969 + 3 ^ 40 * 3656243 * 2
def baseEnd_3656243 : Nat := 417202233030409703588389

theorem tailTrace_3656243 : CollatzResearch.WordTrace tailWord_3656243 prefixEnd_3656243 417202233030409703588389 := by
  unfold tailWord_3656243
  simp only [CollatzResearch.WordTrace]
  refine ⟨133354137693063522435573383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88902758462042348290382255 133354137693063522435573383)
  ·
    refine ⟨200031206539595283653360075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133354137693063522435573383 200031206539595283653360075)
    ·
      refine ⟨300046809809392925480040113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200031206539595283653360075 300046809809392925480040113)
      ·
        refine ⟨225035107357044694110030085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300046809809392925480040113 225035107357044694110030085)
        ·
          refine ⟨42194082629445880145630641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225035107357044694110030085 42194082629445880145630641)
          ·
            refine ⟨31645561972084410109222981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42194082629445880145630641 31645561972084410109222981)
            ·
              refine ⟨5933542869765826895479309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31645561972084410109222981 5933542869765826895479309)
              ·
                refine ⟨2225078576162185085804741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5933542869765826895479309 2225078576162185085804741)
                ·
                  refine ⟨417202233030409703588389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225078576162185085804741 417202233030409703588389)
                  ·
                    rfl

theorem cell22_3656243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 4].length) (baseStart_3656243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656243 prefixEnd_3656243 := by exact prefixLift 3656243
  have htrace : WordTrace (prefixWord ++ tailWord_3656243) baseStart_3656243 baseEnd_3656243 := by
    simpa [prefixWord, tailWord_3656243, baseEnd_3656243] using wordTrace_append hprefix tailTrace_3656243
  have hstable : (prefixWord ++ tailWord_3656243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656243).length < 2 ^ (prefixWord ++ tailWord_3656243).sum := by decide
  have hdescent : baseEnd_3656243 < baseStart_3656243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656256 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_3656256 : Nat := 118140960795 + 3656256 * 2 ^ 59
def prefixEnd_3656256 : Nat := 4983230072969 + 3 ^ 40 * 3656256 * 2
def baseEnd_3656256 : Nat := 1251611149256901410190127

theorem tailTrace_3656256 : CollatzResearch.WordTrace tailWord_3656256 prefixEnd_3656256 1251611149256901410190127 := by
  unfold tailWord_3656256
  simp only [CollatzResearch.WordTrace]
  refine ⟨66677305921008212827898311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88903074561344283770531081 66677305921008212827898311)
  ·
    refine ⟨100015958881512319241847467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66677305921008212827898311 100015958881512319241847467)
    ·
      refine ⟨150023938322268478862771201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100015958881512319241847467 150023938322268478862771201)
      ·
        refine ⟨112517953741701359147078401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150023938322268478862771201 112517953741701359147078401)
        ·
          refine ⟨84388465306276019360308801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112517953741701359147078401 84388465306276019360308801)
          ·
            refine ⟨63291348979707014520231601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84388465306276019360308801 63291348979707014520231601)
            ·
              refine ⟨47468511734780260890173701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63291348979707014520231601 47468511734780260890173701)
              ·
                refine ⟨8900345950271298916907569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47468511734780260890173701 8900345950271298916907569)
                ·
                  refine ⟨6675259462703474187680677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8900345950271298916907569 6675259462703474187680677)
                  ·
                    refine ⟨1251611149256901410190127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675259462703474187680677 1251611149256901410190127)
                    ·
                      rfl

theorem cell22_3656256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_3656256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656256 prefixEnd_3656256 := by exact prefixLift 3656256
  have htrace : WordTrace (prefixWord ++ tailWord_3656256) baseStart_3656256 baseEnd_3656256 := by
    simpa [prefixWord, tailWord_3656256, baseEnd_3656256] using wordTrace_append hprefix tailTrace_3656256
  have hstable : (prefixWord ++ tailWord_3656256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656256).length < 2 ^ (prefixWord ++ tailWord_3656256).sum := by decide
  have hdescent : baseEnd_3656256 < baseStart_3656256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656316 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_3656316 : Nat := 118140960795 + 3656316 * 2 ^ 59
def prefixEnd_3656316 : Nat := 4983230072969 + 3 ^ 40 * 3656316 * 2
def baseEnd_3656316 : Nat := 417210562827693751229981

theorem tailTrace_3656316 : CollatzResearch.WordTrace tailWord_3656316 prefixEnd_3656316 417210562827693751229981 := by
  unfold tailWord_3656316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66678400110899527951490401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88904533481199370601987201 66678400110899527951490401)
  ·
    refine ⟨50008800083174645963617801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66678400110899527951490401 50008800083174645963617801)
    ·
      refine ⟨37506600062380984472713351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50008800083174645963617801 37506600062380984472713351)
      ·
        refine ⟨56259900093571476709070027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37506600062380984472713351 56259900093571476709070027)
        ·
          refine ⟨84389850140357215063605041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56259900093571476709070027 84389850140357215063605041)
          ·
            refine ⟨63292387605267911297703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84389850140357215063605041 63292387605267911297703781)
            ·
              refine ⟨11867322675987733368319459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63292387605267911297703781 11867322675987733368319459)
              ·
                refine ⟨17800984013981600052479189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867322675987733368319459 17800984013981600052479189)
                ·
                  refine ⟨417210562827693751229981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17800984013981600052479189 417210562827693751229981)
                  ·
                    rfl

theorem cell22_3656316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_3656316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656316 prefixEnd_3656316 := by exact prefixLift 3656316
  have htrace : WordTrace (prefixWord ++ tailWord_3656316) baseStart_3656316 baseEnd_3656316 := by
    simpa [prefixWord, tailWord_3656316, baseEnd_3656316] using wordTrace_append hprefix tailTrace_3656316
  have hstable : (prefixWord ++ tailWord_3656316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656316).length < 2 ^ (prefixWord ++ tailWord_3656316).sum := by decide
  have hdescent : baseEnd_3656316 < baseStart_3656316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656320 : List Nat := [2, 1, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_3656320 : Nat := 118140960795 + 3656320 * 2 ^ 59
def prefixEnd_3656320 : Nat := 4983230072969 + 3 ^ 40 * 3656320 * 2
def baseEnd_3656320 : Nat := 1251633057764826576589931

theorem tailTrace_3656320 : CollatzResearch.WordTrace tailWord_3656320 prefixEnd_3656320 1251633057764826576589931 := by
  unfold tailWord_3656320
  simp only [CollatzResearch.WordTrace]
  refine ⟨66678473056892282293063207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88904630742523043057417609 66678473056892282293063207)
  ·
    refine ⟨100017709585338423439594811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66678473056892282293063207 100017709585338423439594811)
    ·
      refine ⟨150026564378007635159392217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100017709585338423439594811 150026564378007635159392217)
      ·
        refine ⟨112519923283505726369544163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150026564378007635159392217 112519923283505726369544163)
        ·
          refine ⟨168779884925258589554316245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112519923283505726369544163 168779884925258589554316245)
          ·
            refine ⟨3955778552935748192679287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168779884925258589554316245 3955778552935748192679287)
            ·
              refine ⟨5933667829403622289018931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3955778552935748192679287 5933667829403622289018931)
              ·
                refine ⟨8900501744105433433528397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5933667829403622289018931 8900501744105433433528397)
                ·
                  refine ⟨3337688154039537537573149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8900501744105433433528397 3337688154039537537573149)
                  ·
                    refine ⟨1251633057764826576589931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337688154039537537573149 1251633057764826576589931)
                    ·
                      rfl

theorem cell22_3656320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_3656320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656320 prefixEnd_3656320 := by exact prefixLift 3656320
  have htrace : WordTrace (prefixWord ++ tailWord_3656320) baseStart_3656320 baseEnd_3656320 := by
    simpa [prefixWord, tailWord_3656320, baseEnd_3656320] using wordTrace_append hprefix tailTrace_3656320
  have hstable : (prefixWord ++ tailWord_3656320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656320).length < 2 ^ (prefixWord ++ tailWord_3656320).sum := by decide
  have hdescent : baseEnd_3656320 < baseStart_3656320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656408 : List Nat := [2, 1, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_3656408 : Nat := 118140960795 + 3656408 * 2 ^ 59
def prefixEnd_3656408 : Nat := 4983230072969 + 3 ^ 40 * 3656408 * 2
def baseEnd_3656408 : Nat := 1251663181963223680389661

theorem tailTrace_3656408 : CollatzResearch.WordTrace tailWord_3656408 prefixEnd_3656408 1251663181963223680389661 := by
  unfold tailWord_3656408
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680077868732877807664939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88906770491643837076886585 66680077868732877807664939)
  ·
    refine ⟨100020116803099316711497409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66680077868732877807664939 100020116803099316711497409)
    ·
      refine ⟨75015087602324487533623057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100020116803099316711497409 75015087602324487533623057)
      ·
        refine ⟨56261315701743365650217293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75015087602324487533623057 56261315701743365650217293)
        ·
          refine ⟨21097993388153762118831485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56261315701743365650217293 21097993388153762118831485)
          ·
            refine ⟨7911747520557660794561807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21097993388153762118831485 7911747520557660794561807)
            ·
              refine ⟨11867621280836491191842711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7911747520557660794561807 11867621280836491191842711)
              ·
                refine ⟨17801431921254736787764067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11867621280836491191842711 17801431921254736787764067)
                ·
                  refine ⟨26702147881882105181646101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17801431921254736787764067 26702147881882105181646101)
                  ·
                    refine ⟨1251663181963223680389661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26702147881882105181646101 1251663181963223680389661)
                    ·
                      rfl

theorem cell22_3656408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_3656408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656408 prefixEnd_3656408 := by exact prefixLift 3656408
  have htrace : WordTrace (prefixWord ++ tailWord_3656408) baseStart_3656408 baseEnd_3656408 := by
    simpa [prefixWord, tailWord_3656408, baseEnd_3656408] using wordTrace_append hprefix tailTrace_3656408
  have hstable : (prefixWord ++ tailWord_3656408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656408).length < 2 ^ (prefixWord ++ tailWord_3656408).sum := by decide
  have hdescent : baseEnd_3656408 < baseStart_3656408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656412 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_3656412 : Nat := 118140960795 + 3656412 * 2 ^ 59
def prefixEnd_3656412 : Nat := 4983230072969 + 3 ^ 40 * 3656412 * 2
def baseEnd_3656412 : Nat := 417221517081656334429883

theorem tailTrace_3656412 : CollatzResearch.WordTrace tailWord_3656412 prefixEnd_3656412 417221517081656334429883 := by
  unfold tailWord_3656412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66680150814725632149237745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88906867752967509532316993 66680150814725632149237745)
  ·
    refine ⟨50010113111044224111928309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66680150814725632149237745 50010113111044224111928309)
    ·
      refine ⟨4688448104160396010493279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50010113111044224111928309 4688448104160396010493279)
      ·
        refine ⟨7032672156240594015739919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4688448104160396010493279 7032672156240594015739919)
        ·
          refine ⟨10549008234360891023609879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7032672156240594015739919 10549008234360891023609879)
          ·
            refine ⟨15823512351541336535414819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549008234360891023609879 15823512351541336535414819)
            ·
              refine ⟨23735268527312004803122229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15823512351541336535414819 23735268527312004803122229)
              ·
                refine ⟨2225181424435500450292709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23735268527312004803122229 2225181424435500450292709)
                ·
                  refine ⟨417221517081656334429883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225181424435500450292709 417221517081656334429883)
                  ·
                    rfl

theorem cell22_3656412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_3656412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656412 prefixEnd_3656412 := by exact prefixLift 3656412
  have htrace : WordTrace (prefixWord ++ tailWord_3656412) baseStart_3656412 baseEnd_3656412 := by
    simpa [prefixWord, tailWord_3656412, baseEnd_3656412] using wordTrace_append hprefix tailTrace_3656412
  have hstable : (prefixWord ++ tailWord_3656412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656412).length < 2 ^ (prefixWord ++ tailWord_3656412).sum := by decide
  have hdescent : baseEnd_3656412 < baseStart_3656412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656528 : List Nat := [2, 1, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_3656528 : Nat := 118140960795 + 3656528 * 2 ^ 59
def prefixEnd_3656528 : Nat := 4983230072969 + 3 ^ 40 * 3656528 * 2
def baseEnd_3656528 : Nat := 1251704260415583367389293

theorem tailTrace_3656528 : CollatzResearch.WordTrace tailWord_3656528 prefixEnd_3656528 1251704260415583367389293 := by
  unfold tailWord_3656528
  simp only [CollatzResearch.WordTrace]
  refine ⟨66682266248515508054849119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88909688331354010739798825 66682266248515508054849119)
  ·
    refine ⟨100023399372773262082273679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66682266248515508054849119 100023399372773262082273679)
    ·
      refine ⟨150035099059159893123410519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100023399372773262082273679 150035099059159893123410519)
      ·
        refine ⟨225052648588739839685115779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150035099059159893123410519 225052648588739839685115779)
        ·
          refine ⟨337578972883109759527673669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225052648588739839685115779 337578972883109759527673669)
          ·
            refine ⟨63296057415583079911438813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337578972883109759527673669 63296057415583079911438813)
            ·
              refine ⟨23736021530843654966789555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63296057415583079911438813 23736021530843654966789555)
              ·
                refine ⟨35604032296265482450184333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23736021530843654966789555 35604032296265482450184333)
                ·
                  refine ⟨13351512111099555918819125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35604032296265482450184333 13351512111099555918819125)
                  ·
                    refine ⟨1251704260415583367389293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13351512111099555918819125 1251704260415583367389293)
                    ·
                      rfl

theorem cell22_3656528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_3656528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656528 prefixEnd_3656528 := by exact prefixLift 3656528
  have htrace : WordTrace (prefixWord ++ tailWord_3656528) baseStart_3656528 baseEnd_3656528 := by
    simpa [prefixWord, tailWord_3656528, baseEnd_3656528] using wordTrace_append hprefix tailTrace_3656528
  have hstable : (prefixWord ++ tailWord_3656528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656528).length < 2 ^ (prefixWord ++ tailWord_3656528).sum := by decide
  have hdescent : baseEnd_3656528 < baseStart_3656528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656547 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 4]
def baseStart_3656547 : Nat := 118140960795 + 3656547 * 2 ^ 59
def prefixEnd_3656547 : Nat := 4983230072969 + 3 ^ 40 * 3656547 * 2
def baseEnd_3656547 : Nat := 417236921501291217054745

theorem tailTrace_3656547 : CollatzResearch.WordTrace tailWord_3656547 prefixEnd_3656547 417236921501291217054745 := by
  unfold tailWord_3656547
  simp only [CollatzResearch.WordTrace]
  refine ⟨133365225483962182354639895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88910150322641454903093263 133365225483962182354639895)
  ·
    refine ⟨200047838225943273531959843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133365225483962182354639895 200047838225943273531959843)
    ·
      refine ⟨300071757338914910297939765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200047838225943273531959843 300071757338914910297939765)
      ·
        refine ⟨28131727250523272840431853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300071757338914910297939765 28131727250523272840431853)
        ·
          refine ⟨10549397718946227315161945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28131727250523272840431853 10549397718946227315161945)
          ·
            refine ⟨7912048289209670486371459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549397718946227315161945 7912048289209670486371459)
            ·
              refine ⟨11868072433814505729557189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912048289209670486371459 11868072433814505729557189)
              ·
                refine ⟨2225263581340219824291973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11868072433814505729557189 2225263581340219824291973)
                ·
                  refine ⟨417236921501291217054745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225263581340219824291973 417236921501291217054745)
                  ·
                    rfl

theorem cell22_3656547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 4].length) (baseStart_3656547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656547 prefixEnd_3656547 := by exact prefixLift 3656547
  have htrace : WordTrace (prefixWord ++ tailWord_3656547) baseStart_3656547 baseEnd_3656547 := by
    simpa [prefixWord, tailWord_3656547, baseEnd_3656547] using wordTrace_append hprefix tailTrace_3656547
  have hstable : (prefixWord ++ tailWord_3656547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656547).length < 2 ^ (prefixWord ++ tailWord_3656547).sum := by decide
  have hdescent : baseEnd_3656547 < baseStart_3656547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656562 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 2, 3]
def baseStart_3656562 : Nat := 118140960795 + 3656562 * 2 ^ 59
def prefixEnd_3656562 : Nat := 4983230072969 + 3 ^ 40 * 3656562 * 2
def baseEnd_3656562 : Nat := 1251715899310418612039189

theorem tailTrace_3656562 : CollatzResearch.WordTrace tailWord_3656562 prefixEnd_3656562 1251715899310418612039189 := by
  unfold tailWord_3656562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33341443144726959979108985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88910515052605226610957293 33341443144726959979108985)
  ·
    refine ⟨25006082358545219984331739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33341443144726959979108985 25006082358545219984331739)
    ·
      refine ⟨37509123537817829976497609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25006082358545219984331739 37509123537817829976497609)
      ·
        refine ⟨28131842653363372482373207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37509123537817829976497609 28131842653363372482373207)
        ·
          refine ⟨42197763980045058723559811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28131842653363372482373207 42197763980045058723559811)
          ·
            refine ⟨63296645970067588085339717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42197763980045058723559811 63296645970067588085339717)
            ·
              refine ⟨11868121119387672766001197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63296645970067588085339717 11868121119387672766001197)
              ·
                refine ⟨4450545419770377287250449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11868121119387672766001197 4450545419770377287250449)
                ·
                  refine ⟨3337909064827782965437837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450545419770377287250449 3337909064827782965437837)
                  ·
                    refine ⟨1251715899310418612039189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337909064827782965437837 1251715899310418612039189)
                    ·
                      rfl

theorem cell22_3656562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_3656562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656562 prefixEnd_3656562 := by exact prefixLift 3656562
  have htrace : WordTrace (prefixWord ++ tailWord_3656562) baseStart_3656562 baseEnd_3656562 := by
    simpa [prefixWord, tailWord_3656562, baseEnd_3656562] using wordTrace_append hprefix tailTrace_3656562
  have hstable : (prefixWord ++ tailWord_3656562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656562).length < 2 ^ (prefixWord ++ tailWord_3656562).sum := by decide
  have hdescent : baseEnd_3656562 < baseStart_3656562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656607 : List Nat := [1, 1, 2, 5, 2, 1, 1, 3, 3, 3]
def baseStart_3656607 : Nat := 118140960795 + 3656607 * 2 ^ 59
def prefixEnd_3656607 : Nat := 4983230072969 + 3 ^ 40 * 3656607 * 2
def baseEnd_3656607 : Nat := 1251731303730053494664051

theorem tailTrace_3656607 : CollatzResearch.WordTrace tailWord_3656607 prefixEnd_3656607 1251731303730053494664051 := by
  unfold tailWord_3656607
  simp only [CollatzResearch.WordTrace]
  refine ⟨133367413863744812601824075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88911609242496541734549383 133367413863744812601824075)
  ·
    refine ⟨200051120795617218902736113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133367413863744812601824075 200051120795617218902736113)
    ·
      refine ⟨150038340596712914177052085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200051120795617218902736113 150038340596712914177052085)
      ·
        refine ⟨14066094430941835704098633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150038340596712914177052085 14066094430941835704098633)
        ·
          refine ⟨10549570823206376778073975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14066094430941835704098633 10549570823206376778073975)
          ·
            refine ⟨15824356234809565167110963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549570823206376778073975 15824356234809565167110963)
            ·
              refine ⟨23736534352214347750666445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15824356234809565167110963 23736534352214347750666445)
              ·
                refine ⟨8901200382080380406499917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23736534352214347750666445 8901200382080380406499917)
                ·
                  refine ⟨3337950143280142652437469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8901200382080380406499917 3337950143280142652437469)
                  ·
                    refine ⟨1251731303730053494664051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337950143280142652437469 1251731303730053494664051)
                    ·
                      rfl

theorem cell22_3656607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_3656607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656607 prefixEnd_3656607 := by exact prefixLift 3656607
  have htrace : WordTrace (prefixWord ++ tailWord_3656607) baseStart_3656607 baseEnd_3656607 := by
    simpa [prefixWord, tailWord_3656607, baseEnd_3656607] using wordTrace_append hprefix tailTrace_3656607
  have hstable : (prefixWord ++ tailWord_3656607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656607).length < 2 ^ (prefixWord ++ tailWord_3656607).sum := by decide
  have hdescent : baseEnd_3656607 < baseStart_3656607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656650 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3656650 : Nat := 118140960795 + 3656650 * 2 ^ 59
def prefixEnd_3656650 : Nat := 4983230072969 + 3 ^ 40 * 3656650 * 2
def baseEnd_3656650 : Nat := 1251746023508815715838919

theorem tailTrace_3656650 : CollatzResearch.WordTrace tailWord_3656650 prefixEnd_3656650 1251746023508815715838919 := by
  unfold tailWord_3656650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342245550647257736409851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88912654801726020630426269 33342245550647257736409851)
  ·
    refine ⟨50013368325970886604614777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33342245550647257736409851 50013368325970886604614777)
    ·
      refine ⟨37510026244478164953461083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50013368325970886604614777 37510026244478164953461083)
      ·
        refine ⟨56265039366717247430191625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37510026244478164953461083 56265039366717247430191625)
        ·
          refine ⟨42198779525037935572643719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56265039366717247430191625 42198779525037935572643719)
          ·
            refine ⟨63298169287556903358965579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42198779525037935572643719 63298169287556903358965579)
            ·
              refine ⟨94947253931335355038448369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63298169287556903358965579 94947253931335355038448369)
              ·
                refine ⟨71210440448501516278836277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94947253931335355038448369 71210440448501516278836277)
                ·
                  refine ⟨6675978792047017151140901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71210440448501516278836277 6675978792047017151140901)
                  ·
                    refine ⟨1251746023508815715838919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6675978792047017151140901 1251746023508815715838919)
                    ·
                      rfl

theorem cell22_3656650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3656650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656650 prefixEnd_3656650 := by exact prefixLift 3656650
  have htrace : WordTrace (prefixWord ++ tailWord_3656650) baseStart_3656650 baseEnd_3656650 := by
    simpa [prefixWord, tailWord_3656650, baseEnd_3656650] using wordTrace_append hprefix tailTrace_3656650
  have hstable : (prefixWord ++ tailWord_3656650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656650).length < 2 ^ (prefixWord ++ tailWord_3656650).sum := by decide
  have hdescent : baseEnd_3656650 < baseStart_3656650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656658 : List Nat := [3, 2, 2, 3, 1, 2, 3, 2, 1, 3]
def baseStart_3656658 : Nat := 118140960795 + 3656658 * 2 ^ 59
def prefixEnd_3656658 : Nat := 4983230072969 + 3 ^ 40 * 3656658 * 2
def baseEnd_3656658 : Nat := 1251748762072306361638895

theorem tailTrace_3656658 : CollatzResearch.WordTrace tailWord_3656658 prefixEnd_3656658 1251748762072306361638895 := by
  unfold tailWord_3656658
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342318496640012077982657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88912849324373365541287085 33342318496640012077982657)
  ·
    refine ⟨25006738872480009058486993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33342318496640012077982657 25006738872480009058486993)
    ·
      refine ⟨18755054154360006793865245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25006738872480009058486993 18755054154360006793865245)
      ·
        refine ⟨7033145307885002547699467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18755054154360006793865245 7033145307885002547699467)
        ·
          refine ⟨10549717961827503821549201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033145307885002547699467 10549717961827503821549201)
          ·
            refine ⟨7912288471370627866161901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10549717961827503821549201 7912288471370627866161901)
            ·
              refine ⟨2967108176763985449810713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7912288471370627866161901 2967108176763985449810713)
              ·
                refine ⟨2225331132572989087358035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967108176763985449810713 2225331132572989087358035)
                ·
                  refine ⟨3337996698859483631037053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225331132572989087358035 3337996698859483631037053)
                  ·
                    refine ⟨1251748762072306361638895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3337996698859483631037053 1251748762072306361638895)
                    ·
                      rfl

theorem cell22_3656658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_3656658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656658 prefixEnd_3656658 := by exact prefixLift 3656658
  have htrace : WordTrace (prefixWord ++ tailWord_3656658) baseStart_3656658 baseEnd_3656658 := by
    simpa [prefixWord, tailWord_3656658, baseEnd_3656658] using wordTrace_append hprefix tailTrace_3656658
  have hstable : (prefixWord ++ tailWord_3656658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656658).length < 2 ^ (prefixWord ++ tailWord_3656658).sum := by decide
  have hdescent : baseEnd_3656658 < baseStart_3656658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656671 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 5]
def baseStart_3656671 : Nat := 118140960795 + 3656671 * 2 ^ 59
def prefixEnd_3656671 : Nat := 4983230072969 + 3 ^ 40 * 3656671 * 2
def baseEnd_3656671 : Nat := 417251070745992887021285

theorem tailTrace_3656671 : CollatzResearch.WordTrace tailWord_3656671 prefixEnd_3656671 417251070745992887021285 := by
  unfold tailWord_3656671
  simp only [CollatzResearch.WordTrace]
  refine ⟨133369748135512951532153867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88913165423675301021435911 133369748135512951532153867)
  ·
    refine ⟨200054622203269427298230801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133369748135512951532153867 200054622203269427298230801)
    ·
      refine ⟨150040966652452070473673101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200054622203269427298230801 150040966652452070473673101)
      ·
        refine ⟨56265362494669526427627413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150040966652452070473673101 56265362494669526427627413)
        ·
          refine ⟨2637438866937634051295035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56265362494669526427627413 2637438866937634051295035)
          ·
            refine ⟨3956158300406451076942553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637438866937634051295035 3956158300406451076942553)
            ·
              refine ⟨2967118725304838307706915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956158300406451076942553 2967118725304838307706915)
              ·
                refine ⟨4450678087957257461560373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967118725304838307706915 4450678087957257461560373)
                ·
                  refine ⟨417251070745992887021285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4450678087957257461560373 417251070745992887021285)
                  ·
                    rfl

theorem cell22_3656671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 5].length) (baseStart_3656671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656671 prefixEnd_3656671 := by exact prefixLift 3656671
  have htrace : WordTrace (prefixWord ++ tailWord_3656671) baseStart_3656671 baseEnd_3656671 := by
    simpa [prefixWord, tailWord_3656671, baseEnd_3656671] using wordTrace_append hprefix tailTrace_3656671
  have hstable : (prefixWord ++ tailWord_3656671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656671).length < 2 ^ (prefixWord ++ tailWord_3656671).sum := by decide
  have hdescent : baseEnd_3656671 < baseStart_3656671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656712 : List Nat := [2, 1, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_3656712 : Nat := 118140960795 + 3656712 * 2 ^ 59
def prefixEnd_3656712 : Nat := 4983230072969 + 3 ^ 40 * 3656712 * 2
def baseEnd_3656712 : Nat := 1251767247375868220788729

theorem tailTrace_3656712 : CollatzResearch.WordTrace tailWord_3656712 prefixEnd_3656712 1251767247375868220788729 := by
  unfold tailWord_3656712
  simp only [CollatzResearch.WordTrace]
  refine ⟨66685621764182207767198195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88914162352242943689597593 66685621764182207767198195)
  ·
    refine ⟨100028432646273311650797293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66685621764182207767198195 100028432646273311650797293)
    ·
      refine ⟨37510662242352491869048985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100028432646273311650797293 37510662242352491869048985)
      ·
        refine ⟨28132996681764368901786739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37510662242352491869048985 28132996681764368901786739)
        ·
          refine ⟨42199495022646553352680109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28132996681764368901786739 42199495022646553352680109)
          ·
            refine ⟨15824810633492457507255041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42199495022646553352680109 15824810633492457507255041)
            ·
              refine ⟨11868607975119343130441281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15824810633492457507255041 11868607975119343130441281)
              ·
                refine ⟨8901455981339507347830961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11868607975119343130441281 8901455981339507347830961)
                ·
                  refine ⟨6676091986004630510873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901455981339507347830961 6676091986004630510873221)
                  ·
                    refine ⟨1251767247375868220788729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676091986004630510873221 1251767247375868220788729)
                    ·
                      rfl

theorem cell22_3656712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_3656712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656712 prefixEnd_3656712 := by exact prefixLift 3656712
  have htrace : WordTrace (prefixWord ++ tailWord_3656712) baseStart_3656712 baseEnd_3656712 := by
    simpa [prefixWord, tailWord_3656712, baseEnd_3656712] using wordTrace_append hprefix tailTrace_3656712
  have hstable : (prefixWord ++ tailWord_3656712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656712).length < 2 ^ (prefixWord ++ tailWord_3656712).sum := by decide
  have hdescent : baseEnd_3656712 < baseStart_3656712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656714 : List Nat := [3, 1, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3656714 : Nat := 118140960795 + 3656714 * 2 ^ 59
def prefixEnd_3656714 : Nat := 4983230072969 + 3 ^ 40 * 3656714 * 2
def baseEnd_3656714 : Nat := 1251767932016740882238723

theorem tailTrace_3656714 : CollatzResearch.WordTrace tailWord_3656714 prefixEnd_3656714 1251767932016740882238723 := by
  unfold tailWord_3656714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33342829118589292468992299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88914210982904779917312797 33342829118589292468992299)
  ·
    refine ⟨50014243677883938703488449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33342829118589292468992299 50014243677883938703488449)
    ·
      refine ⟨37510682758412954027616337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50014243677883938703488449 37510682758412954027616337)
      ·
        refine ⟨28133012068809715520712253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37510682758412954027616337 28133012068809715520712253)
        ·
          refine ⟨10549879525803643320267095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28133012068809715520712253 10549879525803643320267095)
          ·
            refine ⟨15824819288705464980400643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549879525803643320267095 15824819288705464980400643)
            ·
              refine ⟨23737228933058197470600965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15824819288705464980400643 23737228933058197470600965)
              ·
                refine ⟨4450730424948412025737681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23737228933058197470600965 4450730424948412025737681)
                ·
                  refine ⟨3338047818711309019303261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4450730424948412025737681 3338047818711309019303261)
                  ·
                    refine ⟨1251767932016740882238723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338047818711309019303261 1251767932016740882238723)
                    ·
                      rfl

theorem cell22_3656714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3656714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656714 prefixEnd_3656714 := by exact prefixLift 3656714
  have htrace : WordTrace (prefixWord ++ tailWord_3656714) baseStart_3656714 baseEnd_3656714 := by
    simpa [prefixWord, tailWord_3656714, baseEnd_3656714] using wordTrace_append hprefix tailTrace_3656714
  have hstable : (prefixWord ++ tailWord_3656714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656714).length < 2 ^ (prefixWord ++ tailWord_3656714).sum := by decide
  have hdescent : baseEnd_3656714 < baseStart_3656714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656716 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_3656716 : Nat := 118140960795 + 3656716 * 2 ^ 59
def prefixEnd_3656716 : Nat := 4983230072969 + 3 ^ 40 * 3656716 * 2
def baseEnd_3656716 : Nat := 417256205552537847896239

theorem tailTrace_3656716 : CollatzResearch.WordTrace tailWord_3656716 prefixEnd_3656716 417256205552537847896239 := by
  unfold tailWord_3656716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66685694710174962108771001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88914259613566616145028001 66685694710174962108771001)
  ·
    refine ⟨50014271032631221581578251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66685694710174962108771001 50014271032631221581578251)
    ·
      refine ⟨75021406548946832372367377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50014271032631221581578251 75021406548946832372367377)
      ·
        refine ⟨56266054911710124279275533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75021406548946832372367377 56266054911710124279275533)
        ·
          refine ⟨21099770591891296604728325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56266054911710124279275533 21099770591891296604728325)
          ·
            refine ⟨3956206985979618113386561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21099770591891296604728325 3956206985979618113386561)
            ·
              refine ⟨2967155239484713585039921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956206985979618113386561 2967155239484713585039921)
              ·
                refine ⟨2225366429613535188779941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967155239484713585039921 2225366429613535188779941)
                ·
                  refine ⟨417256205552537847896239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225366429613535188779941 417256205552537847896239)
                  ·
                    rfl

theorem cell22_3656716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_3656716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656716 prefixEnd_3656716 := by exact prefixLift 3656716
  have htrace : WordTrace (prefixWord ++ tailWord_3656716) baseStart_3656716 baseEnd_3656716 := by
    simpa [prefixWord, tailWord_3656716, baseEnd_3656716] using wordTrace_append hprefix tailTrace_3656716
  have hstable : (prefixWord ++ tailWord_3656716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656716).length < 2 ^ (prefixWord ++ tailWord_3656716).sum := by decide
  have hdescent : baseEnd_3656716 < baseStart_3656716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656727 : List Nat := [1, 1, 3, 5, 1, 1, 3, 7]
def baseStart_3656727 : Nat := 118140960795 + 3656727 * 2 ^ 59
def prefixEnd_3656727 : Nat := 4983230072969 + 3 ^ 40 * 3656727 * 2
def baseEnd_3656727 : Nat := 139085820242490353518187

theorem tailTrace_3656727 : CollatzResearch.WordTrace tailWord_3656727 prefixEnd_3656727 139085820242490353518187 := by
  unfold tailWord_3656727
  simp only [CollatzResearch.WordTrace]
  refine ⟨133371790623310073096192435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88914527082206715397461623 133371790623310073096192435)
  ·
    refine ⟨200057685934965109644288653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133371790623310073096192435 200057685934965109644288653)
    ·
      refine ⟨75021632225611916116608245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200057685934965109644288653 75021632225611916116608245)
      ·
        refine ⟨7033278021151117135932023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75021632225611916116608245 7033278021151117135932023)
        ·
          refine ⟨10549917031726675703898035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7033278021151117135932023 10549917031726675703898035)
          ·
            refine ⟨15824875547590013555847053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10549917031726675703898035 15824875547590013555847053)
            ·
              refine ⟨5934328330346255083442645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15824875547590013555847053 5934328330346255083442645)
              ·
                refine ⟨139085820242490353518187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5934328330346255083442645 139085820242490353518187)
                ·
                  rfl

theorem cell22_3656727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 7].length) (baseStart_3656727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656727 prefixEnd_3656727 := by exact prefixLift 3656727
  have htrace : WordTrace (prefixWord ++ tailWord_3656727) baseStart_3656727 baseEnd_3656727 := by
    simpa [prefixWord, tailWord_3656727, baseEnd_3656727] using wordTrace_append hprefix tailTrace_3656727
  have hstable : (prefixWord ++ tailWord_3656727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656727).length < 2 ^ (prefixWord ++ tailWord_3656727).sum := by decide
  have hdescent : baseEnd_3656727 < baseStart_3656727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656746 : List Nat := [3, 1, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3656746 : Nat := 118140960795 + 3656746 * 2 ^ 59
def prefixEnd_3656746 : Nat := 4983230072969 + 3 ^ 40 * 3656746 * 2
def baseEnd_3656746 : Nat := 1251778886270703465438625

theorem tailTrace_3656746 : CollatzResearch.WordTrace tailWord_3656746 prefixEnd_3656746 1251778886270703465438625 := by
  unfold tailWord_3656746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33343120902560309835283523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88914989073494159560756061 33343120902560309835283523)
  ·
    refine ⟨50014681353840464752925285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33343120902560309835283523 50014681353840464752925285)
    ·
      refine ⟨9377752753845087141173491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50014681353840464752925285 9377752753845087141173491)
      ·
        refine ⟨14066629130767630711760237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9377752753845087141173491 14066629130767630711760237)
        ·
          refine ⟨5274985924037861516910089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14066629130767630711760237 5274985924037861516910089)
          ·
            refine ⟨3956239443028396137682567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5274985924037861516910089 3956239443028396137682567)
            ·
              refine ⟨5934359164542594206523851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956239443028396137682567 5934359164542594206523851)
              ·
                refine ⟨8901538746813891309785777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934359164542594206523851 8901538746813891309785777)
                ·
                  refine ⟨6676154060110418482339333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901538746813891309785777 6676154060110418482339333)
                  ·
                    refine ⟨1251778886270703465438625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676154060110418482339333 1251778886270703465438625)
                    ·
                      rfl

theorem cell22_3656746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3656746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656746 prefixEnd_3656746 := by exact prefixLift 3656746
  have htrace : WordTrace (prefixWord ++ tailWord_3656746) baseStart_3656746 baseEnd_3656746 := by
    simpa [prefixWord, tailWord_3656746, baseEnd_3656746] using wordTrace_append hprefix tailTrace_3656746
  have hstable : (prefixWord ++ tailWord_3656746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656746).length < 2 ^ (prefixWord ++ tailWord_3656746).sum := by decide
  have hdescent : baseEnd_3656746 < baseStart_3656746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656755 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 7]
def baseStart_3656755 : Nat := 118140960795 + 3656755 * 2 ^ 59
def prefixEnd_3656755 : Nat := 4983230072969 + 3 ^ 40 * 3656755 * 2
def baseEnd_3656755 : Nat := 417260655718210147321199

theorem tailTrace_3656755 : CollatzResearch.WordTrace tailWord_3656755 prefixEnd_3656755 417260655718210147321199 := by
  unfold tailWord_3656755
  simp only [CollatzResearch.WordTrace]
  refine ⟨133372811867208633878211719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88915207911472422585474479 133372811867208633878211719)
  ·
    refine ⟨200059217800812950817317579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133372811867208633878211719 200059217800812950817317579)
    ·
      refine ⟨300088826701219426225976369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200059217800812950817317579 300088826701219426225976369)
      ·
        refine ⟨225066620025914569669482277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300088826701219426225976369 225066620025914569669482277)
        ·
          refine ⟨42199991254858981813027927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225066620025914569669482277 42199991254858981813027927)
          ·
            refine ⟨63299986882288472719541891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42199991254858981813027927 63299986882288472719541891)
            ·
              refine ⟨94949980323432709079312837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63299986882288472719541891 94949980323432709079312837)
              ·
                refine ⟨17803121310643632952371157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94949980323432709079312837 17803121310643632952371157)
                ·
                  refine ⟨417260655718210147321199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17803121310643632952371157 417260655718210147321199)
                  ·
                    rfl

theorem cell22_3656755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_3656755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656755 prefixEnd_3656755 := by exact prefixLift 3656755
  have htrace : WordTrace (prefixWord ++ tailWord_3656755) baseStart_3656755 baseEnd_3656755 := by
    simpa [prefixWord, tailWord_3656755, baseEnd_3656755] using wordTrace_append hprefix tailTrace_3656755
  have hstable : (prefixWord ++ tailWord_3656755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656755).length < 2 ^ (prefixWord ++ tailWord_3656755).sum := by decide
  have hdescent : baseEnd_3656755 < baseStart_3656755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656789 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 5]
def baseStart_3656789 : Nat := 118140960795 + 3656789 * 2 ^ 59
def prefixEnd_3656789 : Nat := 4983230072969 + 3 ^ 40 * 3656789 * 2
def baseEnd_3656789 : Nat := 417264535349821895537831

theorem tailTrace_3656789 : CollatzResearch.WordTrace tailWord_3656789 prefixEnd_3656789 417264535349821895537831 := by
  unfold tailWord_3656789
  simp only [CollatzResearch.WordTrace]
  refine ⟨133374051949085457684949421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88916034632723638456632947 133374051949085457684949421)
  ·
    refine ⟨50015269480907046631856033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133374051949085457684949421 50015269480907046631856033)
    ·
      refine ⟨37511452110680284973892025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50015269480907046631856033 37511452110680284973892025)
      ·
        refine ⟨28133589083010213730419019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37511452110680284973892025 28133589083010213730419019)
        ·
          refine ⟨42200383624515320595628529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28133589083010213730419019 42200383624515320595628529)
          ·
            refine ⟨31650287718386490446721397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42200383624515320595628529 31650287718386490446721397)
            ·
              refine ⟨2967214473598733479380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31650287718386490446721397 2967214473598733479380131)
              ·
                refine ⟨4450821710398100219070197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967214473598733479380131 4450821710398100219070197)
                ·
                  refine ⟨417264535349821895537831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4450821710398100219070197 417264535349821895537831)
                  ·
                    rfl

theorem cell22_3656789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_3656789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656789 prefixEnd_3656789 := by exact prefixLift 3656789
  have htrace : WordTrace (prefixWord ++ tailWord_3656789) baseStart_3656789 baseEnd_3656789 := by
    simpa [prefixWord, tailWord_3656789, baseEnd_3656789] using wordTrace_append hprefix tailTrace_3656789
  have hstable : (prefixWord ++ tailWord_3656789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656789).length < 2 ^ (prefixWord ++ tailWord_3656789).sum := by decide
  have hdescent : baseEnd_3656789 < baseStart_3656789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656864 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_3656864 : Nat := 118140960795 + 3656864 * 2 ^ 59
def prefixEnd_3656864 : Nat := 4983230072969 + 3 ^ 40 * 3656864 * 2
def baseEnd_3656864 : Nat := 1251819280082190490988263

theorem tailTrace_3656864 : CollatzResearch.WordTrace tailWord_3656864 prefixEnd_3656864 1251819280082190490988263 := by
  unfold tailWord_3656864
  simp only [CollatzResearch.WordTrace]
  refine ⟨66688393711906872746964823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88917858282542496995953097 66688393711906872746964823)
  ·
    refine ⟨100032590567860309120447235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66688393711906872746964823 100032590567860309120447235)
    ·
      refine ⟨150048885851790463680670853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100032590567860309120447235 150048885851790463680670853)
      ·
        refine ⟨28134166097210711940125785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150048885851790463680670853 28134166097210711940125785)
        ·
          refine ⟨21100624572908033955094339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28134166097210711940125785 21100624572908033955094339)
          ·
            refine ⟨31650936859362050932641509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21100624572908033955094339 31650936859362050932641509)
            ·
              refine ⟨5934550661130384549870283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31650936859362050932641509 5934550661130384549870283)
              ·
                refine ⟨8901825991695576824805425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5934550661130384549870283 8901825991695576824805425)
                ·
                  refine ⟨6676369493771682618604069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8901825991695576824805425 6676369493771682618604069)
                  ·
                    refine ⟨1251819280082190490988263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676369493771682618604069 1251819280082190490988263)
                    ·
                      rfl

theorem cell22_3656864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_3656864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656864 prefixEnd_3656864 := by exact prefixLift 3656864
  have htrace : WordTrace (prefixWord ++ tailWord_3656864) baseStart_3656864 baseEnd_3656864 := by
    simpa [prefixWord, tailWord_3656864, baseEnd_3656864] using wordTrace_append hprefix tailTrace_3656864
  have hstable : (prefixWord ++ tailWord_3656864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656864).length < 2 ^ (prefixWord ++ tailWord_3656864).sum := by decide
  have hdescent : baseEnd_3656864 < baseStart_3656864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656866 : List Nat := [3, 3, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3656866 : Nat := 118140960795 + 3656866 * 2 ^ 59
def prefixEnd_3656866 : Nat := 4983230072969 + 3 ^ 40 * 3656866 * 2
def baseEnd_3656866 : Nat := 1251819964723063152438257

theorem tailTrace_3656866 : CollatzResearch.WordTrace tailWord_3656866 prefixEnd_3656866 1251819964723063152438257 := by
  unfold tailWord_3656866
  simp only [CollatzResearch.WordTrace]
  refine ⟨33344215092451624958875613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88917906913204333223668301 33344215092451624958875613)
  ·
    refine ⟨12504080659669359359578355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33344215092451624958875613 12504080659669359359578355)
    ·
      refine ⟨18756120989504039039367533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12504080659669359359578355 18756120989504039039367533)
      ·
        refine ⟨7033545371064014639762825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18756120989504039039367533 7033545371064014639762825)
        ·
          refine ⟨5275159028298010979822119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7033545371064014639762825 5275159028298010979822119)
          ·
            refine ⟨7912738542447016469733179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275159028298010979822119 7912738542447016469733179)
            ·
              refine ⟨11869107813670524704599769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7912738542447016469733179 11869107813670524704599769)
              ·
                refine ⟨8901830860252893528449827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11869107813670524704599769 8901830860252893528449827)
                ·
                  refine ⟨13352746290379340292674741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8901830860252893528449827 13352746290379340292674741)
                  ·
                    refine ⟨1251819964723063152438257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13352746290379340292674741 1251819964723063152438257)
                    ·
                      rfl

theorem cell22_3656866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3656866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656866 prefixEnd_3656866 := by exact prefixLift 3656866
  have htrace : WordTrace (prefixWord ++ tailWord_3656866) baseStart_3656866 baseEnd_3656866 := by
    simpa [prefixWord, tailWord_3656866, baseEnd_3656866] using wordTrace_append hprefix tailTrace_3656866
  have hstable : (prefixWord ++ tailWord_3656866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656866).length < 2 ^ (prefixWord ++ tailWord_3656866).sum := by decide
  have hdescent : baseEnd_3656866 < baseStart_3656866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656896 : List Nat := [2, 1, 1, 2, 7, 1, 1, 7]
def baseStart_3656896 : Nat := 118140960795 + 3656896 * 2 ^ 59
def prefixEnd_3656896 : Nat := 4983230072969 + 3 ^ 40 * 3656896 * 2
def baseEnd_3656896 : Nat := 139092248259572563798685

theorem tailTrace_3656896 : CollatzResearch.WordTrace tailWord_3656896 prefixEnd_3656896 139092248259572563798685 := by
  unfold tailWord_3656896
  simp only [CollatzResearch.WordTrace]
  refine ⟨66688977279848907479547271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88918636373131876639396361 66688977279848907479547271)
  ·
    refine ⟨100033465919773361219320907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66688977279848907479547271 100033465919773361219320907)
    ·
      refine ⟨150050198879660041828981361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100033465919773361219320907 150050198879660041828981361)
      ·
        refine ⟨112537649159745031371736021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150050198879660041828981361 112537649159745031371736021)
        ·
          refine ⟨2637601152181524172775063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 112537649159745031371736021 2637601152181524172775063)
          ·
            refine ⟨3956401728272286259162595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2637601152181524172775063 3956401728272286259162595)
            ·
              refine ⟨5934602592408429388743893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3956401728272286259162595 5934602592408429388743893)
              ·
                refine ⟨139092248259572563798685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5934602592408429388743893 139092248259572563798685)
                ·
                  rfl

theorem cell22_3656896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_3656896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656896 prefixEnd_3656896 := by exact prefixLift 3656896
  have htrace : WordTrace (prefixWord ++ tailWord_3656896) baseStart_3656896 baseEnd_3656896 := by
    simpa [prefixWord, tailWord_3656896, baseEnd_3656896] using wordTrace_append hprefix tailTrace_3656896
  have hstable : (prefixWord ++ tailWord_3656896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656896).length < 2 ^ (prefixWord ++ tailWord_3656896).sum := by decide
  have hdescent : baseEnd_3656896 < baseStart_3656896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3656922 : Nat := 118140960795 + 3656922 * 2 ^ 59
def prefixEnd_3656922 : Nat := 4983230072969 + 3 ^ 40 * 3656922 * 2
def baseEnd_3656922 : Nat := 1251839134667497673038085

theorem tailTrace_3656922 : CollatzResearch.WordTrace tailWord_3656922 prefixEnd_3656922 1251839134667497673038085 := by
  unfold tailWord_3656922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33344725714400905349885255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88919268571735747599694013 33344725714400905349885255)
  ·
    refine ⟨50017088571601358024827883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33344725714400905349885255 50017088571601358024827883)
    ·
      refine ⟨75025632857402037037241825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50017088571601358024827883 75025632857402037037241825)
      ·
        refine ⟨56269224643051527777931369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75025632857402037037241825 56269224643051527777931369)
        ·
          refine ⟨42201918482288645833448527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56269224643051527777931369 42201918482288645833448527)
          ·
            refine ⟨63302877723432968750172791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42201918482288645833448527 63302877723432968750172791)
            ·
              refine ⟨94954316585149453125259187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63302877723432968750172791 94954316585149453125259187)
              ·
                refine ⟨142431474877724179687888781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94954316585149453125259187 142431474877724179687888781)
                ·
                  refine ⟨53411803079146567382958293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142431474877724179687888781 53411803079146567382958293)
                  ·
                    refine ⟨1251839134667497673038085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53411803079146567382958293 1251839134667497673038085)
                    ·
                      rfl

theorem cell22_3656922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3656922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656922 prefixEnd_3656922 := by exact prefixLift 3656922
  have htrace : WordTrace (prefixWord ++ tailWord_3656922) baseStart_3656922 baseEnd_3656922 := by
    simpa [prefixWord, tailWord_3656922, baseEnd_3656922] using wordTrace_append hprefix tailTrace_3656922
  have hstable : (prefixWord ++ tailWord_3656922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656922).length < 2 ^ (prefixWord ++ tailWord_3656922).sum := by decide
  have hdescent : baseEnd_3656922 < baseStart_3656922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656928 : List Nat := [2, 1, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_3656928 : Nat := 118140960795 + 3656928 * 2 ^ 59
def prefixEnd_3656928 : Nat := 4983230072969 + 3 ^ 40 * 3656928 * 2
def baseEnd_3656928 : Nat := 1251841188590115657388067

theorem tailTrace_3656928 : CollatzResearch.WordTrace tailWord_3656928 prefixEnd_3656928 1251841188590115657388067 := by
  unfold tailWord_3656928
  simp only [CollatzResearch.WordTrace]
  refine ⟨66689560847790942212129719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88919414463721256282839625 66689560847790942212129719)
  ·
    refine ⟨100034341271686413318194579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66689560847790942212129719 100034341271686413318194579)
    ·
      refine ⟨150051511907529619977291869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100034341271686413318194579 150051511907529619977291869)
      ·
        refine ⟨56269316965323607491484451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150051511907529619977291869 56269316965323607491484451)
        ·
          refine ⟨84403975447985411237226677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56269316965323607491484451 84403975447985411237226677)
          ·
            refine ⟨7912872698248632303490001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84403975447985411237226677 7912872698248632303490001)
            ·
              refine ⟨5934654523686474227617501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912872698248632303490001 5934654523686474227617501)
              ·
                refine ⟨2225495446382427835356563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5934654523686474227617501 2225495446382427835356563)
                ·
                  refine ⟨3338243169573641753034845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2225495446382427835356563 3338243169573641753034845)
                  ·
                    refine ⟨1251841188590115657388067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338243169573641753034845 1251841188590115657388067)
                    ·
                      rfl

theorem cell22_3656928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_3656928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656928 prefixEnd_3656928 := by exact prefixLift 3656928
  have htrace : WordTrace (prefixWord ++ tailWord_3656928) baseStart_3656928 baseEnd_3656928 := by
    simpa [prefixWord, tailWord_3656928, baseEnd_3656928] using wordTrace_append hprefix tailTrace_3656928
  have hstable : (prefixWord ++ tailWord_3656928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656928).length < 2 ^ (prefixWord ++ tailWord_3656928).sum := by decide
  have hdescent : baseEnd_3656928 < baseStart_3656928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656941 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3656941 : Nat := 118140960795 + 3656941 * 2 ^ 59
def prefixEnd_3656941 : Nat := 4983230072969 + 3 ^ 40 * 3656941 * 2
def baseEnd_3656941 : Nat := 417281879585262652271009

theorem tailTrace_3656941 : CollatzResearch.WordTrace tailWord_3656941 prefixEnd_3656941 417281879585262652271009 := by
  unfold tailWord_3656941
  simp only [CollatzResearch.WordTrace]
  refine ⟨133379595844534787644482677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88919730563023191762988451 133379595844534787644482677)
  ·
    refine ⟨12504337110425136341670251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133379595844534787644482677 12504337110425136341670251)
    ·
      refine ⟨18756505665637704512505377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12504337110425136341670251 18756505665637704512505377)
      ·
        refine ⟨14067379249228278384379033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18756505665637704512505377 14067379249228278384379033)
        ·
          refine ⟨10550534436921208788284275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14067379249228278384379033 10550534436921208788284275)
          ·
            refine ⟨15825801655381813182426413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10550534436921208788284275 15825801655381813182426413)
            ·
              refine ⟨5934675620768179943409905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15825801655381813182426413 5934675620768179943409905)
              ·
                refine ⟨4451006715576134957557429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934675620768179943409905 4451006715576134957557429)
                ·
                  refine ⟨417281879585262652271009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451006715576134957557429 417281879585262652271009)
                  ·
                    rfl

theorem cell22_3656941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3656941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656941 prefixEnd_3656941 := by exact prefixLift 3656941
  have htrace : WordTrace (prefixWord ++ tailWord_3656941) baseStart_3656941 baseEnd_3656941 := by
    simpa [prefixWord, tailWord_3656941, baseEnd_3656941] using wordTrace_append hprefix tailTrace_3656941
  have hstable : (prefixWord ++ tailWord_3656941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656941).length < 2 ^ (prefixWord ++ tailWord_3656941).sum := by decide
  have hdescent : baseEnd_3656941 < baseStart_3656941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656958 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3656958 : Nat := 118140960795 + 3656958 * 2 ^ 59
def prefixEnd_3656958 : Nat := 4983230072969 + 3 ^ 40 * 3656958 * 2
def baseEnd_3656958 : Nat := 417283819401068526379325

theorem tailTrace_3656958 : CollatzResearch.WordTrace tailWord_3656958 prefixEnd_3656958 417283819401068526379325 := by
  unfold tailWord_3656958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16672526985684149943481441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88920143923648799698567685 16672526985684149943481441)
  ·
    refine ⟨12504395239263112457611081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16672526985684149943481441 12504395239263112457611081)
    ·
      refine ⟨9378296429447334343208311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12504395239263112457611081 9378296429447334343208311)
      ·
        refine ⟨14067444644171001514812467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9378296429447334343208311 14067444644171001514812467)
        ·
          refine ⟨21101166966256502272218701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14067444644171001514812467 21101166966256502272218701)
          ·
            refine ⟨7912937612346188352082013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21101166966256502272218701 7912937612346188352082013)
            ·
              refine ⟨2967351604629820632030755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7912937612346188352082013 2967351604629820632030755)
              ·
                refine ⟨4451027406944730948046133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967351604629820632030755 4451027406944730948046133)
                ·
                  refine ⟨417283819401068526379325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451027406944730948046133 417283819401068526379325)
                  ·
                    rfl

theorem cell22_3656958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3656958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656958 prefixEnd_3656958 := by exact prefixLift 3656958
  have htrace : WordTrace (prefixWord ++ tailWord_3656958) baseStart_3656958 baseEnd_3656958 := by
    simpa [prefixWord, tailWord_3656958, baseEnd_3656958] using wordTrace_append hprefix tailTrace_3656958
  have hstable : (prefixWord ++ tailWord_3656958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656958).length < 2 ^ (prefixWord ++ tailWord_3656958).sum := by decide
  have hdescent : baseEnd_3656958 < baseStart_3656958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3656971 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 1, 4]
def baseStart_3656971 : Nat := 118140960795 + 3656971 * 2 ^ 59
def prefixEnd_3656971 : Nat := 4983230072969 + 3 ^ 40 * 3656971 * 2
def baseEnd_3656971 : Nat := 1251855908368877878562935

theorem tailTrace_3656971 : CollatzResearch.WordTrace tailWord_3656971 prefixEnd_3656971 1251855908368877878562935 := by
  unfold tailWord_3656971
  simp only [CollatzResearch.WordTrace]
  refine ⟨133380690034426102768074767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88920460022950735178716511 133380690034426102768074767)
  ·
    refine ⟨200071035051639154152112151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133380690034426102768074767 200071035051639154152112151)
    ·
      refine ⟨300106552577458731228168227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200071035051639154152112151 300106552577458731228168227)
      ·
        refine ⟨450159828866188096842252341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300106552577458731228168227 450159828866188096842252341)
        ·
          refine ⟨42202483956205134078961157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450159828866188096842252341 42202483956205134078961157)
          ·
            refine ⟨7912965741788462639805217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42202483956205134078961157 7912965741788462639805217)
            ·
              refine ⟨5934724306341346979853913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7912965741788462639805217 5934724306341346979853913)
              ·
                refine ⟨4451043229756010234890435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5934724306341346979853913 4451043229756010234890435)
                ·
                  refine ⟨6676564844634015352335653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451043229756010234890435 6676564844634015352335653)
                  ·
                    refine ⟨1251855908368877878562935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6676564844634015352335653 1251855908368877878562935)
                    ·
                      rfl

theorem cell22_3656971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 4].length) (baseStart_3656971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3656971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3656971 prefixEnd_3656971 := by exact prefixLift 3656971
  have htrace : WordTrace (prefixWord ++ tailWord_3656971) baseStart_3656971 baseEnd_3656971 := by
    simpa [prefixWord, tailWord_3656971, baseEnd_3656971] using wordTrace_append hprefix tailTrace_3656971
  have hstable : (prefixWord ++ tailWord_3656971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3656971).length < 2 ^ (prefixWord ++ tailWord_3656971).sum := by decide
  have hdescent : baseEnd_3656971 < baseStart_3656971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3656971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657172 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_3657172 : Nat := 118140960795 + 3657172 * 2 ^ 59
def prefixEnd_3657172 : Nat := 4983230072969 + 3 ^ 40 * 3657172 * 2
def baseEnd_3657172 : Nat := 417308238258860118095773

theorem tailTrace_3657172 : CollatzResearch.WordTrace tailWord_3657172 prefixEnd_3657172 417308238258860118095773 := by
  unfold tailWord_3657172
  simp only [CollatzResearch.WordTrace]
  refine ⟨66694010553348957048070885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88925347404465276064094513 66694010553348957048070885)
  ·
    refine ⟨12505126978752929446513291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66694010553348957048070885 12505126978752929446513291)
    ·
      refine ⟨18757690468129394169769937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12505126978752929446513291 18757690468129394169769937)
      ·
        refine ⟨14068267851097045627327453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18757690468129394169769937 14068267851097045627327453)
        ·
          refine ⟨5275600444161392110247795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14068267851097045627327453 5275600444161392110247795)
          ·
            refine ⟨7913400666242088165371693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275600444161392110247795 7913400666242088165371693)
            ·
              refine ⟨2967525249840783062014385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7913400666242088165371693 2967525249840783062014385)
              ·
                refine ⟨2225643937380587296510789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2967525249840783062014385 2225643937380587296510789)
                ·
                  refine ⟨417308238258860118095773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225643937380587296510789 417308238258860118095773)
                  ·
                    rfl

theorem cell22_3657172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_3657172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657172 prefixEnd_3657172 := by exact prefixLift 3657172
  have htrace : WordTrace (prefixWord ++ tailWord_3657172) baseStart_3657172 baseEnd_3657172 := by
    simpa [prefixWord, tailWord_3657172, baseEnd_3657172] using wordTrace_append hprefix tailTrace_3657172
  have hstable : (prefixWord ++ tailWord_3657172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657172).length < 2 ^ (prefixWord ++ tailWord_3657172).sum := by decide
  have hdescent : baseEnd_3657172 < baseStart_3657172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 8]
def baseStart_3657179 : Nat := 118140960795 + 3657179 * 2 ^ 59
def prefixEnd_3657179 : Nat := 4983230072969 + 3 ^ 40 * 3657179 * 2
def baseEnd_3657179 : Nat := 1251927111019634669362297

theorem tailTrace_3657179 : CollatzResearch.WordTrace tailWord_3657179 prefixEnd_3657179 1251927111019634669362297 := by
  unfold tailWord_3657179
  simp only [CollatzResearch.WordTrace]
  refine ⟨133388276417672554291646591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88925517611781702861097727 133388276417672554291646591)
  ·
    refine ⟨200082414626508831437469887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133388276417672554291646591 200082414626508831437469887)
    ·
      refine ⟨300123621939763247156204831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200082414626508831437469887 300123621939763247156204831)
      ·
        refine ⟨450185432909644870734307247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300123621939763247156204831 450185432909644870734307247)
        ·
          refine ⟨675278149364467306101460871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450185432909644870734307247 675278149364467306101460871)
          ·
            refine ⟨1012917224046700959152191307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 675278149364467306101460871 1012917224046700959152191307)
            ·
              refine ⟨1519375836070051438728286961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1012917224046700959152191307 1519375836070051438728286961)
              ·
                refine ⟨1139531877052538579046215221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519375836070051438728286961 1139531877052538579046215221)
                ·
                  refine ⟨106831113473675491785582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1139531877052538579046215221 106831113473675491785582677)
                  ·
                    refine ⟨1251927111019634669362297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106831113473675491785582677 1251927111019634669362297)
                    ·
                      rfl

theorem cell22_3657179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 8].length) (baseStart_3657179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657179 prefixEnd_3657179 := by exact prefixLift 3657179
  have htrace : WordTrace (prefixWord ++ tailWord_3657179) baseStart_3657179 baseEnd_3657179 := by
    simpa [prefixWord, tailWord_3657179, baseEnd_3657179] using wordTrace_append hprefix tailTrace_3657179
  have hstable : (prefixWord ++ tailWord_3657179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657179).length < 2 ^ (prefixWord ++ tailWord_3657179).sum := by decide
  have hdescent : baseEnd_3657179 < baseStart_3657179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657187 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 2, 3]
def baseStart_3657187 : Nat := 118140960795 + 3657187 * 2 ^ 59
def prefixEnd_3657187 : Nat := 4983230072969 + 3 ^ 40 * 3657187 * 2
def baseEnd_3657187 : Nat := 1251929849583125315162273

theorem tailTrace_3657187 : CollatzResearch.WordTrace tailWord_3657187 prefixEnd_3657187 1251929849583125315162273 := by
  unfold tailWord_3657187
  simp only [CollatzResearch.WordTrace]
  refine ⟨133388568201643571657937815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88925712134429047771958543 133388568201643571657937815)
  ·
    refine ⟨200082852302465357486906723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133388568201643571657937815 200082852302465357486906723)
    ·
      refine ⟨300124278453698036230360085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200082852302465357486906723 300124278453698036230360085)
      ·
        refine ⟨14068325552517095448298129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 300124278453698036230360085 14068325552517095448298129)
        ·
          refine ⟨10551244164387821586223597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14068325552517095448298129 10551244164387821586223597)
          ·
            refine ⟨3956716561645433094833849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10551244164387821586223597 3956716561645433094833849)
            ·
              refine ⟨2967537421234074821125387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3956716561645433094833849 2967537421234074821125387)
              ·
                refine ⟨4451306131851112231688081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967537421234074821125387 4451306131851112231688081)
                ·
                  refine ⟨3338479598888334173766061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451306131851112231688081 3338479598888334173766061)
                  ·
                    refine ⟨1251929849583125315162273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338479598888334173766061 1251929849583125315162273)
                    ·
                      rfl

theorem cell22_3657187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 2, 3].length) (baseStart_3657187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657187 prefixEnd_3657187 := by exact prefixLift 3657187
  have htrace : WordTrace (prefixWord ++ tailWord_3657187) baseStart_3657187 baseEnd_3657187 := by
    simpa [prefixWord, tailWord_3657187, baseEnd_3657187] using wordTrace_append hprefix tailTrace_3657187
  have hstable : (prefixWord ++ tailWord_3657187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657187).length < 2 ^ (prefixWord ++ tailWord_3657187).sum := by decide
  have hdescent : baseEnd_3657187 < baseStart_3657187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657198 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3657198 : Nat := 118140960795 + 3657198 * 2 ^ 59
def prefixEnd_3657198 : Nat := 4983230072969 + 3 ^ 40 * 3657198 * 2
def baseEnd_3657198 : Nat := 1251933615107924953137239

theorem tailTrace_3657198 : CollatzResearch.WordTrace tailWord_3657198 prefixEnd_3657198 1251933615107924953137239 := by
  unfold tailWord_3657198
  simp only [CollatzResearch.WordTrace]
  refine ⟨16673621175575465067073531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88925979603069147024392165 16673621175575465067073531)
  ·
    refine ⟨25010431763363197600610297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16673621175575465067073531 25010431763363197600610297)
    ·
      refine ⟨18757823822522398200457723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25010431763363197600610297 18757823822522398200457723)
      ·
        refine ⟨28136735733783597300686585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18757823822522398200457723 28136735733783597300686585)
        ·
          refine ⟨21102551800337697975514939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28136735733783597300686585 21102551800337697975514939)
          ·
            refine ⟨31653827700506546963272409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21102551800337697975514939 31653827700506546963272409)
            ·
              refine ⟨23740370775379910222454307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31653827700506546963272409 23740370775379910222454307)
              ·
                refine ⟨35610556163069865333681461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23740370775379910222454307 35610556163069865333681461)
                ·
                  refine ⟨3338489640287799875032637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35610556163069865333681461 3338489640287799875032637)
                  ·
                    refine ⟨1251933615107924953137239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338489640287799875032637 1251933615107924953137239)
                    ·
                      rfl

theorem cell22_3657198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3657198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657198 prefixEnd_3657198 := by exact prefixLift 3657198
  have htrace : WordTrace (prefixWord ++ tailWord_3657198) baseStart_3657198 baseEnd_3657198 := by
    simpa [prefixWord, tailWord_3657198, baseEnd_3657198] using wordTrace_append hprefix tailTrace_3657198
  have hstable : (prefixWord ++ tailWord_3657198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657198).length < 2 ^ (prefixWord ++ tailWord_3657198).sum := by decide
  have hdescent : baseEnd_3657198 < baseStart_3657198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657258 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3657258 : Nat := 118140960795 + 3657258 * 2 ^ 59
def prefixEnd_3657258 : Nat := 4983230072969 + 3 ^ 40 * 3657258 * 2
def baseEnd_3657258 : Nat := 1251954154334104796637055

theorem tailTrace_3657258 : CollatzResearch.WordTrace tailWord_3657258 prefixEnd_3657258 1251954154334104796637055 := by
  unfold tailWord_3657258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33347789446096587695943107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88927438522924233855848285 33347789446096587695943107)
  ·
    refine ⟨50021684169144881543914661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33347789446096587695943107 50021684169144881543914661)
    ·
      refine ⟨9379065781714665289483999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50021684169144881543914661 9379065781714665289483999)
      ·
        refine ⟨14068598672571997934225999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9379065781714665289483999 14068598672571997934225999)
        ·
          refine ⟨21102898008857996901338999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14068598672571997934225999 21102898008857996901338999)
          ·
            refine ⟨31654347013286995352008499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21102898008857996901338999 31654347013286995352008499)
            ·
              refine ⟨47481520519930493028012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31654347013286995352008499 47481520519930493028012749)
              ·
                refine ⟨17805570194973934885504781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47481520519930493028012749 17805570194973934885504781)
                ·
                  refine ⟨6677088823115225582064293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17805570194973934885504781 6677088823115225582064293)
                  ·
                    refine ⟨1251954154334104796637055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677088823115225582064293 1251954154334104796637055)
                    ·
                      rfl

theorem cell22_3657258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3657258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657258 prefixEnd_3657258 := by exact prefixLift 3657258
  have htrace : WordTrace (prefixWord ++ tailWord_3657258) baseStart_3657258 baseEnd_3657258 := by
    simpa [prefixWord, tailWord_3657258, baseEnd_3657258] using wordTrace_append hprefix tailTrace_3657258
  have hstable : (prefixWord ++ tailWord_3657258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657258).length < 2 ^ (prefixWord ++ tailWord_3657258).sum := by decide
  have hdescent : baseEnd_3657258 < baseStart_3657258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657301 : List Nat := [1, 3, 2, 2, 1, 1, 1, 11]
def baseStart_3657301 : Nat := 118140960795 + 3657301 * 2 ^ 59
def prefixEnd_3657301 : Nat := 4983230072969 + 3 ^ 40 * 3657301 * 2
def baseEnd_3657301 : Nat := 139107652679207446423547

theorem tailTrace_3657301 : CollatzResearch.WordTrace tailWord_3657301 prefixEnd_3657301 139107652679207446423547 := by
  unfold tailWord_3657301
  simp only [CollatzResearch.WordTrace]
  refine ⟨133392726123230569127587757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88928484082153712751725171 133392726123230569127587757)
  ·
    refine ⟨50022272296211463422845409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133392726123230569127587757 50022272296211463422845409)
    ·
      refine ⟨37516704222158597567134057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50022272296211463422845409 37516704222158597567134057)
      ·
        refine ⟨28137528166618948175350543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37516704222158597567134057 28137528166618948175350543)
        ·
          refine ⟨42206292249928422263025815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28137528166618948175350543 42206292249928422263025815)
          ·
            refine ⟨63309438374892633394538723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42206292249928422263025815 63309438374892633394538723)
            ·
              refine ⟨94964157562338950091808085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63309438374892633394538723 94964157562338950091808085)
              ·
                refine ⟨139107652679207446423547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 94964157562338950091808085 139107652679207446423547)
                ·
                  rfl

theorem cell22_3657301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 11].length) (baseStart_3657301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657301 prefixEnd_3657301 := by exact prefixLift 3657301
  have htrace : WordTrace (prefixWord ++ tailWord_3657301) baseStart_3657301 baseEnd_3657301 := by
    simpa [prefixWord, tailWord_3657301, baseEnd_3657301] using wordTrace_append hprefix tailTrace_3657301
  have hstable : (prefixWord ++ tailWord_3657301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657301).length < 2 ^ (prefixWord ++ tailWord_3657301).sum := by decide
  have hdescent : baseEnd_3657301 < baseStart_3657301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657309 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3657309 : Nat := 118140960795 + 3657309 * 2 ^ 59
def prefixEnd_3657309 : Nat := 4983230072969 + 3 ^ 40 * 3657309 * 2
def baseEnd_3657309 : Nat := 1251971612676357663611899

theorem tailTrace_3657309 : CollatzResearch.WordTrace tailWord_3657309 prefixEnd_3657309 1251971612676357663611899 := by
  unfold tailWord_3657309
  simp only [CollatzResearch.WordTrace]
  refine ⟨133393017907201586493878981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88928678604801057662585987 133393017907201586493878981)
  ·
    refine ⟨25011190857600297467602309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133393017907201586493878981 25011190857600297467602309)
    ·
      refine ⟨4689598285800055775175433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25011190857600297467602309 4689598285800055775175433)
      ·
        refine ⟨3517198714350041831381575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4689598285800055775175433 3517198714350041831381575)
        ·
          refine ⟨5275798071525062747072363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3517198714350041831381575 5275798071525062747072363)
          ·
            refine ⟨7913697107287594120608545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275798071525062747072363 7913697107287594120608545)
            ·
              refine ⟨5935272830465695590456409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913697107287594120608545 5935272830465695590456409)
              ·
                refine ⟨4451454622849271692842307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935272830465695590456409 4451454622849271692842307)
                ·
                  refine ⟨6677181934273907539263461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4451454622849271692842307 6677181934273907539263461)
                  ·
                    refine ⟨1251971612676357663611899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677181934273907539263461 1251971612676357663611899)
                    ·
                      rfl

theorem cell22_3657309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3657309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657309 prefixEnd_3657309 := by exact prefixLift 3657309
  have htrace : WordTrace (prefixWord ++ tailWord_3657309) baseStart_3657309 baseEnd_3657309 := by
    simpa [prefixWord, tailWord_3657309, baseEnd_3657309] using wordTrace_append hprefix tailTrace_3657309
  have hstable : (prefixWord ++ tailWord_3657309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657309).length < 2 ^ (prefixWord ++ tailWord_3657309).sum := by decide
  have hdescent : baseEnd_3657309 < baseStart_3657309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657397 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 5]
def baseStart_3657397 : Nat := 118140960795 + 3657397 * 2 ^ 59
def prefixEnd_3657397 : Nat := 4983230072969 + 3 ^ 40 * 3657397 * 2
def baseEnd_3657397 : Nat := 417333912291584922470543

theorem tailTrace_3657397 : CollatzResearch.WordTrace tailWord_3657397 prefixEnd_3657397 417333912291584922470543 := by
  unfold tailWord_3657397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133396227530882777523082445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88930818353921851682054963 133396227530882777523082445)
  ·
    refine ⟨50023585324081041571155917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133396227530882777523082445 50023585324081041571155917)
    ·
      refine ⟨18758844496530390589183469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50023585324081041571155917 18758844496530390589183469)
      ·
        refine ⟨7034566686198896470943801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18758844496530390589183469 7034566686198896470943801)
        ·
          refine ⟨5275925014649172353207851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7034566686198896470943801 5275925014649172353207851)
          ·
            refine ⟨7913887521973758529811777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5275925014649172353207851 7913887521973758529811777)
            ·
              refine ⟨5935415641480318897358833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7913887521973758529811777 5935415641480318897358833)
              ·
                refine ⟨4451561731110239173019125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935415641480318897358833 4451561731110239173019125)
                ·
                  refine ⟨417333912291584922470543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451561731110239173019125 417333912291584922470543)
                  ·
                    rfl

theorem cell22_3657397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_3657397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657397 prefixEnd_3657397 := by exact prefixLift 3657397
  have htrace : WordTrace (prefixWord ++ tailWord_3657397) baseStart_3657397 baseEnd_3657397 := by
    simpa [prefixWord, tailWord_3657397, baseEnd_3657397] using wordTrace_append hprefix tailTrace_3657397
  have hstable : (prefixWord ++ tailWord_3657397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657397).length < 2 ^ (prefixWord ++ tailWord_3657397).sum := by decide
  have hdescent : baseEnd_3657397 < baseStart_3657397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657408 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_3657408 : Nat := 118140960795 + 3657408 * 2 ^ 59
def prefixEnd_3657408 : Nat := 4983230072969 + 3 ^ 40 * 3657408 * 2
def baseEnd_3657408 : Nat := 417335167466518135128865

theorem tailTrace_3657408 : CollatzResearch.WordTrace tailWord_3657408 prefixEnd_3657408 417335167466518135128865 := by
  unfold tailWord_3657408
  simp only [CollatzResearch.WordTrace]
  refine ⟨66698314366921463200866439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88931085822561950934488585 66698314366921463200866439)
  ·
    refine ⟨100047471550382194801299659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66698314366921463200866439 100047471550382194801299659)
    ·
      refine ⟨150071207325573292201949489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100047471550382194801299659 150071207325573292201949489)
      ·
        refine ⟨112553405494179969151462117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150071207325573292201949489 112553405494179969151462117)
        ·
          refine ⟨21103763530158744215899147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112553405494179969151462117 21103763530158744215899147)
          ·
            refine ⟨31655645295238116323848721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21103763530158744215899147 31655645295238116323848721)
            ·
              refine ⟨23741733971428587242886541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31655645295238116323848721 23741733971428587242886541)
              ·
                refine ⟨8903150239285720216082453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23741733971428587242886541 8903150239285720216082453)
                ·
                  refine ⟨417335167466518135128865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8903150239285720216082453 417335167466518135128865)
                  ·
                    rfl

theorem cell22_3657408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_3657408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657408 prefixEnd_3657408 := by exact prefixLift 3657408
  have htrace : WordTrace (prefixWord ++ tailWord_3657408) baseStart_3657408 baseEnd_3657408 := by
    simpa [prefixWord, tailWord_3657408, baseEnd_3657408] using wordTrace_append hprefix tailTrace_3657408
  have hstable : (prefixWord ++ tailWord_3657408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657408).length < 2 ^ (prefixWord ++ tailWord_3657408).sum := by decide
  have hdescent : baseEnd_3657408 < baseStart_3657408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657414 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3657414 : Nat := 118140960795 + 3657414 * 2 ^ 59
def prefixEnd_3657414 : Nat := 4983230072969 + 3 ^ 40 * 3657414 * 2
def baseEnd_3657414 : Nat := 417335852107390796578859

theorem tailTrace_3657414 : CollatzResearch.WordTrace tailWord_3657414 prefixEnd_3657414 417335852107390796578859 := by
  unfold tailWord_3657414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168651486619412169576603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88931231714547459617634197 4168651486619412169576603)
  ·
    refine ⟨6252977229929118254364905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4168651486619412169576603 6252977229929118254364905)
    ·
      refine ⟨4689732922446838690773679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6252977229929118254364905 4689732922446838690773679)
      ·
        refine ⟨7034599383670258036160519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4689732922446838690773679 7034599383670258036160519)
        ·
          refine ⟨10551899075505387054240779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7034599383670258036160519 10551899075505387054240779)
          ·
            refine ⟨15827848613258080581361169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10551899075505387054240779 15827848613258080581361169)
            ·
              refine ⟨11870886459943560436020877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15827848613258080581361169 11870886459943560436020877)
              ·
                refine ⟨4451582422478835163507829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11870886459943560436020877 4451582422478835163507829)
                ·
                  refine ⟨417335852107390796578859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451582422478835163507829 417335852107390796578859)
                  ·
                    rfl

theorem cell22_3657414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3657414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657414 prefixEnd_3657414 := by exact prefixLift 3657414
  have htrace : WordTrace (prefixWord ++ tailWord_3657414) baseStart_3657414 baseEnd_3657414 := by
    simpa [prefixWord, tailWord_3657414, baseEnd_3657414] using wordTrace_append hprefix tailTrace_3657414
  have hstable : (prefixWord ++ tailWord_3657414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657414).length < 2 ^ (prefixWord ++ tailWord_3657414).sum := by decide
  have hdescent : baseEnd_3657414 < baseStart_3657414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657457 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 2, 3]
def baseStart_3657457 : Nat := 118140960795 + 3657457 * 2 ^ 59
def prefixEnd_3657457 : Nat := 4983230072969 + 3 ^ 40 * 3657457 * 2
def baseEnd_3657457 : Nat := 1252022276100934610911445

theorem tailTrace_3657457 : CollatzResearch.WordTrace tailWord_3657457 prefixEnd_3657457 1252022276100934610911445 := by
  unfold tailWord_3657457
  simp only [CollatzResearch.WordTrace]
  refine ⟨133398415910665407770266625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88932277273776938513511083 133398415910665407770266625)
  ·
    refine ⟨100048811932999055827699969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133398415910665407770266625 100048811932999055827699969)
    ·
      refine ⟨75036608949749291870774977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100048811932999055827699969 75036608949749291870774977)
      ·
        refine ⟨56277456712311968903081233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75036608949749291870774977 56277456712311968903081233)
        ·
          refine ⟨42208092534233976677310925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56277456712311968903081233 42208092534233976677310925)
          ·
            refine ⟨15828034700337741253991597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42208092534233976677310925 15828034700337741253991597)
            ·
              refine ⟨5935513012626652970246849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15828034700337741253991597 5935513012626652970246849)
              ·
                refine ⟨4451634759469989727685137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935513012626652970246849 4451634759469989727685137)
                ·
                  refine ⟨3338726069602492295763853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451634759469989727685137 3338726069602492295763853)
                  ·
                    refine ⟨1252022276100934610911445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338726069602492295763853 1252022276100934610911445)
                    ·
                      rfl

theorem cell22_3657457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_3657457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657457 prefixEnd_3657457 := by exact prefixLift 3657457
  have htrace : WordTrace (prefixWord ++ tailWord_3657457) baseStart_3657457 baseEnd_3657457 := by
    simpa [prefixWord, tailWord_3657457, baseEnd_3657457] using wordTrace_append hprefix tailTrace_3657457
  have hstable : (prefixWord ++ tailWord_3657457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657457).length < 2 ^ (prefixWord ++ tailWord_3657457).sum := by decide
  have hdescent : baseEnd_3657457 < baseStart_3657457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657483 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 2, 6]
def baseStart_3657483 : Nat := 118140960795 + 3657483 * 2 ^ 59
def prefixEnd_3657483 : Nat := 4983230072969 + 3 ^ 40 * 3657483 * 2
def baseEnd_3657483 : Nat := 1252031176432279209761365

theorem tailTrace_3657483 : CollatzResearch.WordTrace tailWord_3657483 prefixEnd_3657483 1252031176432279209761365 := by
  unfold tailWord_3657483
  simp only [CollatzResearch.WordTrace]
  refine ⟨133399364208571214210713103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88932909472380809473808735 133399364208571214210713103)
  ·
    refine ⟨200099046312856821316069655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133399364208571214210713103 200099046312856821316069655)
    ·
      refine ⟨300148569469285231974104483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200099046312856821316069655 300148569469285231974104483)
      ·
        refine ⟨450222854203927847961156725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300148569469285231974104483 450222854203927847961156725)
        ·
          refine ⟨42208392581618235746358443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 450222854203927847961156725 42208392581618235746358443)
          ·
            refine ⟨63312588872427353619537665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42208392581618235746358443 63312588872427353619537665)
            ·
              refine ⟨47484441654320515214653249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63312588872427353619537665 47484441654320515214653249)
              ·
                refine ⟨35613331240740386410989937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47484441654320515214653249 35613331240740386410989937)
                ·
                  refine ⟨26709998430555289808242453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35613331240740386410989937 26709998430555289808242453)
                  ·
                    refine ⟨1252031176432279209761365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26709998430555289808242453 1252031176432279209761365)
                    ·
                      rfl

theorem cell22_3657483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 6].length) (baseStart_3657483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657483 prefixEnd_3657483 := by exact prefixLift 3657483
  have htrace : WordTrace (prefixWord ++ tailWord_3657483) baseStart_3657483 baseEnd_3657483 := by
    simpa [prefixWord, tailWord_3657483, baseEnd_3657483] using wordTrace_append hprefix tailTrace_3657483
  have hstable : (prefixWord ++ tailWord_3657483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657483).length < 2 ^ (prefixWord ++ tailWord_3657483).sum := by decide
  have hdescent : baseEnd_3657483 < baseStart_3657483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657532 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_3657532 : Nat := 118140960795 + 3657532 * 2 ^ 59
def prefixEnd_3657532 : Nat := 4983230072969 + 3 ^ 40 * 3657532 * 2
def baseEnd_3657532 : Nat := 417349316711219805095405

theorem tailTrace_3657532 : CollatzResearch.WordTrace tailWord_3657532 prefixEnd_3657532 417349316711219805095405 := by
  unfold tailWord_3657532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66700575692696847789623425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88934100923595797052831233 66700575692696847789623425)
  ·
    refine ⟨50025431769522635842217569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66700575692696847789623425 50025431769522635842217569)
    ·
      refine ⟨37519073827141976881663177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50025431769522635842217569 37519073827141976881663177)
      ·
        refine ⟨28139305370356482661247383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37519073827141976881663177 28139305370356482661247383)
        ·
          refine ⟨42208958055534723991871075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28139305370356482661247383 42208958055534723991871075)
          ·
            refine ⟨63313437083302085987806613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42208958055534723991871075 63313437083302085987806613)
            ·
              refine ⟨2967817363279785280678435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63313437083302085987806613 2967817363279785280678435)
              ·
                refine ⟨4451726044919677921017653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2967817363279785280678435 4451726044919677921017653)
                ·
                  refine ⟨417349316711219805095405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4451726044919677921017653 417349316711219805095405)
                  ·
                    rfl

theorem cell22_3657532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_3657532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657532 prefixEnd_3657532 := by exact prefixLift 3657532
  have htrace : WordTrace (prefixWord ++ tailWord_3657532) baseStart_3657532 baseEnd_3657532 := by
    simpa [prefixWord, tailWord_3657532, baseEnd_3657532] using wordTrace_append hprefix tailTrace_3657532
  have hstable : (prefixWord ++ tailWord_3657532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657532).length < 2 ^ (prefixWord ++ tailWord_3657532).sum := by decide
  have hdescent : baseEnd_3657532 < baseStart_3657532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657545 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 3, 4]
def baseStart_3657545 : Nat := 118140960795 + 3657545 * 2 ^ 59
def prefixEnd_3657545 : Nat := 4983230072969 + 3 ^ 40 * 3657545 * 2
def baseEnd_3657545 : Nat := 1252052400299331714711175

theorem tailTrace_3657545 : CollatzResearch.WordTrace tailWord_3657545 prefixEnd_3657545 1252052400299331714711175 := by
  unfold tailWord_3657545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133401625534346598799470089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88934417022897732532980059 133401625534346598799470089)
  ·
    refine ⟨100051219150759949099602567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133401625534346598799470089 100051219150759949099602567)
    ·
      refine ⟨150076828726139923649403851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100051219150759949099602567 150076828726139923649403851)
      ·
        refine ⟨225115243089209885474105777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150076828726139923649403851 225115243089209885474105777)
        ·
          refine ⟨168836432316907414105579333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225115243089209885474105777 168836432316907414105579333)
          ·
            refine ⟨31656831059420140144796125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168836432316907414105579333 31656831059420140144796125)
            ·
              refine ⟨11871311647282552554298547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31656831059420140144796125 11871311647282552554298547)
              ·
                refine ⟨17806967470923828831447821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871311647282552554298547 17806967470923828831447821)
                ·
                  refine ⟨6677612801596435811792933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17806967470923828831447821 6677612801596435811792933)
                  ·
                    refine ⟨1252052400299331714711175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6677612801596435811792933 1252052400299331714711175)
                    ·
                      rfl

theorem cell22_3657545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 4].length) (baseStart_3657545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657545 prefixEnd_3657545 := by exact prefixLift 3657545
  have htrace : WordTrace (prefixWord ++ tailWord_3657545) baseStart_3657545 baseEnd_3657545 := by
    simpa [prefixWord, tailWord_3657545, baseEnd_3657545] using wordTrace_append hprefix tailTrace_3657545
  have hstable : (prefixWord ++ tailWord_3657545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657545).length < 2 ^ (prefixWord ++ tailWord_3657545).sum := by decide
  have hdescent : baseEnd_3657545 < baseStart_3657545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657575 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3657575 : Nat := 118140960795 + 3657575 * 2 ^ 59
def prefixEnd_3657575 : Nat := 4983230072969 + 3 ^ 40 * 3657575 * 2
def baseEnd_3657575 : Nat := 1252062669912421636461083

theorem tailTrace_3657575 : CollatzResearch.WordTrace tailWord_3657575 prefixEnd_3657575 1252062669912421636461083 := by
  unfold tailWord_3657575
  simp only [CollatzResearch.WordTrace]
  refine ⟨133402719724237913923062179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88935146482825275948708119 133402719724237913923062179)
  ·
    refine ⟨200104079586356870884593269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133402719724237913923062179 200104079586356870884593269)
    ·
      refine ⟨18759757461220956645430619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200104079586356870884593269 18759757461220956645430619)
      ·
        refine ⟨28139636191831434968145929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18759757461220956645430619 28139636191831434968145929)
        ·
          refine ⟨21104727143873576226109447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28139636191831434968145929 21104727143873576226109447)
          ·
            refine ⟨31657090715810364339164171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21104727143873576226109447 31657090715810364339164171)
            ·
              refine ⟨47485636073715546508746257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31657090715810364339164171 47485636073715546508746257)
              ·
                refine ⟨35614227055286659881559693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47485636073715546508746257 35614227055286659881559693)
                ·
                  refine ⟨13355335145732497455584885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35614227055286659881559693 13355335145732497455584885)
                  ·
                    refine ⟨1252062669912421636461083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13355335145732497455584885 1252062669912421636461083)
                    ·
                      rfl

theorem cell22_3657575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3657575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657575 prefixEnd_3657575 := by exact prefixLift 3657575
  have htrace : WordTrace (prefixWord ++ tailWord_3657575) baseStart_3657575 baseEnd_3657575 := by
    simpa [prefixWord, tailWord_3657575, baseEnd_3657575] using wordTrace_append hprefix tailTrace_3657575
  have hstable : (prefixWord ++ tailWord_3657575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657575).length < 2 ^ (prefixWord ++ tailWord_3657575).sum := by decide
  have hdescent : baseEnd_3657575 < baseStart_3657575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657607 : List Nat := [1, 1, 4, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3657607 : Nat := 118140960795 + 3657607 * 2 ^ 59
def prefixEnd_3657607 : Nat := 4983230072969 + 3 ^ 40 * 3657607 * 2
def baseEnd_3657607 : Nat := 1252073624166384219660985

theorem tailTrace_3657607 : CollatzResearch.WordTrace tailWord_3657607 prefixEnd_3657607 1252073624166384219660985 := by
  unfold tailWord_3657607
  simp only [CollatzResearch.WordTrace]
  refine ⟨133403886860121983388227075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88935924573414655592151383 133403886860121983388227075)
  ·
    refine ⟨200105830290182975082340613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133403886860121983388227075 200105830290182975082340613)
    ·
      refine ⟨37519843179409307827938865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200105830290182975082340613 37519843179409307827938865)
      ·
        refine ⟨28139882384556980870954149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37519843179409307827938865 28139882384556980870954149)
        ·
          refine ⟨5276227947104433913303903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28139882384556980870954149 5276227947104433913303903)
          ·
            refine ⟨7914341920656650869955855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5276227947104433913303903 7914341920656650869955855)
            ·
              refine ⟨11871512880984976304933783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7914341920656650869955855 11871512880984976304933783)
              ·
                refine ⟨17807269321477464457400675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11871512880984976304933783 17807269321477464457400675)
                ·
                  refine ⟨26710903982216196686101013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17807269321477464457400675 26710903982216196686101013)
                  ·
                    refine ⟨1252073624166384219660985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26710903982216196686101013 1252073624166384219660985)
                    ·
                      rfl

theorem cell22_3657607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3657607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657607 prefixEnd_3657607 := by exact prefixLift 3657607
  have htrace : WordTrace (prefixWord ++ tailWord_3657607) baseStart_3657607 baseEnd_3657607 := by
    simpa [prefixWord, tailWord_3657607, baseEnd_3657607] using wordTrace_append hprefix tailTrace_3657607
  have hstable : (prefixWord ++ tailWord_3657607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657607).length < 2 ^ (prefixWord ++ tailWord_3657607).sum := by decide
  have hdescent : baseEnd_3657607 < baseStart_3657607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657626 : List Nat := [3, 1, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_3657626 : Nat := 118140960795 + 3657626 * 2 ^ 59
def prefixEnd_3657626 : Nat := 4983230072969 + 3 ^ 40 * 3657626 * 2
def baseEnd_3657626 : Nat := 1252080128254674503435927

theorem tailTrace_3657626 : CollatzResearch.WordTrace tailWord_3657626 prefixEnd_3657626 1252080128254674503435927 := by
  unfold tailWord_3657626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33351144961763287408292183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88936386564702099755445821 33351144961763287408292183)
  ·
    refine ⟨50026717442644931112438275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33351144961763287408292183 50026717442644931112438275)
    ·
      refine ⟨75040076163967396668657413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50026717442644931112438275 75040076163967396668657413)
      ·
        refine ⟨14070014280743886875373265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75040076163967396668657413 14070014280743886875373265)
        ·
          refine ⟨10552510710557915156529949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14070014280743886875373265 10552510710557915156529949)
          ·
            refine ⟨3957191516459218183698731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10552510710557915156529949 3957191516459218183698731)
            ·
              refine ⟨5935787274688827275548097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957191516459218183698731 5935787274688827275548097)
              ·
                refine ⟨4451840456016620456661073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5935787274688827275548097 4451840456016620456661073)
                ·
                  refine ⟨3338880342012465342495805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4451840456016620456661073 3338880342012465342495805)
                  ·
                    refine ⟨1252080128254674503435927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338880342012465342495805 1252080128254674503435927)
                    ·
                      rfl

theorem cell22_3657626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_3657626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657626 prefixEnd_3657626 := by exact prefixLift 3657626
  have htrace : WordTrace (prefixWord ++ tailWord_3657626) baseStart_3657626 baseEnd_3657626 := by
    simpa [prefixWord, tailWord_3657626, baseEnd_3657626] using wordTrace_append hprefix tailTrace_3657626
  have hstable : (prefixWord ++ tailWord_3657626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657626).length < 2 ^ (prefixWord ++ tailWord_3657626).sum := by decide
  have hdescent : baseEnd_3657626 < baseStart_3657626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657727 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 6, 3]
def baseStart_3657727 : Nat := 118140960795 + 3657727 * 2 ^ 59
def prefixEnd_3657727 : Nat := 4983230072969 + 3 ^ 40 * 3657727 * 2
def baseEnd_3657727 : Nat := 1252114702618743906660617

theorem tailTrace_3657727 : CollatzResearch.WordTrace tailWord_3657727 prefixEnd_3657727 1252114702618743906660617 := by
  unfold tailWord_3657727
  simp only [CollatzResearch.WordTrace]
  refine ⟨133408263619687243882595435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88938842413124829255063623 133408263619687243882595435)
  ·
    refine ⟨200112395429530865823893153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133408263619687243882595435 200112395429530865823893153)
    ·
      refine ⟨150084296572148149367919865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200112395429530865823893153 150084296572148149367919865)
      ·
        refine ⟨112563222429111112025939899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150084296572148149367919865 112563222429111112025939899)
        ·
          refine ⟨168844833643666668038909849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112563222429111112025939899 168844833643666668038909849)
          ·
            refine ⟨126633625232750001029182387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168844833643666668038909849 126633625232750001029182387)
            ·
              refine ⟨189950437849125001543773581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126633625232750001029182387 189950437849125001543773581)
              ·
                refine ⟨71231414193421875578915093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189950437849125001543773581 71231414193421875578915093)
                ·
                  refine ⟨3338972540316650417761645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71231414193421875578915093 3338972540316650417761645)
                  ·
                    refine ⟨1252114702618743906660617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3338972540316650417761645 1252114702618743906660617)
                    ·
                      rfl

theorem cell22_3657727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_3657727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657727 prefixEnd_3657727 := by exact prefixLift 3657727
  have htrace : WordTrace (prefixWord ++ tailWord_3657727) baseStart_3657727 baseEnd_3657727 := by
    simpa [prefixWord, tailWord_3657727, baseEnd_3657727] using wordTrace_append hprefix tailTrace_3657727
  have hstable : (prefixWord ++ tailWord_3657727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657727).length < 2 ^ (prefixWord ++ tailWord_3657727).sum := by decide
  have hdescent : baseEnd_3657727 < baseStart_3657727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657729 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 4]
def baseStart_3657729 : Nat := 118140960795 + 3657729 * 2 ^ 59
def prefixEnd_3657729 : Nat := 4983230072969 + 3 ^ 40 * 3657729 * 2
def baseEnd_3657729 : Nat := 417371795753205522703537

theorem tailTrace_3657729 : CollatzResearch.WordTrace tailWord_3657729 prefixEnd_3657729 417371795753205522703537 := by
  unfold tailWord_3657729
  simp only [CollatzResearch.WordTrace]
  refine ⟨133408336565679998224168241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88938891043786665482778827 133408336565679998224168241)
  ·
    refine ⟨100056252424259998668126181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133408336565679998224168241 100056252424259998668126181)
    ·
      refine ⟨18760547329548749750273659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100056252424259998668126181 18760547329548749750273659)
      ·
        refine ⟨28140820994323124625410489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18760547329548749750273659 28140820994323124625410489)
        ·
          refine ⟨21105615745742343469057867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28140820994323124625410489 21105615745742343469057867)
          ·
            refine ⟨31658423618613515203586801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21105615745742343469057867 31658423618613515203586801)
            ·
              refine ⟨23743817713960136402690101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31658423618613515203586801 23743817713960136402690101)
              ·
                refine ⟨2225982910683762787752197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23743817713960136402690101 2225982910683762787752197)
                ·
                  refine ⟨417371795753205522703537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2225982910683762787752197 417371795753205522703537)
                  ·
                    rfl

theorem cell22_3657729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_3657729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657729 prefixEnd_3657729 := by exact prefixLift 3657729
  have htrace : WordTrace (prefixWord ++ tailWord_3657729) baseStart_3657729 baseEnd_3657729 := by
    simpa [prefixWord, tailWord_3657729, baseEnd_3657729] using wordTrace_append hprefix tailTrace_3657729
  have hstable : (prefixWord ++ tailWord_3657729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657729).length < 2 ^ (prefixWord ++ tailWord_3657729).sum := by decide
  have hdescent : baseEnd_3657729 < baseStart_3657729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657789 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3657789 : Nat := 118140960795 + 3657789 * 2 ^ 59
def prefixEnd_3657789 : Nat := 4983230072969 + 3 ^ 40 * 3657789 * 2
def baseEnd_3657789 : Nat := 1252135926485796411610427

theorem tailTrace_3657789 : CollatzResearch.WordTrace tailWord_3657789 prefixEnd_3657789 1252135926485796411610427 := by
  unfold tailWord_3657789
  simp only [CollatzResearch.WordTrace]
  refine ⟨133410524945462628471352421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88940349963641752314234947 133410524945462628471352421)
  ·
    refine ⟨25014473427274242838378579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133410524945462628471352421 25014473427274242838378579)
    ·
      refine ⟨37521710140911364257567869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25014473427274242838378579 37521710140911364257567869)
      ·
        refine ⟨14070641302841761596587951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37521710140911364257567869 14070641302841761596587951)
        ·
          refine ⟨21105961954262642394881927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14070641302841761596587951 21105961954262642394881927)
          ·
            refine ⟨31658942931393963592322891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21105961954262642394881927 31658942931393963592322891)
            ·
              refine ⟨47488414397090945388484337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31658942931393963592322891 47488414397090945388484337)
              ·
                refine ⟨35616310797818209041363253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47488414397090945388484337 35616310797818209041363253)
                ·
                  refine ⟨3339029137295457097627805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35616310797818209041363253 3339029137295457097627805)
                  ·
                    refine ⟨1252135926485796411610427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339029137295457097627805 1252135926485796411610427)
                    ·
                      rfl

theorem cell22_3657789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3657789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657789 prefixEnd_3657789 := by exact prefixLift 3657789
  have htrace : WordTrace (prefixWord ++ tailWord_3657789) baseStart_3657789 baseEnd_3657789 := by
    simpa [prefixWord, tailWord_3657789, baseEnd_3657789] using wordTrace_append hprefix tailTrace_3657789
  have hstable : (prefixWord ++ tailWord_3657789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657789).length < 2 ^ (prefixWord ++ tailWord_3657789).sum := by decide
  have hdescent : baseEnd_3657789 < baseStart_3657789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657806 : List Nat := [4, 1, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3657806 : Nat := 118140960795 + 3657806 * 2 ^ 59
def prefixEnd_3657806 : Nat := 4983230072969 + 3 ^ 40 * 3657806 * 2
def baseEnd_3657806 : Nat := 1252141745933214033935375

theorem tailTrace_3657806 : CollatzResearch.WordTrace tailWord_3657806 prefixEnd_3657806 1252141745933214033935375 := by
  unfold tailWord_3657806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676393123300130046840159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88940763324267360249814181 16676393123300130046840159)
  ·
    refine ⟨25014589684950195070260239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676393123300130046840159 25014589684950195070260239)
    ·
      refine ⟨37521884527425292605390359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25014589684950195070260239 37521884527425292605390359)
      ·
        refine ⟨56282826791137938908085539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37521884527425292605390359 56282826791137938908085539)
        ·
          refine ⟨84424240186706908362128309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56282826791137938908085539 84424240186706908362128309)
          ·
            refine ⟨7914772517503772658949529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84424240186706908362128309 7914772517503772658949529)
            ·
              refine ⟨5936079388127829494212147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7914772517503772658949529 5936079388127829494212147)
              ·
                refine ⟨8904119082191744241318221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936079388127829494212147 8904119082191744241318221)
                ·
                  refine ⟨3339044655821904090494333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8904119082191744241318221 3339044655821904090494333)
                  ·
                    refine ⟨1252141745933214033935375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339044655821904090494333 1252141745933214033935375)
                    ·
                      rfl

theorem cell22_3657806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3657806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657806 prefixEnd_3657806 := by exact prefixLift 3657806
  have htrace : WordTrace (prefixWord ++ tailWord_3657806) baseStart_3657806 baseEnd_3657806 := by
    simpa [prefixWord, tailWord_3657806, baseEnd_3657806] using wordTrace_append hprefix tailTrace_3657806
  have hstable : (prefixWord ++ tailWord_3657806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657806).length < 2 ^ (prefixWord ++ tailWord_3657806).sum := by decide
  have hdescent : baseEnd_3657806 < baseStart_3657806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657817 : List Nat := [1, 2, 1, 2, 2, 1, 3, 3, 2, 5]
def baseStart_3657817 : Nat := 118140960795 + 3657817 * 2 ^ 59
def prefixEnd_3657817 : Nat := 4983230072969 + 3 ^ 40 * 3657817 * 2
def baseEnd_3657817 : Nat := 1252145511458013671910341

theorem tailTrace_3657817 : CollatzResearch.WordTrace tailWord_3657817 prefixEnd_3657817 1252145511458013671910341 := by
  unfold tailWord_3657817
  simp only [CollatzResearch.WordTrace]
  refine ⟨133411546189361189253371705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88941030792907459502247803 133411546189361189253371705)
  ·
    refine ⟨100058659642020891940028779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133411546189361189253371705 100058659642020891940028779)
    ·
      refine ⟨150087989463031337910043169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100058659642020891940028779 150087989463031337910043169)
      ·
        refine ⟨112565992097273503432532377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150087989463031337910043169 112565992097273503432532377)
        ·
          refine ⟨84424494072955127574399283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112565992097273503432532377 84424494072955127574399283)
          ·
            refine ⟨126636741109432691361598925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84424494072955127574399283 126636741109432691361598925)
            ·
              refine ⟨47488777916037259260599597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126636741109432691361598925 47488777916037259260599597)
              ·
                refine ⟨17808291718513972222724849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47488777916037259260599597 17808291718513972222724849)
                ·
                  refine ⟨13356218788885479167043637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17808291718513972222724849 13356218788885479167043637)
                  ·
                    refine ⟨1252145511458013671910341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13356218788885479167043637 1252145511458013671910341)
                    ·
                      rfl

theorem cell22_3657817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 2, 5].length) (baseStart_3657817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657817 prefixEnd_3657817 := by exact prefixLift 3657817
  have htrace : WordTrace (prefixWord ++ tailWord_3657817) baseStart_3657817 baseEnd_3657817 := by
    simpa [prefixWord, tailWord_3657817, baseEnd_3657817] using wordTrace_append hprefix tailTrace_3657817
  have hstable : (prefixWord ++ tailWord_3657817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657817).length < 2 ^ (prefixWord ++ tailWord_3657817).sum := by decide
  have hdescent : baseEnd_3657817 < baseStart_3657817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657870 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3657870 : Nat := 118140960795 + 3657870 * 2 ^ 59
def prefixEnd_3657870 : Nat := 4983230072969 + 3 ^ 40 * 3657870 * 2
def baseEnd_3657870 : Nat := 417387884813713066778393

theorem tailTrace_3657870 : CollatzResearch.WordTrace tailWord_3657870 prefixEnd_3657870 417387884813713066778393 := by
  unfold tailWord_3657870
  simp only [CollatzResearch.WordTrace]
  refine ⟨16676684907271147413131383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88942319505446119536700709 16676684907271147413131383)
  ·
    refine ⟨25015027360906721119697075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16676684907271147413131383 25015027360906721119697075)
    ·
      refine ⟨37522541041360081679545613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25015027360906721119697075 37522541041360081679545613)
      ·
        refine ⟨14070952890510030629829605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37522541041360081679545613 14070952890510030629829605)
        ·
          refine ⟨2638303666970630743093051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14070952890510030629829605 2638303666970630743093051)
          ·
            refine ⟨3957455500455946114639577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638303666970630743093051 3957455500455946114639577)
            ·
              refine ⟨2968091625341959585979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957455500455946114639577 2968091625341959585979683)
              ·
                refine ⟨4452137438012939378969525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968091625341959585979683 4452137438012939378969525)
                ·
                  refine ⟨417387884813713066778393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452137438012939378969525 417387884813713066778393)
                  ·
                    rfl

theorem cell22_3657870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3657870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657870 prefixEnd_3657870 := by exact prefixLift 3657870
  have htrace : WordTrace (prefixWord ++ tailWord_3657870) baseStart_3657870 baseEnd_3657870 := by
    simpa [prefixWord, tailWord_3657870, baseEnd_3657870] using wordTrace_append hprefix tailTrace_3657870
  have hstable : (prefixWord ++ tailWord_3657870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657870).length < 2 ^ (prefixWord ++ tailWord_3657870).sum := by decide
  have hdescent : baseEnd_3657870 < baseStart_3657870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657908 : List Nat := [2, 5, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3657908 : Nat := 118140960795 + 3657908 * 2 ^ 59
def prefixEnd_3657908 : Nat := 4983230072969 + 3 ^ 40 * 3657908 * 2
def baseEnd_3657908 : Nat := 1252176662617719767885063

theorem tailTrace_3657908 : CollatzResearch.WordTrace tailWord_3657908 prefixEnd_3657908 1252176662617719767885063 := by
  unfold tailWord_3657908
  simp only [CollatzResearch.WordTrace]
  refine ⟨66707432616015755897467189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88943243488021007863289585 66707432616015755897467189)
  ·
    refine ⟨6253821807751477115387549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66707432616015755897467189 6253821807751477115387549)
    ·
      refine ⟨2345183177906803918270331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6253821807751477115387549 2345183177906803918270331)
      ·
        refine ⟨3517774766860205877405497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2345183177906803918270331 3517774766860205877405497)
        ·
          refine ⟨2638331075145154408054123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3517774766860205877405497 2638331075145154408054123)
          ·
            refine ⟨3957496612717731612081185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638331075145154408054123 3957496612717731612081185)
            ·
              refine ⟨2968122459538298709060889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3957496612717731612081185 2968122459538298709060889)
              ·
                refine ⟨2226091844653724031795667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968122459538298709060889 2226091844653724031795667)
                ·
                  refine ⟨3339137766980586047693501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226091844653724031795667 3339137766980586047693501)
                  ·
                    refine ⟨1252176662617719767885063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339137766980586047693501 1252176662617719767885063)
                    ·
                      rfl

theorem cell22_3657908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3657908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657908 prefixEnd_3657908 := by exact prefixLift 3657908
  have htrace : WordTrace (prefixWord ++ tailWord_3657908) baseStart_3657908 baseEnd_3657908 := by
    simpa [prefixWord, tailWord_3657908, baseEnd_3657908] using wordTrace_append hprefix tailTrace_3657908
  have hstable : (prefixWord ++ tailWord_3657908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657908).length < 2 ^ (prefixWord ++ tailWord_3657908).sum := by decide
  have hdescent : baseEnd_3657908 < baseStart_3657908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657909 : List Nat := [1, 3, 3, 4, 11]
def baseStart_3657909 : Nat := 118140960795 + 3657909 * 2 ^ 59
def prefixEnd_3657909 : Nat := 4983230072969 + 3 ^ 40 * 3657909 * 2
def baseEnd_3657909 : Nat := 5152991789868955138313

theorem tailTrace_3657909 : CollatzResearch.WordTrace tailWord_3657909 prefixEnd_3657909 5152991789868955138313 := by
  unfold tailWord_3657909
  simp only [CollatzResearch.WordTrace]
  refine ⟨133414901705027888965720781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88943267803351925977147187 133414901705027888965720781)
  ·
    refine ⟨50030588139385458362145293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133414901705027888965720781 50030588139385458362145293)
    ·
      refine ⟨18761470552269546885804485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50030588139385458362145293 18761470552269546885804485)
      ·
        refine ⟨3517775728550540041088341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18761470552269546885804485 3517775728550540041088341)
        ·
          refine ⟨5152991789868955138313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3517775728550540041088341 5152991789868955138313)
          ·
            rfl

theorem cell22_3657909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 11].length) (baseStart_3657909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657909 prefixEnd_3657909 := by exact prefixLift 3657909
  have htrace : WordTrace (prefixWord ++ tailWord_3657909) baseStart_3657909 baseEnd_3657909 := by
    simpa [prefixWord, tailWord_3657909, baseEnd_3657909] using wordTrace_append hprefix tailTrace_3657909
  have hstable : (prefixWord ++ tailWord_3657909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657909).length < 2 ^ (prefixWord ++ tailWord_3657909).sum := by decide
  have hdescent : baseEnd_3657909 < baseStart_3657909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657969 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3657969 : Nat := 118140960795 + 3657969 * 2 ^ 59
def prefixEnd_3657969 : Nat := 4983230072969 + 3 ^ 40 * 3657969 * 2
def baseEnd_3657969 : Nat := 1252197544164335942109875

theorem tailTrace_3657969 : CollatzResearch.WordTrace tailWord_3657969 prefixEnd_3657969 1252197544164335942109875 := by
  unfold tailWord_3657969
  simp only [CollatzResearch.WordTrace]
  refine ⟨133417090084810519212904961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88944726723207012808603307 133417090084810519212904961)
  ·
    refine ⟨100062817563607889409678721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133417090084810519212904961 100062817563607889409678721)
    ·
      refine ⟨75047113172705917057259041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100062817563607889409678721 75047113172705917057259041)
      ·
        refine ⟨56285334879529437792944281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75047113172705917057259041 56285334879529437792944281)
        ·
          refine ⟨42214001159647078344708211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56285334879529437792944281 42214001159647078344708211)
          ·
            refine ⟨63321001739470617517062317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42214001159647078344708211 63321001739470617517062317)
            ·
              refine ⟨23745375652301481568898369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63321001739470617517062317 23745375652301481568898369)
              ·
                refine ⟨17809031739226111176673777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23745375652301481568898369 17809031739226111176673777)
                ·
                  refine ⟨13356773804419583382505333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17809031739226111176673777 13356773804419583382505333)
                  ·
                    refine ⟨1252197544164335942109875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13356773804419583382505333 1252197544164335942109875)
                    ·
                      rfl

theorem cell22_3657969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3657969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657969 prefixEnd_3657969 := by exact prefixLift 3657969
  have htrace : WordTrace (prefixWord ++ tailWord_3657969) baseStart_3657969 baseEnd_3657969 := by
    simpa [prefixWord, tailWord_3657969, baseEnd_3657969] using wordTrace_append hprefix tailTrace_3657969
  have hstable : (prefixWord ++ tailWord_3657969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657969).length < 2 ^ (prefixWord ++ tailWord_3657969).sum := by decide
  have hdescent : baseEnd_3657969 < baseStart_3657969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3657984 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_3657984 : Nat := 118140960795 + 3657984 * 2 ^ 59
def prefixEnd_3657984 : Nat := 4983230072969 + 3 ^ 40 * 3657984 * 2
def baseEnd_3657984 : Nat := 1252202678970880902984829

theorem tailTrace_3657984 : CollatzResearch.WordTrace tailWord_3657984 prefixEnd_3657984 1252202678970880902984829 := by
  unfold tailWord_3657984
  simp only [CollatzResearch.WordTrace]
  refine ⟨66708818589878088387350503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88945091453170784516467337 66708818589878088387350503)
  ·
    refine ⟨100063227884817132581025755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66708818589878088387350503 100063227884817132581025755)
    ·
      refine ⟨150094841827225698871538633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100063227884817132581025755 150094841827225698871538633)
      ·
        refine ⟨112571131370419274153653975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150094841827225698871538633 112571131370419274153653975)
        ·
          refine ⟨168856697055628911230480963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112571131370419274153653975 168856697055628911230480963)
          ·
            refine ⟨253285045583443366845721445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168856697055628911230480963 253285045583443366845721445)
            ·
              refine ⟨47490946046895631283572771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253285045583443366845721445 47490946046895631283572771)
              ·
                refine ⟨71236419070343446925359157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47490946046895631283572771 71236419070343446925359157)
                ·
                  refine ⟨6678414287844698149252421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71236419070343446925359157 6678414287844698149252421)
                  ·
                    refine ⟨1252202678970880902984829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678414287844698149252421 1252202678970880902984829)
                    ·
                      rfl

theorem cell22_3657984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_3657984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3657984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3657984 prefixEnd_3657984 := by exact prefixLift 3657984
  have htrace : WordTrace (prefixWord ++ tailWord_3657984) baseStart_3657984 baseEnd_3657984 := by
    simpa [prefixWord, tailWord_3657984, baseEnd_3657984] using wordTrace_append hprefix tailTrace_3657984
  have hstable : (prefixWord ++ tailWord_3657984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3657984).length < 2 ^ (prefixWord ++ tailWord_3657984).sum := by decide
  have hdescent : baseEnd_3657984 < baseStart_3657984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3657984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658001 : List Nat := [1, 2, 2, 1, 1, 5, 1, 4, 1, 4]
def baseStart_3658001 : Nat := 118140960795 + 3658001 * 2 ^ 59
def prefixEnd_3658001 : Nat := 4983230072969 + 3 ^ 40 * 3658001 * 2
def baseEnd_3658001 : Nat := 1252208498418298525309777

theorem tailTrace_3658001 : CollatzResearch.WordTrace tailWord_3658001 prefixEnd_3658001 1252208498418298525309777 := by
  unfold tailWord_3658001
  simp only [CollatzResearch.WordTrace]
  refine ⟨133418257220694588678069857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88945504813796392452046571 133418257220694588678069857)
  ·
    refine ⟨100063692915520941508552393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133418257220694588678069857 100063692915520941508552393)
    ·
      refine ⟨75047769686640706131414295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100063692915520941508552393 75047769686640706131414295)
      ·
        refine ⟨112571654529961059197121443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75047769686640706131414295 112571654529961059197121443)
        ·
          refine ⟨168857481794941588795682165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112571654529961059197121443 168857481794941588795682165)
          ·
            refine ⟨15830388918275773949595203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 168857481794941588795682165 15830388918275773949595203)
            ·
              refine ⟨23745583377413660924392805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15830388918275773949595203 23745583377413660924392805)
              ·
                refine ⟨4452296883265061423323651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23745583377413660924392805 4452296883265061423323651)
                ·
                  refine ⟨6678445324897592134985477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452296883265061423323651 6678445324897592134985477)
                  ·
                    refine ⟨1252208498418298525309777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678445324897592134985477 1252208498418298525309777)
                    ·
                      rfl

theorem cell22_3658001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_3658001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658001 prefixEnd_3658001 := by exact prefixLift 3658001
  have htrace : WordTrace (prefixWord ++ tailWord_3658001) baseStart_3658001 baseEnd_3658001 := by
    simpa [prefixWord, tailWord_3658001, baseEnd_3658001] using wordTrace_append hprefix tailTrace_3658001
  have hstable : (prefixWord ++ tailWord_3658001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658001).length < 2 ^ (prefixWord ++ tailWord_3658001).sum := by decide
  have hdescent : baseEnd_3658001 < baseStart_3658001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658018 : List Nat := [3, 3, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3658018 : Nat := 118140960795 + 3658018 * 2 ^ 59
def prefixEnd_3658018 : Nat := 4983230072969 + 3 ^ 40 * 3658018 * 2
def baseEnd_3658018 : Nat := 1252214317865716147634725

theorem tailTrace_3658018 : CollatzResearch.WordTrace tailWord_3658018 prefixEnd_3658018 1252214317865716147634725 := by
  unfold tailWord_3658018
  simp only [CollatzResearch.WordTrace]
  refine ⟨33354719315408250145359677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88945918174422000387625805 33354719315408250145359677)
  ·
    refine ⟨12508019743278093804509879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33354719315408250145359677 12508019743278093804509879)
    ·
      refine ⟨18762029614917140706764819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508019743278093804509879 18762029614917140706764819)
      ·
        refine ⟨28143044422375711060147229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18762029614917140706764819 28143044422375711060147229)
        ·
          refine ⟨10553641658390891647555211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28143044422375711060147229 10553641658390891647555211)
          ·
            refine ⟨15830462487586337471332817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10553641658390891647555211 15830462487586337471332817)
            ·
              refine ⟨11872846865689753103499613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15830462487586337471332817 11872846865689753103499613)
              ·
                refine ⟨4452317574633657413812355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11872846865689753103499613 4452317574633657413812355)
                ·
                  refine ⟨6678476361950486120718533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452317574633657413812355 6678476361950486120718533)
                  ·
                    refine ⟨1252214317865716147634725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678476361950486120718533 1252214317865716147634725)
                    ·
                      rfl

theorem cell22_3658018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3658018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658018 prefixEnd_3658018 := by exact prefixLift 3658018
  have htrace : WordTrace (prefixWord ++ tailWord_3658018) baseStart_3658018 baseEnd_3658018 := by
    simpa [prefixWord, tailWord_3658018, baseEnd_3658018] using wordTrace_append hprefix tailTrace_3658018
  have hstable : (prefixWord ++ tailWord_3658018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658018).length < 2 ^ (prefixWord ++ tailWord_3658018).sum := by decide
  have hdescent : baseEnd_3658018 < baseStart_3658018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658031 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 4, 3]
def baseStart_3658031 : Nat := 118140960795 + 3658031 * 2 ^ 59
def prefixEnd_3658031 : Nat := 4983230072969 + 3 ^ 40 * 3658031 * 2
def baseEnd_3658031 : Nat := 1252218768031388447059685

theorem tailTrace_3658031 : CollatzResearch.WordTrace tailWord_3658031 prefixEnd_3658031 1252218768031388447059685 := by
  unfold tailWord_3658031
  simp only [CollatzResearch.WordTrace]
  refine ⟨133419351410585903801661947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88946234273723935867774631 133419351410585903801661947)
  ·
    refine ⟨200129027115878855702492921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133419351410585903801661947 200129027115878855702492921)
    ·
      refine ⟨150096770336909141776869691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200129027115878855702492921 150096770336909141776869691)
      ·
        refine ⟨225145155505363712665304537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150096770336909141776869691 225145155505363712665304537)
        ·
          refine ⟨168858866629022784498978403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225145155505363712665304537 168858866629022784498978403)
          ·
            refine ⟨253288299943534176748467605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168858866629022784498978403 253288299943534176748467605)
            ·
              refine ⟨11872889059853164535084419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253288299943534176748467605 11872889059853164535084419)
              ·
                refine ⟨17809333589779746802626629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11872889059853164535084419 17809333589779746802626629)
                ·
                  refine ⟨3339250048083702525492493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17809333589779746802626629 3339250048083702525492493)
                  ·
                    refine ⟨1252218768031388447059685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339250048083702525492493 1252218768031388447059685)
                    ·
                      rfl

theorem cell22_3658031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_3658031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658031 prefixEnd_3658031 := by exact prefixLift 3658031
  have htrace : WordTrace (prefixWord ++ tailWord_3658031) baseStart_3658031 baseEnd_3658031 := by
    simpa [prefixWord, tailWord_3658031, baseEnd_3658031] using wordTrace_append hprefix tailTrace_3658031
  have hstable : (prefixWord ++ tailWord_3658031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658031).length < 2 ^ (prefixWord ++ tailWord_3658031).sum := by decide
  have hdescent : baseEnd_3658031 < baseStart_3658031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658033 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 6]
def baseStart_3658033 : Nat := 118140960795 + 3658033 * 2 ^ 59
def prefixEnd_3658033 : Nat := 4983230072969 + 3 ^ 40 * 3658033 * 2
def baseEnd_3658033 : Nat := 417406484224087036169893

theorem tailTrace_3658033 : CollatzResearch.WordTrace tailWord_3658033 prefixEnd_3658033 417406484224087036169893 := by
  unfold tailWord_3658033
  simp only [CollatzResearch.WordTrace]
  refine ⟨133419424356578658143234753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88946282904385772095489835 133419424356578658143234753)
  ·
    refine ⟨100064568267433993607426065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133419424356578658143234753 100064568267433993607426065)
    ·
      refine ⟨75048426200575495205569549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100064568267433993607426065 75048426200575495205569549)
      ·
        refine ⟨28143159825215810702088581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75048426200575495205569549 28143159825215810702088581)
        ·
          refine ⟨5276842467227964506641609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28143159825215810702088581 5276842467227964506641609)
          ·
            refine ⟨3957631850420973379981207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276842467227964506641609 3957631850420973379981207)
            ·
              refine ⟨5936447775631460069971811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957631850420973379981207 5936447775631460069971811)
              ·
                refine ⟨8904671663447190104957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936447775631460069971811 8904671663447190104957717)
                ·
                  refine ⟨417406484224087036169893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8904671663447190104957717 417406484224087036169893)
                  ·
                    rfl

theorem cell22_3658033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 6].length) (baseStart_3658033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658033 prefixEnd_3658033 := by exact prefixLift 3658033
  have htrace : WordTrace (prefixWord ++ tailWord_3658033) baseStart_3658033 baseEnd_3658033 := by
    simpa [prefixWord, tailWord_3658033, baseEnd_3658033] using wordTrace_append hprefix tailTrace_3658033
  have hstable : (prefixWord ++ tailWord_3658033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658033).length < 2 ^ (prefixWord ++ tailWord_3658033).sum := by decide
  have hdescent : baseEnd_3658033 < baseStart_3658033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658052 : List Nat := [2, 3, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3658052 : Nat := 118140960795 + 3658052 * 2 ^ 59
def prefixEnd_3658052 : Nat := 4983230072969 + 3 ^ 40 * 3658052 * 2
def baseEnd_3658052 : Nat := 1252225956760551392284621

theorem tailTrace_3658052 : CollatzResearch.WordTrace tailWord_3658052 prefixEnd_3658052 1252225956760551392284621 := by
  unfold tailWord_3658052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66710058671754912194088205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88946744895673216258784273 66710058671754912194088205)
  ·
    refine ⟨25016272001908092072783077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66710058671754912194088205 25016272001908092072783077)
    ·
      refine ⟨4690551000357767263646827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25016272001908092072783077 4690551000357767263646827)
      ·
        refine ⟨7035826500536650895470241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690551000357767263646827 7035826500536650895470241)
        ·
          refine ⟨5276869875402488171602681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7035826500536650895470241 5276869875402488171602681)
          ·
            refine ⟨3957652406551866128702011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5276869875402488171602681 3957652406551866128702011)
            ·
              refine ⟨5936478609827799193053017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957652406551866128702011 5936478609827799193053017)
              ·
                refine ⟨4452358957370849394789763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5936478609827799193053017 4452358957370849394789763)
                ·
                  refine ⟨6678538436056274092184645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4452358957370849394789763 6678538436056274092184645)
                  ·
                    refine ⟨1252225956760551392284621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678538436056274092184645 1252225956760551392284621)
                    ·
                      rfl

theorem cell22_3658052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3658052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658052 prefixEnd_3658052 := by exact prefixLift 3658052
  have htrace : WordTrace (prefixWord ++ tailWord_3658052) baseStart_3658052 baseEnd_3658052 := by
    simpa [prefixWord, tailWord_3658052, baseEnd_3658052] using wordTrace_append hprefix tailTrace_3658052
  have hstable : (prefixWord ++ tailWord_3658052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658052).length < 2 ^ (prefixWord ++ tailWord_3658052).sum := by decide
  have hdescent : baseEnd_3658052 < baseStart_3658052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658093 : List Nat := [1, 5, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3658093 : Nat := 118140960795 + 3658093 * 2 ^ 59
def prefixEnd_3658093 : Nat := 4983230072969 + 3 ^ 40 * 3658093 * 2
def baseEnd_3658093 : Nat := 1252239991898440952009495

theorem tailTrace_3658093 : CollatzResearch.WordTrace tailWord_3658093 prefixEnd_3658093 1252239991898440952009495 := by
  unfold tailWord_3658093
  simp only [CollatzResearch.WordTrace]
  refine ⟨133421612736361288390418933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88947741824240858926945955 133421612736361288390418933)
  ·
    refine ⟨12508276194033870786601775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133421612736361288390418933 12508276194033870786601775)
    ·
      refine ⟨18762414291050806179902663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12508276194033870786601775 18762414291050806179902663)
      ·
        refine ⟨28143621436576209269853995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18762414291050806179902663 28143621436576209269853995)
        ·
          refine ⟨42215432154864313904780993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28143621436576209269853995 42215432154864313904780993)
          ·
            refine ⟨31661574116148235428585745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42215432154864313904780993 31661574116148235428585745)
            ·
              refine ⟨23746180587111176571439309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31661574116148235428585745 23746180587111176571439309)
              ·
                refine ⟨8904817720166691214289741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23746180587111176571439309 8904817720166691214289741)
                ·
                  refine ⟨3339306645062509205358653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8904817720166691214289741 3339306645062509205358653)
                  ·
                    refine ⟨1252239991898440952009495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339306645062509205358653 1252239991898440952009495)
                    ·
                      rfl

theorem cell22_3658093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3658093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658093 prefixEnd_3658093 := by exact prefixLift 3658093
  have htrace : WordTrace (prefixWord ++ tailWord_3658093) baseStart_3658093 baseEnd_3658093 := by
    simpa [prefixWord, tailWord_3658093, baseEnd_3658093] using wordTrace_append hprefix tailTrace_3658093
  have hstable : (prefixWord ++ tailWord_3658093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658093).length < 2 ^ (prefixWord ++ tailWord_3658093).sum := by decide
  have hdescent : baseEnd_3658093 < baseStart_3658093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658114 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3658114 : Nat := 118140960795 + 3658114 * 2 ^ 59
def prefixEnd_3658114 : Nat := 4983230072969 + 3 ^ 40 * 3658114 * 2
def baseEnd_3658114 : Nat := 1252247180627603897234431

theorem tailTrace_3658114 : CollatzResearch.WordTrace tailWord_3658114 prefixEnd_3658114 1252247180627603897234431 := by
  unfold tailWord_3658114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33355594667321302244233349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88948252446190139317955597 33355594667321302244233349)
  ·
    refine ⟨6254174000122744170793753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33355594667321302244233349 6254174000122744170793753)
    ·
      refine ⟨4690630500092058128095315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6254174000122744170793753 4690630500092058128095315)
      ·
        refine ⟨7035945750138087192142973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690630500092058128095315 7035945750138087192142973)
        ·
          refine ⟨2638479656301782697053615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7035945750138087192142973 2638479656301782697053615)
          ·
            refine ⟨3957719484452674045580423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2638479656301782697053615 3957719484452674045580423)
            ·
              refine ⟨5936579226679011068370635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957719484452674045580423 5936579226679011068370635)
              ·
                refine ⟨8904868840018516602555953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5936579226679011068370635 8904868840018516602555953)
                ·
                  refine ⟨6678651630013887451916965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8904868840018516602555953 6678651630013887451916965)
                  ·
                    refine ⟨1252247180627603897234431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678651630013887451916965 1252247180627603897234431)
                    ·
                      rfl

theorem cell22_3658114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3658114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658114 prefixEnd_3658114 := by exact prefixLift 3658114
  have htrace : WordTrace (prefixWord ++ tailWord_3658114) baseStart_3658114 baseEnd_3658114 := by
    simpa [prefixWord, tailWord_3658114, baseEnd_3658114] using wordTrace_append hprefix tailTrace_3658114
  have hstable : (prefixWord ++ tailWord_3658114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658114).length < 2 ^ (prefixWord ++ tailWord_3658114).sum := by decide
  have hdescent : baseEnd_3658114 < baseStart_3658114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658157 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 5]
def baseStart_3658157 : Nat := 118140960795 + 3658157 * 2 ^ 59
def prefixEnd_3658157 : Nat := 4983230072969 + 3 ^ 40 * 3658157 * 2
def baseEnd_3658157 : Nat := 417420633468788706136433

theorem tailTrace_3658157 : CollatzResearch.WordTrace tailWord_3658157 prefixEnd_3658157 417420633468788706136433 := by
  unfold tailWord_3658157
  simp only [CollatzResearch.WordTrace]
  refine ⟨133423947008129427320748725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949298005419618213832483 133423947008129427320748725)
  ·
    refine ⟨12508495032012133811320193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133423947008129427320748725 12508495032012133811320193)
    ·
      refine ⟨9381371274009100358490145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12508495032012133811320193 9381371274009100358490145)
      ·
        refine ⟨7036028455506825268867609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9381371274009100358490145 7036028455506825268867609)
        ·
          refine ⟨5277021341630118951650707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7036028455506825268867609 5277021341630118951650707)
          ·
            refine ⟨7915532012445178427476061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277021341630118951650707 7915532012445178427476061)
            ·
              refine ⟨2968324504666941910303523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7915532012445178427476061 2968324504666941910303523)
              ·
                refine ⟨4452486757000412865455285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968324504666941910303523 4452486757000412865455285)
                ·
                  refine ⟨417420633468788706136433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4452486757000412865455285 417420633468788706136433)
                  ·
                    rfl

theorem cell22_3658157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_3658157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658157 prefixEnd_3658157 := by exact prefixLift 3658157
  have htrace : WordTrace (prefixWord ++ tailWord_3658157) baseStart_3658157 baseEnd_3658157 := by
    simpa [prefixWord, tailWord_3658157, baseEnd_3658157] using wordTrace_append hprefix tailTrace_3658157
  have hstable : (prefixWord ++ tailWord_3658157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658157).length < 2 ^ (prefixWord ++ tailWord_3658157).sum := by decide
  have hdescent : baseEnd_3658157 < baseStart_3658157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658181 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_3658181 : Nat := 118140960795 + 3658181 * 2 ^ 59
def prefixEnd_3658181 : Nat := 4983230072969 + 3 ^ 40 * 3658181 * 2
def baseEnd_3658181 : Nat := 1252270116096838055809225

theorem tailTrace_3658181 : CollatzResearch.WordTrace tailWord_3658181 prefixEnd_3658181 1252270116096838055809225 := by
  unfold tailWord_3658181
  simp only [CollatzResearch.WordTrace]
  refine ⟨133424822360042479419622397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949881573361652946414931 133424822360042479419622397)
  ·
    refine ⟨50034308385015929782358399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133424822360042479419622397 50034308385015929782358399)
    ·
      refine ⟨75051462577523894673537599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50034308385015929782358399 75051462577523894673537599)
      ·
        refine ⟨112577193866285842010306399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75051462577523894673537599 112577193866285842010306399)
        ·
          refine ⟨168865790799428763015459599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112577193866285842010306399 168865790799428763015459599)
          ·
            refine ⟨253298686199143144523189399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168865790799428763015459599 253298686199143144523189399)
            ·
              refine ⟨379948029298714716784784099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253298686199143144523189399 379948029298714716784784099)
              ·
                refine ⟨569922043948072075177176149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379948029298714716784784099 569922043948072075177176149)
                ·
                  refine ⟨6678773952516469630982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 569922043948072075177176149 6678773952516469630982533)
                  ·
                    refine ⟨1252270116096838055809225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678773952516469630982533 1252270116096838055809225)
                    ·
                      rfl

theorem cell22_3658181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_3658181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658181 prefixEnd_3658181 := by exact prefixLift 3658181
  have htrace : WordTrace (prefixWord ++ tailWord_3658181) baseStart_3658181 baseEnd_3658181 := by
    simpa [prefixWord, tailWord_3658181, baseEnd_3658181] using wordTrace_append hprefix tailTrace_3658181
  have hstable : (prefixWord ++ tailWord_3658181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658181).length < 2 ^ (prefixWord ++ tailWord_3658181).sum := by decide
  have hdescent : baseEnd_3658181 < baseStart_3658181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658183 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3658183 : Nat := 118140960795 + 3658183 * 2 ^ 59
def prefixEnd_3658183 : Nat := 4983230072969 + 3 ^ 40 * 3658183 * 2
def baseEnd_3658183 : Nat := 1252270800737710717259219

theorem tailTrace_3658183 : CollatzResearch.WordTrace tailWord_3658183 prefixEnd_3658183 1252270800737710717259219 := by
  unfold tailWord_3658183
  simp only [CollatzResearch.WordTrace]
  refine ⟨133424895306035233761195203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88949930204023489174130135 133424895306035233761195203)
  ·
    refine ⟨200137342959052850641792805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133424895306035233761195203 200137342959052850641792805)
    ·
      refine ⟨37525751804822409495336151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200137342959052850641792805 37525751804822409495336151)
      ·
        refine ⟨56288627707233614243004227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37525751804822409495336151 56288627707233614243004227)
        ·
          refine ⟨84432941560850421364506341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56288627707233614243004227 84432941560850421364506341)
          ·
            refine ⟨15831176542659454005844939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84432941560850421364506341 15831176542659454005844939)
            ·
              refine ⟨23746764813989181008767409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831176542659454005844939 23746764813989181008767409)
              ·
                refine ⟨17810073610491885756575557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23746764813989181008767409 17810073610491885756575557)
                ·
                  refine ⟨3339388801967228579357917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17810073610491885756575557 3339388801967228579357917)
                  ·
                    refine ⟨1252270800737710717259219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339388801967228579357917 1252270800737710717259219)
                    ·
                      rfl

theorem cell22_3658183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3658183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658183 prefixEnd_3658183 := by exact prefixLift 3658183
  have htrace : WordTrace (prefixWord ++ tailWord_3658183) baseStart_3658183 baseEnd_3658183 := by
    simpa [prefixWord, tailWord_3658183, baseEnd_3658183] using wordTrace_append hprefix tailTrace_3658183
  have hstable : (prefixWord ++ tailWord_3658183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658183).length < 2 ^ (prefixWord ++ tailWord_3658183).sum := by decide
  have hdescent : baseEnd_3658183 < baseStart_3658183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658260 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3658260 : Nat := 118140960795 + 3658260 * 2 ^ 59
def prefixEnd_3658260 : Nat := 4983230072969 + 3 ^ 40 * 3658260 * 2
def baseEnd_3658260 : Nat := 1252297159411308183083983

theorem tailTrace_3658260 : CollatzResearch.WordTrace tailWord_3658260 prefixEnd_3658260 1252297159411308183083983 := by
  unfold tailWord_3658260
  simp only [CollatzResearch.WordTrace]
  refine ⟨66713851863378137955874117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88951802484504183941165489 66713851863378137955874117)
  ·
    refine ⟨12508847224383400866726397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66713851863378137955874117 12508847224383400866726397)
    ·
      refine ⟨4690817709143775325022399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12508847224383400866726397 4690817709143775325022399)
      ·
        refine ⟨7036226563715662987533599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4690817709143775325022399 7036226563715662987533599)
        ·
          refine ⟨10554339845573494481300399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7036226563715662987533599 10554339845573494481300399)
          ·
            refine ⟨15831509768360241721950599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554339845573494481300399 15831509768360241721950599)
            ·
              refine ⟨23747264652540362582925899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15831509768360241721950599 23747264652540362582925899)
              ·
                refine ⟨35620896978810543874388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23747264652540362582925899 35620896978810543874388849)
                ·
                  refine ⟨26715672734107907905791637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35620896978810543874388849 26715672734107907905791637)
                  ·
                    refine ⟨1252297159411308183083983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26715672734107907905791637 1252297159411308183083983)
                    ·
                      rfl

theorem cell22_3658260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3658260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658260 prefixEnd_3658260 := by exact prefixLift 3658260
  have htrace : WordTrace (prefixWord ++ tailWord_3658260) baseStart_3658260 baseEnd_3658260 := by
    simpa [prefixWord, tailWord_3658260, baseEnd_3658260] using wordTrace_append hprefix tailTrace_3658260
  have hstable : (prefixWord ++ tailWord_3658260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658260).length < 2 ^ (prefixWord ++ tailWord_3658260).sum := by decide
  have hdescent : baseEnd_3658260 < baseStart_3658260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658273 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3658273 : Nat := 118140960795 + 3658273 * 2 ^ 59
def prefixEnd_3658273 : Nat := 4983230072969 + 3 ^ 40 * 3658273 * 2
def baseEnd_3658273 : Nat := 1252301609576980482508943

theorem tailTrace_3658273 : CollatzResearch.WordTrace tailWord_3658273 prefixEnd_3658273 1252301609576980482508943 := by
  unfold tailWord_3658273
  simp only [CollatzResearch.WordTrace]
  refine ⟨133428177875709179131971473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88952118583806119421314315 133428177875709179131971473)
  ·
    refine ⟨100071133406781884348978605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133428177875709179131971473 100071133406781884348978605)
    ·
      refine ⟨37526675027543206630866977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100071133406781884348978605 37526675027543206630866977)
      ·
        refine ⟨28145006270657404973150233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37526675027543206630866977 28145006270657404973150233)
        ·
          refine ⟨21108754702993053729862675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28145006270657404973150233 21108754702993053729862675)
          ·
            refine ⟨31663132054489580594794013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21108754702993053729862675 31663132054489580594794013)
            ·
              refine ⟨11873674520433592723047755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31663132054489580594794013 11873674520433592723047755)
              ·
                refine ⟨17810511780650389084571633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873674520433592723047755 17810511780650389084571633)
                ·
                  refine ⟨13357883835487791813428725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17810511780650389084571633 13357883835487791813428725)
                  ·
                    refine ⟨1252301609576980482508943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13357883835487791813428725 1252301609576980482508943)
                    ·
                      rfl

theorem cell22_3658273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3658273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658273 prefixEnd_3658273 := by exact prefixLift 3658273
  have htrace : WordTrace (prefixWord ++ tailWord_3658273) baseStart_3658273 baseEnd_3658273 := by
    simpa [prefixWord, tailWord_3658273, baseEnd_3658273] using wordTrace_append hprefix tailTrace_3658273
  have hstable : (prefixWord ++ tailWord_3658273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658273).length < 2 ^ (prefixWord ++ tailWord_3658273).sum := by decide
  have hdescent : baseEnd_3658273 < baseStart_3658273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658279 : List Nat := [1, 1, 7, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3658279 : Nat := 118140960795 + 3658279 * 2 ^ 59
def prefixEnd_3658279 : Nat := 4983230072969 + 3 ^ 40 * 3658279 * 2
def baseEnd_3658279 : Nat := 1252303663499598466858925

theorem tailTrace_3658279 : CollatzResearch.WordTrace tailWord_3658279 prefixEnd_3658279 1252303663499598466858925 := by
  unfold tailWord_3658279
  simp only [CollatzResearch.WordTrace]
  refine ⟨133428396713687442156689891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88952264475791628104459927 133428396713687442156689891)
  ·
    refine ⟨200142595070531163235034837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133428396713687442156689891 200142595070531163235034837)
    ·
      refine ⟨4690842071965574138321129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 200142595070531163235034837 4690842071965574138321129)
      ·
        refine ⟨3518131553974180603740847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4690842071965574138321129 3518131553974180603740847)
        ·
          refine ⟨5277197330961270905611271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3518131553974180603740847 5277197330961270905611271)
          ·
            refine ⟨7915795996441906358416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277197330961270905611271 7915795996441906358416907)
            ·
              refine ⟨11873693994662859537625361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7915795996441906358416907 11873693994662859537625361)
              ·
                refine ⟨8905270495997144653219021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11873693994662859537625361 8905270495997144653219021)
                ·
                  refine ⟨3339476435998929244957133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8905270495997144653219021 3339476435998929244957133)
                  ·
                    refine ⟨1252303663499598466858925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339476435998929244957133 1252303663499598466858925)
                    ·
                      rfl

theorem cell22_3658279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3658279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658279 prefixEnd_3658279 := by exact prefixLift 3658279
  have htrace : WordTrace (prefixWord ++ tailWord_3658279) baseStart_3658279 baseEnd_3658279 := by
    simpa [prefixWord, tailWord_3658279, baseEnd_3658279] using wordTrace_append hprefix tailTrace_3658279
  have hstable : (prefixWord ++ tailWord_3658279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658279).length < 2 ^ (prefixWord ++ tailWord_3658279).sum := by decide
  have hdescent : baseEnd_3658279 < baseStart_3658279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658288 : List Nat := [2, 1, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_3658288 : Nat := 118140960795 + 3658288 * 2 ^ 59
def prefixEnd_3658288 : Nat := 4983230072969 + 3 ^ 40 * 3658288 * 2
def baseEnd_3658288 : Nat := 1252306744383525443383897

theorem tailTrace_3658288 : CollatzResearch.WordTrace tailWord_3658288 prefixEnd_3658288 1252306744383525443383897 := by
  unfold tailWord_3658288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66714362485327418346883759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88952483313769891129178345 66714362485327418346883759)
  ·
    refine ⟨100071543727991127520325639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66714362485327418346883759 100071543727991127520325639)
    ·
      refine ⟨150107315591986691280488459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100071543727991127520325639 150107315591986691280488459)
      ·
        refine ⟨225160973387980036920732689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150107315591986691280488459 225160973387980036920732689)
        ·
          refine ⟨168870730040985027690549517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225160973387980036920732689 168870730040985027690549517)
          ·
            refine ⟨63326523765369385383956069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168870730040985027690549517 63326523765369385383956069)
            ·
              refine ⟨11873723206006759759491763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63326523765369385383956069 11873723206006759759491763)
              ·
                refine ⟨17810584809010139639237645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873723206006759759491763 17810584809010139639237645)
                ·
                  refine ⟨6678969303378802364714117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17810584809010139639237645 6678969303378802364714117)
                  ·
                    refine ⟨1252306744383525443383897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6678969303378802364714117 1252306744383525443383897)
                    ·
                      rfl

theorem cell22_3658288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_3658288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658288 prefixEnd_3658288 := by exact prefixLift 3658288
  have htrace : WordTrace (prefixWord ++ tailWord_3658288) baseStart_3658288 baseEnd_3658288 := by
    simpa [prefixWord, tailWord_3658288, baseEnd_3658288] using wordTrace_append hprefix tailTrace_3658288
  have hstable : (prefixWord ++ tailWord_3658288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658288).length < 2 ^ (prefixWord ++ tailWord_3658288).sum := by decide
  have hdescent : baseEnd_3658288 < baseStart_3658288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658318 : List Nat := [4, 1, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3658318 : Nat := 118140960795 + 3658318 * 2 ^ 59
def prefixEnd_3658318 : Nat := 4983230072969 + 3 ^ 40 * 3658318 * 2
def baseEnd_3658318 : Nat := 1252317013996615365133805

theorem tailTrace_3658318 : CollatzResearch.WordTrace tailWord_3658318 prefixEnd_3658318 1252317013996615365133805 := by
  unfold tailWord_3658318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678727395068268977169951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88953212773697434544906405 16678727395068268977169951)
  ·
    refine ⟨25018091092602403465754927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16678727395068268977169951 25018091092602403465754927)
    ·
      refine ⟨37527136638903605198632391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25018091092602403465754927 37527136638903605198632391)
      ·
        refine ⟨56290704958355407797948587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37527136638903605198632391 56290704958355407797948587)
        ·
          refine ⟨84436057437533111696922881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56290704958355407797948587 84436057437533111696922881)
          ·
            refine ⟨63327043078149833772692161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84436057437533111696922881 63327043078149833772692161)
            ·
              refine ⟨47495282308612375329519121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63327043078149833772692161 47495282308612375329519121)
              ·
                refine ⟨35621461731459281497139341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47495282308612375329519121 35621461731459281497139341)
                ·
                  refine ⟨13358048149297230561427253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35621461731459281497139341 13358048149297230561427253)
                  ·
                    refine ⟨1252317013996615365133805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13358048149297230561427253 1252317013996615365133805)
                    ·
                      rfl

theorem cell22_3658318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3658318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658318 prefixEnd_3658318 := by exact prefixLift 3658318
  have htrace : WordTrace (prefixWord ++ tailWord_3658318) baseStart_3658318 baseEnd_3658318 := by
    simpa [prefixWord, tailWord_3658318, baseEnd_3658318] using wordTrace_append hprefix tailTrace_3658318
  have hstable : (prefixWord ++ tailWord_3658318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658318).length < 2 ^ (prefixWord ++ tailWord_3658318).sum := by decide
  have hdescent : baseEnd_3658318 < baseStart_3658318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658335 : List Nat := [1, 1, 2, 3, 1, 1, 1, 7, 2, 3]
def baseStart_3658335 : Nat := 118140960795 + 3658335 * 2 ^ 59
def prefixEnd_3658335 : Nat := 4983230072969 + 3 ^ 40 * 3658335 * 2
def baseEnd_3658335 : Nat := 1252322833444032987458753

theorem tailTrace_3658335 : CollatzResearch.WordTrace tailWord_3658335 prefixEnd_3658335 1252322833444032987458753 := by
  unfold tailWord_3658335
  simp only [CollatzResearch.WordTrace]
  refine ⟨133430439201484563720728459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88953626134323042480485639 133430439201484563720728459)
  ·
    refine ⟨200145658802226845581092689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133430439201484563720728459 200145658802226845581092689)
    ·
      refine ⟨150109244101670134185819517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200145658802226845581092689 150109244101670134185819517)
      ·
        refine ⟨56290966538126300319682319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150109244101670134185819517 56290966538126300319682319)
        ·
          refine ⟨84436449807189450479523479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56290966538126300319682319 84436449807189450479523479)
          ·
            refine ⟨126654674710784175719285219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84436449807189450479523479 126654674710784175719285219)
            ·
              refine ⟨189982012066176263578927829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126654674710784175719285219 189982012066176263578927829)
              ·
                refine ⟨4452703407801006177631121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 189982012066176263578927829 4452703407801006177631121)
                ·
                  refine ⟨3339527555850754633223341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452703407801006177631121 3339527555850754633223341)
                  ·
                    refine ⟨1252322833444032987458753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339527555850754633223341 1252322833444032987458753)
                    ·
                      rfl

theorem cell22_3658335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_3658335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658335 prefixEnd_3658335 := by exact prefixLift 3658335
  have htrace : WordTrace (prefixWord ++ tailWord_3658335) baseStart_3658335 baseEnd_3658335 := by
    simpa [prefixWord, tailWord_3658335, baseEnd_3658335] using wordTrace_append hprefix tailTrace_3658335
  have hstable : (prefixWord ++ tailWord_3658335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658335).length < 2 ^ (prefixWord ++ tailWord_3658335).sum := by decide
  have hdescent : baseEnd_3658335 < baseStart_3658335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658350 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3658350 : Nat := 118140960795 + 3658350 * 2 ^ 59
def prefixEnd_3658350 : Nat := 4983230072969 + 3 ^ 40 * 3658350 * 2
def baseEnd_3658350 : Nat := 1252327968250577948333707

theorem tailTrace_3658350 : CollatzResearch.WordTrace tailWord_3658350 prefixEnd_3658350 1252327968250577948333707 := by
  unfold tailWord_3658350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16678873287053777660315563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88953990864286814188349669 16678873287053777660315563)
  ·
    refine ⟨25018309930580666490473345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16678873287053777660315563 25018309930580666490473345)
    ·
      refine ⟨18763732447935499867855009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25018309930580666490473345 18763732447935499867855009)
      ·
        refine ⟨14072799335951624900891257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18763732447935499867855009 14072799335951624900891257)
        ·
          refine ⟨10554599501963718675668443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14072799335951624900891257 10554599501963718675668443)
          ·
            refine ⟨15831899252945578013502665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10554599501963718675668443 15831899252945578013502665)
            ·
              refine ⟨11873924439709183510126999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15831899252945578013502665 11873924439709183510126999)
              ·
                refine ⟨17810886659563775265190499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11873924439709183510126999 17810886659563775265190499)
                ·
                  refine ⟨26716329989345662897785749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17810886659563775265190499 26716329989345662897785749)
                  ·
                    refine ⟨1252327968250577948333707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26716329989345662897785749 1252327968250577948333707)
                    ·
                      rfl

theorem cell22_3658350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3658350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658350 prefixEnd_3658350 := by exact prefixLift 3658350
  have htrace : WordTrace (prefixWord ++ tailWord_3658350) baseStart_3658350 baseEnd_3658350 := by
    simpa [prefixWord, tailWord_3658350, baseEnd_3658350] using wordTrace_append hprefix tailTrace_3658350
  have hstable : (prefixWord ++ tailWord_3658350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658350).length < 2 ^ (prefixWord ++ tailWord_3658350).sum := by decide
  have hdescent : baseEnd_3658350 < baseStart_3658350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658354 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3658354 : Nat := 118140960795 + 3658354 * 2 ^ 59
def prefixEnd_3658354 : Nat := 4983230072969 + 3 ^ 40 * 3658354 * 2
def baseEnd_3658354 : Nat := 417443112510774423744565

theorem tailTrace_3658354 : CollatzResearch.WordTrace tailWord_3658354 prefixEnd_3658354 417443112510774423744565 := by
  unfold tailWord_3658354
  simp only [CollatzResearch.WordTrace]
  refine ⟨33357783047103932491417529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88954088125610486643780077 33357783047103932491417529)
  ·
    refine ⟨25018337285327949368563147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33357783047103932491417529 25018337285327949368563147)
    ·
      refine ⟨37527505927991924052844721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25018337285327949368563147 37527505927991924052844721)
      ·
        refine ⟨28145629445993943039633541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37527505927991924052844721 28145629445993943039633541)
        ·
          refine ⟨5277305521123864319931289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28145629445993943039633541 5277305521123864319931289)
          ·
            refine ⟨3957979140842898239948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5277305521123864319931289 3957979140842898239948467)
            ·
              refine ⟨5936968711264347359922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3957979140842898239948467 5936968711264347359922701)
              ·
                refine ⟨2226363266724130259971013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5936968711264347359922701 2226363266724130259971013)
                ·
                  refine ⟨417443112510774423744565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226363266724130259971013 417443112510774423744565)
                  ·
                    rfl

theorem cell22_3658354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3658354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658354 prefixEnd_3658354 := by exact prefixLift 3658354
  have htrace : WordTrace (prefixWord ++ tailWord_3658354) baseStart_3658354 baseEnd_3658354 := by
    simpa [prefixWord, tailWord_3658354, baseEnd_3658354] using wordTrace_append hprefix tailTrace_3658354
  have hstable : (prefixWord ++ tailWord_3658354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658354).length < 2 ^ (prefixWord ++ tailWord_3658354).sum := by decide
  have hdescent : baseEnd_3658354 < baseStart_3658354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658365 : List Nat := [1, 4, 1, 1, 5, 2, 8]
def baseStart_3658365 : Nat := 118140960795 + 3658365 * 2 ^ 59
def prefixEnd_3658365 : Nat := 4983230072969 + 3 ^ 40 * 3658365 * 2
def baseEnd_3658365 : Nat := 46382707520634181822543

theorem tailTrace_3658365 : CollatzResearch.WordTrace tailWord_3658365 prefixEnd_3658365 46382707520634181822543 := by
  unfold tailWord_3658365
  simp only [CollatzResearch.WordTrace]
  refine ⟨133431533391375878844320549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88954355594250585896213699 133431533391375878844320549)
  ·
    refine ⟨25018412510882977283310103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133431533391375878844320549 25018412510882977283310103)
    ·
      refine ⟨37527618766324465924965155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25018412510882977283310103 37527618766324465924965155)
      ·
        refine ⟨56291428149486698887447733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37527618766324465924965155 56291428149486698887447733)
        ·
          refine ⟨5277321389014378020698225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56291428149486698887447733 5277321389014378020698225)
          ·
            refine ⟨3957991041760783515523669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5277321389014378020698225 3957991041760783515523669)
            ·
              refine ⟨46382707520634181822543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3957991041760783515523669 46382707520634181822543)
              ·
                rfl

theorem cell22_3658365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 8].length) (baseStart_3658365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658365 prefixEnd_3658365 := by exact prefixLift 3658365
  have htrace : WordTrace (prefixWord ++ tailWord_3658365) baseStart_3658365 baseEnd_3658365 := by
    simpa [prefixWord, tailWord_3658365, baseEnd_3658365] using wordTrace_append hprefix tailTrace_3658365
  have hstable : (prefixWord ++ tailWord_3658365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658365).length < 2 ^ (prefixWord ++ tailWord_3658365).sum := by decide
  have hdescent : baseEnd_3658365 < baseStart_3658365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658380 : List Nat := [2, 2, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_3658380 : Nat := 118140960795 + 3658380 * 2 ^ 59
def prefixEnd_3658380 : Nat := 4983230072969 + 3 ^ 40 * 3658380 * 2
def baseEnd_3658380 : Nat := 1252338237863667870083615

theorem tailTrace_3658380 : CollatzResearch.WordTrace tailWord_3658380 prefixEnd_3658380 1252338237863667870083615 := by
  unfold tailWord_3658380
  simp only [CollatzResearch.WordTrace]
  refine ⟨66716040243160768203058297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88954720324214357604077729 66716040243160768203058297)
  ·
    refine ⟨50037030182370576152293723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66716040243160768203058297 50037030182370576152293723)
    ·
      refine ⟨75055545273555864228440585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50037030182370576152293723 75055545273555864228440585)
      ·
        refine ⟨56291658955166898171330439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75055545273555864228440585 56291658955166898171330439)
        ·
          refine ⟨84437488432750347256995659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56291658955166898171330439 84437488432750347256995659)
          ·
            refine ⟨126656232649125520885493489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84437488432750347256995659 126656232649125520885493489)
            ·
              refine ⟨94992174486844140664120117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126656232649125520885493489 94992174486844140664120117)
              ·
                refine ⟨8905516358141638187261261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94992174486844140664120117 8905516358141638187261261)
                ·
                  refine ⟨3339568634303114320222973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8905516358141638187261261 3339568634303114320222973)
                  ·
                    refine ⟨1252338237863667870083615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339568634303114320222973 1252338237863667870083615)
                    ·
                      rfl

theorem cell22_3658380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_3658380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658380 prefixEnd_3658380 := by exact prefixLift 3658380
  have htrace : WordTrace (prefixWord ++ tailWord_3658380) baseStart_3658380 baseEnd_3658380 := by
    simpa [prefixWord, tailWord_3658380, baseEnd_3658380] using wordTrace_append hprefix tailTrace_3658380
  have hstable : (prefixWord ++ tailWord_3658380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658380).length < 2 ^ (prefixWord ++ tailWord_3658380).sum := by decide
  have hdescent : baseEnd_3658380 < baseStart_3658380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658386 : List Nat := [3, 2, 3, 1, 2, 3, 2, 1, 2, 3]
def baseStart_3658386 : Nat := 118140960795 + 3658386 * 2 ^ 59
def prefixEnd_3658386 : Nat := 4983230072969 + 3 ^ 40 * 3658386 * 2
def baseEnd_3658386 : Nat := 1252340291786285854433597

theorem tailTrace_3658386 : CollatzResearch.WordTrace tailWord_3658386 prefixEnd_3658386 1252340291786285854433597 := by
  unfold tailWord_3658386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33358074831074949857708753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88954866216199866287223341 33358074831074949857708753)
  ·
    refine ⟨25018556123306212393281565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33358074831074949857708753 25018556123306212393281565)
    ·
      refine ⟨9381958546239829647480587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25018556123306212393281565 9381958546239829647480587)
      ·
        refine ⟨14072937819359744471220881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9381958546239829647480587 14072937819359744471220881)
        ·
          refine ⟨10554703364519808353415661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14072937819359744471220881 10554703364519808353415661)
          ·
            refine ⟨3958013761694928132530873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10554703364519808353415661 3958013761694928132530873)
            ·
              refine ⟨2968510321271196099398155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958013761694928132530873 2968510321271196099398155)
              ·
                refine ⟨4452765481906794149097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968510321271196099398155 4452765481906794149097233)
                ·
                  refine ⟨3339574111430095611822925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4452765481906794149097233 3339574111430095611822925)
                  ·
                    refine ⟨1252340291786285854433597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339574111430095611822925 1252340291786285854433597)
                    ·
                      rfl

theorem cell22_3658386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_3658386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658386 prefixEnd_3658386 := by exact prefixLift 3658386
  have htrace : WordTrace (prefixWord ++ tailWord_3658386) baseStart_3658386 baseEnd_3658386 := by
    simpa [prefixWord, tailWord_3658386, baseEnd_3658386] using wordTrace_append hprefix tailTrace_3658386
  have hstable : (prefixWord ++ tailWord_3658386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658386).length < 2 ^ (prefixWord ++ tailWord_3658386).sum := by decide
  have hdescent : baseEnd_3658386 < baseStart_3658386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658431 : List Nat := [1, 1, 2, 2, 2, 6, 2, 2, 1, 3]
def baseStart_3658431 : Nat := 118140960795 + 3658431 * 2 ^ 59
def prefixEnd_3658431 : Nat := 4983230072969 + 3 ^ 40 * 3658431 * 2
def baseEnd_3658431 : Nat := 1252355696205920737058459

theorem tailTrace_3658431 : CollatzResearch.WordTrace tailWord_3658431 prefixEnd_3658431 1252355696205920737058459 := by
  unfold tailWord_3658431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133433940609136772116223147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88955960406091181410815431 133433940609136772116223147)
  ·
    refine ⟨200150910913705158174334721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133433940609136772116223147 200150910913705158174334721)
    ·
      refine ⟨150113183185278868630751041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200150910913705158174334721 150113183185278868630751041)
      ·
        refine ⟨112584887388959151473063281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150113183185278868630751041 112584887388959151473063281)
        ·
          refine ⟨84438665541719363604797461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112584887388959151473063281 84438665541719363604797461)
          ·
            refine ⟨3958062447268095168974881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84438665541719363604797461 3958062447268095168974881)
            ·
              refine ⟨2968546835451071376731161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958062447268095168974881 2968546835451071376731161)
              ·
                refine ⟨2226410126588303532548371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2968546835451071376731161 2226410126588303532548371)
                ·
                  refine ⟨3339615189882455298822557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226410126588303532548371 3339615189882455298822557)
                  ·
                    refine ⟨1252355696205920737058459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339615189882455298822557 1252355696205920737058459)
                    ·
                      rfl

theorem cell22_3658431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_3658431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658431 prefixEnd_3658431 := by exact prefixLift 3658431
  have htrace : WordTrace (prefixWord ++ tailWord_3658431) baseStart_3658431 baseEnd_3658431 := by
    simpa [prefixWord, tailWord_3658431, baseEnd_3658431] using wordTrace_append hprefix tailTrace_3658431
  have hstable : (prefixWord ++ tailWord_3658431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658431).length < 2 ^ (prefixWord ++ tailWord_3658431).sum := by decide
  have hdescent : baseEnd_3658431 < baseStart_3658431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658440 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_3658440 : Nat := 118140960795 + 3658440 * 2 ^ 59
def prefixEnd_3658440 : Nat := 4983230072969 + 3 ^ 40 * 3658440 * 2
def baseEnd_3658440 : Nat := 1252358777089847713583431

theorem tailTrace_3658440 : CollatzResearch.WordTrace tailWord_3658440 prefixEnd_3658440 1252358777089847713583431 := by
  unfold tailWord_3658440
  simp only [CollatzResearch.WordTrace]
  refine ⟨66717134433052083326650387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88956179244069444435533849 66717134433052083326650387)
  ·
    refine ⟨100075701649578124989975581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66717134433052083326650387 100075701649578124989975581)
    ·
      refine ⟨37528388118591796871240843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100075701649578124989975581 37528388118591796871240843)
      ·
        refine ⟨56292582177887695306861265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37528388118591796871240843 56292582177887695306861265)
        ·
          refine ⟨42219436633415771480145949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56292582177887695306861265 42219436633415771480145949)
          ·
            refine ⟨15832288737530914305054731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42219436633415771480145949 15832288737530914305054731)
            ·
              refine ⟨23748433106296371457582097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15832288737530914305054731 23748433106296371457582097)
              ·
                refine ⟨17811324829722278593186573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23748433106296371457582097 17811324829722278593186573)
                ·
                  refine ⟨6679246811145854472444965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17811324829722278593186573 6679246811145854472444965)
                  ·
                    refine ⟨1252358777089847713583431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6679246811145854472444965 1252358777089847713583431)
                    ·
                      rfl

theorem cell22_3658440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_3658440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658440 prefixEnd_3658440 := by exact prefixLift 3658440
  have htrace : WordTrace (prefixWord ++ tailWord_3658440) baseStart_3658440 baseEnd_3658440 := by
    simpa [prefixWord, tailWord_3658440, baseEnd_3658440] using wordTrace_append hprefix tailTrace_3658440
  have hstable : (prefixWord ++ tailWord_3658440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658440).length < 2 ^ (prefixWord ++ tailWord_3658440).sum := by decide
  have hdescent : baseEnd_3658440 < baseStart_3658440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658455 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 6]
def baseStart_3658455 : Nat := 118140960795 + 3658455 * 2 ^ 59
def prefixEnd_3658455 : Nat := 4983230072969 + 3 ^ 40 * 3658455 * 2
def baseEnd_3658455 : Nat := 417454637298797558152795

theorem tailTrace_3658455 : CollatzResearch.WordTrace tailWord_3658455 prefixEnd_3658455 417454637298797558152795 := by
  unfold tailWord_3658455
  simp only [CollatzResearch.WordTrace]
  refine ⟨133434815961049824215096819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88956543974033216143397879 133434815961049824215096819)
  ·
    refine ⟨200152223941574736322645229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133434815961049824215096819 200152223941574736322645229)
    ·
      refine ⟨75057083978090526120991961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200152223941574736322645229 75057083978090526120991961)
      ·
        refine ⟨56292812983567894590743971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75057083978090526120991961 56292812983567894590743971)
        ·
          refine ⟨84439219475351841886115957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56292812983567894590743971 84439219475351841886115957)
          ·
            refine ⟨7916176825814235176823371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84439219475351841886115957 7916176825814235176823371)
            ·
              refine ⟨11874265238721352765235057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916176825814235176823371 11874265238721352765235057)
              ·
                refine ⟨8905698929041014573926293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11874265238721352765235057 8905698929041014573926293)
                ·
                  refine ⟨417454637298797558152795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8905698929041014573926293 417454637298797558152795)
                  ·
                    rfl

theorem cell22_3658455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 6].length) (baseStart_3658455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658455 prefixEnd_3658455 := by exact prefixLift 3658455
  have htrace : WordTrace (prefixWord ++ tailWord_3658455) baseStart_3658455 baseEnd_3658455 := by
    simpa [prefixWord, tailWord_3658455, baseEnd_3658455] using wordTrace_append hprefix tailTrace_3658455
  have hstable : (prefixWord ++ tailWord_3658455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658455).length < 2 ^ (prefixWord ++ tailWord_3658455).sum := by decide
  have hdescent : baseEnd_3658455 < baseStart_3658455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658500 : List Nat := [2, 3, 2, 2, 1, 1, 2, 9]
def baseStart_3658500 : Nat := 118140960795 + 3658500 * 2 ^ 59
def prefixEnd_3658500 : Nat := 4983230072969 + 3 ^ 40 * 3658500 * 2
def baseEnd_3658500 : Nat := 139153257368447506342583

theorem tailTrace_3658500 : CollatzResearch.WordTrace tailWord_3658500 prefixEnd_3658500 139153257368447506342583 := by
  unfold tailWord_3658500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66718228622943398450242477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88957638163924531266989969 66718228622943398450242477)
  ·
    refine ⟨25019335733603774418840929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66718228622943398450242477 25019335733603774418840929)
    ·
      refine ⟨18764501800202830814130697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25019335733603774418840929 18764501800202830814130697)
      ·
        refine ⟨14073376350152123110598023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18764501800202830814130697 14073376350152123110598023)
        ·
          refine ⟨21110064525228184665897035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14073376350152123110598023 21110064525228184665897035)
          ·
            refine ⟨31665096787842276998845553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21110064525228184665897035 31665096787842276998845553)
            ·
              refine ⟨23748822590881707749134165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31665096787842276998845553 23748822590881707749134165)
              ·
                refine ⟨139153257368447506342583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23748822590881707749134165 139153257368447506342583)
                ·
                  rfl

theorem cell22_3658500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_3658500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658500 prefixEnd_3658500 := by exact prefixLift 3658500
  have htrace : WordTrace (prefixWord ++ tailWord_3658500) baseStart_3658500 baseEnd_3658500 := by
    simpa [prefixWord, tailWord_3658500, baseEnd_3658500] using wordTrace_append hprefix tailTrace_3658500
  have hstable : (prefixWord ++ tailWord_3658500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658500).length < 2 ^ (prefixWord ++ tailWord_3658500).sum := by decide
  have hdescent : baseEnd_3658500 < baseStart_3658500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658545 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 7]
def baseStart_3658545 : Nat := 118140960795 + 3658545 * 2 ^ 59
def prefixEnd_3658545 : Nat := 4983230072969 + 3 ^ 40 * 3658545 * 2
def baseEnd_3658545 : Nat := 417464906911887479902703

theorem tailTrace_3658545 : CollatzResearch.WordTrace tailWord_3658545 prefixEnd_3658545 417464906911887479902703 := by
  unfold tailWord_3658545
  simp only [CollatzResearch.WordTrace]
  refine ⟨133438098530723769585873089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88958732353815846390582059 133438098530723769585873089)
  ·
    refine ⟨100078573898042827189404817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133438098530723769585873089 100078573898042827189404817)
    ·
      refine ⟨75058930423532120392053613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100078573898042827189404817 75058930423532120392053613)
      ·
        refine ⟨28147098908824545147020105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75058930423532120392053613 28147098908824545147020105)
        ·
          refine ⟨21110324181618408860265079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28147098908824545147020105 21110324181618408860265079)
          ·
            refine ⟨31665486272427613290397619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21110324181618408860265079 31665486272427613290397619)
            ·
              refine ⟨47498229408641419935596429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31665486272427613290397619 47498229408641419935596429)
              ·
                refine ⟨17811836028240532475848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47498229408641419935596429 17811836028240532475848661)
                ·
                  refine ⟨417464906911887479902703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17811836028240532475848661 417464906911887479902703)
                  ·
                    rfl

theorem cell22_3658545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 7].length) (baseStart_3658545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658545 prefixEnd_3658545 := by exact prefixLift 3658545
  have htrace : WordTrace (prefixWord ++ tailWord_3658545) baseStart_3658545 baseEnd_3658545 := by
    simpa [prefixWord, tailWord_3658545, baseEnd_3658545] using wordTrace_append hprefix tailTrace_3658545
  have hstable : (prefixWord ++ tailWord_3658545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658545).length < 2 ^ (prefixWord ++ tailWord_3658545).sum := by decide
  have hdescent : baseEnd_3658545 < baseStart_3658545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658549 : List Nat := [1, 3, 3, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3658549 : Nat := 118140960795 + 3658549 * 2 ^ 59
def prefixEnd_3658549 : Nat := 4983230072969 + 3 ^ 40 * 3658549 * 2
def baseEnd_3658549 : Nat := 1252396090017407762608097

theorem tailTrace_3658549 : CollatzResearch.WordTrace tailWord_3658549 prefixEnd_3658549 1252396090017407762608097 := by
  unfold tailWord_3658549
  simp only [CollatzResearch.WordTrace]
  refine ⟨133438244422709278269018701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88958829615139518846012467 133438244422709278269018701)
  ·
    refine ⟨50039341658515979350882013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133438244422709278269018701 50039341658515979350882013)
    ·
      refine ⟨18764753121943492256580755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50039341658515979350882013 18764753121943492256580755)
      ·
        refine ⟨28147129682915238384871133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18764753121943492256580755 28147129682915238384871133)
        ·
          refine ⟨10555173631093214394326675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28147129682915238384871133 10555173631093214394326675)
          ·
            refine ⟨15832760446639821591490013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555173631093214394326675 15832760446639821591490013)
            ·
              refine ⟨5937285167489933096808755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15832760446639821591490013 5937285167489933096808755)
              ·
                refine ⟨8905927751234899645213133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5937285167489933096808755 8905927751234899645213133)
                ·
                  refine ⟨3339722906713087366954925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8905927751234899645213133 3339722906713087366954925)
                  ·
                    refine ⟨1252396090017407762608097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339722906713087366954925 1252396090017407762608097)
                    ·
                      rfl

theorem cell22_3658549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3658549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658549 prefixEnd_3658549 := by exact prefixLift 3658549
  have htrace : WordTrace (prefixWord ++ tailWord_3658549) baseStart_3658549 baseEnd_3658549 := by
    simpa [prefixWord, tailWord_3658549, baseEnd_3658549] using wordTrace_append hprefix tailTrace_3658549
  have hstable : (prefixWord ++ tailWord_3658549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658549).length < 2 ^ (prefixWord ++ tailWord_3658549).sum := by decide
  have hdescent : baseEnd_3658549 < baseStart_3658549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658560 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_3658560 : Nat := 118140960795 + 3658560 * 2 ^ 59
def prefixEnd_3658560 : Nat := 4983230072969 + 3 ^ 40 * 3658560 * 2
def baseEnd_3658560 : Nat := 1252399855542207400583063

theorem tailTrace_3658560 : CollatzResearch.WordTrace tailWord_3658560 prefixEnd_3658560 1252399855542207400583063 := by
  unfold tailWord_3658560
  simp only [CollatzResearch.WordTrace]
  refine ⟨66719322812834713573834567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88959097083779618098446089 66719322812834713573834567)
  ·
    refine ⟨100078984219252070360751851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66719322812834713573834567 100078984219252070360751851)
    ·
      refine ⟨150118476328878105541127777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100078984219252070360751851 150118476328878105541127777)
      ·
        refine ⟨112588857246658579155845833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150118476328878105541127777 112588857246658579155845833)
        ·
          refine ⟨84441642934993934366884375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112588857246658579155845833 84441642934993934366884375)
          ·
            refine ⟨126662464402490901550326563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84441642934993934366884375 126662464402490901550326563)
            ·
              refine ⟨189993696603736352325489845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126662464402490901550326563 189993696603736352325489845)
              ·
                refine ⟨17811909056600283030514673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189993696603736352325489845 17811909056600283030514673)
                ·
                  refine ⟨13358931792450212272886005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17811909056600283030514673 13358931792450212272886005)
                  ·
                    refine ⟨1252399855542207400583063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13358931792450212272886005 1252399855542207400583063)
                    ·
                      rfl

theorem cell22_3658560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_3658560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658560 prefixEnd_3658560 := by exact prefixLift 3658560
  have htrace : WordTrace (prefixWord ++ tailWord_3658560) baseStart_3658560 baseEnd_3658560 := by
    simpa [prefixWord, tailWord_3658560, baseEnd_3658560] using wordTrace_append hprefix tailTrace_3658560
  have hstable : (prefixWord ++ tailWord_3658560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658560).length < 2 ^ (prefixWord ++ tailWord_3658560).sum := by decide
  have hdescent : baseEnd_3658560 < baseStart_3658560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658635 : List Nat := [1, 1, 1, 1, 4, 2, 2, 10]
def baseStart_3658635 : Nat := 118140960795 + 3658635 * 2 ^ 59
def prefixEnd_3658635 : Nat := 4983230072969 + 3 ^ 40 * 3658635 * 2
def baseEnd_3658635 : Nat := 139158392174992467217537

theorem tailTrace_3658635 : CollatzResearch.WordTrace tailWord_3658635 prefixEnd_3658635 139158392174992467217537 := by
  unfold tailWord_3658635
  simp only [CollatzResearch.WordTrace]
  refine ⟨133441381100397714956649359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88960920733598476637766239 133441381100397714956649359)
  ·
    refine ⟨200162071650596572434974039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133441381100397714956649359 200162071650596572434974039)
    ·
      refine ⟨300243107475894858652461059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200162071650596572434974039 300243107475894858652461059)
      ·
        refine ⟨450364661213842287978691589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300243107475894858652461059 450364661213842287978691589)
        ·
          refine ⟨84443373977595428996004673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 450364661213842287978691589 84443373977595428996004673)
          ·
            refine ⟨63332530483196571747003505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84443373977595428996004673 63332530483196571747003505)
            ·
              refine ⟨47499397862397428810252629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63332530483196571747003505 47499397862397428810252629)
              ·
                refine ⟨139158392174992467217537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47499397862397428810252629 139158392174992467217537)
                ·
                  rfl

theorem cell22_3658635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 10].length) (baseStart_3658635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658635 prefixEnd_3658635 := by exact prefixLift 3658635
  have htrace : WordTrace (prefixWord ++ tailWord_3658635) baseStart_3658635 baseEnd_3658635 := by
    simpa [prefixWord, tailWord_3658635, baseEnd_3658635] using wordTrace_append hprefix tailTrace_3658635
  have hstable : (prefixWord ++ tailWord_3658635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658635).length < 2 ^ (prefixWord ++ tailWord_3658635).sum := by decide
  have hdescent : baseEnd_3658635 < baseStart_3658635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658667 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 7, 3]
def baseStart_3658667 : Nat := 118140960795 + 3658667 * 2 ^ 59
def prefixEnd_3658667 : Nat := 4983230072969 + 3 ^ 40 * 3658667 * 2
def baseEnd_3658667 : Nat := 1252436483828894788157735

theorem tailTrace_3658667 : CollatzResearch.WordTrace tailWord_3658667 prefixEnd_3658667 1252436483828894788157735 := by
  unfold tailWord_3658667
  simp only [CollatzResearch.WordTrace]
  refine ⟨133442548236281784421814255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88961698824187856281209503 133442548236281784421814255)
  ·
    refine ⟨200163822354422676632721383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133442548236281784421814255 200163822354422676632721383)
    ·
      refine ⟨300245733531634014949082075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200163822354422676632721383 300245733531634014949082075)
      ·
        refine ⟨450368600297451022423623113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300245733531634014949082075 450368600297451022423623113)
        ·
          refine ⟨337776450223088266817717335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450368600297451022423623113 337776450223088266817717335)
          ·
            refine ⟨506664675334632400226576003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337776450223088266817717335 506664675334632400226576003)
            ·
              refine ⟨759997013001948600339864005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 506664675334632400226576003 759997013001948600339864005)
              ·
                refine ⟨142499439937865362563724501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 759997013001948600339864005 142499439937865362563724501)
                ·
                  refine ⟨3339830623543719435087293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142499439937865362563724501 3339830623543719435087293)
                  ·
                    refine ⟨1252436483828894788157735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339830623543719435087293 1252436483828894788157735)
                    ·
                      rfl

theorem cell22_3658667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 7, 3].length) (baseStart_3658667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658667 prefixEnd_3658667 := by exact prefixLift 3658667
  have htrace : WordTrace (prefixWord ++ tailWord_3658667) baseStart_3658667 baseEnd_3658667 := by
    simpa [prefixWord, tailWord_3658667, baseEnd_3658667] using wordTrace_append hprefix tailTrace_3658667
  have hstable : (prefixWord ++ tailWord_3658667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658667).length < 2 ^ (prefixWord ++ tailWord_3658667).sum := by decide
  have hdescent : baseEnd_3658667 < baseStart_3658667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658673 : List Nat := [1, 2, 2, 4, 3, 1, 3, 1, 2, 3]
def baseStart_3658673 : Nat := 118140960795 + 3658673 * 2 ^ 59
def prefixEnd_3658673 : Nat := 4983230072969 + 3 ^ 40 * 3658673 * 2
def baseEnd_3658673 : Nat := 1252438537751512772507717

theorem tailTrace_3658673 : CollatzResearch.WordTrace tailWord_3658673 prefixEnd_3658673 1252438537751512772507717 := by
  unfold tailWord_3658673
  simp only [CollatzResearch.WordTrace]
  refine ⟨133442767074260047446532673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88961844716173364964355115 133442767074260047446532673)
  ·
    refine ⟨100082075305695035584899505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133442767074260047446532673 100082075305695035584899505)
    ·
      refine ⟨75061556479271276688674629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100082075305695035584899505 75061556479271276688674629)
      ·
        refine ⟨14074041839863364379126493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75061556479271276688674629 14074041839863364379126493)
        ·
          refine ⟨5277765689948761642172435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14074041839863364379126493 5277765689948761642172435)
          ·
            refine ⟨7916648534923142463258653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5277765689948761642172435 7916648534923142463258653)
            ·
              refine ⟨2968743200596178423721995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7916648534923142463258653 2968743200596178423721995)
              ·
                refine ⟨4453114800894267635582993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2968743200596178423721995 4453114800894267635582993)
                ·
                  refine ⟨3339836100670700726687245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453114800894267635582993 3339836100670700726687245)
                  ·
                    refine ⟨1252438537751512772507717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339836100670700726687245 1252438537751512772507717)
                    ·
                      rfl

theorem cell22_3658673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 1, 2, 3].length) (baseStart_3658673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658673 prefixEnd_3658673 := by exact prefixLift 3658673
  have htrace : WordTrace (prefixWord ++ tailWord_3658673) baseStart_3658673 baseEnd_3658673 := by
    simpa [prefixWord, tailWord_3658673, baseEnd_3658673] using wordTrace_append hprefix tailTrace_3658673
  have hstable : (prefixWord ++ tailWord_3658673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658673).length < 2 ^ (prefixWord ++ tailWord_3658673).sum := by decide
  have hdescent : baseEnd_3658673 < baseStart_3658673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658776 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_3658776 : Nat := 118140960795 + 3658776 * 2 ^ 59
def prefixEnd_3658776 : Nat := 4983230072969 + 3 ^ 40 * 3658776 * 2
def baseEnd_3658776 : Nat := 417491265585484945727467

theorem tailTrace_3658776 : CollatzResearch.WordTrace tailWord_3658776 prefixEnd_3658776 417491265585484945727467 := by
  unfold tailWord_3658776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66723261896443448018766091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88964349195257930691688121 66723261896443448018766091)
  ·
    refine ⟨100084892844665172028149137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66723261896443448018766091 100084892844665172028149137)
    ·
      refine ⟨75063669633498879021111853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100084892844665172028149137 75063669633498879021111853)
      ·
        refine ⟨28148876112562079632916945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75063669633498879021111853 28148876112562079632916945)
        ·
          refine ⟨21111657084421559724687709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28148876112562079632916945 21111657084421559724687709)
          ·
            refine ⟨7916871406658084896757891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21111657084421559724687709 7916871406658084896757891)
            ·
              refine ⟨11875307109987127345136837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916871406658084896757891 11875307109987127345136837)
              ·
                refine ⟨2226620083122586377213157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11875307109987127345136837 2226620083122586377213157)
                ·
                  refine ⟨417491265585484945727467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226620083122586377213157 417491265585484945727467)
                  ·
                    rfl

theorem cell22_3658776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_3658776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658776 prefixEnd_3658776 := by exact prefixLift 3658776
  have htrace : WordTrace (prefixWord ++ tailWord_3658776) baseStart_3658776 baseEnd_3658776 := by
    simpa [prefixWord, tailWord_3658776, baseEnd_3658776] using wordTrace_append hprefix tailTrace_3658776
  have hstable : (prefixWord ++ tailWord_3658776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658776).length < 2 ^ (prefixWord ++ tailWord_3658776).sum := by decide
  have hdescent : baseEnd_3658776 < baseStart_3658776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658791 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3658791 : Nat := 118140960795 + 3658791 * 2 ^ 59
def prefixEnd_3658791 : Nat := 4983230072969 + 3 ^ 40 * 3658791 * 2
def baseEnd_3658791 : Nat := 1252478931562999798057355

theorem tailTrace_3658791 : CollatzResearch.WordTrace tailWord_3658791 prefixEnd_3658791 1252478931562999798057355 := by
  unfold tailWord_3658791
  simp only [CollatzResearch.WordTrace]
  refine ⟨133447070887832553599328227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88964713925221702399552151 133447070887832553599328227)
  ·
    refine ⟨200170606331748830398992341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133447070887832553599328227 200170606331748830398992341)
    ·
      refine ⟨4691498585900363212476383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 200170606331748830398992341 4691498585900363212476383)
      ·
        refine ⟨7037247878850544818714575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691498585900363212476383 7037247878850544818714575)
        ·
          refine ⟨10555871818275817228071863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037247878850544818714575 10555871818275817228071863)
          ·
            refine ⟨15833807727413725842107795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10555871818275817228071863 15833807727413725842107795)
            ·
              refine ⟨23750711591120588763161693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15833807727413725842107795 23750711591120588763161693)
              ·
                refine ⟨8906516846670220786185635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23750711591120588763161693 8906516846670220786185635)
                ·
                  refine ⟨13359775270005331179278453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8906516846670220786185635 13359775270005331179278453)
                  ·
                    refine ⟨1252478931562999798057355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13359775270005331179278453 1252478931562999798057355)
                    ·
                      rfl

theorem cell22_3658791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3658791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658791 prefixEnd_3658791 := by exact prefixLift 3658791
  have htrace : WordTrace (prefixWord ++ tailWord_3658791) baseStart_3658791 baseEnd_3658791 := by
    simpa [prefixWord, tailWord_3658791, baseEnd_3658791] using wordTrace_append hprefix tailTrace_3658791
  have hstable : (prefixWord ++ tailWord_3658791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658791).length < 2 ^ (prefixWord ++ tailWord_3658791).sum := by decide
  have hdescent : baseEnd_3658791 < baseStart_3658791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658806 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3658806 : Nat := 118140960795 + 3658806 * 2 ^ 59
def prefixEnd_3658806 : Nat := 4983230072969 + 3 ^ 40 * 3658806 * 2
def baseEnd_3658806 : Nat := 1252484066369544758932309

theorem tailTrace_3658806 : CollatzResearch.WordTrace tailWord_3658806 prefixEnd_3658806 1252484066369544758932309 := by
  unfold tailWord_3658806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8340476123923638197570267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88965078655185474107416181 8340476123923638197570267)
  ·
    refine ⟨12510714185885457296355401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8340476123923638197570267 12510714185885457296355401)
    ·
      refine ⟨9383035639414092972266551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12510714185885457296355401 9383035639414092972266551)
      ·
        refine ⟨14074553459121139458399827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383035639414092972266551 14074553459121139458399827)
        ·
          refine ⟨21111830188681709187599741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14074553459121139458399827 21111830188681709187599741)
          ·
            refine ⟨7916936320755640945349903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21111830188681709187599741 7916936320755640945349903)
            ·
              refine ⟨11875404481133461418024855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7916936320755640945349903 11875404481133461418024855)
              ·
                refine ⟨17813106721700192127037283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11875404481133461418024855 17813106721700192127037283)
                ·
                  refine ⟨26719660082550288190555925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17813106721700192127037283 26719660082550288190555925)
                  ·
                    refine ⟨1252484066369544758932309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26719660082550288190555925 1252484066369544758932309)
                    ·
                      rfl

theorem cell22_3658806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3658806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658806 prefixEnd_3658806 := by exact prefixLift 3658806
  have htrace : WordTrace (prefixWord ++ tailWord_3658806) baseStart_3658806 baseEnd_3658806 := by
    simpa [prefixWord, tailWord_3658806, baseEnd_3658806] using wordTrace_append hprefix tailTrace_3658806
  have hstable : (prefixWord ++ tailWord_3658806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658806).length < 2 ^ (prefixWord ++ tailWord_3658806).sum := by decide
  have hdescent : baseEnd_3658806 < baseStart_3658806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658819 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 5, 3]
def baseStart_3658819 : Nat := 118140960795 + 3658819 * 2 ^ 59
def prefixEnd_3658819 : Nat := 4983230072969 + 3 ^ 40 * 3658819 * 2
def baseEnd_3658819 : Nat := 1252488516535217058357269

theorem tailTrace_3658819 : CollatzResearch.WordTrace tailWord_3658819 prefixEnd_3658819 1252488516535217058357269 := by
  unfold tailWord_3658819
  simp only [CollatzResearch.WordTrace]
  refine ⟨133448092131731114381347511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88965394754487409587565007 133448092131731114381347511)
  ·
    refine ⟨200172138197596671572021267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133448092131731114381347511 200172138197596671572021267)
    ·
      refine ⟨300258207296395007358031901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200172138197596671572021267 300258207296395007358031901)
      ·
        refine ⟨112596827736148127759261963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300258207296395007358031901 112596827736148127759261963)
        ·
          refine ⟨168895241604222191638892945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112596827736148127759261963 168895241604222191638892945)
          ·
            refine ⟨126671431203166643729169709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168895241604222191638892945 126671431203166643729169709)
            ·
              refine ⟨47501786701187491398438641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126671431203166643729169709 47501786701187491398438641)
              ·
                refine ⟨35626340025890618548828981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47501786701187491398438641 35626340025890618548828981)
                ·
                  refine ⟨3339969377427245488952717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35626340025890618548828981 3339969377427245488952717)
                  ·
                    refine ⟨1252488516535217058357269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339969377427245488952717 1252488516535217058357269)
                    ·
                      rfl

theorem cell22_3658819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 5, 3].length) (baseStart_3658819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658819 prefixEnd_3658819 := by exact prefixLift 3658819
  have htrace : WordTrace (prefixWord ++ tailWord_3658819) baseStart_3658819 baseEnd_3658819 := by
    simpa [prefixWord, tailWord_3658819, baseEnd_3658819] using wordTrace_append hprefix tailTrace_3658819
  have hstable : (prefixWord ++ tailWord_3658819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658819).length < 2 ^ (prefixWord ++ tailWord_3658819).sum := by decide
  have hdescent : baseEnd_3658819 < baseStart_3658819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658836 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3658836 : Nat := 118140960795 + 3658836 * 2 ^ 59
def prefixEnd_3658836 : Nat := 4983230072969 + 3 ^ 40 * 3658836 * 2
def baseEnd_3658836 : Nat := 1252494335982634680682217

theorem tailTrace_3658836 : CollatzResearch.WordTrace tailWord_3658836 prefixEnd_3658836 1252494335982634680682217 := by
  unfold tailWord_3658836
  simp only [CollatzResearch.WordTrace]
  refine ⟨66724356086334763142358181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88965808115113017523144241 66724356086334763142358181)
  ·
    refine ⟨12510816766187768089192159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66724356086334763142358181 12510816766187768089192159)
    ·
      refine ⟨18766225149281652133788239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12510816766187768089192159 18766225149281652133788239)
      ·
        refine ⟨28149337723922478200682359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18766225149281652133788239 28149337723922478200682359)
        ·
          refine ⟨42224006585883717301023539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28149337723922478200682359 42224006585883717301023539)
          ·
            refine ⟨63336009878825575951535309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42224006585883717301023539 63336009878825575951535309)
            ·
              refine ⟨23751003704559590981825741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63336009878825575951535309 23751003704559590981825741)
              ·
                refine ⟨8906626389209846618184653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23751003704559590981825741 8906626389209846618184653)
                ·
                  refine ⟨3339984895953692481819245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8906626389209846618184653 3339984895953692481819245)
                  ·
                    refine ⟨1252494335982634680682217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3339984895953692481819245 1252494335982634680682217)
                    ·
                      rfl

theorem cell22_3658836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3658836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658836 prefixEnd_3658836 := by exact prefixLift 3658836
  have htrace : WordTrace (prefixWord ++ tailWord_3658836) baseStart_3658836 baseEnd_3658836 := by
    simpa [prefixWord, tailWord_3658836, baseEnd_3658836] using wordTrace_append hprefix tailTrace_3658836
  have hstable : (prefixWord ++ tailWord_3658836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658836).length < 2 ^ (prefixWord ++ tailWord_3658836).sum := by decide
  have hdescent : baseEnd_3658836 < baseStart_3658836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658849 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 5]
def baseStart_3658849 : Nat := 118140960795 + 3658849 * 2 ^ 59
def prefixEnd_3658849 : Nat := 4983230072969 + 3 ^ 40 * 3658849 * 2
def baseEnd_3658849 : Nat := 417499595382768993369059

theorem tailTrace_3658849 : CollatzResearch.WordTrace tailWord_3658849 prefixEnd_3658849 417499595382768993369059 := by
  unfold tailWord_3658849
  simp only [CollatzResearch.WordTrace]
  refine ⟨133449186321622429504939601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88966124214414953003293067 133449186321622429504939601)
  ·
    refine ⟨100086889741216822128704701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133449186321622429504939601 100086889741216822128704701)
    ·
      refine ⟨37532583652956308298264263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100086889741216822128704701 37532583652956308298264263)
      ·
        refine ⟨56298875479434462447396395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37532583652956308298264263 56298875479434462447396395)
        ·
          refine ⟨84448313219151693671094593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56298875479434462447396395 84448313219151693671094593)
          ·
            refine ⟨63336234914363770253320945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84448313219151693671094593 63336234914363770253320945)
            ·
              refine ⟨47502176185772827689990709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63336234914363770253320945 47502176185772827689990709)
              ·
                refine ⟨4453329017416202595936629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47502176185772827689990709 4453329017416202595936629)
                ·
                  refine ⟨417499595382768993369059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453329017416202595936629 417499595382768993369059)
                  ·
                    rfl

theorem cell22_3658849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 5].length) (baseStart_3658849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658849 prefixEnd_3658849 := by exact prefixLift 3658849
  have htrace : WordTrace (prefixWord ++ tailWord_3658849) baseStart_3658849 baseEnd_3658849 := by
    simpa [prefixWord, tailWord_3658849, baseEnd_3658849] using wordTrace_append hprefix tailTrace_3658849
  have hstable : (prefixWord ++ tailWord_3658849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658849).length < 2 ^ (prefixWord ++ tailWord_3658849).sum := by decide
  have hdescent : baseEnd_3658849 < baseStart_3658849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658941 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3658941 : Nat := 118140960795 + 3658941 * 2 ^ 59
def prefixEnd_3658941 : Nat := 4983230072969 + 3 ^ 40 * 3658941 * 2
def baseEnd_3658941 : Nat := 1252530279628449406806895

theorem tailTrace_3658941 : CollatzResearch.WordTrace tailWord_3658941 prefixEnd_3658941 1252530279628449406806895 := by
  unfold tailWord_3658941
  simp only [CollatzResearch.WordTrace]
  refine ⟨133452541837289129217288677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88968361224859419478192451 133452541837289129217288677)
  ·
    refine ⟨25022351594491711728241627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133452541837289129217288677 25022351594491711728241627)
    ·
      refine ⟨37533527391737567592362441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25022351594491711728241627 37533527391737567592362441)
      ·
        refine ⟨28150145543803175694271831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37533527391737567592362441 28150145543803175694271831)
        ·
          refine ⟨42225218315704763541407747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28150145543803175694271831 42225218315704763541407747)
          ·
            refine ⟨63337827473557145312111621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42225218315704763541407747 63337827473557145312111621)
            ·
              refine ⟨11875842651291964746020929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63337827473557145312111621 11875842651291964746020929)
              ·
                refine ⟨8906881988468973559515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11875842651291964746020929 8906881988468973559515697)
                ·
                  refine ⟨6680161491351730169636773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8906881988468973559515697 6680161491351730169636773)
                  ·
                    refine ⟨1252530279628449406806895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680161491351730169636773 1252530279628449406806895)
                    ·
                      rfl

theorem cell22_3658941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3658941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658941 prefixEnd_3658941 := by exact prefixLift 3658941
  have htrace : WordTrace (prefixWord ++ tailWord_3658941) baseStart_3658941 baseEnd_3658941 := by
    simpa [prefixWord, tailWord_3658941, baseEnd_3658941] using wordTrace_append hprefix tailTrace_3658941
  have hstable : (prefixWord ++ tailWord_3658941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658941).length < 2 ^ (prefixWord ++ tailWord_3658941).sum := by decide
  have hdescent : baseEnd_3658941 < baseStart_3658941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658945 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 4]
def baseStart_3658945 : Nat := 118140960795 + 3658945 * 2 ^ 59
def prefixEnd_3658945 : Nat := 4983230072969 + 3 ^ 40 * 3658945 * 2
def baseEnd_3658945 : Nat := 417510549636731576568961

theorem tailTrace_3658945 : CollatzResearch.WordTrace tailWord_3658945 prefixEnd_3658945 417510549636731576568961 := by
  unfold tailWord_3658945
  simp only [CollatzResearch.WordTrace]
  refine ⟨133452687729274637900434289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88968458486183091933622859 133452687729274637900434289)
  ·
    refine ⟨100089515796955978425325717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133452687729274637900434289 100089515796955978425325717)
    ·
      refine ⟨4691696052982311488687143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100089515796955978425325717 4691696052982311488687143)
      ·
        refine ⟨7037544079473467233030715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4691696052982311488687143 7037544079473467233030715)
        ·
          refine ⟨10556316119210200849546073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7037544079473467233030715 10556316119210200849546073)
          ·
            refine ⟨7917237089407650637159555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10556316119210200849546073 7917237089407650637159555)
            ·
              refine ⟨11875855634111475955739333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917237089407650637159555 11875855634111475955739333)
              ·
                refine ⟨2226722931395901741701125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11875855634111475955739333 2226722931395901741701125)
                ·
                  refine ⟨417510549636731576568961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226722931395901741701125 417510549636731576568961)
                  ·
                    rfl

theorem cell22_3658945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 4].length) (baseStart_3658945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658945 prefixEnd_3658945 := by exact prefixLift 3658945
  have htrace : WordTrace (prefixWord ++ tailWord_3658945) baseStart_3658945 baseEnd_3658945 := by
    simpa [prefixWord, tailWord_3658945, baseEnd_3658945] using wordTrace_append hprefix tailTrace_3658945
  have hstable : (prefixWord ++ tailWord_3658945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658945).length < 2 ^ (prefixWord ++ tailWord_3658945).sum := by decide
  have hdescent : baseEnd_3658945 < baseStart_3658945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658969 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 4, 6]
def baseStart_3658969 : Nat := 118140960795 + 3658969 * 2 ^ 59
def prefixEnd_3658969 : Nat := 4983230072969 + 3 ^ 40 * 3658969 * 2
def baseEnd_3658969 : Nat := 1252539864600666667106809

theorem tailTrace_3658969 : CollatzResearch.WordTrace tailWord_3658969 prefixEnd_3658969 1252539864600666667106809 := by
  unfold tailWord_3658969
  simp only [CollatzResearch.WordTrace]
  refine ⟨133453563081187689999307961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88969042054125126666205307 133453563081187689999307961)
  ·
    refine ⟨100090172310890767499480971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133453563081187689999307961 100090172310890767499480971)
    ·
      refine ⟨150135258466336151249221457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100090172310890767499480971 150135258466336151249221457)
      ·
        refine ⟨112601443849752113436916093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150135258466336151249221457 112601443849752113436916093)
        ·
          refine ⟨42225541443657042538843535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112601443849752113436916093 42225541443657042538843535)
          ·
            refine ⟨63338312165485563808265303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42225541443657042538843535 63338312165485563808265303)
            ·
              refine ⟨95007468248228345712397955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63338312165485563808265303 95007468248228345712397955)
              ·
                refine ⟨142511202372342518568596933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95007468248228345712397955 142511202372342518568596933)
                ·
                  refine ⟨26720850444814222231611925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142511202372342518568596933 26720850444814222231611925)
                  ·
                    refine ⟨1252539864600666667106809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26720850444814222231611925 1252539864600666667106809)
                    ·
                      rfl

theorem cell22_3658969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 6].length) (baseStart_3658969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658969 prefixEnd_3658969 := by exact prefixLift 3658969
  have htrace : WordTrace (prefixWord ++ tailWord_3658969) baseStart_3658969 baseEnd_3658969 := by
    simpa [prefixWord, tailWord_3658969, baseEnd_3658969] using wordTrace_append hprefix tailTrace_3658969
  have hstable : (prefixWord ++ tailWord_3658969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658969).length < 2 ^ (prefixWord ++ tailWord_3658969).sum := by decide
  have hdescent : baseEnd_3658969 < baseStart_3658969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3658999 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3658999 : Nat := 118140960795 + 3658999 * 2 ^ 59
def prefixEnd_3658999 : Nat := 4983230072969 + 3 ^ 40 * 3658999 * 2
def baseEnd_3658999 : Nat := 1252550134213756588856717

theorem tailTrace_3658999 : CollatzResearch.WordTrace tailWord_3658999 prefixEnd_3658999 1252550134213756588856717 := by
  unfold tailWord_3658999
  simp only [CollatzResearch.WordTrace]
  refine ⟨133454657271079005122900051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88969771514052670081933367 133454657271079005122900051)
  ·
    refine ⟨200181985906618507684350077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133454657271079005122900051 200181985906618507684350077)
    ·
      refine ⟨75068244714981940381631279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200181985906618507684350077 75068244714981940381631279)
      ·
        refine ⟨112602367072472910572446919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75068244714981940381631279 112602367072472910572446919)
        ·
          refine ⟨168903550608709365858670379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112602367072472910572446919 168903550608709365858670379)
          ·
            refine ⟨253355325913064048788005569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168903550608709365858670379 253355325913064048788005569)
            ·
              refine ⟨190016494434798036591004177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253355325913064048788005569 190016494434798036591004177)
              ·
                refine ⟨142512370826098527443253133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190016494434798036591004177 142512370826098527443253133)
                ·
                  refine ⟨53442139059786947791219925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142512370826098527443253133 53442139059786947791219925)
                  ·
                    refine ⟨1252550134213756588856717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53442139059786947791219925 1252550134213756588856717)
                    ·
                      rfl

theorem cell22_3658999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3658999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3658999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3658999 prefixEnd_3658999 := by exact prefixLift 3658999
  have htrace : WordTrace (prefixWord ++ tailWord_3658999) baseStart_3658999 baseEnd_3658999 := by
    simpa [prefixWord, tailWord_3658999, baseEnd_3658999] using wordTrace_append hprefix tailTrace_3658999
  have hstable : (prefixWord ++ tailWord_3658999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3658999).length < 2 ^ (prefixWord ++ tailWord_3658999).sum := by decide
  have hdescent : baseEnd_3658999 < baseStart_3658999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3658999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659039 : List Nat := [1, 1, 2, 4, 5, 1, 1, 3, 1, 3]
def baseStart_3659039 : Nat := 118140960795 + 3659039 * 2 ^ 59
def prefixEnd_3659039 : Nat := 4983230072969 + 3 ^ 40 * 3659039 * 2
def baseEnd_3659039 : Nat := 1252563827031209817856595

theorem tailTrace_3659039 : CollatzResearch.WordTrace tailWord_3659039 prefixEnd_3659039 1252563827031209817856595 := by
  unfold tailWord_3659039
  simp only [CollatzResearch.WordTrace]
  refine ⟨133456116190934091954356171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88970744127289394636237447 133456116190934091954356171)
  ·
    refine ⟨200184174286401137931534257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133456116190934091954356171 200184174286401137931534257)
    ·
      refine ⟨150138130714800853448650693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200184174286401137931534257 150138130714800853448650693)
      ·
        refine ⟨28150899509025160021622005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150138130714800853448650693 28150899509025160021622005)
        ·
          refine ⟨2639146828971108752027063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28150899509025160021622005 2639146828971108752027063)
          ·
            refine ⟨3958720243456663128040595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639146828971108752027063 3958720243456663128040595)
            ·
              refine ⟨5938080365184994692060893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958720243456663128040595 5938080365184994692060893)
              ·
                refine ⟨2226780136944373009522835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938080365184994692060893 2226780136944373009522835)
                ·
                  refine ⟨3340170205416559514284253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2226780136944373009522835 3340170205416559514284253)
                  ·
                    refine ⟨1252563827031209817856595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340170205416559514284253 1252563827031209817856595)
                    ·
                      rfl

theorem cell22_3659039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_3659039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659039 prefixEnd_3659039 := by exact prefixLift 3659039
  have htrace : WordTrace (prefixWord ++ tailWord_3659039) baseStart_3659039 baseEnd_3659039 := by
    simpa [prefixWord, tailWord_3659039, baseEnd_3659039] using wordTrace_append hprefix tailTrace_3659039
  have hstable : (prefixWord ++ tailWord_3659039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659039).length < 2 ^ (prefixWord ++ tailWord_3659039).sum := by decide
  have hdescent : baseEnd_3659039 < baseStart_3659039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659069 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 5]
def baseStart_3659069 : Nat := 118140960795 + 3659069 * 2 ^ 59
def prefixEnd_3659069 : Nat := 4983230072969 + 3 ^ 40 * 3659069 * 2
def baseEnd_3659069 : Nat := 417524698881433246535501

theorem tailTrace_3659069 : CollatzResearch.WordTrace tailWord_3659069 prefixEnd_3659069 417524698881433246535501 := by
  unfold tailWord_3659069
  simp only [CollatzResearch.WordTrace]
  refine ⟨133457210380825407077948261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88971473587216938051965507 133457210380825407077948261)
  ·
    refine ⟨25023226946404763827115299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133457210380825407077948261 25023226946404763827115299)
    ·
      refine ⟨37534840419607145740672949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25023226946404763827115299 37534840419607145740672949)
      ·
        refine ⟨3518891289338169913188089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37534840419607145740672949 3518891289338169913188089)
        ·
          refine ⟨2639168467003627434891067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3518891289338169913188089 2639168467003627434891067)
          ·
            refine ⟨3958752700505441152336601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639168467003627434891067 3958752700505441152336601)
            ·
              refine ⟨2969064525379080864252451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958752700505441152336601 2969064525379080864252451)
              ·
                refine ⟨4453596788068621296378677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969064525379080864252451 4453596788068621296378677)
                ·
                  refine ⟨417524698881433246535501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453596788068621296378677 417524698881433246535501)
                  ·
                    rfl

theorem cell22_3659069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_3659069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659069 prefixEnd_3659069 := by exact prefixLift 3659069
  have htrace : WordTrace (prefixWord ++ tailWord_3659069) baseStart_3659069 baseEnd_3659069 := by
    simpa [prefixWord, tailWord_3659069, baseEnd_3659069] using wordTrace_append hprefix tailTrace_3659069
  have hstable : (prefixWord ++ tailWord_3659069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659069).length < 2 ^ (prefixWord ++ tailWord_3659069).sum := by decide
  have hdescent : baseEnd_3659069 < baseStart_3659069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659093 : List Nat := [1, 3, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_3659093 : Nat := 118140960795 + 3659093 * 2 ^ 59
def prefixEnd_3659093 : Nat := 4983230072969 + 3 ^ 40 * 3659093 * 2
def baseEnd_3659093 : Nat := 1252582312334771677006429

theorem tailTrace_3659093 : CollatzResearch.WordTrace tailWord_3659093 prefixEnd_3659093 1252582312334771677006429 := by
  unfold tailWord_3659093
  simp only [CollatzResearch.WordTrace]
  refine ⟨133458085732738459176821933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88972057155158972784547955 133458085732738459176821933)
  ·
    refine ⟨50046782149776922191308225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133458085732738459176821933 50046782149776922191308225)
    ·
      refine ⟨37535086612332691643481169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50046782149776922191308225 37535086612332691643481169)
      ·
        refine ⟨28151314959249518732610877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37535086612332691643481169 28151314959249518732610877)
        ·
          refine ⟨10556743109718569524729079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28151314959249518732610877 10556743109718569524729079)
          ·
            refine ⟨15835114664577854287093619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10556743109718569524729079 15835114664577854287093619)
            ·
              refine ⟨23752671996866781430640429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15835114664577854287093619 23752671996866781430640429)
              ·
                refine ⟨8907251998825043036490161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23752671996866781430640429 8907251998825043036490161)
                ·
                  refine ⟨6680438999118782277367621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8907251998825043036490161 6680438999118782277367621)
                  ·
                    refine ⟨1252582312334771677006429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6680438999118782277367621 1252582312334771677006429)
                    ·
                      rfl

theorem cell22_3659093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_3659093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659093 prefixEnd_3659093 := by exact prefixLift 3659093
  have htrace : WordTrace (prefixWord ++ tailWord_3659093) baseStart_3659093 baseEnd_3659093 := by
    simpa [prefixWord, tailWord_3659093, baseEnd_3659093] using wordTrace_append hprefix tailTrace_3659093
  have hstable : (prefixWord ++ tailWord_3659093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659093).length < 2 ^ (prefixWord ++ tailWord_3659093).sum := by decide
  have hdescent : baseEnd_3659093 < baseStart_3659093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659112 : List Nat := [2, 1, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3659112 : Nat := 118140960795 + 3659112 * 2 ^ 59
def prefixEnd_3659112 : Nat := 4983230072969 + 3 ^ 40 * 3659112 * 2
def baseEnd_3659112 : Nat := 1252588816423061960781371

theorem tailTrace_3659112 : CollatzResearch.WordTrace tailWord_3659112 prefixEnd_3659112 1252588816423061960781371 := by
  unfold tailWord_3659112
  simp only [CollatzResearch.WordTrace]
  refine ⟨66729389359834812710881795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88972519146446416947842393 66729389359834812710881795)
  ·
    refine ⟨100094084039752219066322693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66729389359834812710881795 100094084039752219066322693)
    ·
      refine ⟨18767640757453541074935505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100094084039752219066322693 18767640757453541074935505)
      ·
        refine ⟨14075730568090155806201629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18767640757453541074935505 14075730568090155806201629)
        ·
          refine ⟨5278398963033808427325611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14075730568090155806201629 5278398963033808427325611)
          ·
            refine ⟨7917598444550712640988417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278398963033808427325611 7917598444550712640988417)
            ·
              refine ⟨5938198833413034480741313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7917598444550712640988417 5938198833413034480741313)
              ·
                refine ⟨4453649125059775860555985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938198833413034480741313 4453649125059775860555985)
                ·
                  refine ⟨3340236843794831895416989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453649125059775860555985 3340236843794831895416989)
                  ·
                    refine ⟨1252588816423061960781371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340236843794831895416989 1252588816423061960781371)
                    ·
                      rfl

theorem cell22_3659112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3659112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659112 prefixEnd_3659112 := by exact prefixLift 3659112
  have htrace : WordTrace (prefixWord ++ tailWord_3659112) baseStart_3659112 baseEnd_3659112 := by
    simpa [prefixWord, tailWord_3659112, baseEnd_3659112] using wordTrace_append hprefix tailTrace_3659112
  have hstable : (prefixWord ++ tailWord_3659112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659112).length < 2 ^ (prefixWord ++ tailWord_3659112).sum := by decide
  have hdescent : baseEnd_3659112 < baseStart_3659112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659114 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_3659114 : Nat := 118140960795 + 3659114 * 2 ^ 59
def prefixEnd_3659114 : Nat := 4983230072969 + 3 ^ 40 * 3659114 * 2
def baseEnd_3659114 : Nat := 417529833687978207410455

theorem tailTrace_3659114 : CollatzResearch.WordTrace tailWord_3659114 prefixEnd_3659114 417529833687978207410455 := by
  unfold tailWord_3659114
  simp only [CollatzResearch.WordTrace]
  refine ⟨33364712916415594940834099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88972567777108253175557597 33364712916415594940834099)
  ·
    refine ⟨50047069374623392411251149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33364712916415594940834099 50047069374623392411251149)
    ·
      refine ⟨18767651015483772154219181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50047069374623392411251149 18767651015483772154219181)
      ·
        refine ⟨7037869130806414557832193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18767651015483772154219181 7037869130806414557832193)
        ·
          refine ⟨5278401848104810918374145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7037869130806414557832193 5278401848104810918374145)
          ·
            refine ⟨3958801386078608188780609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278401848104810918374145 3958801386078608188780609)
            ·
              refine ⟨2969101039558956141585457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3958801386078608188780609 2969101039558956141585457)
              ·
                refine ⟨2226825779669217106189093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969101039558956141585457 2226825779669217106189093)
                ·
                  refine ⟨417529833687978207410455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226825779669217106189093 417529833687978207410455)
                  ·
                    rfl

theorem cell22_3659114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_3659114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659114 prefixEnd_3659114 := by exact prefixLift 3659114
  have htrace : WordTrace (prefixWord ++ tailWord_3659114) baseStart_3659114 baseEnd_3659114 := by
    simpa [prefixWord, tailWord_3659114, baseEnd_3659114] using wordTrace_append hprefix tailTrace_3659114
  have hstable : (prefixWord ++ tailWord_3659114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659114).length < 2 ^ (prefixWord ++ tailWord_3659114).sum := by decide
  have hdescent : baseEnd_3659114 < baseStart_3659114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659121 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3659121 : Nat := 118140960795 + 3659121 * 2 ^ 59
def prefixEnd_3659121 : Nat := 4983230072969 + 3 ^ 40 * 3659121 * 2
def baseEnd_3659121 : Nat := 1252591897306988937306343

theorem tailTrace_3659121 : CollatzResearch.WordTrace tailWord_3659121 prefixEnd_3659121 1252591897306988937306343 := by
  unfold tailWord_3659121
  simp only [CollatzResearch.WordTrace]
  refine ⟨133459106976637019958841217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88972737984424679972560811 133459106976637019958841217)
  ·
    refine ⟨100094330232477764969130913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133459106976637019958841217 100094330232477764969130913)
    ·
      refine ⟨75070747674358323726848185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100094330232477764969130913 75070747674358323726848185)
      ·
        refine ⟨56303060755768742795136139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75070747674358323726848185 56303060755768742795136139)
        ·
          refine ⟨84454591133653114192704209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56303060755768742795136139 84454591133653114192704209)
          ·
            refine ⟨63340943350239835644528157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84454591133653114192704209 63340943350239835644528157)
            ·
              refine ⟨23752853756339938366698059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63340943350239835644528157 23752853756339938366698059)
              ·
                refine ⟨35629280634509907550047089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23752853756339938366698059 35629280634509907550047089)
                ·
                  refine ⟨26721960475882430662535317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35629280634509907550047089 26721960475882430662535317)
                  ·
                    refine ⟨1252591897306988937306343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26721960475882430662535317 1252591897306988937306343)
                    ·
                      rfl

theorem cell22_3659121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3659121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659121 prefixEnd_3659121 := by exact prefixLift 3659121
  have htrace : WordTrace (prefixWord ++ tailWord_3659121) baseStart_3659121 baseEnd_3659121 := by
    simpa [prefixWord, tailWord_3659121, baseEnd_3659121] using wordTrace_append hprefix tailTrace_3659121
  have hstable : (prefixWord ++ tailWord_3659121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659121).length < 2 ^ (prefixWord ++ tailWord_3659121).sum := by decide
  have hdescent : baseEnd_3659121 < baseStart_3659121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659125 : List Nat := [1, 3, 4, 1, 3, 2, 1, 7]
def baseStart_3659125 : Nat := 118140960795 + 3659125 * 2 ^ 59
def prefixEnd_3659125 : Nat := 4983230072969 + 3 ^ 40 * 3659125 * 2
def baseEnd_3659125 : Nat := 139177029620970473356259

theorem tailTrace_3659125 : CollatzResearch.WordTrace tailWord_3659125 prefixEnd_3659125 139177029620970473356259 := by
  unfold tailWord_3659125
  simp only [CollatzResearch.WordTrace]
  refine ⟨133459252868622528641986829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88972835245748352427991219 133459252868622528641986829)
  ·
    refine ⟨50047219825733448240745061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133459252868622528641986829 50047219825733448240745061)
    ·
      refine ⟨9383853717325021545139699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50047219825733448240745061 9383853717325021545139699)
      ·
        refine ⟨14075780575987532317709549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9383853717325021545139699 14075780575987532317709549)
        ·
          refine ⟨5278417715995324619141081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14075780575987532317709549 5278417715995324619141081)
          ·
            refine ⟨3958813286996493464355811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5278417715995324619141081 3958813286996493464355811)
            ·
              refine ⟨5938219930494740196533717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3958813286996493464355811 5938219930494740196533717)
              ·
                refine ⟨139177029620970473356259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5938219930494740196533717 139177029620970473356259)
                ·
                  rfl

theorem cell22_3659125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 7].length) (baseStart_3659125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659125 prefixEnd_3659125 := by exact prefixLift 3659125
  have htrace : WordTrace (prefixWord ++ tailWord_3659125) baseStart_3659125 baseEnd_3659125 := by
    simpa [prefixWord, tailWord_3659125, baseEnd_3659125] using wordTrace_append hprefix tailTrace_3659125
  have hstable : (prefixWord ++ tailWord_3659125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659125).length < 2 ^ (prefixWord ++ tailWord_3659125).sum := by decide
  have hdescent : baseEnd_3659125 < baseStart_3659125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659140 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_3659140 : Nat := 118140960795 + 3659140 * 2 ^ 59
def prefixEnd_3659140 : Nat := 4983230072969 + 3 ^ 40 * 3659140 * 2
def baseEnd_3659140 : Nat := 1252598401395279221081285

theorem tailTrace_3659140 : CollatzResearch.WordTrace tailWord_3659140 prefixEnd_3659140 1252598401395279221081285 := by
  unfold tailWord_3659140
  simp only [CollatzResearch.WordTrace]
  refine ⟨66729899981784093101891437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88973199975712124135855249 66729899981784093101891437)
  ·
    refine ⟨25023712493169034913209289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66729899981784093101891437 25023712493169034913209289)
    ·
      refine ⟨18767784369876776184906967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25023712493169034913209289 18767784369876776184906967)
      ·
        refine ⟨28151676554815164277360451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18767784369876776184906967 28151676554815164277360451)
        ·
          refine ⟨42227514832222746416040677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28151676554815164277360451 42227514832222746416040677)
          ·
            refine ⟨7917659031041764953007627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42227514832222746416040677 7917659031041764953007627)
            ·
              refine ⟨11876488546562647429511441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7917659031041764953007627 11876488546562647429511441)
              ·
                refine ⟨8907366409921985572133581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11876488546562647429511441 8907366409921985572133581)
                ·
                  refine ⟨3340262403720744589550093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8907366409921985572133581 3340262403720744589550093)
                  ·
                    refine ⟨1252598401395279221081285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340262403720744589550093 1252598401395279221081285)
                    ·
                      rfl

theorem cell22_3659140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_3659140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659140 prefixEnd_3659140 := by exact prefixLift 3659140
  have htrace : WordTrace (prefixWord ++ tailWord_3659140) baseStart_3659140 baseEnd_3659140 := by
    simpa [prefixWord, tailWord_3659140, baseEnd_3659140] using wordTrace_append hprefix tailTrace_3659140
  have hstable : (prefixWord ++ tailWord_3659140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659140).length < 2 ^ (prefixWord ++ tailWord_3659140).sum := by decide
  have hdescent : baseEnd_3659140 < baseStart_3659140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659170 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3659170 : Nat := 118140960795 + 3659170 * 2 ^ 59
def prefixEnd_3659170 : Nat := 4983230072969 + 3 ^ 40 * 3659170 * 2
def baseEnd_3659170 : Nat := 417536223669456380943731

theorem tailTrace_3659170 : CollatzResearch.WordTrace tailWord_3659170 prefixEnd_3659170 417536223669456380943731 := by
  unfold tailWord_3659170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33365223538364875331843741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88973929435639667551583309 33365223538364875331843741)
  ·
    refine ⟨12511958826886828249441403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33365223538364875331843741 12511958826886828249441403)
    ·
      refine ⟨18767938240330242374162105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12511958826886828249441403 18767938240330242374162105)
      ·
        refine ⟨14075953680247681780621579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18767938240330242374162105 14075953680247681780621579)
        ·
          refine ⟨21113930520371522670932369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14075953680247681780621579 21113930520371522670932369)
          ·
            refine ⟨15835447890278642003199277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21113930520371522670932369 15835447890278642003199277)
            ·
              refine ⟨5938292958854490751199729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15835447890278642003199277 5938292958854490751199729)
              ·
                refine ⟨4453719719140868063399797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938292958854490751199729 4453719719140868063399797)
                ·
                  refine ⟨417536223669456380943731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4453719719140868063399797 417536223669456380943731)
                  ·
                    rfl

theorem cell22_3659170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3659170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659170 prefixEnd_3659170 := by exact prefixLift 3659170
  have htrace : WordTrace (prefixWord ++ tailWord_3659170) baseStart_3659170 baseEnd_3659170 := by
    simpa [prefixWord, tailWord_3659170, baseEnd_3659170] using wordTrace_append hprefix tailTrace_3659170
  have hstable : (prefixWord ++ tailWord_3659170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659170).length < 2 ^ (prefixWord ++ tailWord_3659170).sum := by decide
  have hdescent : baseEnd_3659170 < baseStart_3659170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659215 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 4]
def baseStart_3659215 : Nat := 118140960795 + 3659215 * 2 ^ 59
def prefixEnd_3659215 : Nat := 4983230072969 + 3 ^ 40 * 3659215 * 2
def baseEnd_3659215 : Nat := 417541358476001341818685

theorem tailTrace_3659215 : CollatzResearch.WordTrace tailWord_3659215 prefixEnd_3659215 417541358476001341818685 := by
  unfold tailWord_3659215
  simp only [CollatzResearch.WordTrace]
  refine ⟨133462535438296474012763099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88975023625530982675175399 133462535438296474012763099)
  ·
    refine ⟨200193803157444711019144649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133462535438296474012763099 200193803157444711019144649)
    ·
      refine ⟨150145352368083533264358487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200193803157444711019144649 150145352368083533264358487)
      ·
        refine ⟨225218028552125299896537731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150145352368083533264358487 225218028552125299896537731)
        ·
          refine ⟨337827042828187949844806597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225218028552125299896537731 337827042828187949844806597)
          ·
            refine ⟨63342570530285240595901237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 337827042828187949844806597 63342570530285240595901237)
            ·
              refine ⟨5938365987214241305865741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63342570530285240595901237 5938365987214241305865741)
              ·
                refine ⟨2226887245205340489699653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5938365987214241305865741 2226887245205340489699653)
                ·
                  refine ⟨417541358476001341818685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2226887245205340489699653 417541358476001341818685)
                  ·
                    rfl

theorem cell22_3659215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 4].length) (baseStart_3659215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659215 prefixEnd_3659215 := by exact prefixLift 3659215
  have htrace : WordTrace (prefixWord ++ tailWord_3659215) baseStart_3659215 baseEnd_3659215 := by
    simpa [prefixWord, tailWord_3659215, baseEnd_3659215] using wordTrace_append hprefix tailTrace_3659215
  have hstable : (prefixWord ++ tailWord_3659215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659215).length < 2 ^ (prefixWord ++ tailWord_3659215).sum := by decide
  have hdescent : baseEnd_3659215 < baseStart_3659215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659247 : List Nat := [1, 1, 2, 1, 4, 1, 6, 1, 2, 3]
def baseStart_3659247 : Nat := 118140960795 + 3659247 * 2 ^ 59
def prefixEnd_3659247 : Nat := 4983230072969 + 3 ^ 40 * 3659247 * 2
def baseEnd_3659247 : Nat := 1252635029681966608655957

theorem tailTrace_3659247 : CollatzResearch.WordTrace tailWord_3659247 prefixEnd_3659247 1252635029681966608655957 := by
  unfold tailWord_3659247
  simp only [CollatzResearch.WordTrace]
  refine ⟨133463702574180543477927995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88975801716120362318618663 133463702574180543477927995)
  ·
    refine ⟨200195553861270815216891993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133463702574180543477927995 200195553861270815216891993)
    ·
      refine ⟨150146665395953111412668995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200195553861270815216891993 150146665395953111412668995)
      ·
        refine ⟨225219998093929667119003493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150146665395953111412668995 225219998093929667119003493)
        ·
          refine ⟨42228749642611812584813155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225219998093929667119003493 42228749642611812584813155)
          ·
            refine ⟨63343124463917718877219733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42228749642611812584813155 63343124463917718877219733)
            ·
              refine ⟨2969208959246143072369675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63343124463917718877219733 2969208959246143072369675)
              ·
                refine ⟨4453813438869214608554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969208959246143072369675 4453813438869214608554513)
                ·
                  refine ⟨3340360079151910956415885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4453813438869214608554513 3340360079151910956415885)
                  ·
                    refine ⟨1252635029681966608655957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340360079151910956415885 1252635029681966608655957)
                    ·
                      rfl

theorem cell22_3659247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_3659247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659247 prefixEnd_3659247 := by exact prefixLift 3659247
  have htrace : WordTrace (prefixWord ++ tailWord_3659247) baseStart_3659247 baseEnd_3659247 := by
    simpa [prefixWord, tailWord_3659247, baseEnd_3659247] using wordTrace_append hprefix tailTrace_3659247
  have hstable : (prefixWord ++ tailWord_3659247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659247).length < 2 ^ (prefixWord ++ tailWord_3659247).sum := by decide
  have hdescent : baseEnd_3659247 < baseStart_3659247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659277 : List Nat := [1, 7, 1, 1, 2, 10]
def baseStart_3659277 : Nat := 118140960795 + 3659277 * 2 ^ 59
def prefixEnd_3659277 : Nat := 4983230072969 + 3 ^ 40 * 3659277 * 2
def baseEnd_3659277 : Nat := 15464756781420450992665

theorem tailTrace_3659277 : CollatzResearch.WordTrace tailWord_3659277 prefixEnd_3659277 15464756781420450992665 := by
  unfold tailWord_3659277
  simp only [CollatzResearch.WordTrace]
  refine ⟨133464796764071858601520085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88976531176047905734346723 133464796764071858601520085)
  ·
    refine ⟨3128081174157934185973127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 133464796764071858601520085 3128081174157934185973127)
    ·
      refine ⟨4692121761236901278959691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128081174157934185973127 4692121761236901278959691)
      ·
        refine ⟨7038182641855351918439537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692121761236901278959691 7038182641855351918439537)
        ·
          refine ⟨5278636981391513938829653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038182641855351918439537 5278636981391513938829653)
          ·
            refine ⟨15464756781420450992665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5278636981391513938829653 15464756781420450992665)
            ·
              rfl

theorem cell22_3659277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 10].length) (baseStart_3659277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659277 prefixEnd_3659277 := by exact prefixLift 3659277
  have htrace : WordTrace (prefixWord ++ tailWord_3659277) baseStart_3659277 baseEnd_3659277 := by
    simpa [prefixWord, tailWord_3659277, baseEnd_3659277] using wordTrace_append hprefix tailTrace_3659277
  have hstable : (prefixWord ++ tailWord_3659277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659277).length < 2 ^ (prefixWord ++ tailWord_3659277).sum := by decide
  have hdescent : baseEnd_3659277 < baseStart_3659277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659333 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 8]
def baseStart_3659333 : Nat := 118140960795 + 3659333 * 2 ^ 59
def prefixEnd_3659333 : Nat := 4983230072969 + 3 ^ 40 * 3659333 * 2
def baseEnd_3659333 : Nat := 417554823079830350335231

theorem tailTrace_3659333 : CollatzResearch.WordTrace tailWord_3659333 prefixEnd_3659333 417554823079830350335231 := by
  unfold tailWord_3659333
  simp only [CollatzResearch.WordTrace]
  refine ⟨133466839251868980165558653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88977892834579320110372435 133466839251868980165558653)
  ·
    refine ⟨50050064719450867562084495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133466839251868980165558653 50050064719450867562084495)
    ·
      refine ⟨75075097079176301343126743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50050064719450867562084495 75075097079176301343126743)
      ·
        refine ⟨112612645618764452014690115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75075097079176301343126743 112612645618764452014690115)
        ·
          refine ⟨168918968428146678022035173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112612645618764452014690115 168918968428146678022035173)
          ·
            refine ⟨31672306580277502129131595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168918968428146678022035173 31672306580277502129131595)
            ·
              refine ⟨47508459870416253193697393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31672306580277502129131595 47508459870416253193697393)
              ·
                refine ⟨35631344902812189895273045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47508459870416253193697393 35631344902812189895273045)
                ·
                  refine ⟨417554823079830350335231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35631344902812189895273045 417554823079830350335231)
                  ·
                    rfl

theorem cell22_3659333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_3659333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659333 prefixEnd_3659333 := by exact prefixLift 3659333
  have htrace : WordTrace (prefixWord ++ tailWord_3659333) baseStart_3659333 baseEnd_3659333 := by
    simpa [prefixWord, tailWord_3659333, baseEnd_3659333] using wordTrace_append hprefix tailTrace_3659333
  have hstable : (prefixWord ++ tailWord_3659333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659333).length < 2 ^ (prefixWord ++ tailWord_3659333).sum := by decide
  have hdescent : baseEnd_3659333 < baseStart_3659333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659416 : List Nat := [2, 1, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_3659416 : Nat := 118140960795 + 3659416 * 2 ^ 59
def prefixEnd_3659416 : Nat := 4983230072969 + 3 ^ 40 * 3659416 * 2
def baseEnd_3659416 : Nat := 1252692881835706501180439

theorem tailTrace_3659416 : CollatzResearch.WordTrace tailWord_3659416 prefixEnd_3659416 1252692881835706501180439 := by
  unfold tailWord_3659416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66734933255284142670415051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88979911007045523560553401 66734933255284142670415051)
  ·
    refine ⟨100102399882926214005622577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66734933255284142670415051 100102399882926214005622577)
    ·
      refine ⟨75076799912194660504216933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100102399882926214005622577 75076799912194660504216933)
      ·
        refine ⟨14076899983536498844540675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75076799912194660504216933 14076899983536498844540675)
        ·
          refine ⟨21115349975304748266811013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14076899983536498844540675 21115349975304748266811013)
          ·
            refine ⟨3959128120369640300027065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21115349975304748266811013 3959128120369640300027065)
            ·
              refine ⟨2969346090277230225020299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3959128120369640300027065 2969346090277230225020299)
              ·
                refine ⟨4454019135415845337530449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969346090277230225020299 4454019135415845337530449)
                ·
                  refine ⟨3340514351561884003147837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4454019135415845337530449 3340514351561884003147837)
                  ·
                    refine ⟨1252692881835706501180439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340514351561884003147837 1252692881835706501180439)
                    ·
                      rfl

theorem cell22_3659416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_3659416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659416 prefixEnd_3659416 := by exact prefixLift 3659416
  have htrace : WordTrace (prefixWord ++ tailWord_3659416) baseStart_3659416 baseEnd_3659416 := by
    simpa [prefixWord, tailWord_3659416, baseEnd_3659416] using wordTrace_append hprefix tailTrace_3659416
  have hstable : (prefixWord ++ tailWord_3659416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659416).length < 2 ^ (prefixWord ++ tailWord_3659416).sum := by decide
  have hdescent : baseEnd_3659416 < baseStart_3659416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659455 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3659455 : Nat := 118140960795 + 3659455 * 2 ^ 59
def prefixEnd_3659455 : Nat := 4983230072969 + 3 ^ 40 * 3659455 * 2
def baseEnd_3659455 : Nat := 1252706232332723399455319

theorem tailTrace_3659455 : CollatzResearch.WordTrace tailWord_3659455 prefixEnd_3659455 1252706232332723399455319 := by
  unfold tailWord_3659455
  simp only [CollatzResearch.WordTrace]
  refine ⟨133471288957426995001499819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88980859304951330000999879 133471288957426995001499819)
  ·
    refine ⟨200206933436140492502249729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133471288957426995001499819 200206933436140492502249729)
    ·
      refine ⟨150155200077105369376687297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200206933436140492502249729 150155200077105369376687297)
      ·
        refine ⟨112616400057829027032515473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150155200077105369376687297 112616400057829027032515473)
        ·
          refine ⟨84462300043371770274386605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112616400057829027032515473 84462300043371770274386605)
          ·
            refine ⟨31673362516264413852894977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84462300043371770274386605 31673362516264413852894977)
            ·
              refine ⟨23755021887198310389671233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31673362516264413852894977 23755021887198310389671233)
              ·
                refine ⟨17816266415398732792253425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23755021887198310389671233 17816266415398732792253425)
                ·
                  refine ⟨13362199811549049594190069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17816266415398732792253425 13362199811549049594190069)
                  ·
                    refine ⟨1252706232332723399455319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13362199811549049594190069 1252706232332723399455319)
                    ·
                      rfl

theorem cell22_3659455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3659455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659455 prefixEnd_3659455 := by exact prefixLift 3659455
  have htrace : WordTrace (prefixWord ++ tailWord_3659455) baseStart_3659455 baseEnd_3659455 := by
    simpa [prefixWord, tailWord_3659455, baseEnd_3659455] using wordTrace_append hprefix tailTrace_3659455
  have hstable : (prefixWord ++ tailWord_3659455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659455).length < 2 ^ (prefixWord ++ tailWord_3659455).sum := by decide
  have hdescent : baseEnd_3659455 < baseStart_3659455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659478 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3659478 : Nat := 118140960795 + 3659478 * 2 ^ 59
def prefixEnd_3659478 : Nat := 4983230072969 + 3 ^ 40 * 3659478 * 2
def baseEnd_3659478 : Nat := 1252714105702759006130249

theorem tailTrace_3659478 : CollatzResearch.WordTrace tailWord_3659478 prefixEnd_3659478 1252714105702759006130249 := by
  unfold tailWord_3659478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8342007989771479370599193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88981418557562446619724725 8342007989771479370599193)
  ·
    refine ⟨6256505992328609527949395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8342007989771479370599193 6256505992328609527949395)
    ·
      refine ⟨9384758988492914291924093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6256505992328609527949395 9384758988492914291924093)
      ·
        refine ⟨3519284620684842859471535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9384758988492914291924093 3519284620684842859471535)
        ·
          refine ⟨5278926931027264289207303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519284620684842859471535 5278926931027264289207303)
          ·
            refine ⟨7918390396540896433810955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5278926931027264289207303 7918390396540896433810955)
            ·
              refine ⟨11877585594811344650716433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918390396540896433810955 11877585594811344650716433)
              ·
                refine ⟨8908189196108508488037325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877585594811344650716433 8908189196108508488037325)
                ·
                  refine ⟨3340570948540690683013997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8908189196108508488037325 3340570948540690683013997)
                  ·
                    refine ⟨1252714105702759006130249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340570948540690683013997 1252714105702759006130249)
                    ·
                      rfl

theorem cell22_3659478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3659478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659478 prefixEnd_3659478 := by exact prefixLift 3659478
  have htrace : WordTrace (prefixWord ++ tailWord_3659478) baseStart_3659478 baseEnd_3659478 := by
    simpa [prefixWord, tailWord_3659478, baseEnd_3659478] using wordTrace_append hprefix tailTrace_3659478
  have hstable : (prefixWord ++ tailWord_3659478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659478).length < 2 ^ (prefixWord ++ tailWord_3659478).sum := by decide
  have hdescent : baseEnd_3659478 < baseStart_3659478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659487 : List Nat := [1, 1, 2, 3, 2, 2, 2, 4, 1, 4]
def baseStart_3659487 : Nat := 118140960795 + 3659487 * 2 ^ 59
def prefixEnd_3659487 : Nat := 4983230072969 + 3 ^ 40 * 3659487 * 2
def baseEnd_3659487 : Nat := 1252717186586685982655221

theorem tailTrace_3659487 : CollatzResearch.WordTrace tailWord_3659487 prefixEnd_3659487 1252717186586685982655221 := by
  unfold tailWord_3659487
  simp only [CollatzResearch.WordTrace]
  refine ⟨133472456093311064466664715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88981637395540709644443143 133472456093311064466664715)
  ·
    refine ⟨200208684139966596699997073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133472456093311064466664715 200208684139966596699997073)
    ·
      refine ⟨150156513104974947524997805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200208684139966596699997073 150156513104974947524997805)
      ·
        refine ⟨56308692414365605321874177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150156513104974947524997805 56308692414365605321874177)
        ·
          refine ⟨42231519310774203991405633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56308692414365605321874177 42231519310774203991405633)
          ·
            refine ⟨31673639483080652993554225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42231519310774203991405633 31673639483080652993554225)
            ·
              refine ⟨23755229612310489745165669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31673639483080652993554225 23755229612310489745165669)
              ·
                refine ⟨4454105552308216827218563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23755229612310489745165669 4454105552308216827218563)
                ·
                  refine ⟨6681158328462325240827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4454105552308216827218563 6681158328462325240827845)
                  ·
                    refine ⟨1252717186586685982655221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681158328462325240827845 1252717186586685982655221)
                    ·
                      rfl

theorem cell22_3659487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_3659487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659487 prefixEnd_3659487 := by exact prefixLift 3659487
  have htrace : WordTrace (prefixWord ++ tailWord_3659487) baseStart_3659487 baseEnd_3659487 := by
    simpa [prefixWord, tailWord_3659487, baseEnd_3659487] using wordTrace_append hprefix tailTrace_3659487
  have hstable : (prefixWord ++ tailWord_3659487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659487).length < 2 ^ (prefixWord ++ tailWord_3659487).sum := by decide
  have hdescent : baseEnd_3659487 < baseStart_3659487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659508 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3659508 : Nat := 118140960795 + 3659508 * 2 ^ 59
def prefixEnd_3659508 : Nat := 4983230072969 + 3 ^ 40 * 3659508 * 2
def baseEnd_3659508 : Nat := 417574791771949642626719

theorem tailTrace_3659508 : CollatzResearch.WordTrace tailWord_3659508 prefixEnd_3659508 417574791771949642626719 := by
  unfold tailWord_3659508
  simp only [CollatzResearch.WordTrace]
  refine ⟨66736611013117492526589589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88982148017489990035452785 66736611013117492526589589)
  ·
    refine ⟨3128278641239882462183887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66736611013117492526589589 3128278641239882462183887)
    ·
      refine ⟨4692417961859823693275831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3128278641239882462183887 4692417961859823693275831)
      ·
        refine ⟨7038626942789735539913747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4692417961859823693275831 7038626942789735539913747)
        ·
          refine ⟨10557940414184603309870621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038626942789735539913747 10557940414184603309870621)
          ·
            refine ⟨3959227655319226241201483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10557940414184603309870621 3959227655319226241201483)
            ·
              refine ⟨5938841482978839361802225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959227655319226241201483 5938841482978839361802225)
              ·
                refine ⟨4454131112234129521351669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5938841482978839361802225 4454131112234129521351669)
                ·
                  refine ⟨417574791771949642626719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454131112234129521351669 417574791771949642626719)
                  ·
                    rfl

theorem cell22_3659508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3659508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659508 prefixEnd_3659508 := by exact prefixLift 3659508
  have htrace : WordTrace (prefixWord ++ tailWord_3659508) baseStart_3659508 baseEnd_3659508 := by
    simpa [prefixWord, tailWord_3659508, baseEnd_3659508] using wordTrace_append hprefix tailTrace_3659508
  have hstable : (prefixWord ++ tailWord_3659508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659508).length < 2 ^ (prefixWord ++ tailWord_3659508).sum := by decide
  have hdescent : baseEnd_3659508 < baseStart_3659508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659534 : List Nat := [4, 1, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_3659534 : Nat := 118140960795 + 3659534 * 2 ^ 59
def prefixEnd_3659534 : Nat := 4983230072969 + 3 ^ 40 * 3659534 * 2
def baseEnd_3659534 : Nat := 1252733275647193526730077

theorem tailTrace_3659534 : CollatzResearch.WordTrace tailWord_3659534 prefixEnd_3659534 1252733275647193526730077 := by
  unfold tailWord_3659534
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684271290517598936703207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88982780216093860995750437 16684271290517598936703207)
  ·
    refine ⟨25026406935776398405054811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684271290517598936703207 25026406935776398405054811)
    ·
      refine ⟨37539610403664597607582217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25026406935776398405054811 37539610403664597607582217)
      ·
        refine ⟨28154707802748448205686663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37539610403664597607582217 28154707802748448205686663)
        ·
          refine ⟨42232061704122672308529995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28154707802748448205686663 42232061704122672308529995)
          ·
            refine ⟨63348092556184008462794993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42232061704122672308529995 63348092556184008462794993)
            ·
              refine ⟨47511069417138006347096245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63348092556184008462794993 47511069417138006347096245)
              ·
                refine ⟨4454162757856688095040273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47511069417138006347096245 4454162757856688095040273)
                ·
                  refine ⟨3340622068392516071280205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4454162757856688095040273 3340622068392516071280205)
                  ·
                    refine ⟨1252733275647193526730077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340622068392516071280205 1252733275647193526730077)
                    ·
                      rfl

theorem cell22_3659534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_3659534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659534 prefixEnd_3659534 := by exact prefixLift 3659534
  have htrace : WordTrace (prefixWord ++ tailWord_3659534) baseStart_3659534 baseEnd_3659534 := by
    simpa [prefixWord, tailWord_3659534, baseEnd_3659534] using wordTrace_append hprefix tailTrace_3659534
  have hstable : (prefixWord ++ tailWord_3659534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659534).length < 2 ^ (prefixWord ++ tailWord_3659534).sum := by decide
  have hdescent : baseEnd_3659534 < baseStart_3659534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659566 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3659566 : Nat := 118140960795 + 3659566 * 2 ^ 59
def prefixEnd_3659566 : Nat := 4983230072969 + 3 ^ 40 * 3659566 * 2
def baseEnd_3659566 : Nat := 1252744229901156109929979

theorem tailTrace_3659566 : CollatzResearch.WordTrace tailWord_3659566 prefixEnd_3659566 1252744229901156109929979 := by
  unfold tailWord_3659566
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684417182503107619848819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88983558306683240639193701 16684417182503107619848819)
  ·
    refine ⟨25026625773754661429773229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684417182503107619848819 25026625773754661429773229)
    ·
      refine ⟨9384984665157998036164961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25026625773754661429773229 9384984665157998036164961)
      ·
        refine ⟨7038738498868498527123721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9384984665157998036164961 7038738498868498527123721)
        ·
          refine ⟨5279053874151373895342791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7038738498868498527123721 5279053874151373895342791)
          ·
            refine ⟨7918580811227060843014187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279053874151373895342791 7918580811227060843014187)
            ·
              refine ⟨11877871216840591264521281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7918580811227060843014187 11877871216840591264521281)
              ·
                refine ⟨8908403412630443448390961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11877871216840591264521281 8908403412630443448390961)
                ·
                  refine ⟨6681302559472832586293221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8908403412630443448390961 6681302559472832586293221)
                  ·
                    refine ⟨1252744229901156109929979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6681302559472832586293221 1252744229901156109929979)
                    ·
                      rfl

theorem cell22_3659566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3659566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659566 prefixEnd_3659566 := by exact prefixLift 3659566
  have htrace : WordTrace (prefixWord ++ tailWord_3659566) baseStart_3659566 baseEnd_3659566 := by
    simpa [prefixWord, tailWord_3659566, baseEnd_3659566] using wordTrace_append hprefix tailTrace_3659566
  have hstable : (prefixWord ++ tailWord_3659566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659566).length < 2 ^ (prefixWord ++ tailWord_3659566).sum := by decide
  have hdescent : baseEnd_3659566 < baseStart_3659566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659630 : List Nat := [4, 1, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3659630 : Nat := 118140960795 + 3659630 * 2 ^ 59
def prefixEnd_3659630 : Nat := 4983230072969 + 3 ^ 40 * 3659630 * 2
def baseEnd_3659630 : Nat := 1252766138409081276329783

theorem tailTrace_3659630 : CollatzResearch.WordTrace tailWord_3659630 prefixEnd_3659630 1252766138409081276329783 := by
  unfold tailWord_3659630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16684708966474124986140043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88985114487861999926080229 16684708966474124986140043)
  ·
    refine ⟨25027063449711187479210065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16684708966474124986140043 25027063449711187479210065)
    ·
      refine ⟨18770297587283390609407549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25027063449711187479210065 18770297587283390609407549)
      ·
        refine ⟨7038861595231271478527831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18770297587283390609407549 7038861595231271478527831)
        ·
          refine ⟨10558292392846907217791747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7038861595231271478527831 10558292392846907217791747)
          ·
            refine ⟨15837438589270360826687621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10558292392846907217791747 15837438589270360826687621)
            ·
              refine ⟨2969519735488192655003929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15837438589270360826687621 2969519735488192655003929)
              ·
                refine ⟨2227139801616144491252947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969519735488192655003929 2227139801616144491252947)
                ·
                  refine ⟨3340709702424216736879421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227139801616144491252947 3340709702424216736879421)
                  ·
                    refine ⟨1252766138409081276329783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340709702424216736879421 1252766138409081276329783)
                    ·
                      rfl

theorem cell22_3659630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3659630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659630 prefixEnd_3659630 := by exact prefixLift 3659630
  have htrace : WordTrace (prefixWord ++ tailWord_3659630) baseStart_3659630 baseEnd_3659630 := by
    simpa [prefixWord, tailWord_3659630, baseEnd_3659630] using wordTrace_append hprefix tailTrace_3659630
  have hstable : (prefixWord ++ tailWord_3659630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659630).length < 2 ^ (prefixWord ++ tailWord_3659630).sum := by decide
  have hdescent : baseEnd_3659630 < baseStart_3659630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659669 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_3659669 : Nat := 118140960795 + 3659669 * 2 ^ 59
def prefixEnd_3659669 : Nat := 4983230072969 + 3 ^ 40 * 3659669 * 2
def baseEnd_3659669 : Nat := 1252779488906098174604663

theorem tailTrace_3659669 : CollatzResearch.WordTrace tailWord_3659669 prefixEnd_3659669 1252779488906098174604663 := by
  unfold tailWord_3659669
  simp only [CollatzResearch.WordTrace]
  refine ⟨133479094178651709549790061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88986062785767806366526707 133479094178651709549790061)
  ·
    refine ⟨50054660316994391081171273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133479094178651709549790061 50054660316994391081171273)
    ·
      refine ⟨37540995237745793310878455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50054660316994391081171273 37540995237745793310878455)
      ·
        refine ⟨56311492856618689966317683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37540995237745793310878455 56311492856618689966317683)
        ·
          refine ⟨84467239284928034949476525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56311492856618689966317683 84467239284928034949476525)
          ·
            refine ⟨31675214731848013106053697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84467239284928034949476525 31675214731848013106053697)
            ·
              refine ⟨23756411048886009829540273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31675214731848013106053697 23756411048886009829540273)
              ·
                refine ⟨17817308286664507372155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23756411048886009829540273 17817308286664507372155205)
                ·
                  refine ⟨3340745303749595132279101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17817308286664507372155205 3340745303749595132279101)
                  ·
                    refine ⟨1252779488906098174604663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340745303749595132279101 1252779488906098174604663)
                    ·
                      rfl

theorem cell22_3659669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_3659669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659669 prefixEnd_3659669 := by exact prefixLift 3659669
  have htrace : WordTrace (prefixWord ++ tailWord_3659669) baseStart_3659669 baseEnd_3659669 := by
    simpa [prefixWord, tailWord_3659669, baseEnd_3659669] using wordTrace_append hprefix tailTrace_3659669
  have hstable : (prefixWord ++ tailWord_3659669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659669).length < 2 ^ (prefixWord ++ tailWord_3659669).sum := by decide
  have hdescent : baseEnd_3659669 < baseStart_3659669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659671 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 4]
def baseStart_3659671 : Nat := 118140960795 + 3659671 * 2 ^ 59
def prefixEnd_3659671 : Nat := 4983230072969 + 3 ^ 40 * 3659671 * 2
def baseEnd_3659671 : Nat := 417593391182323612018219

theorem tailTrace_3659671 : CollatzResearch.WordTrace tailWord_3659671 prefixEnd_3659671 417593391182323612018219 := by
  unfold tailWord_3659671
  simp only [CollatzResearch.WordTrace]
  refine ⟨133479167124644463891362867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88986111416429642594241911 133479167124644463891362867)
  ·
    refine ⟨200218750686966695837044301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133479167124644463891362867 200218750686966695837044301)
    ·
      refine ⟨75082031507612510938891613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200218750686966695837044301 75082031507612510938891613)
      ·
        refine ⟨28155761815354691602084355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75082031507612510938891613 28155761815354691602084355)
        ·
          refine ⟨42233642723032037403126533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28155761815354691602084355 42233642723032037403126533)
          ·
            refine ⟨7918808010568507013086225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42233642723032037403126533 7918808010568507013086225)
            ·
              refine ⟨5939106007926380259814669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918808010568507013086225 5939106007926380259814669)
              ·
                refine ⟨2227164752972392597430501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5939106007926380259814669 2227164752972392597430501)
                ·
                  refine ⟨417593391182323612018219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2227164752972392597430501 417593391182323612018219)
                  ·
                    rfl

theorem cell22_3659671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 4].length) (baseStart_3659671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659671 prefixEnd_3659671 := by exact prefixLift 3659671
  have htrace : WordTrace (prefixWord ++ tailWord_3659671) baseStart_3659671 baseEnd_3659671 := by
    simpa [prefixWord, tailWord_3659671, baseEnd_3659671] using wordTrace_append hprefix tailTrace_3659671
  have hstable : (prefixWord ++ tailWord_3659671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659671).length < 2 ^ (prefixWord ++ tailWord_3659671).sum := by decide
  have hdescent : baseEnd_3659671 < baseStart_3659671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659688 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_3659688 : Nat := 118140960795 + 3659688 * 2 ^ 59
def prefixEnd_3659688 : Nat := 4983230072969 + 3 ^ 40 * 3659688 * 2
def baseEnd_3659688 : Nat := 417595330998129486126535

theorem tailTrace_3659688 : CollatzResearch.WordTrace tailWord_3659688 prefixEnd_3659688 417595330998129486126535 := by
  unfold tailWord_3659688
  simp only [CollatzResearch.WordTrace]
  refine ⟨66739893582791437897365859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88986524777055250529821145 66739893582791437897365859)
  ·
    refine ⟨100109840374187156846048789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66739893582791437897365859 100109840374187156846048789)
    ·
      refine ⟨4692648767540022977158537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100109840374187156846048789 4692648767540022977158537)
      ·
        refine ⟨3519486575655017232868903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4692648767540022977158537 3519486575655017232868903)
        ·
          refine ⟨5279229863482525849303355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3519486575655017232868903 5279229863482525849303355)
          ·
            refine ⟨7918844795223788773955033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279229863482525849303355 7918844795223788773955033)
            ·
              refine ⟨5939133596417841580466275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7918844795223788773955033 5939133596417841580466275)
              ·
                refine ⟨8908700394626762370699413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939133596417841580466275 8908700394626762370699413)
                ·
                  refine ⟨417595330998129486126535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8908700394626762370699413 417595330998129486126535)
                  ·
                    rfl

theorem cell22_3659688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_3659688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659688 prefixEnd_3659688 := by exact prefixLift 3659688
  have htrace : WordTrace (prefixWord ++ tailWord_3659688) baseStart_3659688 baseEnd_3659688 := by
    simpa [prefixWord, tailWord_3659688, baseEnd_3659688] using wordTrace_append hprefix tailTrace_3659688
  have hstable : (prefixWord ++ tailWord_3659688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659688).length < 2 ^ (prefixWord ++ tailWord_3659688).sum := by decide
  have hdescent : baseEnd_3659688 < baseStart_3659688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659727 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 9]
def baseStart_3659727 : Nat := 118140960795 + 3659727 * 2 ^ 59
def prefixEnd_3659727 : Nat := 4983230072969 + 3 ^ 40 * 3659727 * 2
def baseEnd_3659727 : Nat := 417599781163801785551495

theorem tailTrace_3659727 : CollatzResearch.WordTrace tailWord_3659727 prefixEnd_3659727 417599781163801785551495 := by
  unfold tailWord_3659727
  simp only [CollatzResearch.WordTrace]
  refine ⟨133481209612441585455401435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88987473074961056970267623 133481209612441585455401435)
  ·
    refine ⟨200221814418662378183102153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133481209612441585455401435 200221814418662378183102153)
    ·
      refine ⟨150166360813996783637326615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200221814418662378183102153 150166360813996783637326615)
      ·
        refine ⟨225249541220995175455989923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150166360813996783637326615 225249541220995175455989923)
        ·
          refine ⟨337874311831492763183984885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225249541220995175455989923 337874311831492763183984885)
          ·
            refine ⟨31675716734202446548498583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 337874311831492763183984885 31675716734202446548498583)
            ·
              refine ⟨47513575101303669822747875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31675716734202446548498583 47513575101303669822747875)
              ·
                refine ⟨71270362651955504734121813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47513575101303669822747875 71270362651955504734121813)
                ·
                  refine ⟨417599781163801785551495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71270362651955504734121813 417599781163801785551495)
                  ·
                    rfl

theorem cell22_3659727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 9].length) (baseStart_3659727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659727 prefixEnd_3659727 := by exact prefixLift 3659727
  have htrace : WordTrace (prefixWord ++ tailWord_3659727) baseStart_3659727 baseEnd_3659727 := by
    simpa [prefixWord, tailWord_3659727, baseEnd_3659727] using wordTrace_append hprefix tailTrace_3659727
  have hstable : (prefixWord ++ tailWord_3659727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659727).length < 2 ^ (prefixWord ++ tailWord_3659727).sum := by decide
  have hdescent : baseEnd_3659727 < baseStart_3659727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659761 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 5]
def baseStart_3659761 : Nat := 118140960795 + 3659761 * 2 ^ 59
def prefixEnd_3659761 : Nat := 4983230072969 + 3 ^ 40 * 3659761 * 2
def baseEnd_3659761 : Nat := 417603660795413533768127

theorem tailTrace_3659761 : CollatzResearch.WordTrace tailWord_3659761 prefixEnd_3659761 417603660795413533768127 := by
  unfold tailWord_3659761
  simp only [CollatzResearch.WordTrace]
  refine ⟨133482449694318409262139137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88988299796212272841426091 133482449694318409262139137)
  ·
    refine ⟨100111837270738806946604353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133482449694318409262139137 100111837270738806946604353)
    ·
      refine ⟨75083877953054105209953265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100111837270738806946604353 75083877953054105209953265)
      ·
        refine ⟨56312908464790578907464949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75083877953054105209953265 56312908464790578907464949)
        ·
          refine ⟨5279335168574116772574839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56312908464790578907464949 5279335168574116772574839)
          ·
            refine ⟨7919002752861175158862259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5279335168574116772574839 7919002752861175158862259)
            ·
              refine ⟨11878504129291762738293389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7919002752861175158862259 11878504129291762738293389)
              ·
                refine ⟨4454439048484411026860021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11878504129291762738293389 4454439048484411026860021)
                ·
                  refine ⟨417603660795413533768127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454439048484411026860021 417603660795413533768127)
                  ·
                    rfl

theorem cell22_3659761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 5].length) (baseStart_3659761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659761 prefixEnd_3659761 := by exact prefixLift 3659761
  have htrace : WordTrace (prefixWord ++ tailWord_3659761) baseStart_3659761 baseEnd_3659761 := by
    simpa [prefixWord, tailWord_3659761, baseEnd_3659761] using wordTrace_append hprefix tailTrace_3659761
  have hstable : (prefixWord ++ tailWord_3659761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659761).length < 2 ^ (prefixWord ++ tailWord_3659761).sum := by decide
  have hdescent : baseEnd_3659761 < baseStart_3659761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659799 : List Nat := [1, 1, 3, 5, 3, 1, 2, 2, 1, 3]
def baseStart_3659799 : Nat := 118140960795 + 3659799 * 2 ^ 59
def prefixEnd_3659799 : Nat := 4983230072969 + 3 ^ 40 * 3659799 * 2
def baseEnd_3659799 : Nat := 1252823990562821168854265

theorem tailTrace_3659799 : CollatzResearch.WordTrace tailWord_3659799 prefixEnd_3659799 1252823990562821168854265 := by
  unfold tailWord_3659799
  simp only [CollatzResearch.WordTrace]
  refine ⟨133483835668180741752022451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88989223778787161168014967 133483835668180741752022451)
  ·
    refine ⟨200225753502271112628033677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133483835668180741752022451 200225753502271112628033677)
    ·
      refine ⟨75084657563351667235512629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200225753502271112628033677 75084657563351667235512629)
      ·
        refine ⟨7039186646564218803329309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75084657563351667235512629 7039186646564218803329309)
        ·
          refine ⟨2639694992461582051248491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7039186646564218803329309 2639694992461582051248491)
          ·
            refine ⟨3959542488692373076872737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2639694992461582051248491 3959542488692373076872737)
            ·
              refine ⟨2969656866519279807654553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3959542488692373076872737 2969656866519279807654553)
              ·
                refine ⟨2227242649889459855740915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2969656866519279807654553 2227242649889459855740915)
                ·
                  refine ⟨3340863974834189783611373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227242649889459855740915 3340863974834189783611373)
                  ·
                    refine ⟨1252823990562821168854265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340863974834189783611373 1252823990562821168854265)
                    ·
                      rfl

theorem cell22_3659799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_3659799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659799 prefixEnd_3659799 := by exact prefixLift 3659799
  have htrace : WordTrace (prefixWord ++ tailWord_3659799) baseStart_3659799 baseEnd_3659799 := by
    simpa [prefixWord, tailWord_3659799, baseEnd_3659799] using wordTrace_append hprefix tailTrace_3659799
  have hstable : (prefixWord ++ tailWord_3659799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659799).length < 2 ^ (prefixWord ++ tailWord_3659799).sum := by decide
  have hdescent : baseEnd_3659799 < baseStart_3659799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659900 : List Nat := [2, 2, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_3659900 : Nat := 118140960795 + 3659900 * 2 ^ 59
def prefixEnd_3659900 : Nat := 4983230072969 + 3 ^ 40 * 3659900 * 2
def baseEnd_3659900 : Nat := 1252858564926890572078955

theorem tailTrace_3659900 : CollatzResearch.WordTrace tailWord_3659900 prefixEnd_3659900 1252858564926890572078955 := by
  unfold tailWord_3659900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66743759720407418000724577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88991679627209890667632769 66743759720407418000724577)
  ·
    refine ⟨50057819790305563500543433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66743759720407418000724577 50057819790305563500543433)
    ·
      refine ⟨37543364842729172625407575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50057819790305563500543433 37543364842729172625407575)
      ·
        refine ⟨56315047264093758938111363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37543364842729172625407575 56315047264093758938111363)
        ·
          refine ⟨84472570896140638407167045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56315047264093758938111363 84472570896140638407167045)
          ·
            refine ⟨15838607043026369701343821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84472570896140638407167045 15838607043026369701343821)
            ·
              refine ⟨5939477641134888638003933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15838607043026369701343821 5939477641134888638003933)
              ·
                refine ⟨2227304115425583239251475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5939477641134888638003933 2227304115425583239251475)
                ·
                  refine ⟨3340956173138374858877213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227304115425583239251475 3340956173138374858877213)
                  ·
                    refine ⟨1252858564926890572078955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3340956173138374858877213 1252858564926890572078955)
                    ·
                      rfl

theorem cell22_3659900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_3659900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659900 prefixEnd_3659900 := by exact prefixLift 3659900
  have htrace : WordTrace (prefixWord ++ tailWord_3659900) baseStart_3659900 baseEnd_3659900 := by
    simpa [prefixWord, tailWord_3659900, baseEnd_3659900] using wordTrace_append hprefix tailTrace_3659900
  have hstable : (prefixWord ++ tailWord_3659900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659900).length < 2 ^ (prefixWord ++ tailWord_3659900).sum := by decide
  have hdescent : baseEnd_3659900 < baseStart_3659900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659973 : List Nat := [1, 3, 1, 1, 1, 1, 5, 4, 2, 3]
def baseStart_3659973 : Nat := 118140960795 + 3659973 * 2 ^ 59
def prefixEnd_3659973 : Nat := 4983230072969 + 3 ^ 40 * 3659973 * 2
def baseEnd_3659973 : Nat := 1252883554318742715003731

theorem tailTrace_3659973 : CollatzResearch.WordTrace tailWord_3659973 prefixEnd_3659973 1252883554318742715003731 := by
  unfold tailWord_3659973
  simp only [CollatzResearch.WordTrace]
  refine ⟨133490181969550369468856573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88993454646366912979237715 133490181969550369468856573)
  ·
    refine ⟨50058818238581388550821215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133490181969550369468856573 50058818238581388550821215)
    ·
      refine ⟨75088227357872082826231823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50058818238581388550821215 75088227357872082826231823)
      ·
        refine ⟨112632341036808124239347735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75088227357872082826231823 112632341036808124239347735)
        ·
          refine ⟨168948511555212186359021603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112632341036808124239347735 168948511555212186359021603)
          ·
            refine ⟨253422767332818279538532405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168948511555212186359021603 253422767332818279538532405)
            ·
              refine ⟨23758384437451713706737413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253422767332818279538532405 23758384437451713706737413)
              ·
                refine ⟨4454697082022196320013265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23758384437451713706737413 4454697082022196320013265)
                ·
                  refine ⟨3341022811516647240009949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4454697082022196320013265 3341022811516647240009949)
                  ·
                    refine ⟨1252883554318742715003731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341022811516647240009949 1252883554318742715003731)
                    ·
                      rfl

theorem cell22_3659973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_3659973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659973 prefixEnd_3659973 := by exact prefixLift 3659973
  have htrace : WordTrace (prefixWord ++ tailWord_3659973) baseStart_3659973 baseEnd_3659973 := by
    simpa [prefixWord, tailWord_3659973, baseEnd_3659973] using wordTrace_append hprefix tailTrace_3659973
  have hstable : (prefixWord ++ tailWord_3659973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659973).length < 2 ^ (prefixWord ++ tailWord_3659973).sum := by decide
  have hdescent : baseEnd_3659973 < baseStart_3659973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3659990 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_3659990 : Nat := 118140960795 + 3659990 * 2 ^ 59
def prefixEnd_3659990 : Nat := 4983230072969 + 3 ^ 40 * 3659990 * 2
def baseEnd_3659990 : Nat := 1252889373766160337328679

theorem tailTrace_3659990 : CollatzResearch.WordTrace tailWord_3659990 prefixEnd_3659990 1252889373766160337328679 := by
  unfold tailWord_3659990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8343175125655548835764089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88993868006992520914816949 8343175125655548835764089)
  ·
    refine ⟨6257381344241661626823067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8343175125655548835764089 6257381344241661626823067)
    ·
      refine ⟨9386072016362492440234601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6257381344241661626823067 9386072016362492440234601)
      ·
        refine ⟨7039554012271869330175951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9386072016362492440234601 7039554012271869330175951)
        ·
          refine ⟨10559331018407803995263927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039554012271869330175951 10559331018407803995263927)
          ·
            refine ⟨15838996527611705992895891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10559331018407803995263927 15838996527611705992895891)
            ·
              refine ⟨23758494791417558989343837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15838996527611705992895891 23758494791417558989343837)
              ·
                refine ⟨8909435546781584621003939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23758494791417558989343837 8909435546781584621003939)
                ·
                  refine ⟨13364153320172376931505909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909435546781584621003939 13364153320172376931505909)
                  ·
                    refine ⟨1252889373766160337328679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13364153320172376931505909 1252889373766160337328679)
                    ·
                      rfl

theorem cell22_3659990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_3659990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3659990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3659990 prefixEnd_3659990 := by exact prefixLift 3659990
  have htrace : WordTrace (prefixWord ++ tailWord_3659990) baseStart_3659990 baseEnd_3659990 := by
    simpa [prefixWord, tailWord_3659990, baseEnd_3659990] using wordTrace_append hprefix tailTrace_3659990
  have hstable : (prefixWord ++ tailWord_3659990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3659990).length < 2 ^ (prefixWord ++ tailWord_3659990).sum := by decide
  have hdescent : baseEnd_3659990 < baseStart_3659990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3659990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660005 : List Nat := [1, 3, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_3660005 : Nat := 118140960795 + 3660005 * 2 ^ 59
def prefixEnd_3660005 : Nat := 4983230072969 + 3 ^ 40 * 3660005 * 2
def baseEnd_3660005 : Nat := 1252894508572705298203633

theorem tailTrace_3660005 : CollatzResearch.WordTrace tailWord_3660005 prefixEnd_3660005 1252894508572705298203633 := by
  unfold tailWord_3660005
  simp only [CollatzResearch.WordTrace]
  refine ⟨133491349105434438934021469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88994232736956292622680979 133491349105434438934021469)
  ·
    refine ⟨50059255914537914600258051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133491349105434438934021469 50059255914537914600258051)
    ·
      refine ⟨75088883871806871900387077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50059255914537914600258051 75088883871806871900387077)
      ·
        refine ⟨14079165725963788481322577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75088883871806871900387077 14079165725963788481322577)
        ·
          refine ⟨10559374294472841360991933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14079165725963788481322577 10559374294472841360991933)
          ·
            refine ⟨3959765360427315510371975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10559374294472841360991933 3959765360427315510371975)
            ·
              refine ⟨5939648040640973265557963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959765360427315510371975 5939648040640973265557963)
              ·
                refine ⟨8909472060961459898336945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5939648040640973265557963 8909472060961459898336945)
                ·
                  refine ⟨6682104045721094923752709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8909472060961459898336945 6682104045721094923752709)
                  ·
                    refine ⟨1252894508572705298203633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682104045721094923752709 1252894508572705298203633)
                    ·
                      rfl

theorem cell22_3660005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_3660005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660005 prefixEnd_3660005 := by exact prefixLift 3660005
  have htrace : WordTrace (prefixWord ++ tailWord_3660005) baseStart_3660005 baseEnd_3660005 := by
    simpa [prefixWord, tailWord_3660005, baseEnd_3660005] using wordTrace_append hprefix tailTrace_3660005
  have hstable : (prefixWord ++ tailWord_3660005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660005).length < 2 ^ (prefixWord ++ tailWord_3660005).sum := by decide
  have hdescent : baseEnd_3660005 < baseStart_3660005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660031 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 7]
def baseStart_3660031 : Nat := 118140960795 + 3660031 * 2 ^ 59
def prefixEnd_3660031 : Nat := 4983230072969 + 3 ^ 40 * 3660031 * 2
def baseEnd_3660031 : Nat := 417634469634683299017851

theorem tailTrace_3660031 : CollatzResearch.WordTrace tailWord_3660031 prefixEnd_3660031 417634469634683299017851 := by
  unfold tailWord_3660031
  simp only [CollatzResearch.WordTrace]
  refine ⟨133492297403340245374467947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88994864935560163582978631 133492297403340245374467947)
  ·
    refine ⟨200238446105010368061701921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133492297403340245374467947 200238446105010368061701921)
    ·
      refine ⟨150178834578757776046276441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200238446105010368061701921 150178834578757776046276441)
      ·
        refine ⟨112634125934068332034707331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150178834578757776046276441 112634125934068332034707331)
        ·
          refine ⟨168951188901102498052060997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112634125934068332034707331 168951188901102498052060997)
          ·
            refine ⟨31678347918956718384761437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168951188901102498052060997 31678347918956718384761437)
            ·
              refine ⟨11879380469608769394285539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31678347918956718384761437 11879380469608769394285539)
              ·
                refine ⟨17819070704413154091428309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11879380469608769394285539 17819070704413154091428309)
                ·
                  refine ⟨417634469634683299017851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17819070704413154091428309 417634469634683299017851)
                  ·
                    rfl

theorem cell22_3660031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 7].length) (baseStart_3660031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660031 prefixEnd_3660031 := by exact prefixLift 3660031
  have htrace : WordTrace (prefixWord ++ tailWord_3660031) baseStart_3660031 baseEnd_3660031 := by
    simpa [prefixWord, tailWord_3660031, baseEnd_3660031] using wordTrace_append hprefix tailTrace_3660031
  have hstable : (prefixWord ++ tailWord_3660031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660031).length < 2 ^ (prefixWord ++ tailWord_3660031).sum := by decide
  have hdescent : baseEnd_3660031 < baseStart_3660031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660035 : List Nat := [1, 1, 1, 3, 2, 3, 1, 6, 1, 3]
def baseStart_3660035 : Nat := 118140960795 + 3660035 * 2 ^ 59
def prefixEnd_3660035 : Nat := 4983230072969 + 3 ^ 40 * 3660035 * 2
def baseEnd_3660035 : Nat := 1252904778185795219953541

theorem tailTrace_3660035 : CollatzResearch.WordTrace tailWord_3660035 prefixEnd_3660035 1252904778185795219953541 := by
  unfold tailWord_3660035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133492443295325754057613559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88994962196883836038409039 133492443295325754057613559)
  ·
    refine ⟨200238664942988631086420339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133492443295325754057613559 200238664942988631086420339)
    ·
      refine ⟨300357997414482946629630509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200238664942988631086420339 300357997414482946629630509)
      ·
        refine ⟨112634249030431104986111441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300357997414482946629630509 112634249030431104986111441)
        ·
          refine ⟨84475686772823328739583581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112634249030431104986111441 84475686772823328739583581)
          ·
            refine ⟨31678382539808748277343843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84475686772823328739583581 31678382539808748277343843)
            ·
              refine ⟨47517573809713122416015765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31678382539808748277343843 47517573809713122416015765)
              ·
                refine ⟨2227386272330302613250739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47517573809713122416015765 2227386272330302613250739)
                ·
                  refine ⟨3341079408495453919876109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227386272330302613250739 3341079408495453919876109)
                  ·
                    refine ⟨1252904778185795219953541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341079408495453919876109 1252904778185795219953541)
                    ·
                      rfl

theorem cell22_3660035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 6, 1, 3].length) (baseStart_3660035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660035 prefixEnd_3660035 := by exact prefixLift 3660035
  have htrace : WordTrace (prefixWord ++ tailWord_3660035) baseStart_3660035 baseEnd_3660035 := by
    simpa [prefixWord, tailWord_3660035, baseEnd_3660035] using wordTrace_append hprefix tailTrace_3660035
  have hstable : (prefixWord ++ tailWord_3660035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660035).length < 2 ^ (prefixWord ++ tailWord_3660035).sum := by decide
  have hdescent : baseEnd_3660035 < baseStart_3660035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660069 : List Nat := [1, 3, 1, 2, 5, 2, 1, 3, 1, 3]
def baseStart_3660069 : Nat := 118140960795 + 3660069 * 2 ^ 59
def prefixEnd_3660069 : Nat := 4983230072969 + 3 ^ 40 * 3660069 * 2
def baseEnd_3660069 : Nat := 1252916417080630464603437

theorem tailTrace_3660069 : CollatzResearch.WordTrace tailWord_3660069 prefixEnd_3660069 1252916417080630464603437 := by
  unfold tailWord_3660069
  simp only [CollatzResearch.WordTrace]
  refine ⟨133493683377202577864351261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88995788918135051909567507 133493683377202577864351261)
  ·
    refine ⟨50060131266450966699131723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133493683377202577864351261 50060131266450966699131723)
    ·
      refine ⟨75090196899676450048697585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50060131266450966699131723 75090196899676450048697585)
      ·
        refine ⟨56317647674757337536523189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75090196899676450048697585 56317647674757337536523189)
        ·
          refine ⟨5279779469508500394049049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56317647674757337536523189 5279779469508500394049049)
          ·
            refine ⟨3959834602131375295536787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5279779469508500394049049 3959834602131375295536787)
            ·
              refine ⟨5939751903197062943305181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3959834602131375295536787 5939751903197062943305181)
              ·
                refine ⟨2227406963698898603739443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5939751903197062943305181 2227406963698898603739443)
                ·
                  refine ⟨3341110445548347905609165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227406963698898603739443 3341110445548347905609165)
                  ·
                    refine ⟨1252916417080630464603437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341110445548347905609165 1252916417080630464603437)
                    ·
                      rfl

theorem cell22_3660069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_3660069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660069 prefixEnd_3660069 := by exact prefixLift 3660069
  have htrace : WordTrace (prefixWord ++ tailWord_3660069) baseStart_3660069 baseEnd_3660069 := by
    simpa [prefixWord, tailWord_3660069, baseEnd_3660069] using wordTrace_append hprefix tailTrace_3660069
  have hstable : (prefixWord ++ tailWord_3660069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660069).length < 2 ^ (prefixWord ++ tailWord_3660069).sum := by decide
  have hdescent : baseEnd_3660069 < baseStart_3660069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660076 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_3660076 : Nat := 118140960795 + 3660076 * 2 ^ 59
def prefixEnd_3660076 : Nat := 4983230072969 + 3 ^ 40 * 3660076 * 2
def baseEnd_3660076 : Nat := 417639604441228259892805

theorem tailTrace_3660076 : CollatzResearch.WordTrace tailWord_3660076 prefixEnd_3660076 417639604441228259892805 := by
  unfold tailWord_3660076
  simp only [CollatzResearch.WordTrace]
  refine ⟨66746969344088609029928041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88995959125451478706570721 66746969344088609029928041)
  ·
    refine ⟨50060227008066456772446031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66746969344088609029928041 50060227008066456772446031)
    ·
      refine ⟨75090340512099685158669047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50060227008066456772446031 75090340512099685158669047)
      ·
        refine ⟨112635510768149527738003571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75090340512099685158669047 112635510768149527738003571)
        ·
          refine ⟨168953266152224291607005357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112635510768149527738003571 168953266152224291607005357)
          ·
            refine ⟨63357474807084109352627009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168953266152224291607005357 63357474807084109352627009)
            ·
              refine ⟨47518106105313082014470257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63357474807084109352627009 47518106105313082014470257)
              ·
                refine ⟨35638579578984811510852693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47518106105313082014470257 35638579578984811510852693)
                ·
                  refine ⟨417639604441228259892805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35638579578984811510852693 417639604441228259892805)
                  ·
                    rfl

theorem cell22_3660076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_3660076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660076 prefixEnd_3660076 := by exact prefixLift 3660076
  have htrace : WordTrace (prefixWord ++ tailWord_3660076) baseStart_3660076 baseEnd_3660076 := by
    simpa [prefixWord, tailWord_3660076, baseEnd_3660076] using wordTrace_append hprefix tailTrace_3660076
  have hstable : (prefixWord ++ tailWord_3660076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660076).length < 2 ^ (prefixWord ++ tailWord_3660076).sum := by decide
  have hdescent : baseEnd_3660076 < baseStart_3660076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660108 : List Nat := [2, 2, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_3660108 : Nat := 118140960795 + 3660108 * 2 ^ 59
def prefixEnd_3660108 : Nat := 4983230072969 + 3 ^ 40 * 3660108 * 2
def baseEnd_3660108 : Nat := 1252929767577647362878317

theorem tailTrace_3660108 : CollatzResearch.WordTrace tailWord_3660108 prefixEnd_3660108 1252929767577647362878317 := by
  unfold tailWord_3660108
  simp only [CollatzResearch.WordTrace]
  refine ⟨66747552912030643762510489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88996737216040858350013985 66747552912030643762510489)
  ·
    refine ⟨50060664684022982821882867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66747552912030643762510489 50060664684022982821882867)
    ·
      refine ⟨75090997026034474232824301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50060664684022982821882867 75090997026034474232824301)
      ·
        refine ⟨28159123884762927837309113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75090997026034474232824301 28159123884762927837309113)
        ·
          refine ⟨21119342913572195877981835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28159123884762927837309113 21119342913572195877981835)
          ·
            refine ⟨31679014370358293816972753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21119342913572195877981835 31679014370358293816972753)
            ·
              refine ⟨23759260777768720362729565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31679014370358293816972753 23759260777768720362729565)
              ·
                refine ⟨8909722791663270136023587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23759260777768720362729565 8909722791663270136023587)
                ·
                  refine ⟨13364584187494905204035381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8909722791663270136023587 13364584187494905204035381)
                  ·
                    refine ⟨1252929767577647362878317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13364584187494905204035381 1252929767577647362878317)
                    ·
                      rfl

theorem cell22_3660108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_3660108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660108 prefixEnd_3660108 := by exact prefixLift 3660108
  have htrace : WordTrace (prefixWord ++ tailWord_3660108) baseStart_3660108 baseEnd_3660108 := by
    simpa [prefixWord, tailWord_3660108, baseEnd_3660108] using wordTrace_append hprefix tailTrace_3660108
  have hstable : (prefixWord ++ tailWord_3660108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660108).length < 2 ^ (prefixWord ++ tailWord_3660108).sum := by decide
  have hdescent : baseEnd_3660108 < baseStart_3660108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660138 : List Nat := [3, 1, 3, 3, 1, 11]
def baseStart_3660138 : Nat := 118140960795 + 3660138 * 2 ^ 59
def prefixEnd_3660138 : Nat := 4983230072969 + 3 ^ 40 * 3660138 * 2
def baseEnd_3660138 : Nat := 15468395520873299810225

theorem tailTrace_3660138 : CollatzResearch.WordTrace tailWord_3660138 prefixEnd_3660138 15468395520873299810225 := by
  unfold tailWord_3660138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33374050003488150662153267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88997466675968401765742045 33374050003488150662153267)
  ·
    refine ⟨50061075005232225993229901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33374050003488150662153267 50061075005232225993229901)
    ·
      refine ⟨18772903126962084747461213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50061075005232225993229901 18772903126962084747461213)
      ·
        refine ⟨7039838672610781780297955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18772903126962084747461213 7039838672610781780297955)
        ·
          refine ⟨10559758008916172670446933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7039838672610781780297955 10559758008916172670446933)
          ·
            refine ⟨15468395520873299810225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10559758008916172670446933 15468395520873299810225)
            ·
              rfl

theorem cell22_3660138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 11].length) (baseStart_3660138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660138 prefixEnd_3660138 := by exact prefixLift 3660138
  have htrace : WordTrace (prefixWord ++ tailWord_3660138) baseStart_3660138 baseEnd_3660138 := by
    simpa [prefixWord, tailWord_3660138, baseEnd_3660138] using wordTrace_append hprefix tailTrace_3660138
  have hstable : (prefixWord ++ tailWord_3660138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660138).length < 2 ^ (prefixWord ++ tailWord_3660138).sum := by decide
  have hdescent : baseEnd_3660138 < baseStart_3660138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660168 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_3660168 : Nat := 118140960795 + 3660168 * 2 ^ 59
def prefixEnd_3660168 : Nat := 4983230072969 + 3 ^ 40 * 3660168 * 2
def baseEnd_3660168 : Nat := 1252950306803827206378133

theorem tailTrace_3660168 : CollatzResearch.WordTrace tailWord_3660168 prefixEnd_3660168 1252950306803827206378133 := by
  unfold tailWord_3660168
  simp only [CollatzResearch.WordTrace]
  refine ⟨66748647101921958886102579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88998196135895945181470105 66748647101921958886102579)
  ·
    refine ⟨100122970652882938329153869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66748647101921958886102579 100122970652882938329153869)
    ·
      refine ⟨37546113994831101873432701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100122970652882938329153869 37546113994831101873432701)
      ·
        refine ⟨14079792748061663202537263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37546113994831101873432701 14079792748061663202537263)
        ·
          refine ⟨21119689122092494803805895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14079792748061663202537263 21119689122092494803805895)
          ·
            refine ⟨31679533683138742205708843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21119689122092494803805895 31679533683138742205708843)
            ·
              refine ⟨47519300524708113308563265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31679533683138742205708843 47519300524708113308563265)
              ·
                refine ⟨35639475393531084981422449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47519300524708113308563265 35639475393531084981422449)
                ·
                  refine ⟨26729606545148313736066837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35639475393531084981422449 26729606545148313736066837)
                  ·
                    refine ⟨1252950306803827206378133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26729606545148313736066837 1252950306803827206378133)
                    ·
                      rfl

theorem cell22_3660168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_3660168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660168 prefixEnd_3660168 := by exact prefixLift 3660168
  have htrace : WordTrace (prefixWord ++ tailWord_3660168) baseStart_3660168 baseEnd_3660168 := by
    simpa [prefixWord, tailWord_3660168, baseEnd_3660168] using wordTrace_append hprefix tailTrace_3660168
  have hstable : (prefixWord ++ tailWord_3660168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660168).length < 2 ^ (prefixWord ++ tailWord_3660168).sum := by decide
  have hdescent : baseEnd_3660168 < baseStart_3660168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660217 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 5]
def baseStart_3660217 : Nat := 118140960795 + 3660217 * 2 ^ 59
def prefixEnd_3660217 : Nat := 4983230072969 + 3 ^ 40 * 3660217 * 2
def baseEnd_3660217 : Nat := 417655693501735803967661

theorem tailTrace_3660217 : CollatzResearch.WordTrace tailWord_3660217 prefixEnd_3660217 417655693501735803967661 := by
  unfold tailWord_3660217
  simp only [CollatzResearch.WordTrace]
  refine ⟨133499081380666399140738905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88999387587110932760492603 133499081380666399140738905)
  ·
    refine ⟨100124311035499799355554179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133499081380666399140738905 100124311035499799355554179)
    ·
      refine ⟨150186466553249699033331269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100124311035499799355554179 150186466553249699033331269)
      ·
        refine ⟨28159962478734318568749613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150186466553249699033331269 28159962478734318568749613)
        ·
          refine ⟨10559985929525369463281105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28159962478734318568749613 10559985929525369463281105)
          ·
            refine ⟨7919989447144027097460829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10559985929525369463281105 7919989447144027097460829)
            ·
              refine ⟨2969996042679010161547811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7919989447144027097460829 2969996042679010161547811)
              ·
                refine ⟨4454994064018515242321717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2969996042679010161547811 4454994064018515242321717)
                ·
                  refine ⟨417655693501735803967661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4454994064018515242321717 417655693501735803967661)
                  ·
                    rfl

theorem cell22_3660217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 5].length) (baseStart_3660217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660217 prefixEnd_3660217 := by exact prefixLift 3660217
  have htrace : WordTrace (prefixWord ++ tailWord_3660217) baseStart_3660217 baseEnd_3660217 := by
    simpa [prefixWord, tailWord_3660217, baseEnd_3660217] using wordTrace_append hprefix tailTrace_3660217
  have hstable : (prefixWord ++ tailWord_3660217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660217).length < 2 ^ (prefixWord ++ tailWord_3660217).sum := by decide
  have hdescent : baseEnd_3660217 < baseStart_3660217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660292 : List Nat := [2, 3, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_3660292 : Nat := 118140960795 + 3660292 * 2 ^ 59
def prefixEnd_3660292 : Nat := 4983230072969 + 3 ^ 40 * 3660292 * 2
def baseEnd_3660292 : Nat := 1252992754537932216277753

theorem tailTrace_3660292 : CollatzResearch.WordTrace tailWord_3660292 prefixEnd_3660292 1252992754537932216277753 := by
  unfold tailWord_3660292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66750908427697343474859565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89001211236929791299812753 66750908427697343474859565)
  ·
    refine ⟨25031590660386503803072337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66750908427697343474859565 25031590660386503803072337)
    ·
      refine ⟨18773692995289877852304253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25031590660386503803072337 18773692995289877852304253)
      ·
        refine ⟨7040134873233704194614095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18773692995289877852304253 7040134873233704194614095)
        ·
          refine ⟨10560202309850556291921143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040134873233704194614095 10560202309850556291921143)
          ·
            refine ⟨15840303464775834437881715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10560202309850556291921143 15840303464775834437881715)
            ·
              refine ⟨23760455197163751656822573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15840303464775834437881715 23760455197163751656822573)
              ·
                refine ⟨8910170698936406871308465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23760455197163751656822573 8910170698936406871308465)
                ·
                  refine ⟨6682628024202305153481349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8910170698936406871308465 6682628024202305153481349)
                  ·
                    refine ⟨1252992754537932216277753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6682628024202305153481349 1252992754537932216277753)
                    ·
                      rfl

theorem cell22_3660292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_3660292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660292 prefixEnd_3660292 := by exact prefixLift 3660292
  have htrace : WordTrace (prefixWord ++ tailWord_3660292) baseStart_3660292 baseEnd_3660292 := by
    simpa [prefixWord, tailWord_3660292, baseEnd_3660292] using wordTrace_append hprefix tailTrace_3660292
  have hstable : (prefixWord ++ tailWord_3660292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660292).length < 2 ^ (prefixWord ++ tailWord_3660292).sum := by decide
  have hdescent : baseEnd_3660292 < baseStart_3660292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660303 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_3660303 : Nat := 118140960795 + 3660303 * 2 ^ 59
def prefixEnd_3660303 : Nat := 4983230072969 + 3 ^ 40 * 3660303 * 2
def baseEnd_3660303 : Nat := 1252996520062731854252719

theorem tailTrace_3660303 : CollatzResearch.WordTrace tailWord_3660303 prefixEnd_3660303 1252996520062731854252719 := by
  unfold tailWord_3660303
  simp only [CollatzResearch.WordTrace]
  refine ⟨133502218058354835828369563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89001478705569890552246375 133502218058354835828369563)
  ·
    refine ⟨200253327087532253742554345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133502218058354835828369563 200253327087532253742554345)
    ·
      refine ⟨150189995315649190306915759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200253327087532253742554345 150189995315649190306915759)
      ·
        refine ⟨225284992973473785460373639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150189995315649190306915759 225284992973473785460373639)
        ·
          refine ⟨337927489460210678190560459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225284992973473785460373639 337927489460210678190560459)
          ·
            refine ⟨506891234190316017285840689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337927489460210678190560459 506891234190316017285840689)
            ·
              refine ⟨380168425642737012964380517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 506891234190316017285840689 380168425642737012964380517)
              ·
                refine ⟨71281579808013189930821347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380168425642737012964380517 71281579808013189930821347)
                ·
                  refine ⟨106922369712019784896232021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71281579808013189930821347 106922369712019784896232021)
                  ·
                    refine ⟨1252996520062731854252719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106922369712019784896232021 1252996520062731854252719)
                    ·
                      rfl

theorem cell22_3660303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_3660303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660303 prefixEnd_3660303 := by exact prefixLift 3660303
  have htrace : WordTrace (prefixWord ++ tailWord_3660303) baseStart_3660303 baseEnd_3660303 := by
    simpa [prefixWord, tailWord_3660303, baseEnd_3660303] using wordTrace_append hprefix tailTrace_3660303
  have hstable : (prefixWord ++ tailWord_3660303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660303).length < 2 ^ (prefixWord ++ tailWord_3660303).sum := by decide
  have hdescent : baseEnd_3660303 < baseStart_3660303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660305 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 7, 3]
def baseStart_3660305 : Nat := 118140960795 + 3660305 * 2 ^ 59
def prefixEnd_3660305 : Nat := 4983230072969 + 3 ^ 40 * 3660305 * 2
def baseEnd_3660305 : Nat := 1252997204703604515702713

theorem tailTrace_3660305 : CollatzResearch.WordTrace tailWord_3660305 prefixEnd_3660305 1252997204703604515702713 := by
  unfold tailWord_3660305
  simp only [CollatzResearch.WordTrace]
  refine ⟨133502291004347590169942369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89001527336231726779961579 133502291004347590169942369)
  ·
    refine ⟨100126718253260692627456777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133502291004347590169942369 100126718253260692627456777)
    ·
      refine ⟨75095038689945519470592583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100126718253260692627456777 75095038689945519470592583)
      ·
        refine ⟨112642558034918279205888875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75095038689945519470592583 112642558034918279205888875)
        ·
          refine ⟨168963837052377418808833313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112642558034918279205888875 168963837052377418808833313)
          ·
            refine ⟨126722877789283064106624985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168963837052377418808833313 126722877789283064106624985)
            ·
              refine ⟨95042158341962298079968739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126722877789283064106624985 95042158341962298079968739)
              ·
                refine ⟨142563237512943447119953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95042158341962298079968739 142563237512943447119953109)
                ·
                  refine ⟨3341325879209612041873901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142563237512943447119953109 3341325879209612041873901)
                  ·
                    refine ⟨1252997204703604515702713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341325879209612041873901 1252997204703604515702713)
                    ·
                      rfl

theorem cell22_3660305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_3660305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660305 prefixEnd_3660305 := by exact prefixLift 3660305
  have htrace : WordTrace (prefixWord ++ tailWord_3660305) baseStart_3660305 baseEnd_3660305 := by
    simpa [prefixWord, tailWord_3660305, baseEnd_3660305] using wordTrace_append hprefix tailTrace_3660305
  have hstable : (prefixWord ++ tailWord_3660305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660305).length < 2 ^ (prefixWord ++ tailWord_3660305).sum := by decide
  have hdescent : baseEnd_3660305 < baseStart_3660305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660311 : List Nat := [1, 1, 3, 6, 1, 1, 2, 2, 2, 3]
def baseStart_3660311 : Nat := 118140960795 + 3660311 * 2 ^ 59
def prefixEnd_3660311 : Nat := 4983230072969 + 3 ^ 40 * 3660311 * 2
def baseEnd_3660311 : Nat := 1252999258626222500052695

theorem tailTrace_3660311 : CollatzResearch.WordTrace tailWord_3660311 prefixEnd_3660311 1252999258626222500052695 := by
  unfold tailWord_3660311
  simp only [CollatzResearch.WordTrace]
  refine ⟨133502509842325853194660787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89001673228217235463107191 133502509842325853194660787)
  ·
    refine ⟨200253764763488779791991181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133502509842325853194660787 200253764763488779791991181)
    ·
      refine ⟨75095161786308292421996693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200253764763488779791991181 75095161786308292421996693)
      ·
        refine ⟨3520085708733201207281095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75095161786308292421996693 3520085708733201207281095)
        ·
          refine ⟨5280128563099801810921643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520085708733201207281095 5280128563099801810921643)
          ·
            refine ⟨7920192844649702716382465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5280128563099801810921643 7920192844649702716382465)
            ·
              refine ⟨5940144633487277037286849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7920192844649702716382465 5940144633487277037286849)
              ·
                refine ⟨4455108475115457777965137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5940144633487277037286849 4455108475115457777965137)
                ·
                  refine ⟨3341331356336593333473853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455108475115457777965137 3341331356336593333473853)
                  ·
                    refine ⟨1252999258626222500052695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341331356336593333473853 1252999258626222500052695)
                    ·
                      rfl

theorem cell22_3660311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_3660311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660311 prefixEnd_3660311 := by exact prefixLift 3660311
  have htrace : WordTrace (prefixWord ++ tailWord_3660311) baseStart_3660311 baseEnd_3660311 := by
    simpa [prefixWord, tailWord_3660311, baseEnd_3660311] using wordTrace_append hprefix tailTrace_3660311
  have hstable : (prefixWord ++ tailWord_3660311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660311).length < 2 ^ (prefixWord ++ tailWord_3660311).sum := by decide
  have hdescent : baseEnd_3660311 < baseStart_3660311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660322 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3660322 : Nat := 118140960795 + 3660322 * 2 ^ 59
def prefixEnd_3660322 : Nat := 4983230072969 + 3 ^ 40 * 3660322 * 2
def baseEnd_3660322 : Nat := 1253003024151022138027661

theorem tailTrace_3660322 : CollatzResearch.WordTrace tailWord_3660322 prefixEnd_3660322 1253003024151022138027661 := by
  unfold tailWord_3660322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33375727761321500518327805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89001940696857334715540813 33375727761321500518327805)
  ·
    refine ⟨12515897910495562694372927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33375727761321500518327805 12515897910495562694372927)
    ·
      refine ⟨18773846865743344041559391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12515897910495562694372927 18773846865743344041559391)
      ·
        refine ⟨28160770298615016062339087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18773846865743344041559391 28160770298615016062339087)
        ·
          refine ⟨42241155447922524093508631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28160770298615016062339087 42241155447922524093508631)
          ·
            refine ⟨63361733171883786140262947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42241155447922524093508631 63361733171883786140262947)
            ·
              refine ⟨95042599757825679210394421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63361733171883786140262947 95042599757825679210394421)
              ·
                refine ⟨8910243727296157425974477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95042599757825679210394421 8910243727296157425974477)
                ·
                  refine ⟨3341341397736059034740429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8910243727296157425974477 3341341397736059034740429)
                  ·
                    refine ⟨1253003024151022138027661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341341397736059034740429 1253003024151022138027661)
                    ·
                      rfl

theorem cell22_3660322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3660322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660322 prefixEnd_3660322 := by exact prefixLift 3660322
  have htrace : WordTrace (prefixWord ++ tailWord_3660322) baseStart_3660322 baseEnd_3660322 := by
    simpa [prefixWord, tailWord_3660322, baseEnd_3660322] using wordTrace_append hprefix tailTrace_3660322
  have hstable : (prefixWord ++ tailWord_3660322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660322).length < 2 ^ (prefixWord ++ tailWord_3660322).sum := by decide
  have hdescent : baseEnd_3660322 < baseStart_3660322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660324 : List Nat := [2, 3, 1, 5, 1, 2, 1, 7]
def baseStart_3660324 : Nat := 118140960795 + 3660324 * 2 ^ 59
def prefixEnd_3660324 : Nat := 4983230072969 + 3 ^ 40 * 3660324 * 2
def baseEnd_3660324 : Nat := 139222634310210533275295

theorem tailTrace_3660324 : CollatzResearch.WordTrace tailWord_3660324 prefixEnd_3660324 139222634310210533275295 := by
  unfold tailWord_3660324
  simp only [CollatzResearch.WordTrace]
  refine ⟨66751491995639378207442013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89001989327519170943256017 66751491995639378207442013)
  ·
    refine ⟨25031809498364766827790755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66751491995639378207442013 25031809498364766827790755)
    ·
      refine ⟨37547714247547150241686133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25031809498364766827790755 37547714247547150241686133)
      ·
        refine ⟨3520098210707545335158075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37547714247547150241686133 3520098210707545335158075)
        ·
          refine ⟨5280147316061318002737113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520098210707545335158075 5280147316061318002737113)
          ·
            refine ⟨3960110487045988502052835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280147316061318002737113 3960110487045988502052835)
            ·
              refine ⟨5940165730568982753079253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960110487045988502052835 5940165730568982753079253)
              ·
                refine ⟨139222634310210533275295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5940165730568982753079253 139222634310210533275295)
                ·
                  rfl

theorem cell22_3660324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_3660324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660324 prefixEnd_3660324 := by exact prefixLift 3660324
  have htrace : WordTrace (prefixWord ++ tailWord_3660324) baseStart_3660324 baseEnd_3660324 := by
    simpa [prefixWord, tailWord_3660324, baseEnd_3660324] using wordTrace_append hprefix tailTrace_3660324
  have hstable : (prefixWord ++ tailWord_3660324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660324).length < 2 ^ (prefixWord ++ tailWord_3660324).sum := by decide
  have hdescent : baseEnd_3660324 < baseStart_3660324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660395 : List Nat := [1, 1, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_3660395 : Nat := 118140960795 + 3660395 * 2 ^ 59
def prefixEnd_3660395 : Nat := 4983230072969 + 3 ^ 40 * 3660395 * 2
def baseEnd_3660395 : Nat := 1253028013542874280952437

theorem tailTrace_3660395 : CollatzResearch.WordTrace tailWord_3660395 prefixEnd_3660395 1253028013542874280952437 := by
  unfold tailWord_3660395
  simp only [CollatzResearch.WordTrace]
  refine ⟨133505573574021535540718639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89003715716014357027145759 133505573574021535540718639)
  ·
    refine ⟨200258360361032303311077959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133505573574021535540718639 200258360361032303311077959)
    ·
      refine ⟨300387540541548454966616939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200258360361032303311077959 300387540541548454966616939)
      ·
        refine ⟨450581310812322682449925409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300387540541548454966616939 450581310812322682449925409)
        ·
          refine ⟨337935983109242011837444057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450581310812322682449925409 337935983109242011837444057)
          ·
            refine ⟨253451987331931508878083043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337935983109242011837444057 253451987331931508878083043)
            ·
              refine ⟨380177980997897263317124565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253451987331931508878083043 380177980997897263317124565)
              ·
                refine ⟨8910421429638217108995107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 380177980997897263317124565 8910421429638217108995107)
                ·
                  refine ⟨13365632144457325663492661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8910421429638217108995107 13365632144457325663492661)
                  ·
                    refine ⟨1253028013542874280952437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13365632144457325663492661 1253028013542874280952437)
                    ·
                      rfl

theorem cell22_3660395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_3660395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660395 prefixEnd_3660395 := by exact prefixLift 3660395
  have htrace : WordTrace (prefixWord ++ tailWord_3660395) baseStart_3660395 baseEnd_3660395 := by
    simpa [prefixWord, tailWord_3660395, baseEnd_3660395] using wordTrace_append hprefix tailTrace_3660395
  have hstable : (prefixWord ++ tailWord_3660395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660395).length < 2 ^ (prefixWord ++ tailWord_3660395).sum := by decide
  have hdescent : baseEnd_3660395 < baseStart_3660395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660397 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3660397 : Nat := 118140960795 + 3660397 * 2 ^ 59
def prefixEnd_3660397 : Nat := 4983230072969 + 3 ^ 40 * 3660397 * 2
def baseEnd_3660397 : Nat := 417676232727915647467477

theorem tailTrace_3660397 : CollatzResearch.WordTrace tailWord_3660397 prefixEnd_3660397 417676232727915647467477 := by
  unfold tailWord_3660397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133505646520014289882291445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89003764346676193254860963 133505646520014289882291445)
  ·
    refine ⟨12516154361251339676464823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133505646520014289882291445 12516154361251339676464823)
    ·
      refine ⟨18774231541877009514697235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12516154361251339676464823 18774231541877009514697235)
      ·
        refine ⟨28161347312815514272045853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18774231541877009514697235 28161347312815514272045853)
        ·
          refine ⟨10560505242305817852017195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28161347312815514272045853 10560505242305817852017195)
          ·
            refine ⟨15840757863458726778025793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10560505242305817852017195 15840757863458726778025793)
            ·
              refine ⟨11880568397594045083519345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15840757863458726778025793 11880568397594045083519345)
              ·
                refine ⟨8910426298195533812639509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11880568397594045083519345 8910426298195533812639509)
                ·
                  refine ⟨417676232727915647467477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8910426298195533812639509 417676232727915647467477)
                  ·
                    rfl

theorem cell22_3660397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3660397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660397 prefixEnd_3660397 := by exact prefixLift 3660397
  have htrace : WordTrace (prefixWord ++ tailWord_3660397) baseStart_3660397 baseEnd_3660397 := by
    simpa [prefixWord, tailWord_3660397, baseEnd_3660397] using wordTrace_append hprefix tailTrace_3660397
  have hstable : (prefixWord ++ tailWord_3660397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660397).length < 2 ^ (prefixWord ++ tailWord_3660397).sum := by decide
  have hdescent : baseEnd_3660397 < baseStart_3660397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660412 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_3660412 : Nat := 118140960795 + 3660412 * 2 ^ 59
def prefixEnd_3660412 : Nat := 4983230072969 + 3 ^ 40 * 3660412 * 2
def baseEnd_3660412 : Nat := 1253033832990291903277385

theorem tailTrace_3660412 : CollatzResearch.WordTrace tailWord_3660412 prefixEnd_3660412 1253033832990291903277385 := by
  unfold tailWord_3660412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66753096807479973722043745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89004129076639964962724993 66753096807479973722043745)
  ·
    refine ⟨50064822605609980291532809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66753096807479973722043745 50064822605609980291532809)
    ·
      refine ⟨37548616954207485218649607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50064822605609980291532809 37548616954207485218649607)
      ·
        refine ⟨56322925431311227827974411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37548616954207485218649607 56322925431311227827974411)
        ·
          refine ⟨84484388146966841741961617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56322925431311227827974411 84484388146966841741961617)
          ·
            refine ⟨63363291110225131306471213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84484388146966841741961617 63363291110225131306471213)
            ·
              refine ⟨23761234166334424239926705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63363291110225131306471213 23761234166334424239926705)
              ·
                refine ⟨17820925624750818179945029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23761234166334424239926705 17820925624750818179945029)
                ·
                  refine ⟨3341423554640778408739693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17820925624750818179945029 3341423554640778408739693)
                  ·
                    refine ⟨1253033832990291903277385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341423554640778408739693 1253033832990291903277385)
                    ·
                      rfl

theorem cell22_3660412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_3660412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660412 prefixEnd_3660412 := by exact prefixLift 3660412
  have htrace : WordTrace (prefixWord ++ tailWord_3660412) baseStart_3660412 baseEnd_3660412 := by
    simpa [prefixWord, tailWord_3660412, baseEnd_3660412] using wordTrace_append hprefix tailTrace_3660412
  have hstable : (prefixWord ++ tailWord_3660412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660412).length < 2 ^ (prefixWord ++ tailWord_3660412).sum := by decide
  have hdescent : baseEnd_3660412 < baseStart_3660412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660446 : List Nat := [4, 3, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3660446 : Nat := 118140960795 + 3660446 * 2 ^ 59
def prefixEnd_3660446 : Nat := 4983230072969 + 3 ^ 40 * 3660446 * 2
def baseEnd_3660446 : Nat := 1253045471885127147927281

theorem tailTrace_3660446 : CollatzResearch.WordTrace tailWord_3660446 prefixEnd_3660446 1253045471885127147927281 := by
  unfold tailWord_3660446
  simp only [CollatzResearch.WordTrace]
  refine ⟨16688429212104596406353149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89004955797891180833883461 16688429212104596406353149)
  ·
    refine ⟨6258160954539223652382431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16688429212104596406353149 6258160954539223652382431)
    ·
      refine ⟨9387241431808835478573647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6258160954539223652382431 9387241431808835478573647)
      ·
        refine ⟨14080862147713253217860471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9387241431808835478573647 14080862147713253217860471)
        ·
          refine ⟨21121293221569879826790707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14080862147713253217860471 21121293221569879826790707)
          ·
            refine ⟨31681939832354819740186061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21121293221569879826790707 31681939832354819740186061)
            ·
              refine ⟨11880727437133057402569773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31681939832354819740186061 11880727437133057402569773)
              ·
                refine ⟨4455272788924896525963665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11880727437133057402569773 4455272788924896525963665)
                ·
                  refine ⟨3341454591693672394472749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4455272788924896525963665 3341454591693672394472749)
                  ·
                    refine ⟨1253045471885127147927281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341454591693672394472749 1253045471885127147927281)
                    ·
                      rfl

theorem cell22_3660446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3660446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660446 prefixEnd_3660446 := by exact prefixLift 3660446
  have htrace : WordTrace (prefixWord ++ tailWord_3660446) baseStart_3660446 baseEnd_3660446 := by
    simpa [prefixWord, tailWord_3660446, baseEnd_3660446] using wordTrace_append hprefix tailTrace_3660446
  have hstable : (prefixWord ++ tailWord_3660446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660446).length < 2 ^ (prefixWord ++ tailWord_3660446).sum := by decide
  have hdescent : baseEnd_3660446 < baseStart_3660446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660493 : List Nat := [1, 6, 2, 1, 3, 1, 1, 7]
def baseStart_3660493 : Nat := 118140960795 + 3660493 * 2 ^ 59
def prefixEnd_3660493 : Nat := 4983230072969 + 3 ^ 40 * 3660493 * 2
def baseEnd_3660493 : Nat := 139229062327292743555793

theorem tailTrace_3660493 : CollatzResearch.WordTrace tailWord_3660493 prefixEnd_3660493 139229062327292743555793 := by
  unfold tailWord_3660493
  simp only [CollatzResearch.WordTrace]
  refine ⟨133509147927666498277786133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89006098618444332185190755 133509147927666498277786133)
  ·
    refine ⟨6258241309109367106771225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133509147927666498277786133 6258241309109367106771225)
    ·
      refine ⟨4693680981832025330078419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6258241309109367106771225 4693680981832025330078419)
      ·
        refine ⟨7040521472748037995117629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693680981832025330078419 7040521472748037995117629)
        ·
          refine ⟨2640195552280514248169111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7040521472748037995117629 2640195552280514248169111)
          ·
            refine ⟨3960293328420771372253667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2640195552280514248169111 3960293328420771372253667)
            ·
              refine ⟨5940439992631157058380501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960293328420771372253667 5940439992631157058380501)
              ·
                refine ⟨139229062327292743555793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5940439992631157058380501 139229062327292743555793)
                ·
                  rfl

theorem cell22_3660493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 7].length) (baseStart_3660493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660493 prefixEnd_3660493 := by exact prefixLift 3660493
  have htrace : WordTrace (prefixWord ++ tailWord_3660493) baseStart_3660493 baseEnd_3660493 := by
    simpa [prefixWord, tailWord_3660493, baseEnd_3660493] using wordTrace_append hprefix tailTrace_3660493
  have hstable : (prefixWord ++ tailWord_3660493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660493).length < 2 ^ (prefixWord ++ tailWord_3660493).sum := by decide
  have hdescent : baseEnd_3660493 < baseStart_3660493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660577 : List Nat := [1, 2, 3, 2, 1, 2, 3, 8]
def baseStart_3660577 : Nat := 118140960795 + 3660577 * 2 ^ 59
def prefixEnd_3660577 : Nat := 4983230072969 + 3 ^ 40 * 3660577 * 2
def baseEnd_3660577 : Nat := 139232257318031830322431

theorem tailTrace_3660577 : CollatzResearch.WordTrace tailWord_3660577 prefixEnd_3660577 139232257318031830322431 := by
  unfold tailWord_3660577
  simp only [CollatzResearch.WordTrace]
  refine ⟨133512211659362180623843985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89008141106241453749229323 133512211659362180623843985)
  ·
    refine ⟨100134158744521635467882989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133512211659362180623843985 100134158744521635467882989)
    ·
      refine ⟨37550309529195613300456121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100134158744521635467882989 37550309529195613300456121)
      ·
        refine ⟨28162732146896709975342091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37550309529195613300456121 28162732146896709975342091)
        ·
          refine ⟨42244098220345064963013137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28162732146896709975342091 42244098220345064963013137)
          ·
            refine ⟨31683073665258798722259853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42244098220345064963013137 31683073665258798722259853)
            ·
              refine ⟨11881152624472049520847445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31683073665258798722259853 11881152624472049520847445)
              ·
                refine ⟨139232257318031830322431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11881152624472049520847445 139232257318031830322431)
                ·
                  rfl

theorem cell22_3660577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 8].length) (baseStart_3660577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660577 prefixEnd_3660577 := by exact prefixLift 3660577
  have htrace : WordTrace (prefixWord ++ tailWord_3660577) baseStart_3660577 baseEnd_3660577 := by
    simpa [prefixWord, tailWord_3660577, baseEnd_3660577] using wordTrace_append hprefix tailTrace_3660577
  have hstable : (prefixWord ++ tailWord_3660577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660577).length < 2 ^ (prefixWord ++ tailWord_3660577).sum := by decide
  have hdescent : baseEnd_3660577 < baseStart_3660577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660669 : List Nat := [1, 4, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3660669 : Nat := 118140960795 + 3660669 * 2 ^ 59
def prefixEnd_3660669 : Nat := 4983230072969 + 3 ^ 40 * 3660669 * 2
def baseEnd_3660669 : Nat := 1253121809342428899601597

theorem tailTrace_3660669 : CollatzResearch.WordTrace tailWord_3660669 prefixEnd_3660669 1253121809342428899601597 := by
  unfold tailWord_3660669
  simp only [CollatzResearch.WordTrace]
  refine ⟨133515567175028880336193061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89010378116685920224128707 133515567175028880336193061)
  ·
    refine ⟨25034168845317915063036199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133515567175028880336193061 25034168845317915063036199)
    ·
      refine ⟨37551253267976872594554299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25034168845317915063036199 37551253267976872594554299)
      ·
        refine ⟨56326879901965308891831449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37551253267976872594554299 56326879901965308891831449)
        ·
          refine ⟨42245159926473981668873587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56326879901965308891831449 42245159926473981668873587)
          ·
            refine ⟨63367739889710972503310381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42245159926473981668873587 63367739889710972503310381)
            ·
              refine ⟨23762902458641614688741393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63367739889710972503310381 23762902458641614688741393)
              ·
                refine ⟨17822176843981211016556045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23762902458641614688741393 17822176843981211016556045)
                ·
                  refine ⟨6683316316492954131208517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17822176843981211016556045 6683316316492954131208517)
                  ·
                    refine ⟨1253121809342428899601597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683316316492954131208517 1253121809342428899601597)
                    ·
                      rfl

theorem cell22_3660669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3660669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660669 prefixEnd_3660669 := by exact prefixLift 3660669
  have htrace : WordTrace (prefixWord ++ tailWord_3660669) baseStart_3660669 baseEnd_3660669 := by
    simpa [prefixWord, tailWord_3660669, baseEnd_3660669] using wordTrace_append hprefix tailTrace_3660669
  have hstable : (prefixWord ++ tailWord_3660669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660669).length < 2 ^ (prefixWord ++ tailWord_3660669).sum := by decide
  have hdescent : baseEnd_3660669 < baseStart_3660669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660694 : List Nat := [5, 3, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3660694 : Nat := 118140960795 + 3660694 * 2 ^ 59
def prefixEnd_3660694 : Nat := 4983230072969 + 3 ^ 40 * 3660694 * 2
def baseEnd_3660694 : Nat := 1253130367353337167726521

theorem tailTrace_3660694 : CollatzResearch.WordTrace tailWord_3660694 prefixEnd_3660694 1253130367353337167726521 := by
  unfold tailWord_3660694
  simp only [CollatzResearch.WordTrace]
  refine ⟨8344779937496144350365821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89010985999958873070568757 8344779937496144350365821)
  ·
    refine ⟨3129292476561054131387183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8344779937496144350365821 3129292476561054131387183)
    ·
      refine ⟨4693938714841581197080775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129292476561054131387183 4693938714841581197080775)
      ·
        refine ⟨7040908072262371795621163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4693938714841581197080775 7040908072262371795621163)
        ·
          refine ⟨10561362108393557693431745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7040908072262371795621163 10561362108393557693431745)
          ·
            refine ⟨7921021581295168270073809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10561362108393557693431745 7921021581295168270073809)
            ·
              refine ⟨5940766185971376202555357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921021581295168270073809 5940766185971376202555357)
              ·
                refine ⟨2227787319739266075958259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5940766185971376202555357 2227787319739266075958259)
                ·
                  refine ⟨3341680979608899113937389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227787319739266075958259 3341680979608899113937389)
                  ·
                    refine ⟨1253130367353337167726521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341680979608899113937389 1253130367353337167726521)
                    ·
                      rfl

theorem cell22_3660694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3660694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660694 prefixEnd_3660694 := by exact prefixLift 3660694
  have htrace : WordTrace (prefixWord ++ tailWord_3660694) baseStart_3660694 baseEnd_3660694 := by
    simpa [prefixWord, tailWord_3660694, baseEnd_3660694] using wordTrace_append hprefix tailTrace_3660694
  have hstable : (prefixWord ++ tailWord_3660694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660694).length < 2 ^ (prefixWord ++ tailWord_3660694).sum := by decide
  have hdescent : baseEnd_3660694 < baseStart_3660694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660703 : List Nat := [1, 1, 2, 5, 2, 1, 4, 1, 1, 4]
def baseStart_3660703 : Nat := 118140960795 + 3660703 * 2 ^ 59
def prefixEnd_3660703 : Nat := 4983230072969 + 3 ^ 40 * 3660703 * 2
def baseEnd_3660703 : Nat := 1253133448237264144251493

theorem tailTrace_3660703 : CollatzResearch.WordTrace tailWord_3660703 prefixEnd_3660703 1253133448237264144251493 := by
  unfold tailWord_3660703
  simp only [CollatzResearch.WordTrace]
  refine ⟨133516807256905704142930763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89011204837937136095287175 133516807256905704142930763)
  ·
    refine ⟨200275210885358556214396145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133516807256905704142930763 200275210885358556214396145)
    ·
      refine ⟨150206408164018917160797109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200275210885358556214396145 150206408164018917160797109)
      ·
        refine ⟨14081850765376773483824729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150206408164018917160797109 14081850765376773483824729)
        ·
          refine ⟨10561388074032580112868547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14081850765376773483824729 10561388074032580112868547)
          ·
            refine ⟨15842082111048870169302821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10561388074032580112868547 15842082111048870169302821)
            ·
              refine ⟨2970390395821663156744279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15842082111048870169302821 2970390395821663156744279)
              ·
                refine ⟨4455585593732494735116419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970390395821663156744279 4455585593732494735116419)
                ·
                  refine ⟨6683378390598742102674629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4455585593732494735116419 6683378390598742102674629)
                  ·
                    refine ⟨1253133448237264144251493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683378390598742102674629 1253133448237264144251493)
                    ·
                      rfl

theorem cell22_3660703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_3660703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660703 prefixEnd_3660703 := by exact prefixLift 3660703
  have htrace : WordTrace (prefixWord ++ tailWord_3660703) baseStart_3660703 baseEnd_3660703 := by
    simpa [prefixWord, tailWord_3660703, baseEnd_3660703] using wordTrace_append hprefix tailTrace_3660703
  have hstable : (prefixWord ++ tailWord_3660703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660703).length < 2 ^ (prefixWord ++ tailWord_3660703).sum := by decide
  have hdescent : baseEnd_3660703 < baseStart_3660703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660733 : List Nat := [1, 4, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3660733 : Nat := 118140960795 + 3660733 * 2 ^ 59
def prefixEnd_3660733 : Nat := 4983230072969 + 3 ^ 40 * 3660733 * 2
def baseEnd_3660733 : Nat := 1253143717850354066001401

theorem tailTrace_3660733 : CollatzResearch.WordTrace tailWord_3660733 prefixEnd_3660733 1253143717850354066001401 := by
  unfold tailWord_3660733
  simp only [CollatzResearch.WordTrace]
  refine ⟨133517901446797019266522853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89011934297864679511015235 133517901446797019266522853)
  ·
    refine ⟨25034606521274441112473035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133517901446797019266522853 25034606521274441112473035)
    ·
      refine ⟨37551909781911661668709553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25034606521274441112473035 37551909781911661668709553)
      ·
        refine ⟨28163932336433746251532165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37551909781911661668709553 28163932336433746251532165)
        ·
          refine ⟨5280737313081327422162281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28163932336433746251532165 5280737313081327422162281)
          ·
            refine ⟨3960552984810995566621711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280737313081327422162281 3960552984810995566621711)
            ·
              refine ⟨5940829477216493349932567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960552984810995566621711 5940829477216493349932567)
              ·
                refine ⟨8911244215824740024898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940829477216493349932567 8911244215824740024898851)
                ·
                  refine ⟨13366866323737110037348277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8911244215824740024898851 13366866323737110037348277)
                  ·
                    refine ⟨1253143717850354066001401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13366866323737110037348277 1253143717850354066001401)
                    ·
                      rfl

theorem cell22_3660733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3660733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660733 prefixEnd_3660733 := by exact prefixLift 3660733
  have htrace : WordTrace (prefixWord ++ tailWord_3660733) baseStart_3660733 baseEnd_3660733 := by
    simpa [prefixWord, tailWord_3660733, baseEnd_3660733] using wordTrace_append hprefix tailTrace_3660733
  have hstable : (prefixWord ++ tailWord_3660733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660733).length < 2 ^ (prefixWord ++ tailWord_3660733).sum := by decide
  have hdescent : baseEnd_3660733 < baseStart_3660733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660778 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3660778 : Nat := 118140960795 + 3660778 * 2 ^ 59
def prefixEnd_3660778 : Nat := 4983230072969 + 3 ^ 40 * 3660778 * 2
def baseEnd_3660778 : Nat := 1253159122269988948626263

theorem tailTrace_3660778 : CollatzResearch.WordTrace tailWord_3660778 prefixEnd_3660778 1253159122269988948626263 := by
  unfold tailWord_3660778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33379885682908497987977747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89013028487755994634607325 33379885682908497987977747)
  ·
    refine ⟨50069828524362746981966621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33379885682908497987977747 50069828524362746981966621)
    ·
      refine ⟨18776185696636030118237483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50069828524362746981966621 18776185696636030118237483)
      ·
        refine ⟨28164278544954045177356225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18776185696636030118237483 28164278544954045177356225)
        ·
          refine ⟨21123208908715533883017169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28164278544954045177356225 21123208908715533883017169)
          ·
            refine ⟨15842406681536650412262877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21123208908715533883017169 15842406681536650412262877)
            ·
              refine ⟨5940902505576243904598579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15842406681536650412262877 5940902505576243904598579)
              ·
                refine ⟨8911353758364365856897869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5940902505576243904598579 8911353758364365856897869)
                ·
                  refine ⟨3341757659386637196336701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8911353758364365856897869 3341757659386637196336701)
                  ·
                    refine ⟨1253159122269988948626263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341757659386637196336701 1253159122269988948626263)
                    ·
                      rfl

theorem cell22_3660778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3660778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660778 prefixEnd_3660778 := by exact prefixLift 3660778
  have htrace : WordTrace (prefixWord ++ tailWord_3660778) baseStart_3660778 baseEnd_3660778 := by
    simpa [prefixWord, tailWord_3660778, baseEnd_3660778] using wordTrace_append hprefix tailTrace_3660778
  have hstable : (prefixWord ++ tailWord_3660778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660778).length < 2 ^ (prefixWord ++ tailWord_3660778).sum := by decide
  have hdescent : baseEnd_3660778 < baseStart_3660778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660829 : List Nat := [1, 4, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3660829 : Nat := 118140960795 + 3660829 * 2 ^ 59
def prefixEnd_3660829 : Nat := 4983230072969 + 3 ^ 40 * 3660829 * 2
def baseEnd_3660829 : Nat := 1253176580612241815601107

theorem tailTrace_3660829 : CollatzResearch.WordTrace tailWord_3660829 prefixEnd_3660829 1253176580612241815601107 := by
  unfold tailWord_3660829
  simp only [CollatzResearch.WordTrace]
  refine ⟨133521402854449227662017541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89014268569632818441345027 133521402854449227662017541)
  ·
    refine ⟨25035263035209230186628289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133521402854449227662017541 25035263035209230186628289)
    ·
      refine ⟨18776447276406922639971217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25035263035209230186628289 18776447276406922639971217)
      ·
        refine ⟨14082335457305191979978413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18776447276406922639971217 14082335457305191979978413)
        ·
          refine ⟨5280875796489446992491905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14082335457305191979978413 5280875796489446992491905)
          ·
            refine ⟨3960656847367085244368929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5280875796489446992491905 3960656847367085244368929)
            ·
              refine ⟨2970492635525313933276697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3960656847367085244368929 2970492635525313933276697)
              ·
                refine ⟨2227869476643985449957523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2970492635525313933276697 2227869476643985449957523)
                ·
                  refine ⟨3341804214965978174936285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227869476643985449957523 3341804214965978174936285)
                  ·
                    refine ⟨1253176580612241815601107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341804214965978174936285 1253176580612241815601107)
                    ·
                      rfl

theorem cell22_3660829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3660829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660829 prefixEnd_3660829 := by exact prefixLift 3660829
  have htrace : WordTrace (prefixWord ++ tailWord_3660829) baseStart_3660829 baseEnd_3660829 := by
    simpa [prefixWord, tailWord_3660829, baseEnd_3660829] using wordTrace_append hprefix tailTrace_3660829
  have hstable : (prefixWord ++ tailWord_3660829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660829).length < 2 ^ (prefixWord ++ tailWord_3660829).sum := by decide
  have hdescent : baseEnd_3660829 < baseStart_3660829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660851 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 6, 3]
def baseStart_3660851 : Nat := 118140960795 + 3660851 * 2 ^ 59
def prefixEnd_3660851 : Nat := 4983230072969 + 3 ^ 40 * 3660851 * 2
def baseEnd_3660851 : Nat := 1253184111661841091551039

theorem tailTrace_3660851 : CollatzResearch.WordTrace tailWord_3660851 prefixEnd_3660851 1253184111661841091551039 := by
  unfold tailWord_3660851
  simp only [CollatzResearch.WordTrace]
  refine ⟨133522205260369525419318407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89014803506913016946212271 133522205260369525419318407)
  ·
    refine ⟨200283307890554288128977611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133522205260369525419318407 200283307890554288128977611)
    ·
      refine ⟨300424961835831432193466417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200283307890554288128977611 300424961835831432193466417)
      ·
        refine ⟨225318721376873574145099813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300424961835831432193466417 225318721376873574145099813)
        ·
          refine ⟨42247260258163795152206215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225318721376873574145099813 42247260258163795152206215)
          ·
            refine ⟨63370890387245692728309323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42247260258163795152206215 63370890387245692728309323)
            ·
              refine ⟨95056335580868539092463985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63370890387245692728309323 95056335580868539092463985)
              ·
                refine ⟨71292251685651404319347989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95056335580868539092463985 71292251685651404319347989)
                ·
                  refine ⟨3341824297764909577469437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71292251685651404319347989 3341824297764909577469437)
                  ·
                    refine ⟨1253184111661841091551039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341824297764909577469437 1253184111661841091551039)
                    ·
                      rfl

theorem cell22_3660851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 6, 3].length) (baseStart_3660851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660851 prefixEnd_3660851 := by exact prefixLift 3660851
  have htrace : WordTrace (prefixWord ++ tailWord_3660851) baseStart_3660851 baseEnd_3660851 := by
    simpa [prefixWord, tailWord_3660851, baseEnd_3660851] using wordTrace_append hprefix tailTrace_3660851
  have hstable : (prefixWord ++ tailWord_3660851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660851).length < 2 ^ (prefixWord ++ tailWord_3660851).sum := by decide
  have hdescent : baseEnd_3660851 < baseStart_3660851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660994 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3660994 : Nat := 118140960795 + 3660994 * 2 ^ 59
def prefixEnd_3660994 : Nat := 4983230072969 + 3 ^ 40 * 3660994 * 2
def baseEnd_3660994 : Nat := 417744354494745461741867

theorem tailTrace_3660994 : CollatzResearch.WordTrace tailWord_3660994 prefixEnd_3660994 417744354494745461741867 := by
  unfold tailWord_3660994
  simp only [CollatzResearch.WordTrace]
  refine ⟨33381855224712865210443509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89018280599234307227849357 33381855224712865210443509)
  ·
    refine ⟨3129548927316831113479079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33381855224712865210443509 3129548927316831113479079)
    ·
      refine ⟨4694323390975246670218619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129548927316831113479079 4694323390975246670218619)
      ·
        refine ⟨7041485086462870005327929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694323390975246670218619 7041485086462870005327929)
        ·
          refine ⟨5281113814847152503995947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7041485086462870005327929 5281113814847152503995947)
          ·
            refine ⟨7921670722270728755993921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281113814847152503995947 7921670722270728755993921)
            ·
              refine ⟨5941253041703046566995441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7921670722270728755993921 5941253041703046566995441)
              ·
                refine ⟨4455939781277284925246581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941253041703046566995441 4455939781277284925246581)
                ·
                  refine ⟨417744354494745461741867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4455939781277284925246581 417744354494745461741867)
                  ·
                    rfl

theorem cell22_3660994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3660994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660994 prefixEnd_3660994 := by exact prefixLift 3660994
  have htrace : WordTrace (prefixWord ++ tailWord_3660994) baseStart_3660994 baseEnd_3660994 := by
    simpa [prefixWord, tailWord_3660994, baseEnd_3660994] using wordTrace_append hprefix tailTrace_3660994
  have hstable : (prefixWord ++ tailWord_3660994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660994).length < 2 ^ (prefixWord ++ tailWord_3660994).sum := by decide
  have hdescent : baseEnd_3660994 < baseStart_3660994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3660998 : List Nat := [6, 1, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_3660998 : Nat := 118140960795 + 3660998 * 2 ^ 59
def prefixEnd_3660998 : Nat := 4983230072969 + 3 ^ 40 * 3660998 * 2
def baseEnd_3660998 : Nat := 1253234432765981708125589

theorem tailTrace_3660998 : CollatzResearch.WordTrace tailWord_3660998 prefixEnd_3660998 1253234432765981708125589 := by
  unfold tailWord_3660998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4172736462213655297653739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89018377860557979683279765 4172736462213655297653739)
  ·
    refine ⟨6259104693320482946480609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4172736462213655297653739 6259104693320482946480609)
    ·
      refine ⟨4694328519990362209860457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6259104693320482946480609 4694328519990362209860457)
      ·
        refine ⟨3520746389992771657395343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694328519990362209860457 3520746389992771657395343)
        ·
          refine ⟨5281119584989157486093015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3520746389992771657395343 5281119584989157486093015)
          ·
            refine ⟨7921679377483736229139523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281119584989157486093015 7921679377483736229139523)
            ·
              refine ⟨11882519066225604343709285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7921679377483736229139523 11882519066225604343709285)
              ·
                refine ⟨2227972324917300814445491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11882519066225604343709285 2227972324917300814445491)
                ·
                  refine ⟨3341958487375951221668237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2227972324917300814445491 3341958487375951221668237)
                  ·
                    refine ⟨1253234432765981708125589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3341958487375951221668237 1253234432765981708125589)
                    ·
                      rfl

theorem cell22_3660998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_3660998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3660998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3660998 prefixEnd_3660998 := by exact prefixLift 3660998
  have htrace : WordTrace (prefixWord ++ tailWord_3660998) baseStart_3660998 baseEnd_3660998 := by
    simpa [prefixWord, tailWord_3660998, baseEnd_3660998] using wordTrace_append hprefix tailTrace_3660998
  have hstable : (prefixWord ++ tailWord_3660998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3660998).length < 2 ^ (prefixWord ++ tailWord_3660998).sum := by decide
  have hdescent : baseEnd_3660998 < baseStart_3660998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3660998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661035 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 2, 4]
def baseStart_3661035 : Nat := 118140960795 + 3661035 * 2 ^ 59
def prefixEnd_3661035 : Nat := 4983230072969 + 3 ^ 40 * 3661035 * 2
def baseEnd_3661035 : Nat := 1253247098622125944950475

theorem tailTrace_3661035 : CollatzResearch.WordTrace tailWord_3661035 prefixEnd_3661035 1253247098622125944950475 := by
  unfold tailWord_3661035
  simp only [CollatzResearch.WordTrace]
  refine ⟨133528916291702924844016559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89019277527801949896011039 133528916291702924844016559)
  ·
    refine ⟨200293374437554387266024839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133528916291702924844016559 200293374437554387266024839)
    ·
      refine ⟨300440061656331580899037259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200293374437554387266024839 300440061656331580899037259)
      ·
        refine ⟨450660092484497371348555889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300440061656331580899037259 450660092484497371348555889)
        ·
          refine ⟨337995069363373028511416917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450660092484497371348555889 337995069363373028511416917)
          ·
            refine ⟨3960879719102027677868167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 337995069363373028511416917 3960879719102027677868167)
            ·
              refine ⟨5941319578653041516802251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960879719102027677868167 5941319578653041516802251)
              ·
                refine ⟨8911979367979562275203377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941319578653041516802251 8911979367979562275203377)
                ·
                  refine ⟨6683984525984671706402533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8911979367979562275203377 6683984525984671706402533)
                  ·
                    refine ⟨1253247098622125944950475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6683984525984671706402533 1253247098622125944950475)
                    ·
                      rfl

theorem cell22_3661035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 4].length) (baseStart_3661035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661035 prefixEnd_3661035 := by exact prefixLift 3661035
  have htrace : WordTrace (prefixWord ++ tailWord_3661035) baseStart_3661035 baseEnd_3661035 := by
    simpa [prefixWord, tailWord_3661035, baseEnd_3661035] using wordTrace_append hprefix tailTrace_3661035
  have hstable : (prefixWord ++ tailWord_3661035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661035).length < 2 ^ (prefixWord ++ tailWord_3661035).sum := by decide
  have hdescent : baseEnd_3661035 < baseStart_3661035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661054 : List Nat := [4, 2, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3661054 : Nat := 118140960795 + 3661054 * 2 ^ 59
def prefixEnd_3661054 : Nat := 4983230072969 + 3 ^ 40 * 3661054 * 2
def baseEnd_3661054 : Nat := 1253253602710416228725417

theorem tailTrace_3661054 : CollatzResearch.WordTrace tailWord_3661054 prefixEnd_3661054 1253253602710416228725417 := by
  unfold tailWord_3661054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16691201159829261386119777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89019739519089394059305477 16691201159829261386119777)
  ·
    refine ⟨12518400869871946039589833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16691201159829261386119777 12518400869871946039589833)
    ·
      refine ⟨9388800652403959529692375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12518400869871946039589833 9388800652403959529692375)
      ·
        refine ⟨14083200978605939294538563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9388800652403959529692375 14083200978605939294538563)
        ·
          refine ⟨21124801467908908941807845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14083200978605939294538563 21124801467908908941807845)
          ·
            refine ⟨3960900275232920426588971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21124801467908908941807845 3960900275232920426588971)
            ·
              refine ⟨5941350412849380639883457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3960900275232920426588971 5941350412849380639883457)
              ·
                refine ⟨4456012809637035479912593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941350412849380639883457 4456012809637035479912593)
                ·
                  refine ⟨3342009607227776609934445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456012809637035479912593 3342009607227776609934445)
                  ·
                    refine ⟨1253253602710416228725417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342009607227776609934445 1253253602710416228725417)
                    ·
                      rfl

theorem cell22_3661054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3661054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661054 prefixEnd_3661054 := by exact prefixLift 3661054
  have htrace : WordTrace (prefixWord ++ tailWord_3661054) baseStart_3661054 baseEnd_3661054 := by
    simpa [prefixWord, tailWord_3661054, baseEnd_3661054] using wordTrace_append hprefix tailTrace_3661054
  have hstable : (prefixWord ++ tailWord_3661054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661054).length < 2 ^ (prefixWord ++ tailWord_3661054).sum := by decide
  have hdescent : baseEnd_3661054 < baseStart_3661054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661065 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 3, 3]
def baseStart_3661065 : Nat := 118140960795 + 3661065 * 2 ^ 59
def prefixEnd_3661065 : Nat := 4983230072969 + 3 ^ 40 * 3661065 * 2
def baseEnd_3661065 : Nat := 1253257368235215866700383

theorem tailTrace_3661065 : CollatzResearch.WordTrace tailWord_3661065 prefixEnd_3661065 1253257368235215866700383 := by
  unfold tailWord_3661065
  simp only [CollatzResearch.WordTrace]
  refine ⟨133530010481594239967608649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89020006987729493311739099 133530010481594239967608649)
  ·
    refine ⟨100147507861195679975706487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133530010481594239967608649 100147507861195679975706487)
    ·
      refine ⟨150221261791793519963559731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100147507861195679975706487 150221261791793519963559731)
      ·
        refine ⟨225331892687690279945339597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150221261791793519963559731 225331892687690279945339597)
        ·
          refine ⟨84499459757883854979502349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225331892687690279945339597 84499459757883854979502349)
          ·
            refine ⟨31687297409206445617313381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84499459757883854979502349 31687297409206445617313381)
            ·
              refine ⟨5941368264226208553246259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31687297409206445617313381 5941368264226208553246259)
              ·
                refine ⟨8912052396339312829869389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941368264226208553246259 8912052396339312829869389)
                ·
                  refine ⟨3342019648627242311201021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8912052396339312829869389 3342019648627242311201021)
                  ·
                    refine ⟨1253257368235215866700383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342019648627242311201021 1253257368235215866700383)
                    ·
                      rfl

theorem cell22_3661065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 3, 3].length) (baseStart_3661065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661065 prefixEnd_3661065 := by exact prefixLift 3661065
  have htrace : WordTrace (prefixWord ++ tailWord_3661065) baseStart_3661065 baseEnd_3661065 := by
    simpa [prefixWord, tailWord_3661065, baseEnd_3661065] using wordTrace_append hprefix tailTrace_3661065
  have hstable : (prefixWord ++ tailWord_3661065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661065).length < 2 ^ (prefixWord ++ tailWord_3661065).sum := by decide
  have hdescent : baseEnd_3661065 < baseStart_3661065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661153 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3661153 : Nat := 118140960795 + 3661153 * 2 ^ 59
def prefixEnd_3661153 : Nat := 4983230072969 + 3 ^ 40 * 3661153 * 2
def baseEnd_3661153 : Nat := 1253287492433612970500113

theorem tailTrace_3661153 : CollatzResearch.WordTrace tailWord_3661153 prefixEnd_3661153 1253287492433612970500113 := by
  unfold tailWord_3661153
  simp only [CollatzResearch.WordTrace]
  refine ⟨133533220105275430996812113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89022146736850287331208075 133533220105275430996812113)
  ·
    refine ⟨100149915078956573247609085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133533220105275430996812113 100149915078956573247609085)
    ·
      refine ⟨37556218154608714967853407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100149915078956573247609085 37556218154608714967853407)
      ·
        refine ⟨56334327231913072451780111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37556218154608714967853407 56334327231913072451780111)
        ·
          refine ⟨84501490847869608677670167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56334327231913072451780111 84501490847869608677670167)
          ·
            refine ⟨126752236271804413016505251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84501490847869608677670167 126752236271804413016505251)
            ·
              refine ⟨190128354407706619524757877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126752236271804413016505251 190128354407706619524757877)
              ·
                refine ⟨17824533225722495580446051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190128354407706619524757877 17824533225722495580446051)
                ·
                  refine ⟨26736799838583743370669077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17824533225722495580446051 26736799838583743370669077)
                  ·
                    refine ⟨1253287492433612970500113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26736799838583743370669077 1253287492433612970500113)
                    ·
                      rfl

theorem cell22_3661153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3661153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661153 prefixEnd_3661153 := by exact prefixLift 3661153
  have htrace : WordTrace (prefixWord ++ tailWord_3661153) baseStart_3661153 baseEnd_3661153 := by
    simpa [prefixWord, tailWord_3661153, baseEnd_3661153] using wordTrace_append hprefix tailTrace_3661153
  have hstable : (prefixWord ++ tailWord_3661153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661153).length < 2 ^ (prefixWord ++ tailWord_3661153).sum := by decide
  have hdescent : baseEnd_3661153 < baseStart_3661153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661155 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_3661155 : Nat := 118140960795 + 3661155 * 2 ^ 59
def prefixEnd_3661155 : Nat := 4983230072969 + 3 ^ 40 * 3661155 * 2
def baseEnd_3661155 : Nat := 1253288177074485631950107

theorem tailTrace_3661155 : CollatzResearch.WordTrace tailWord_3661155 prefixEnd_3661155 1253288177074485631950107 := by
  unfold tailWord_3661155
  simp only [CollatzResearch.WordTrace]
  refine ⟨133533293051268185338384919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89022195367512123558923279 133533293051268185338384919)
  ·
    refine ⟨200299939576902278007577379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133533293051268185338384919 200299939576902278007577379)
    ·
      refine ⟨300449909365353417011366069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200299939576902278007577379 300449909365353417011366069)
      ·
        refine ⟨28167179003001882844815569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300449909365353417011366069 28167179003001882844815569)
        ·
          refine ⟨21125384252251412133611677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28167179003001882844815569 21125384252251412133611677)
          ·
            refine ⟨7922019094594279550104379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21125384252251412133611677 7922019094594279550104379)
            ·
              refine ⟨11883028641891419325156569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922019094594279550104379 11883028641891419325156569)
              ·
                refine ⟨8912271481418564493867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11883028641891419325156569 8912271481418564493867427)
                ·
                  refine ⟨13368407222127846740801141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8912271481418564493867427 13368407222127846740801141)
                  ·
                    refine ⟨1253288177074485631950107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13368407222127846740801141 1253288177074485631950107)
                    ·
                      rfl

theorem cell22_3661155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_3661155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661155 prefixEnd_3661155 := by exact prefixLift 3661155
  have htrace : WordTrace (prefixWord ++ tailWord_3661155) baseStart_3661155 baseEnd_3661155 := by
    simpa [prefixWord, tailWord_3661155, baseEnd_3661155] using wordTrace_append hprefix tailTrace_3661155
  have hstable : (prefixWord ++ tailWord_3661155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661155).length < 2 ^ (prefixWord ++ tailWord_3661155).sum := by decide
  have hdescent : baseEnd_3661155 < baseStart_3661155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661159 : List Nat := [1, 1, 5, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3661159 : Nat := 118140960795 + 3661159 * 2 ^ 59
def prefixEnd_3661159 : Nat := 4983230072969 + 3 ^ 40 * 3661159 * 2
def baseEnd_3661159 : Nat := 1253289546356230954850095

theorem tailTrace_3661159 : CollatzResearch.WordTrace tailWord_3661159 prefixEnd_3661159 1253289546356230954850095 := by
  unfold tailWord_3661159
  simp only [CollatzResearch.WordTrace]
  refine ⟨133533438943253694021530531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89022292628835796014353687 133533438943253694021530531)
  ·
    refine ⟨200300158414880541032295797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133533438943253694021530531 200300158414880541032295797)
    ·
      refine ⟨18778139851395050721777731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200300158414880541032295797 18778139851395050721777731)
      ·
        refine ⟨28167209777092576082666597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18778139851395050721777731 28167209777092576082666597)
        ·
          refine ⟨5281351833204858015499987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28167209777092576082666597 5281351833204858015499987)
          ·
            refine ⟨7922027749807287023249981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5281351833204858015499987 7922027749807287023249981)
            ·
              refine ⟨2970760406177732633718743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7922027749807287023249981 2970760406177732633718743)
              ·
                refine ⟨4456140609266598950578115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970760406177732633718743 4456140609266598950578115)
                ·
                  refine ⟨6684210913899898425867173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4456140609266598950578115 6684210913899898425867173)
                  ·
                    refine ⟨1253289546356230954850095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684210913899898425867173 1253289546356230954850095)
                    ·
                      rfl

theorem cell22_3661159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3661159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661159 prefixEnd_3661159 := by exact prefixLift 3661159
  have htrace : WordTrace (prefixWord ++ tailWord_3661159) baseStart_3661159 baseEnd_3661159 := by
    simpa [prefixWord, tailWord_3661159, baseEnd_3661159] using wordTrace_append hprefix tailTrace_3661159
  have hstable : (prefixWord ++ tailWord_3661159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661159).length < 2 ^ (prefixWord ++ tailWord_3661159).sum := by decide
  have hdescent : baseEnd_3661159 < baseStart_3661159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661170 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_3661170 : Nat := 118140960795 + 3661170 * 2 ^ 59
def prefixEnd_3661170 : Nat := 4983230072969 + 3 ^ 40 * 3661170 * 2
def baseEnd_3661170 : Nat := 1253293311881030592825061

theorem tailTrace_3661170 : CollatzResearch.WordTrace tailWord_3661170 prefixEnd_3661170 1253293311881030592825061 := by
  unfold tailWord_3661170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33383460036553460725045241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89022560097475895266787309 33383460036553460725045241)
  ·
    refine ⟨25037595027415095543783931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33383460036553460725045241 25037595027415095543783931)
    ·
      refine ⟨37556392541122643315675897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25037595027415095543783931 37556392541122643315675897)
      ·
        refine ⟨28167294405841982486756923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37556392541122643315675897 28167294405841982486756923)
        ·
          refine ⟨42250941608762973730135385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28167294405841982486756923 42250941608762973730135385)
          ·
            refine ⟨31688206206572230297601539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42250941608762973730135385 31688206206572230297601539)
            ·
              refine ⟨47532309309858345446402309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31688206206572230297601539 47532309309858345446402309)
              ·
                refine ⟨8912307995598439771200433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47532309309858345446402309 8912307995598439771200433)
                ·
                  refine ⟨6684230996698829828400325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912307995598439771200433 6684230996698829828400325)
                  ·
                    refine ⟨1253293311881030592825061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684230996698829828400325 1253293311881030592825061)
                    ·
                      rfl

theorem cell22_3661170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_3661170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661170 prefixEnd_3661170 := by exact prefixLift 3661170
  have htrace : WordTrace (prefixWord ++ tailWord_3661170) baseStart_3661170 baseEnd_3661170 := by
    simpa [prefixWord, tailWord_3661170, baseEnd_3661170] using wordTrace_append hprefix tailTrace_3661170
  have hstable : (prefixWord ++ tailWord_3661170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661170).length < 2 ^ (prefixWord ++ tailWord_3661170).sum := by decide
  have hdescent : baseEnd_3661170 < baseStart_3661170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661204 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_3661204 : Nat := 118140960795 + 3661204 * 2 ^ 59
def prefixEnd_3661204 : Nat := 4983230072969 + 3 ^ 40 * 3661204 * 2
def baseEnd_3661204 : Nat := 1253304950775865837474957

theorem tailTrace_3661204 : CollatzResearch.WordTrace tailWord_3661204 prefixEnd_3661204 1253304950775865837474957 := by
  unfold tailWord_3661204
  simp only [CollatzResearch.WordTrace]
  refine ⟨66767540114045333353459333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89023386818727111137945777 66767540114045333353459333)
  ·
    refine ⟨12518913771383500003773625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66767540114045333353459333 12518913771383500003773625)
    ·
      refine ⟨9389185328537625002830219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12518913771383500003773625 9389185328537625002830219)
      ·
        refine ⟨14083777992806437504245329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9389185328537625002830219 14083777992806437504245329)
        ·
          refine ⟨10562833494604828128183997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14083777992806437504245329 10562833494604828128183997)
          ·
            refine ⟨3961062560476810548068999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10562833494604828128183997 3961062560476810548068999)
            ·
              refine ⟨5941593840715215822103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961062560476810548068999 5941593840715215822103499)
              ·
                refine ⟨8912390761072823733155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5941593840715215822103499 8912390761072823733155249)
                ·
                  refine ⟨6684293070804617799866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912390761072823733155249 6684293070804617799866437)
                  ·
                    refine ⟨1253304950775865837474957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684293070804617799866437 1253304950775865837474957)
                    ·
                      rfl

theorem cell22_3661204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_3661204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661204 prefixEnd_3661204 := by exact prefixLift 3661204
  have htrace : WordTrace (prefixWord ++ tailWord_3661204) baseStart_3661204 baseEnd_3661204 := by
    simpa [prefixWord, tailWord_3661204, baseEnd_3661204] using wordTrace_append hprefix tailTrace_3661204
  have hstable : (prefixWord ++ tailWord_3661204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661204).length < 2 ^ (prefixWord ++ tailWord_3661204).sum := by decide
  have hdescent : baseEnd_3661204 < baseStart_3661204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661245 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3661245 : Nat := 118140960795 + 3661245 * 2 ^ 59
def prefixEnd_3661245 : Nat := 4983230072969 + 3 ^ 40 * 3661245 * 2
def baseEnd_3661245 : Nat := 1253318985913755397199831

theorem tailTrace_3661245 : CollatzResearch.WordTrace tailWord_3661245 prefixEnd_3661245 1253318985913755397199831 := by
  unfold tailWord_3661245
  simp only [CollatzResearch.WordTrace]
  refine ⟨133536575620942130709161189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89024383747294753806107459 133536575620942130709161189)
  ·
    refine ⟨25038107928926649507967723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133536575620942130709161189 25038107928926649507967723)
    ·
      refine ⟨37557161893389974261951585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25038107928926649507967723 37557161893389974261951585)
      ·
        refine ⟨28167871420042480696463689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37557161893389974261951585 28167871420042480696463689)
        ·
          refine ⟨21125903565031860522347767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28167871420042480696463689 21125903565031860522347767)
          ·
            refine ⟨31688855347547790783521651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21125903565031860522347767 31688855347547790783521651)
            ·
              refine ⟨47533283021321686175282477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31688855347547790783521651 47533283021321686175282477)
              ·
                refine ⟨17824981132995632315730929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47533283021321686175282477 17824981132995632315730929)
                ·
                  refine ⟨13368735849746724236798197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17824981132995632315730929 13368735849746724236798197)
                  ·
                    refine ⟨1253318985913755397199831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13368735849746724236798197 1253318985913755397199831)
                    ·
                      rfl

theorem cell22_3661245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3661245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661245 prefixEnd_3661245 := by exact prefixLift 3661245
  have htrace : WordTrace (prefixWord ++ tailWord_3661245) baseStart_3661245 baseEnd_3661245 := by
    simpa [prefixWord, tailWord_3661245, baseEnd_3661245] using wordTrace_append hprefix tailTrace_3661245
  have hstable : (prefixWord ++ tailWord_3661245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661245).length < 2 ^ (prefixWord ++ tailWord_3661245).sum := by decide
  have hdescent : baseEnd_3661245 < baseStart_3661245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661268 : List Nat := [2, 4, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_3661268 : Nat := 118140960795 + 3661268 * 2 ^ 59
def prefixEnd_3661268 : Nat := 4983230072969 + 3 ^ 40 * 3661268 * 2
def baseEnd_3661268 : Nat := 1253326859283791003874761

theorem tailTrace_3661268 : CollatzResearch.WordTrace tailWord_3661268 prefixEnd_3661268 1253326859283791003874761 := by
  unfold tailWord_3661268
  simp only [CollatzResearch.WordTrace]
  refine ⟨66768707249929402818624229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89024942999905870424832305 66768707249929402818624229)
  ·
    refine ⟨12519132609361763028492043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66768707249929402818624229 12519132609361763028492043)
    ·
      refine ⟨18778698914042644542738065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12519132609361763028492043 18778698914042644542738065)
      ·
        refine ⟨14084024185531983407053549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18778698914042644542738065 14084024185531983407053549)
        ·
          refine ⟨5281509069574493777645081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14084024185531983407053549 5281509069574493777645081)
          ·
            refine ⟨3961131802180870333233811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5281509069574493777645081 3961131802180870333233811)
            ·
              refine ⟨5941697703271305499850717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961131802180870333233811 5941697703271305499850717)
              ·
                refine ⟨2228136638726739562444019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941697703271305499850717 2228136638726739562444019)
                ·
                  refine ⟨3342204958090109343666029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228136638726739562444019 3342204958090109343666029)
                  ·
                    refine ⟨1253326859283791003874761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342204958090109343666029 1253326859283791003874761)
                    ·
                      rfl

theorem cell22_3661268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_3661268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661268 prefixEnd_3661268 := by exact prefixLift 3661268
  have htrace : WordTrace (prefixWord ++ tailWord_3661268) baseStart_3661268 baseEnd_3661268 := by
    simpa [prefixWord, tailWord_3661268, baseEnd_3661268] using wordTrace_append hprefix tailTrace_3661268
  have hstable : (prefixWord ++ tailWord_3661268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661268).length < 2 ^ (prefixWord ++ tailWord_3661268).sum := by decide
  have hdescent : baseEnd_3661268 < baseStart_3661268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661305 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_3661305 : Nat := 118140960795 + 3661305 * 2 ^ 59
def prefixEnd_3661305 : Nat := 4983230072969 + 3 ^ 40 * 3661305 * 2
def baseEnd_3661305 : Nat := 1253339525139935240699647

theorem tailTrace_3661305 : CollatzResearch.WordTrace tailWord_3661305 prefixEnd_3661305 1253339525139935240699647 := by
  unfold tailWord_3661305
  simp only [CollatzResearch.WordTrace]
  refine ⟨133538764000724760956345369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89025842667149840637563579 133538764000724760956345369)
  ·
    refine ⟨100154073000543570717259027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133538764000724760956345369 100154073000543570717259027)
    ·
      refine ⟨150231109500815356075888541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100154073000543570717259027 150231109500815356075888541)
      ·
        refine ⟨56336666062805758528458203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150231109500815356075888541 56336666062805758528458203)
        ·
          refine ⟨84504999094208637792687305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56336666062805758528458203 84504999094208637792687305)
          ·
            refine ⟨63378749320656478344515479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84504999094208637792687305 63378749320656478344515479)
            ·
              refine ⟨95068123980984717516773219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63378749320656478344515479 95068123980984717516773219)
              ·
                refine ⟨142602185971477076275159829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95068123980984717516773219 142602185971477076275159829)
                ·
                  refine ⟨6684477467412987950398117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142602185971477076275159829 6684477467412987950398117)
                  ·
                    refine ⟨1253339525139935240699647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684477467412987950398117 1253339525139935240699647)
                    ·
                      rfl

theorem cell22_3661305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_3661305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661305 prefixEnd_3661305 := by exact prefixLift 3661305
  have htrace : WordTrace (prefixWord ++ tailWord_3661305) baseStart_3661305 baseEnd_3661305 := by
    simpa [prefixWord, tailWord_3661305, baseEnd_3661305] using wordTrace_append hprefix tailTrace_3661305
  have hstable : (prefixWord ++ tailWord_3661305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661305).length < 2 ^ (prefixWord ++ tailWord_3661305).sum := by decide
  have hdescent : baseEnd_3661305 < baseStart_3661305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661307 : List Nat := [1, 1, 1, 1, 1, 3, 2, 7, 2, 3]
def baseStart_3661307 : Nat := 118140960795 + 3661307 * 2 ^ 59
def prefixEnd_3661307 : Nat := 4983230072969 + 3 ^ 40 * 3661307 * 2
def baseEnd_3661307 : Nat := 1253340209780807902149641

theorem tailTrace_3661307 : CollatzResearch.WordTrace tailWord_3661307 prefixEnd_3661307 1253340209780807902149641 := by
  unfold tailWord_3661307
  simp only [CollatzResearch.WordTrace]
  refine ⟨133538836946717515297918175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89025891297811676865278783 133538836946717515297918175)
  ·
    refine ⟨200308255420076272946877263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133538836946717515297918175 200308255420076272946877263)
    ·
      refine ⟨300462383130114409420315895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200308255420076272946877263 300462383130114409420315895)
      ·
        refine ⟨450693574695171614130473843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300462383130114409420315895 450693574695171614130473843)
        ·
          refine ⟨676040362042757421195710765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450693574695171614130473843 676040362042757421195710765)
          ·
            refine ⟨253515135766034032948391537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 676040362042757421195710765 253515135766034032948391537)
            ·
              refine ⟨190136351824525524711293653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253515135766034032948391537 190136351824525524711293653)
              ·
                refine ⟨4456320745887316985420945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190136351824525524711293653 4456320745887316985420945)
                ·
                  refine ⟨3342240559415487739065709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456320745887316985420945 3342240559415487739065709)
                  ·
                    refine ⟨1253340209780807902149641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342240559415487739065709 1253340209780807902149641)
                    ·
                      rfl

theorem cell22_3661307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 3].length) (baseStart_3661307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661307 prefixEnd_3661307 := by exact prefixLift 3661307
  have htrace : WordTrace (prefixWord ++ tailWord_3661307) baseStart_3661307 baseEnd_3661307 := by
    simpa [prefixWord, tailWord_3661307, baseEnd_3661307] using wordTrace_append hprefix tailTrace_3661307
  have hstable : (prefixWord ++ tailWord_3661307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661307).length < 2 ^ (prefixWord ++ tailWord_3661307).sum := by decide
  have hdescent : baseEnd_3661307 < baseStart_3661307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661320 : List Nat := [2, 1, 3, 2, 1, 1, 4, 8]
def baseStart_3661320 : Nat := 118140960795 + 3661320 * 2 ^ 59
def prefixEnd_3661320 : Nat := 4983230072969 + 3 ^ 40 * 3661320 * 2
def baseEnd_3661320 : Nat := 139260517771831133508289

theorem tailTrace_3661320 : CollatzResearch.WordTrace tailWord_3661320 prefixEnd_3661320 139260517771831133508289 := by
  unfold tailWord_3661320
  simp only [CollatzResearch.WordTrace]
  refine ⟨66769655547835209259070707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89026207397113612345427609 66769655547835209259070707)
  ·
    refine ⟨100154483321752813888606061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66769655547835209259070707 100154483321752813888606061)
    ·
      refine ⟨37557931245657305208227273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100154483321752813888606061 37557931245657305208227273)
      ·
        refine ⟨28168448434242978906170455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37557931245657305208227273 28168448434242978906170455)
        ·
          refine ⟨42252672651364468359255683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28168448434242978906170455 42252672651364468359255683)
          ·
            refine ⟨63379008977046702538883525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42252672651364468359255683 63379008977046702538883525)
            ·
              refine ⟨11883564183196256726040661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63379008977046702538883525 11883564183196256726040661)
              ·
                refine ⟨139260517771831133508289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11883564183196256726040661 139260517771831133508289)
                ·
                  rfl

theorem cell22_3661320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_3661320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661320 prefixEnd_3661320 := by exact prefixLift 3661320
  have htrace : WordTrace (prefixWord ++ tailWord_3661320) baseStart_3661320 baseEnd_3661320 := by
    simpa [prefixWord, tailWord_3661320, baseEnd_3661320] using wordTrace_append hprefix tailTrace_3661320
  have hstable : (prefixWord ++ tailWord_3661320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661320).length < 2 ^ (prefixWord ++ tailWord_3661320).sum := by decide
  have hdescent : baseEnd_3661320 < baseStart_3661320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661322 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_3661322 : Nat := 118140960795 + 3661322 * 2 ^ 59
def prefixEnd_3661322 : Nat := 4983230072969 + 3 ^ 40 * 3661322 * 2
def baseEnd_3661322 : Nat := 1253345344587352863024595

theorem tailTrace_3661322 : CollatzResearch.WordTrace tailWord_3661322 prefixEnd_3661322 1253345344587352863024595 := by
  unfold tailWord_3661322
  simp only [CollatzResearch.WordTrace]
  refine ⟨33384846010415793214928555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89026256027775448573142813 33384846010415793214928555)
  ·
    refine ⟨50077269015623689822392833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33384846010415793214928555 50077269015623689822392833)
    ·
      refine ⟨37557951761717767366794625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50077269015623689822392833 37557951761717767366794625)
      ·
        refine ⟨28168463821288325525095969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37557951761717767366794625 28168463821288325525095969)
        ·
          refine ⟨21126347865966244143821977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28168463821288325525095969 21126347865966244143821977)
          ·
            refine ⟨15844760899474683107866483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21126347865966244143821977 15844760899474683107866483)
            ·
              refine ⟨23767141349212024661799725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15844760899474683107866483 23767141349212024661799725)
              ·
                refine ⟨8912678005954509248174897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23767141349212024661799725 8912678005954509248174897)
                ·
                  refine ⟨6684508504465881936131173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8912678005954509248174897 6684508504465881936131173)
                  ·
                    refine ⟨1253345344587352863024595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6684508504465881936131173 1253345344587352863024595)
                    ·
                      rfl

theorem cell22_3661322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_3661322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661322 prefixEnd_3661322 := by exact prefixLift 3661322
  have htrace : WordTrace (prefixWord ++ tailWord_3661322) baseStart_3661322 baseEnd_3661322 := by
    simpa [prefixWord, tailWord_3661322, baseEnd_3661322] using wordTrace_append hprefix tailTrace_3661322
  have hstable : (prefixWord ++ tailWord_3661322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661322).length < 2 ^ (prefixWord ++ tailWord_3661322).sum := by decide
  have hdescent : baseEnd_3661322 < baseStart_3661322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661369 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 3, 3]
def baseStart_3661369 : Nat := 118140960795 + 3661369 * 2 ^ 59
def prefixEnd_3661369 : Nat := 4983230072969 + 3 ^ 40 * 3661369 * 2
def baseEnd_3661369 : Nat := 1253361433647860407099451

theorem tailTrace_3661369 : CollatzResearch.WordTrace tailWord_3661369 prefixEnd_3661369 1253361433647860407099451 := by
  unfold tailWord_3661369
  simp only [CollatzResearch.WordTrace]
  refine ⟨133541098272492899886675161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89027398848328599924450107 133541098272492899886675161)
  ·
    refine ⟨100155823704369674915006371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133541098272492899886675161 100155823704369674915006371)
    ·
      refine ⟨150233735556554512372509557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100155823704369674915006371 150233735556554512372509557)
      ·
        refine ⟨14084412708426985534922771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150233735556554512372509557 14084412708426985534922771)
        ·
          refine ⟨21126619062640478302384157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14084412708426985534922771 21126619062640478302384157)
          ·
            refine ⟨7922482148490179363394059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21126619062640478302384157 7922482148490179363394059)
            ·
              refine ⟨11883723222735269045091089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922482148490179363394059 11883723222735269045091089)
              ·
                refine ⟨8912792417051451783818317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11883723222735269045091089 8912792417051451783818317)
                ·
                  refine ⟨3342297156394294418931869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8912792417051451783818317 3342297156394294418931869)
                  ·
                    refine ⟨1253361433647860407099451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342297156394294418931869 1253361433647860407099451)
                    ·
                      rfl

theorem cell22_3661369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 3].length) (baseStart_3661369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661369 prefixEnd_3661369 := by exact prefixLift 3661369
  have htrace : WordTrace (prefixWord ++ tailWord_3661369) baseStart_3661369 baseEnd_3661369 := by
    simpa [prefixWord, tailWord_3661369, baseEnd_3661369] using wordTrace_append hprefix tailTrace_3661369
  have hstable : (prefixWord ++ tailWord_3661369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661369).length < 2 ^ (prefixWord ++ tailWord_3661369).sum := by decide
  have hdescent : baseEnd_3661369 < baseStart_3661369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661386 : List Nat := [3, 1, 2, 1, 1, 3, 4, 3, 1, 3]
def baseStart_3661386 : Nat := 118140960795 + 3661386 * 2 ^ 59
def prefixEnd_3661386 : Nat := 4983230072969 + 3 ^ 40 * 3661386 * 2
def baseEnd_3661386 : Nat := 1253367253095278029424399

theorem tailTrace_3661386 : CollatzResearch.WordTrace tailWord_3661386 prefixEnd_3661386 1253367253095278029424399 := by
  unfold tailWord_3661386
  simp only [CollatzResearch.WordTrace]
  refine ⟨33385429578357827947511003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89027812208954207860029341 33385429578357827947511003)
  ·
    refine ⟨50078144367536741921266505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33385429578357827947511003 50078144367536741921266505)
    ·
      refine ⟨37558608275652556440949879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50078144367536741921266505 37558608275652556440949879)
      ·
        refine ⟨56337912413478834661424819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37558608275652556440949879 56337912413478834661424819)
        ·
          refine ⟨84506868620218251992137229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56337912413478834661424819 84506868620218251992137229)
          ·
            refine ⟨31690075732581844497051461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84506868620218251992137229 31690075732581844497051461)
            ·
              refine ⟨5941889199859095843197149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31690075732581844497051461 5941889199859095843197149)
              ·
                refine ⟨2228208449947160941198931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5941889199859095843197149 2228208449947160941198931)
                ·
                  refine ⟨3342312674920741411798397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228208449947160941198931 3342312674920741411798397)
                  ·
                    refine ⟨1253367253095278029424399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342312674920741411798397 1253367253095278029424399)
                    ·
                      rfl

theorem cell22_3661386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_3661386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661386 prefixEnd_3661386 := by exact prefixLift 3661386
  have htrace : WordTrace (prefixWord ++ tailWord_3661386) baseStart_3661386 baseEnd_3661386 := by
    simpa [prefixWord, tailWord_3661386, baseEnd_3661386] using wordTrace_append hprefix tailTrace_3661386
  have hstable : (prefixWord ++ tailWord_3661386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661386).length < 2 ^ (prefixWord ++ tailWord_3661386).sum := by decide
  have hdescent : baseEnd_3661386 < baseStart_3661386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661399 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 5]
def baseStart_3661399 : Nat := 118140960795 + 3661399 * 2 ^ 59
def prefixEnd_3661399 : Nat := 4983230072969 + 3 ^ 40 * 3661399 * 2
def baseEnd_3661399 : Nat := 417790567753650109616453

theorem tailTrace_3661399 : CollatzResearch.WordTrace tailWord_3661399 prefixEnd_3661399 417790567753650109616453 := by
  unfold tailWord_3661399
  simp only [CollatzResearch.WordTrace]
  refine ⟨133542192462384215010267251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89028128308256143340178167 133542192462384215010267251)
  ·
    refine ⟨200313288693576322515400877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133542192462384215010267251 200313288693576322515400877)
    ·
      refine ⟨75117483260091120943275329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200313288693576322515400877 75117483260091120943275329)
      ·
        refine ⟨56338112445068340707456497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75117483260091120943275329 56338112445068340707456497)
        ·
          refine ⟨42253584333801255530592373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56338112445068340707456497 42253584333801255530592373)
          ·
            refine ⟨3961273531293867705993035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42253584333801255530592373 3961273531293867705993035)
            ·
              refine ⟨5941910296940801558989553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3961273531293867705993035 5941910296940801558989553)
              ·
                refine ⟨4456432722705601169242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5941910296940801558989553 4456432722705601169242165)
                ·
                  refine ⟨417790567753650109616453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456432722705601169242165 417790567753650109616453)
                  ·
                    rfl

theorem cell22_3661399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 5].length) (baseStart_3661399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661399 prefixEnd_3661399 := by exact prefixLift 3661399
  have htrace : WordTrace (prefixWord ++ tailWord_3661399) baseStart_3661399 baseEnd_3661399 := by
    simpa [prefixWord, tailWord_3661399, baseEnd_3661399] using wordTrace_append hprefix tailTrace_3661399
  have hstable : (prefixWord ++ tailWord_3661399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661399).length < 2 ^ (prefixWord ++ tailWord_3661399).sum := by decide
  have hdescent : baseEnd_3661399 < baseStart_3661399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661416 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_3661416 : Nat := 118140960795 + 3661416 * 2 ^ 59
def prefixEnd_3661416 : Nat := 4983230072969 + 3 ^ 40 * 3661416 * 2
def baseEnd_3661416 : Nat := 417792507569455983724769

theorem tailTrace_3661416 : CollatzResearch.WordTrace tailWord_3661416 prefixEnd_3661416 417792507569455983724769 := by
  unfold tailWord_3661416
  simp only [CollatzResearch.WordTrace]
  refine ⟨66771406251661313456818051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89028541668881751275757401 66771406251661313456818051)
  ·
    refine ⟨100157109377491970185227077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66771406251661313456818051 100157109377491970185227077)
    ·
      refine ⟨18779458008279744409730077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100157109377491970185227077 18779458008279744409730077)
      ·
        refine ⟨7042296753104904153648779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18779458008279744409730077 7042296753104904153648779)
        ·
          refine ⟨10563445129657356230473169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042296753104904153648779 10563445129657356230473169)
          ·
            refine ⟨7922583847243017172854877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10563445129657356230473169 7922583847243017172854877)
            ·
              refine ⟨2970968942716131439820579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7922583847243017172854877 2970968942716131439820579)
              ·
                refine ⟨4456453414074197159730869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2970968942716131439820579 4456453414074197159730869)
                ·
                  refine ⟨417792507569455983724769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4456453414074197159730869 417792507569455983724769)
                  ·
                    rfl

theorem cell22_3661416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_3661416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661416 prefixEnd_3661416 := by exact prefixLift 3661416
  have htrace : WordTrace (prefixWord ++ tailWord_3661416) baseStart_3661416 baseEnd_3661416 := by
    simpa [prefixWord, tailWord_3661416, baseEnd_3661416] using wordTrace_append hprefix tailTrace_3661416
  have hstable : (prefixWord ++ tailWord_3661416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661416).length < 2 ^ (prefixWord ++ tailWord_3661416).sum := by decide
  have hdescent : baseEnd_3661416 < baseStart_3661416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661472 : List Nat := [2, 1, 1, 4, 3, 1, 1, 9]
def baseStart_3661472 : Nat := 118140960795 + 3661472 * 2 ^ 59
def prefixEnd_3661472 : Nat := 4983230072969 + 3 ^ 40 * 3661472 * 2
def baseEnd_3661472 : Nat := 139266299183644719086015

theorem tailTrace_3661472 : CollatzResearch.WordTrace tailWord_3661472 prefixEnd_3661472 139266299183644719086015 := by
  unfold tailWord_3661472
  simp only [CollatzResearch.WordTrace]
  refine ⟨66772427495559874238837335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89029903327413165651783113 66772427495559874238837335)
  ·
    refine ⟨100158641243339811358256003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66772427495559874238837335 100158641243339811358256003)
    ·
      refine ⟨150237961865009717037384005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100158641243339811358256003 150237961865009717037384005)
      ·
        refine ⟨28169617849689321944509501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150237961865009717037384005 28169617849689321944509501)
        ·
          refine ⟨10563606693633495729191063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28169617849689321944509501 10563606693633495729191063)
          ·
            refine ⟨15845410040450243593786595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563606693633495729191063 15845410040450243593786595)
            ·
              refine ⟨23768115060675365390679893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15845410040450243593786595 23768115060675365390679893)
              ·
                refine ⟨139266299183644719086015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23768115060675365390679893 139266299183644719086015)
                ·
                  rfl

theorem cell22_3661472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_3661472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661472 prefixEnd_3661472 := by exact prefixLift 3661472
  have htrace : WordTrace (prefixWord ++ tailWord_3661472) baseStart_3661472 baseEnd_3661472 := by
    simpa [prefixWord, tailWord_3661472, baseEnd_3661472] using wordTrace_append hprefix tailTrace_3661472
  have hstable : (prefixWord ++ tailWord_3661472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661472).length < 2 ^ (prefixWord ++ tailWord_3661472).sum := by decide
  have hdescent : baseEnd_3661472 < baseStart_3661472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661476 : List Nat := [2, 3, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_3661476 : Nat := 118140960795 + 3661476 * 2 ^ 59
def prefixEnd_3661476 : Nat := 4983230072969 + 3 ^ 40 * 3661476 * 2
def baseEnd_3661476 : Nat := 1253398061934547794674123

theorem tailTrace_3661476 : CollatzResearch.WordTrace tailWord_3661476 prefixEnd_3661476 1253398061934547794674123 := by
  unfold tailWord_3661476
  simp only [CollatzResearch.WordTrace]
  refine ⟨66772500441552628580410141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89030000588736838107213521 66772500441552628580410141)
  ·
    refine ⟨25039687665582235717653803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66772500441552628580410141 25039687665582235717653803)
    ·
      refine ⟨37559531498373353576480705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25039687665582235717653803 37559531498373353576480705)
      ·
        refine ⟨28169648623780015182360529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37559531498373353576480705 28169648623780015182360529)
        ·
          refine ⟨21127236467835011386770397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28169648623780015182360529 21127236467835011386770397)
          ·
            refine ⟨7922713675438129270038899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21127236467835011386770397 7922713675438129270038899)
            ·
              refine ⟨11884070513157193905058349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7922713675438129270038899 11884070513157193905058349)
              ·
                refine ⟨4456526442433947714396881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11884070513157193905058349 4456526442433947714396881)
                ·
                  refine ⟨3342394831825460785797661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456526442433947714396881 3342394831825460785797661)
                  ·
                    refine ⟨1253398061934547794674123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342394831825460785797661 1253398061934547794674123)
                    ·
                      rfl

theorem cell22_3661476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_3661476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661476 prefixEnd_3661476 := by exact prefixLift 3661476
  have htrace : WordTrace (prefixWord ++ tailWord_3661476) baseStart_3661476 baseEnd_3661476 := by
    simpa [prefixWord, tailWord_3661476, baseEnd_3661476] using wordTrace_append hprefix tailTrace_3661476
  have hstable : (prefixWord ++ tailWord_3661476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661476).length < 2 ^ (prefixWord ++ tailWord_3661476).sum := by decide
  have hdescent : baseEnd_3661476 < baseStart_3661476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661506 : List Nat := [3, 5, 1, 2, 11]
def baseStart_3661506 : Nat := 118140960795 + 3661506 * 2 ^ 59
def prefixEnd_3661506 : Nat := 4983230072969 + 3 ^ 40 * 3661506 * 2
def baseEnd_3661506 : Nat := 5158058977562295129317

theorem tailTrace_3661506 : CollatzResearch.WordTrace tailWord_3661506 prefixEnd_3661506 5158058977562295129317 := by
  unfold tailWord_3661506
  simp only [CollatzResearch.WordTrace]
  refine ⟨33386523768249143071103093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89030730048664381522941581 33386523768249143071103093)
  ·
    refine ⟨3129986603273357162915915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33386523768249143071103093 3129986603273357162915915)
    ·
      refine ⟨4694979904910035744373873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3129986603273357162915915 4694979904910035744373873)
      ·
        refine ⟨3521234928682526808280405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4694979904910035744373873 3521234928682526808280405)
        ·
          refine ⟨5158058977562295129317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3521234928682526808280405 5158058977562295129317)
          ·
            rfl

theorem cell22_3661506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 11].length) (baseStart_3661506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661506 prefixEnd_3661506 := by exact prefixLift 3661506
  have htrace : WordTrace (prefixWord ++ tailWord_3661506) baseStart_3661506 baseEnd_3661506 := by
    simpa [prefixWord, tailWord_3661506, baseEnd_3661506] using wordTrace_append hprefix tailTrace_3661506
  have hstable : (prefixWord ++ tailWord_3661506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661506).length < 2 ^ (prefixWord ++ tailWord_3661506).sum := by decide
  have hdescent : baseEnd_3661506 < baseStart_3661506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661510 : List Nat := [6, 1, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3661510 : Nat := 118140960795 + 3661510 * 2 ^ 59
def prefixEnd_3661510 : Nat := 4983230072969 + 3 ^ 40 * 3661510 * 2
def baseEnd_3661510 : Nat := 1253409700829383039324019

theorem tailTrace_3661510 : CollatzResearch.WordTrace tailWord_3661510 prefixEnd_3661510 1253409700829383039324019 := by
  unfold tailWord_3661510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173320030155690030236187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89030827309988053978371989 4173320030155690030236187)
  ·
    refine ⟨6259980045233535045354281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4173320030155690030236187 6259980045233535045354281)
    ·
      refine ⟨4694985033925151284015711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6259980045233535045354281 4694985033925151284015711)
      ·
        refine ⟨7042477550887726926023567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4694985033925151284015711 7042477550887726926023567)
        ·
          refine ⟨10563716326331590389035351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042477550887726926023567 10563716326331590389035351)
          ·
            refine ⟨15845574489497385583553027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10563716326331590389035351 15845574489497385583553027)
            ·
              refine ⟨23768361734246078375329541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15845574489497385583553027 23768361734246078375329541)
              ·
                refine ⟨4456567825171139695374289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23768361734246078375329541 4456567825171139695374289)
                ·
                  refine ⟨3342425868878354771530717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456567825171139695374289 3342425868878354771530717)
                  ·
                    refine ⟨1253409700829383039324019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342425868878354771530717 1253409700829383039324019)
                    ·
                      rfl

theorem cell22_3661510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3661510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661510 prefixEnd_3661510 := by exact prefixLift 3661510
  have htrace : WordTrace (prefixWord ++ tailWord_3661510) baseStart_3661510 baseEnd_3661510 := by
    simpa [prefixWord, tailWord_3661510, baseEnd_3661510] using wordTrace_append hprefix tailTrace_3661510
  have hstable : (prefixWord ++ tailWord_3661510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661510).length < 2 ^ (prefixWord ++ tailWord_3661510).sum := by decide
  have hdescent : baseEnd_3661510 < baseStart_3661510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661562 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_3661562 : Nat := 118140960795 + 3661562 * 2 ^ 59
def prefixEnd_3661562 : Nat := 4983230072969 + 3 ^ 40 * 3661562 * 2
def baseEnd_3661562 : Nat := 417809167164024079007953

theorem tailTrace_3661562 : CollatzResearch.WordTrace tailWord_3661562 prefixEnd_3661562 417809167164024079007953 := by
  unfold tailWord_3661562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387034390198423462112735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89032091707195795898967293 33387034390198423462112735)
  ·
    refine ⟨50080551585297635193169103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33387034390198423462112735 50080551585297635193169103)
    ·
      refine ⟨75120827377946452789753655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50080551585297635193169103 75120827377946452789753655)
      ·
        refine ⟨112681241066919679184630483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75120827377946452789753655 112681241066919679184630483)
        ·
          refine ⟨169021861600379518776945725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112681241066919679184630483 169021861600379518776945725)
          ·
            refine ⟨63383198100142319541354647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169021861600379518776945725 63383198100142319541354647)
            ·
              refine ⟨95074797150213479312031971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63383198100142319541354647 95074797150213479312031971)
              ·
                refine ⟨142612195725320218968047957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95074797150213479312031971 142612195725320218968047957)
                ·
                  refine ⟨417809167164024079007953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142612195725320218968047957 417809167164024079007953)
                  ·
                    rfl

theorem cell22_3661562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_3661562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661562 prefixEnd_3661562 := by exact prefixLift 3661562
  have htrace : WordTrace (prefixWord ++ tailWord_3661562) baseStart_3661562 baseEnd_3661562 := by
    simpa [prefixWord, tailWord_3661562, baseEnd_3661562] using wordTrace_append hprefix tailTrace_3661562
  have hstable : (prefixWord ++ tailWord_3661562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661562).length < 2 ^ (prefixWord ++ tailWord_3661562).sum := by decide
  have hdescent : baseEnd_3661562 < baseStart_3661562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661624 : List Nat := [2, 1, 2, 1, 3, 5, 8]
def baseStart_3661624 : Nat := 118140960795 + 3661624 * 2 ^ 59
def prefixEnd_3661624 : Nat := 4983230072969 + 3 ^ 40 * 3661624 * 2
def baseEnd_3661624 : Nat := 46424026865152768221247

theorem tailTrace_3661624 : CollatzResearch.WordTrace tailWord_3661624 prefixEnd_3661624 46424026865152768221247 := by
  unfold tailWord_3661624
  simp only [CollatzResearch.WordTrace]
  refine ⟨66775199443284539218603963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89033599257712718958138617 66775199443284539218603963)
  ·
    refine ⟨100162799164926808827905945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66775199443284539218603963 100162799164926808827905945)
    ·
      refine ⟨75122099373695106620929459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100162799164926808827905945 75122099373695106620929459)
      ·
        refine ⟨112683149060542659931394189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75122099373695106620929459 112683149060542659931394189)
        ·
          refine ⟨42256180897703497474272821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112683149060542659931394189 42256180897703497474272821)
          ·
            refine ⟨3961516959159702888213077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42256180897703497474272821 3961516959159702888213077)
            ·
              refine ⟨46424026865152768221247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3961516959159702888213077 46424026865152768221247)
              ·
                rfl

theorem cell22_3661624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 8].length) (baseStart_3661624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661624 prefixEnd_3661624 := by exact prefixLift 3661624
  have htrace : WordTrace (prefixWord ++ tailWord_3661624) baseStart_3661624 baseEnd_3661624 := by
    simpa [prefixWord, tailWord_3661624, baseEnd_3661624] using wordTrace_append hprefix tailTrace_3661624
  have hstable : (prefixWord ++ tailWord_3661624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661624).length < 2 ^ (prefixWord ++ tailWord_3661624).sum := by decide
  have hdescent : baseEnd_3661624 < baseStart_3661624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661626 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_3661626 : Nat := 118140960795 + 3661626 * 2 ^ 59
def prefixEnd_3661626 : Nat := 4983230072969 + 3 ^ 40 * 3661626 * 2
def baseEnd_3661626 : Nat := 1253449409999997403423663

theorem tailTrace_3661626 : CollatzResearch.WordTrace tailWord_3661626 prefixEnd_3661626 1253449409999997403423663 := by
  unfold tailWord_3661626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33387617958140458194695183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89033647888374555185853821 33387617958140458194695183)
  ·
    refine ⟨50081426937210687292042775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33387617958140458194695183 50081426937210687292042775)
    ·
      refine ⟨75122140405816030938064163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50081426937210687292042775 75122140405816030938064163)
      ·
        refine ⟨112683210608724046407096245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75122140405816030938064163 112683210608724046407096245)
        ·
          refine ⟨10564050994567879350665273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112683210608724046407096245 10564050994567879350665273)
          ·
            refine ⟨7923038245925909512998955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10564050994567879350665273 7923038245925909512998955)
            ·
              refine ⟨11884557368888864269498433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923038245925909512998955 11884557368888864269498433)
              ·
                refine ⟨8913418026666648202123825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11884557368888864269498433 8913418026666648202123825)
                ·
                  refine ⟨6685063519999986151592869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8913418026666648202123825 6685063519999986151592869)
                  ·
                    refine ⟨1253449409999997403423663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685063519999986151592869 1253449409999997403423663)
                    ·
                      rfl

theorem cell22_3661626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_3661626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661626 prefixEnd_3661626 := by exact prefixLift 3661626
  have htrace : WordTrace (prefixWord ++ tailWord_3661626) baseStart_3661626 baseEnd_3661626 := by
    simpa [prefixWord, tailWord_3661626, baseEnd_3661626] using wordTrace_append hprefix tailTrace_3661626
  have hstable : (prefixWord ++ tailWord_3661626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661626).length < 2 ^ (prefixWord ++ tailWord_3661626).sum := by decide
  have hdescent : baseEnd_3661626 < baseStart_3661626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661630 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 4]
def baseStart_3661630 : Nat := 118140960795 + 3661630 * 2 ^ 59
def prefixEnd_3661630 : Nat := 4983230072969 + 3 ^ 40 * 3661630 * 2
def baseEnd_3661630 : Nat := 417816926427247575441217

theorem tailTrace_3661630 : CollatzResearch.WordTrace tailWord_3661630 prefixEnd_3661630 417816926427247575441217 := by
  unfold tailWord_3661630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16693827215568417682740793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89033745149698227641284229 16693827215568417682740793)
  ·
    refine ⟨12520370411676313262055595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16693827215568417682740793 12520370411676313262055595)
    ·
      refine ⟨18780555617514469893083393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12520370411676313262055595 18780555617514469893083393)
      ·
        refine ⟨14085416713135852419812545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18780555617514469893083393 14085416713135852419812545)
        ·
          refine ⟨10564062534851889314859409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14085416713135852419812545 10564062534851889314859409)
          ·
            refine ⟨7923046901138916986144557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10564062534851889314859409 7923046901138916986144557)
            ·
              refine ⟨2971142587927093869804209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7923046901138916986144557 2971142587927093869804209)
              ·
                refine ⟨2228356940945320402353157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971142587927093869804209 2228356940945320402353157)
                ·
                  refine ⟨417816926427247575441217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228356940945320402353157 417816926427247575441217)
                  ·
                    rfl

theorem cell22_3661630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_3661630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661630 prefixEnd_3661630 := by exact prefixLift 3661630
  have htrace : WordTrace (prefixWord ++ tailWord_3661630) baseStart_3661630 baseEnd_3661630 := by
    simpa [prefixWord, tailWord_3661630, baseEnd_3661630] using wordTrace_append hprefix tailTrace_3661630
  have hstable : (prefixWord ++ tailWord_3661630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661630).length < 2 ^ (prefixWord ++ tailWord_3661630).sum := by decide
  have hdescent : baseEnd_3661630 < baseStart_3661630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661645 : List Nat := [1, 6, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3661645 : Nat := 118140960795 + 3661645 * 2 ^ 59
def prefixEnd_3661645 : Nat := 4983230072969 + 3 ^ 40 * 3661645 * 2
def baseEnd_3661645 : Nat := 1253455914088287687198605

theorem tailTrace_3661645 : CollatzResearch.WordTrace tailWord_3661645 prefixEnd_3661645 1253455914088287687198605 := by
  unfold tailWord_3661645
  simp only [CollatzResearch.WordTrace]
  refine ⟨133551164819492999023722389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89034109879661999349148259 133551164819492999023722389)
  ·
    refine ⟨6260210850913734329236987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133551164819492999023722389 6260210850913734329236987)
    ·
      refine ⟨9390316276370601493855481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6260210850913734329236987 9390316276370601493855481)
      ·
        refine ⟨7042737207277951120391611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9390316276370601493855481 7042737207277951120391611)
        ·
          refine ⟨10564105810916926680587417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7042737207277951120391611 10564105810916926680587417)
          ·
            refine ⟨7923079358187695010440563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10564105810916926680587417 7923079358187695010440563)
            ·
              refine ⟨11884619037281542515660845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7923079358187695010440563 11884619037281542515660845)
              ·
                refine ⟨4456732138980578443372817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11884619037281542515660845 4456732138980578443372817)
                ·
                  refine ⟨3342549104235433832529613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456732138980578443372817 3342549104235433832529613)
                  ·
                    refine ⟨1253455914088287687198605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342549104235433832529613 1253455914088287687198605)
                    ·
                      rfl

theorem cell22_3661645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3661645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661645 prefixEnd_3661645 := by exact prefixLift 3661645
  have htrace : WordTrace (prefixWord ++ tailWord_3661645) baseStart_3661645 baseEnd_3661645 := by
    simpa [prefixWord, tailWord_3661645, baseEnd_3661645] using wordTrace_append hprefix tailTrace_3661645
  have hstable : (prefixWord ++ tailWord_3661645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661645).length < 2 ^ (prefixWord ++ tailWord_3661645).sum := by decide
  have hdescent : baseEnd_3661645 < baseStart_3661645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661690 : List Nat := [3, 1, 1, 1, 1, 1, 8, 2, 1, 3]
def baseStart_3661690 : Nat := 118140960795 + 3661690 * 2 ^ 59
def prefixEnd_3661690 : Nat := 4983230072969 + 3 ^ 40 * 3661690 * 2
def baseEnd_3661690 : Nat := 1253471318507922569823467

theorem tailTrace_3661690 : CollatzResearch.WordTrace tailWord_3661690 prefixEnd_3661690 1253471318507922569823467 := by
  unfold tailWord_3661690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33388201526082492927277631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89035204069553314472740349 33388201526082492927277631)
  ·
    refine ⟨50082302289123739390916447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33388201526082492927277631 50082302289123739390916447)
    ·
      refine ⟨75123453433685609086374671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50082302289123739390916447 75123453433685609086374671)
      ·
        refine ⟨112685180150528413629562007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75123453433685609086374671 112685180150528413629562007)
        ·
          refine ⟨169027770225792620444343011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112685180150528413629562007 169027770225792620444343011)
          ·
            refine ⟨253541655338688930666514517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169027770225792620444343011 253541655338688930666514517)
            ·
              refine ⟨2971191273500260906248217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 253541655338688930666514517 2971191273500260906248217)
              ·
                refine ⟨2228393455125195679686163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971191273500260906248217 2228393455125195679686163)
                ·
                  refine ⟨3342590182687793519529245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228393455125195679686163 3342590182687793519529245)
                  ·
                    refine ⟨1253471318507922569823467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342590182687793519529245 1253471318507922569823467)
                    ·
                      rfl

theorem cell22_3661690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_3661690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661690 prefixEnd_3661690 := by exact prefixLift 3661690
  have htrace : WordTrace (prefixWord ++ tailWord_3661690) baseStart_3661690 baseEnd_3661690 := by
    simpa [prefixWord, tailWord_3661690, baseEnd_3661690] using wordTrace_append hprefix tailTrace_3661690
  have hstable : (prefixWord ++ tailWord_3661690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661690).length < 2 ^ (prefixWord ++ tailWord_3661690).sum := by decide
  have hdescent : baseEnd_3661690 < baseStart_3661690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661759 : List Nat := [1, 1, 2, 2, 2, 1, 4, 9]
def baseStart_3661759 : Nat := 118140960795 + 3661759 * 2 ^ 59
def prefixEnd_3661759 : Nat := 4983230072969 + 3 ^ 40 * 3661759 * 2
def baseEnd_3661759 : Nat := 139277215402003265538695

theorem tailTrace_3661759 : CollatzResearch.WordTrace tailWord_3661759 prefixEnd_3661759 139277215402003265538695 := by
  unfold tailWord_3661759
  simp only [CollatzResearch.WordTrace]
  refine ⟨133555322741079996493372331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89036881827386664328914887 133555322741079996493372331)
  ·
    refine ⟨200332984111619994740058497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133555322741079996493372331 200332984111619994740058497)
    ·
      refine ⟨150249738083714996055043873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200332984111619994740058497 150249738083714996055043873)
      ·
        refine ⟨112687303562786247041282905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150249738083714996055043873 112687303562786247041282905)
        ·
          refine ⟨84515477672089685280962179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112687303562786247041282905 84515477672089685280962179)
          ·
            refine ⟨126773216508134527921443269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84515477672089685280962179 126773216508134527921443269)
            ·
              refine ⟨23769978095275223985270613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126773216508134527921443269 23769978095275223985270613)
              ·
                refine ⟨139277215402003265538695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23769978095275223985270613 139277215402003265538695)
                ·
                  rfl

theorem cell22_3661759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 9].length) (baseStart_3661759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661759 prefixEnd_3661759 := by exact prefixLift 3661759
  have htrace : WordTrace (prefixWord ++ tailWord_3661759) baseStart_3661759 baseEnd_3661759 := by
    simpa [prefixWord, tailWord_3661759, baseEnd_3661759] using wordTrace_append hprefix tailTrace_3661759
  have hstable : (prefixWord ++ tailWord_3661759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661759).length < 2 ^ (prefixWord ++ tailWord_3661759).sum := by decide
  have hdescent : baseEnd_3661759 < baseStart_3661759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661776 : List Nat := [2, 1, 1, 1, 1, 2, 8, 6]
def baseStart_3661776 : Nat := 118140960795 + 3661776 * 2 ^ 59
def prefixEnd_3661776 : Nat := 4983230072969 + 3 ^ 40 * 3661776 * 2
def baseEnd_3661776 : Nat := 139277862007271890241467

theorem tailTrace_3661776 : CollatzResearch.WordTrace tailWord_3661776 prefixEnd_3661776 139277862007271890241467 := by
  unfold tailWord_3661776
  simp only [CollatzResearch.WordTrace]
  refine ⟨66777971391009204198370591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89037295188012272264494121 66777971391009204198370591)
  ·
    refine ⟨100166957086513806297555887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66777971391009204198370591 100166957086513806297555887)
    ·
      refine ⟨150250435629770709446333831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100166957086513806297555887 150250435629770709446333831)
      ·
        refine ⟨225375653444656064169500747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150250435629770709446333831 225375653444656064169500747)
        ·
          refine ⟨338063480166984096254251121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225375653444656064169500747 338063480166984096254251121)
          ·
            refine ⟨253547610125238072190688341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338063480166984096254251121 253547610125238072190688341)
            ·
              refine ⟨2971261056155133658484629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 253547610125238072190688341 2971261056155133658484629)
              ·
                refine ⟨139277862007271890241467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2971261056155133658484629 139277862007271890241467)
                ·
                  rfl

theorem cell22_3661776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_3661776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661776 prefixEnd_3661776 := by exact prefixLift 3661776
  have htrace : WordTrace (prefixWord ++ tailWord_3661776) baseStart_3661776 baseEnd_3661776 := by
    simpa [prefixWord, tailWord_3661776, baseEnd_3661776] using wordTrace_append hprefix tailTrace_3661776
  have hstable : (prefixWord ++ tailWord_3661776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661776).length < 2 ^ (prefixWord ++ tailWord_3661776).sum := by decide
  have hdescent : baseEnd_3661776 < baseStart_3661776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661808 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_3661808 : Nat := 118140960795 + 3661808 * 2 ^ 59
def prefixEnd_3661808 : Nat := 4983230072969 + 3 ^ 40 * 3661808 * 2
def baseEnd_3661808 : Nat := 1253511712319409595373105

theorem tailTrace_3661808 : CollatzResearch.WordTrace tailWord_3661808 prefixEnd_3661808 1253511712319409595373105 := by
  unfold tailWord_3661808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66778554958951238930953039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89038073278601651907937385 66778554958951238930953039)
  ·
    refine ⟨100167832438426858396429559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66778554958951238930953039 100167832438426858396429559)
    ·
      refine ⟨150251748657640287594644339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100167832438426858396429559 150251748657640287594644339)
      ·
        refine ⟨225377622986460431391966509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150251748657640287594644339 225377622986460431391966509)
        ·
          refine ⟨84516608619922661771987441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225377622986460431391966509 84516608619922661771987441)
          ·
            refine ⟨63387456464941996328990581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84516608619922661771987441 63387456464941996328990581)
            ·
              refine ⟨5942574043588312155842867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63387456464941996328990581 5942574043588312155842867)
              ·
                refine ⟨8913861065382468233764301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942574043588312155842867 8913861065382468233764301)
                ·
                  refine ⟨3342697899518425587661613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8913861065382468233764301 3342697899518425587661613)
                  ·
                    refine ⟨1253511712319409595373105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342697899518425587661613 1253511712319409595373105)
                    ·
                      rfl

theorem cell22_3661808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_3661808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661808 prefixEnd_3661808 := by exact prefixLift 3661808
  have htrace : WordTrace (prefixWord ++ tailWord_3661808) baseStart_3661808 baseEnd_3661808 := by
    simpa [prefixWord, tailWord_3661808, baseEnd_3661808] using wordTrace_append hprefix tailTrace_3661808
  have hstable : (prefixWord ++ tailWord_3661808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661808).length < 2 ^ (prefixWord ++ tailWord_3661808).sum := by decide
  have hdescent : baseEnd_3661808 < baseStart_3661808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661814 : List Nat := [5, 1, 1, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3661814 : Nat := 118140960795 + 3661814 * 2 ^ 59
def prefixEnd_3661814 : Nat := 4983230072969 + 3 ^ 40 * 3661814 * 2
def baseEnd_3661814 : Nat := 1253513766242027579723087

theorem tailTrace_3661814 : CollatzResearch.WordTrace tailWord_3661814 prefixEnd_3661814 1253513766242027579723087 := by
  unfold tailWord_3661814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8347333047242546305414031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89038219170587160591082997 8347333047242546305414031)
  ·
    refine ⟨12520999570863819458121047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8347333047242546305414031 12520999570863819458121047)
    ·
      refine ⟨18781499356295729187181571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12520999570863819458121047 18781499356295729187181571)
      ·
        refine ⟨28172249034443593780772357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18781499356295729187181571 28172249034443593780772357)
        ·
          refine ⟨5282296693958173833894817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28172249034443593780772357 5282296693958173833894817)
          ·
            refine ⟨3961722520468630375421113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282296693958173833894817 3961722520468630375421113)
            ·
              refine ⟨2971291890351472781565835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961722520468630375421113 2971291890351472781565835)
              ·
                refine ⟨4456937835527209172348753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971291890351472781565835 4456937835527209172348753)
                ·
                  refine ⟨3342703376645406879261565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4456937835527209172348753 3342703376645406879261565)
                  ·
                    refine ⟨1253513766242027579723087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342703376645406879261565 1253513766242027579723087)
                    ·
                      rfl

theorem cell22_3661814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3661814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661814 prefixEnd_3661814 := by exact prefixLift 3661814
  have htrace : WordTrace (prefixWord ++ tailWord_3661814) baseStart_3661814 baseEnd_3661814 := by
    simpa [prefixWord, tailWord_3661814, baseEnd_3661814] using wordTrace_append hprefix tailTrace_3661814
  have hstable : (prefixWord ++ tailWord_3661814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661814).length < 2 ^ (prefixWord ++ tailWord_3661814).sum := by decide
  have hdescent : baseEnd_3661814 < baseStart_3661814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661898 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_3661898 : Nat := 118140960795 + 3661898 * 2 ^ 59
def prefixEnd_3661898 : Nat := 4983230072969 + 3 ^ 40 * 3661898 * 2
def baseEnd_3661898 : Nat := 1253542521158679360622829

theorem tailTrace_3661898 : CollatzResearch.WordTrace tailWord_3661898 prefixEnd_3661898 1253542521158679360622829 := by
  unfold tailWord_3661898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33390098121894105808170587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89040261658384282155121565 33390098121894105808170587)
  ·
    refine ⟨50085147182841158712255881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33390098121894105808170587 50085147182841158712255881)
    ·
      refine ⟨37563860387130869034191911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50085147182841158712255881 37563860387130869034191911)
      ·
        refine ⟨56345790580696303551287867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37563860387130869034191911 56345790580696303551287867)
        ·
          refine ⟨84518685871044455326931801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56345790580696303551287867 84518685871044455326931801)
          ·
            refine ⟨63389014403283341495198851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84518685871044455326931801 63389014403283341495198851)
            ·
              refine ⟨95083521604925012242798277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63389014403283341495198851 95083521604925012242798277)
              ·
                refine ⟨17828160300923439795524677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95083521604925012242798277 17828160300923439795524677)
                ·
                  refine ⟨3342780056423144961660877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17828160300923439795524677 3342780056423144961660877)
                  ·
                    refine ⟨1253542521158679360622829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342780056423144961660877 1253542521158679360622829)
                    ·
                      rfl

theorem cell22_3661898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_3661898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661898 prefixEnd_3661898 := by exact prefixLift 3661898
  have htrace : WordTrace (prefixWord ++ tailWord_3661898) baseStart_3661898 baseEnd_3661898 := by
    simpa [prefixWord, tailWord_3661898, baseEnd_3661898] using wordTrace_append hprefix tailTrace_3661898
  have hstable : (prefixWord ++ tailWord_3661898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661898).length < 2 ^ (prefixWord ++ tailWord_3661898).sum := by decide
  have hdescent : baseEnd_3661898 < baseStart_3661898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661902 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 1, 4]
def baseStart_3661902 : Nat := 118140960795 + 3661902 * 2 ^ 59
def prefixEnd_3661902 : Nat := 4983230072969 + 3 ^ 40 * 3661902 * 2
def baseEnd_3661902 : Nat := 1253543890440424683522817

theorem tailTrace_3661902 : CollatzResearch.WordTrace tailWord_3661902 prefixEnd_3661902 1253543890440424683522817 := by
  unfold tailWord_3661902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16695067297445241489478495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89040358919707954610551973 16695067297445241489478495)
  ·
    refine ⟨25042600946167862234217743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16695067297445241489478495 25042600946167862234217743)
    ·
      refine ⟨37563901419251793351326615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25042600946167862234217743 37563901419251793351326615)
      ·
        refine ⟨56345852128877690026989923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37563901419251793351326615 56345852128877690026989923)
        ·
          refine ⟨84518778193316535040484885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56345852128877690026989923 84518778193316535040484885)
          ·
            refine ⟨3961817727811712580022729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84518778193316535040484885 3961817727811712580022729)
            ·
              refine ⟨2971363295858784435017047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961817727811712580022729 2971363295858784435017047)
              ·
                refine ⟨4457044943788176652525571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971363295858784435017047 4457044943788176652525571)
                ·
                  refine ⟨6685567415682264978788357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457044943788176652525571 6685567415682264978788357)
                  ·
                    refine ⟨1253543890440424683522817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685567415682264978788357 1253543890440424683522817)
                    ·
                      rfl

theorem cell22_3661902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_3661902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661902 prefixEnd_3661902 := by exact prefixLift 3661902
  have htrace : WordTrace (prefixWord ++ tailWord_3661902) baseStart_3661902 baseEnd_3661902 := by
    simpa [prefixWord, tailWord_3661902, baseEnd_3661902] using wordTrace_append hprefix tailTrace_3661902
  have hstable : (prefixWord ++ tailWord_3661902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661902).length < 2 ^ (prefixWord ++ tailWord_3661902).sum := by decide
  have hdescent : baseEnd_3661902 < baseStart_3661902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661917 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3661917 : Nat := 118140960795 + 3661917 * 2 ^ 59
def prefixEnd_3661917 : Nat := 4983230072969 + 3 ^ 40 * 3661917 * 2
def baseEnd_3661917 : Nat := 417849675082323214799257

theorem tailTrace_3661917 : CollatzResearch.WordTrace tailWord_3661917 prefixEnd_3661917 417849675082323214799257 := by
  unfold tailWord_3661917
  simp only [CollatzResearch.WordTrace]
  refine ⟨133561085474507589477624005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89040723649671726318416003 133561085474507589477624005)
  ·
    refine ⟨25042703526470173027054501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133561085474507589477624005 25042703526470173027054501)
    ·
      refine ⟨4695506911213157442572719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25042703526470173027054501 4695506911213157442572719)
      ·
        refine ⟨7043260366819736163859079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4695506911213157442572719 7043260366819736163859079)
        ·
          refine ⟨10564890550229604245788619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7043260366819736163859079 10564890550229604245788619)
          ·
            refine ⟨15847335825344406368682929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10564890550229604245788619 15847335825344406368682929)
            ·
              refine ⟨11885501869008304776512197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15847335825344406368682929 11885501869008304776512197)
              ·
                refine ⟨2228531600439057145596037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11885501869008304776512197 2228531600439057145596037)
                ·
                  refine ⟨417849675082323214799257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228531600439057145596037 417849675082323214799257)
                  ·
                    rfl

theorem cell22_3661917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3661917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661917 prefixEnd_3661917 := by exact prefixLift 3661917
  have htrace : WordTrace (prefixWord ++ tailWord_3661917) baseStart_3661917 baseEnd_3661917 := by
    simpa [prefixWord, tailWord_3661917, baseEnd_3661917] using wordTrace_append hprefix tailTrace_3661917
  have hstable : (prefixWord ++ tailWord_3661917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661917).length < 2 ^ (prefixWord ++ tailWord_3661917).sum := by decide
  have hdescent : baseEnd_3661917 < baseStart_3661917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661932 : List Nat := [2, 2, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_3661932 : Nat := 118140960795 + 3661932 * 2 ^ 59
def prefixEnd_3661932 : Nat := 4983230072969 + 3 ^ 40 * 3661932 * 2
def baseEnd_3661932 : Nat := 1253554160053514605272725

theorem tailTrace_3661932 : CollatzResearch.WordTrace tailWord_3661932 prefixEnd_3661932 1253554160053514605272725 := by
  unfold tailWord_3661932
  simp only [CollatzResearch.WordTrace]
  refine ⟨66780816284726623519710025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89041088379635498026280033 66780816284726623519710025)
  ·
    refine ⟨50085612213544967639782519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66780816284726623519710025 50085612213544967639782519)
    ·
      refine ⟨75128418320317451459673779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50085612213544967639782519 75128418320317451459673779)
      ·
        refine ⟨112692627480476177189510669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75128418320317451459673779 112692627480476177189510669)
        ·
          refine ⟨42259735305178566446066501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112692627480476177189510669 42259735305178566446066501)
          ·
            refine ⟨7923700369720981208637469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42259735305178566446066501 7923700369720981208637469)
            ·
              refine ⟨2971387638645367953239051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7923700369720981208637469 2971387638645367953239051)
              ·
                refine ⟨4457081457968051929858577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971387638645367953239051 4457081457968051929858577)
                ·
                  refine ⟨3342811093476038947393933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457081457968051929858577 3342811093476038947393933)
                  ·
                    refine ⟨1253554160053514605272725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342811093476038947393933 1253554160053514605272725)
                    ·
                      rfl

theorem cell22_3661932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_3661932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661932 prefixEnd_3661932 := by exact prefixLift 3661932
  have htrace : WordTrace (prefixWord ++ tailWord_3661932) baseStart_3661932 baseEnd_3661932 := by
    simpa [prefixWord, tailWord_3661932, baseEnd_3661932] using wordTrace_append hprefix tailTrace_3661932
  have hstable : (prefixWord ++ tailWord_3661932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661932).length < 2 ^ (prefixWord ++ tailWord_3661932).sum := by decide
  have hdescent : baseEnd_3661932 < baseStart_3661932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661945 : List Nat := [1, 2, 1, 3, 4, 3, 2, 6]
def baseStart_3661945 : Nat := 118140960795 + 3661945 * 2 ^ 59
def prefixEnd_3661945 : Nat := 4983230072969 + 3 ^ 40 * 3661945 * 2
def baseEnd_3661945 : Nat := 139284290024354100521965

theorem tailTrace_3661945 : CollatzResearch.WordTrace tailWord_3661945 prefixEnd_3661945 139284290024354100521965 := by
  unfold tailWord_3661945
  simp only [CollatzResearch.WordTrace]
  refine ⟨133562106718406150259643289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89041404478937433506428859 133562106718406150259643289)
  ·
    refine ⟨100171580038804612694732467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133562106718406150259643289 100171580038804612694732467)
    ·
      refine ⟨150257370058206919042098701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100171580038804612694732467 150257370058206919042098701)
      ·
        refine ⟨56346513771827594640787013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150257370058206919042098701 56346513771827594640787013)
        ·
          refine ⟨10564971332217673995147565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56346513771827594640787013 10564971332217673995147565)
          ·
            refine ⟨3961864249581627748180337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10564971332217673995147565 3961864249581627748180337)
            ·
              refine ⟨2971398187186220811135253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961864249581627748180337 2971398187186220811135253)
              ·
                refine ⟨139284290024354100521965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2971398187186220811135253 139284290024354100521965)
                ·
                  rfl

theorem cell22_3661945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 6].length) (baseStart_3661945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661945 prefixEnd_3661945 := by exact prefixLift 3661945
  have htrace : WordTrace (prefixWord ++ tailWord_3661945) baseStart_3661945 baseEnd_3661945 := by
    simpa [prefixWord, tailWord_3661945, baseEnd_3661945] using wordTrace_append hprefix tailTrace_3661945
  have hstable : (prefixWord ++ tailWord_3661945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661945).length < 2 ^ (prefixWord ++ tailWord_3661945).sum := by decide
  have hdescent : baseEnd_3661945 < baseStart_3661945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3661973 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 5]
def baseStart_3661973 : Nat := 118140960795 + 3661973 * 2 ^ 59
def prefixEnd_3661973 : Nat := 4983230072969 + 3 ^ 40 * 3661973 * 2
def baseEnd_3661973 : Nat := 417856065063801388332533

theorem tailTrace_3661973 : CollatzResearch.WordTrace tailWord_3661973 prefixEnd_3661973 417856065063801388332533 := by
  unfold tailWord_3661973
  simp only [CollatzResearch.WordTrace]
  refine ⟨133563127962304711041662573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89042085308203140694441715 133563127962304711041662573)
  ·
    refine ⟨50086172985864266640623465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133563127962304711041662573 50086172985864266640623465)
    ·
      refine ⟨37564629739398199980467599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50086172985864266640623465 37564629739398199980467599)
      ·
        refine ⟨56346944609097299970701399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37564629739398199980467599 56346944609097299970701399)
        ·
          refine ⟨84520416913645949956052099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56346944609097299970701399 84520416913645949956052099)
          ·
            refine ⟨126780625370468924934078149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84520416913645949956052099 126780625370468924934078149)
            ·
              refine ⟨23771367256962923425139653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126780625370468924934078149 23771367256962923425139653)
              ·
                refine ⟨4457131360680548142213685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23771367256962923425139653 4457131360680548142213685)
                ·
                  refine ⟨417856065063801388332533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4457131360680548142213685 417856065063801388332533)
                  ·
                    rfl

theorem cell22_3661973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_3661973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3661973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3661973 prefixEnd_3661973 := by exact prefixLift 3661973
  have htrace : WordTrace (prefixWord ++ tailWord_3661973) baseStart_3661973 baseEnd_3661973 := by
    simpa [prefixWord, tailWord_3661973, baseEnd_3661973] using wordTrace_append hprefix tailTrace_3661973
  have hstable : (prefixWord ++ tailWord_3661973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3661973).length < 2 ^ (prefixWord ++ tailWord_3661973).sum := by decide
  have hdescent : baseEnd_3661973 < baseStart_3661973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3661973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662028 : List Nat := [2, 2, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_3662028 : Nat := 118140960795 + 3662028 * 2 ^ 59
def prefixEnd_3662028 : Nat := 4983230072969 + 3 ^ 40 * 3662028 * 2
def baseEnd_3662028 : Nat := 1253587022815402354872431

theorem tailTrace_3662028 : CollatzResearch.WordTrace tailWord_3662028 prefixEnd_3662028 1253587022815402354872431 := by
  unfold tailWord_3662028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66782566988552727717457369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89043422651403636956609825 66782566988552727717457369)
  ·
    refine ⟨50086925241414545788093027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66782566988552727717457369 50086925241414545788093027)
    ·
      refine ⟨75130387862121818682139541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50086925241414545788093027 75130387862121818682139541)
      ·
        refine ⟨3521736931036960250725291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75130387862121818682139541 3521736931036960250725291)
        ·
          refine ⟨5282605396555440376087937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3521736931036960250725291 5282605396555440376087937)
          ·
            refine ⟨3961954047416580282065953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282605396555440376087937 3961954047416580282065953)
            ·
              refine ⟨2971465535562435211549465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3961954047416580282065953 2971465535562435211549465)
              ·
                refine ⟨2228599151671826408662099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971465535562435211549465 2228599151671826408662099)
                ·
                  refine ⟨3342898727507739612993149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2228599151671826408662099 3342898727507739612993149)
                  ·
                    refine ⟨1253587022815402354872431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342898727507739612993149 1253587022815402354872431)
                    ·
                      rfl

theorem cell22_3662028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_3662028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662028 prefixEnd_3662028 := by exact prefixLift 3662028
  have htrace : WordTrace (prefixWord ++ tailWord_3662028) baseStart_3662028 baseEnd_3662028 := by
    simpa [prefixWord, tailWord_3662028, baseEnd_3662028] using wordTrace_append hprefix tailTrace_3662028
  have hstable : (prefixWord ++ tailWord_3662028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662028).length < 2 ^ (prefixWord ++ tailWord_3662028).sum := by decide
  have hdescent : baseEnd_3662028 < baseStart_3662028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662048 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_3662048 : Nat := 118140960795 + 3662048 * 2 ^ 59
def prefixEnd_3662048 : Nat := 4983230072969 + 3 ^ 40 * 3662048 * 2
def baseEnd_3662048 : Nat := 1253593869224128969372369

theorem tailTrace_3662048 : CollatzResearch.WordTrace tailWord_3662048 prefixEnd_3662048 1253593869224128969372369 := by
  unfold tailWord_3662048
  simp only [CollatzResearch.WordTrace]
  refine ⟨66782931718516499425321399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89043908958021999233761865 66782931718516499425321399)
  ·
    refine ⟨100174397577774749137982099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66782931718516499425321399 100174397577774749137982099)
    ·
      refine ⟨150261596366662123706973149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100174397577774749137982099 150261596366662123706973149)
      ·
        refine ⟨56348098637498296390114931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150261596366662123706973149 56348098637498296390114931)
        ·
          refine ⟨84522147956247444585172397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56348098637498296390114931 84522147956247444585172397)
          ·
            refine ⟨31695805483592791719439649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84522147956247444585172397 31695805483592791719439649)
            ·
              refine ⟨23771854112694593789579737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31695805483592791719439649 23771854112694593789579737)
              ·
                refine ⟨17828890584520945342184803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23771854112694593789579737 17828890584520945342184803)
                ·
                  refine ⟨26743335876781418013277205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17828890584520945342184803 26743335876781418013277205)
                  ·
                    refine ⟨1253593869224128969372369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26743335876781418013277205 1253593869224128969372369)
                    ·
                      rfl

theorem cell22_3662048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_3662048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662048 prefixEnd_3662048 := by exact prefixLift 3662048
  have htrace : WordTrace (prefixWord ++ tailWord_3662048) baseStart_3662048 baseEnd_3662048 := by
    simpa [prefixWord, tailWord_3662048, baseEnd_3662048] using wordTrace_append hprefix tailTrace_3662048
  have hstable : (prefixWord ++ tailWord_3662048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662048).length < 2 ^ (prefixWord ++ tailWord_3662048).sum := by decide
  have hdescent : baseEnd_3662048 < baseStart_3662048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662065 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_3662065 : Nat := 118140960795 + 3662065 * 2 ^ 59
def prefixEnd_3662065 : Nat := 4983230072969 + 3 ^ 40 * 3662065 * 2
def baseEnd_3662065 : Nat := 1253599688671546591697317

theorem tailTrace_3662065 : CollatzResearch.WordTrace tailWord_3662065 prefixEnd_3662065 1253599688671546591697317 := by
  unfold tailWord_3662065
  simp only [CollatzResearch.WordTrace]
  refine ⟨133566483477971410754011649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89044322318647607169341099 133566483477971410754011649)
  ·
    refine ⟨100174862608478558065508737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133566483477971410754011649 100174862608478558065508737)
    ·
      refine ⟨75131146956358918549131553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100174862608478558065508737 75131146956358918549131553)
      ·
        refine ⟨56348360217269188911848665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75131146956358918549131553 56348360217269188911848665)
        ·
          refine ⟨42261270162951891683886499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56348360217269188911848665 42261270162951891683886499)
          ·
            refine ⟨63391905244427837525829749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42261270162951891683886499 63391905244427837525829749)
            ·
              refine ⟨5942991116665109768046539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63391905244427837525829749 5942991116665109768046539)
              ·
                refine ⟨8914486674997664652069809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5942991116665109768046539 8914486674997664652069809)
                ·
                  refine ⟨6685865006248248489052357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8914486674997664652069809 6685865006248248489052357)
                  ·
                    refine ⟨1253599688671546591697317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6685865006248248489052357 1253599688671546591697317)
                    ·
                      rfl

theorem cell22_3662065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_3662065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662065 prefixEnd_3662065 := by exact prefixLift 3662065
  have htrace : WordTrace (prefixWord ++ tailWord_3662065) baseStart_3662065 baseEnd_3662065 := by
    simpa [prefixWord, tailWord_3662065, baseEnd_3662065] using wordTrace_append hprefix tailTrace_3662065
  have hstable : (prefixWord ++ tailWord_3662065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662065).length < 2 ^ (prefixWord ++ tailWord_3662065).sum := by decide
  have hdescent : baseEnd_3662065 < baseStart_3662065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662112 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_3662112 : Nat := 118140960795 + 3662112 * 2 ^ 59
def prefixEnd_3662112 : Nat := 4983230072969 + 3 ^ 40 * 3662112 * 2
def baseEnd_3662112 : Nat := 1253615777732054135772173

theorem tailTrace_3662112 : CollatzResearch.WordTrace tailWord_3662112 prefixEnd_3662112 1253615777732054135772173 := by
  unfold tailWord_3662112
  simp only [CollatzResearch.WordTrace]
  refine ⟨66784098854400568890486295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89045465139200758520648393 66784098854400568890486295)
  ·
    refine ⟨100176148281600853335729443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66784098854400568890486295 100176148281600853335729443)
    ·
      refine ⟨150264222422401280003594165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100176148281600853335729443 150264222422401280003594165)
      ·
        refine ⟨14087270852100120000336953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150264222422401280003594165 14087270852100120000336953)
        ·
          refine ⟨10565453139075090000252715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14087270852100120000336953 10565453139075090000252715)
          ·
            refine ⟨15848179708612635000379073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10565453139075090000252715 15848179708612635000379073)
            ·
              refine ⟨11886134781459476250284305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15848179708612635000379073 11886134781459476250284305)
              ·
                refine ⟨8914601086094607187713229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11886134781459476250284305 8914601086094607187713229)
                ·
                  refine ⟨3342975407285477695392461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8914601086094607187713229 3342975407285477695392461)
                  ·
                    refine ⟨1253615777732054135772173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3342975407285477695392461 1253615777732054135772173)
                    ·
                      rfl

theorem cell22_3662112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_3662112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662112 prefixEnd_3662112 := by exact prefixLift 3662112
  have htrace : WordTrace (prefixWord ++ tailWord_3662112) baseStart_3662112 baseEnd_3662112 := by
    simpa [prefixWord, tailWord_3662112, baseEnd_3662112] using wordTrace_append hprefix tailTrace_3662112
  have hstable : (prefixWord ++ tailWord_3662112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662112).length < 2 ^ (prefixWord ++ tailWord_3662112).sum := by decide
  have hdescent : baseEnd_3662112 < baseStart_3662112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662185 : List Nat := [1, 2, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_3662185 : Nat := 118140960795 + 3662185 * 2 ^ 59
def prefixEnd_3662185 : Nat := 4983230072969 + 3 ^ 40 * 3662185 * 2
def baseEnd_3662185 : Nat := 1253640767123906278696949

theorem tailTrace_3662185 : CollatzResearch.WordTrace tailWord_3662185 prefixEnd_3662185 1253640767123906278696949 := by
  unfold tailWord_3662185
  simp only [CollatzResearch.WordTrace]
  refine ⟨133570860237536671248380009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89047240158357780832253339 133570860237536671248380009)
  ·
    refine ⟨100178145178152503436285007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133570860237536671248380009 100178145178152503436285007)
    ·
      refine ⟨150267217767228755154427511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100178145178152503436285007 150267217767228755154427511)
      ·
        refine ⟨225400826650843132731641267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150267217767228755154427511 225400826650843132731641267)
        ·
          refine ⟨338101239976264699097461901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225400826650843132731641267 338101239976264699097461901)
          ·
            refine ⟨126787964991099262161548213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338101239976264699097461901 126787964991099262161548213)
            ·
              refine ⟨11886371717915555827645145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126787964991099262161548213 11886371717915555827645145)
              ·
                refine ⟨8914778788436666870733859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11886371717915555827645145 8914778788436666870733859)
                ·
                  refine ⟨13372168182655000306100789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8914778788436666870733859 13372168182655000306100789)
                  ·
                    refine ⟨1253640767123906278696949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13372168182655000306100789 1253640767123906278696949)
                    ·
                      rfl

theorem cell22_3662185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_3662185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662185 prefixEnd_3662185 := by exact prefixLift 3662185
  have htrace : WordTrace (prefixWord ++ tailWord_3662185) baseStart_3662185 baseEnd_3662185 := by
    simpa [prefixWord, tailWord_3662185, baseEnd_3662185] using wordTrace_append hprefix tailTrace_3662185
  have hstable : (prefixWord ++ tailWord_3662185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662185).length < 2 ^ (prefixWord ++ tailWord_3662185).sum := by decide
  have hdescent : baseEnd_3662185 < baseStart_3662185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662189 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 1, 4]
def baseStart_3662189 : Nat := 118140960795 + 3662189 * 2 ^ 59
def prefixEnd_3662189 : Nat := 4983230072969 + 3 ^ 40 * 3662189 * 2
def baseEnd_3662189 : Nat := 1253642136405651601596937

theorem tailTrace_3662189 : CollatzResearch.WordTrace tailWord_3662189 prefixEnd_3662189 1253642136405651601596937 := by
  unfold tailWord_3662189
  simp only [CollatzResearch.WordTrace]
  refine ⟨133571006129522179931525621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89047337419681453287683747 133571006129522179931525621)
  ·
    refine ⟨12522281824642704368580527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133571006129522179931525621 12522281824642704368580527)
    ·
      refine ⟨18783422736964056552870791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12522281824642704368580527 18783422736964056552870791)
      ·
        refine ⟨28175134105446084829306187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18783422736964056552870791 28175134105446084829306187)
        ·
          refine ⟨42262701158169127243959281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28175134105446084829306187 42262701158169127243959281)
          ·
            refine ⟨31697025868626845432969461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42262701158169127243959281 31697025868626845432969461)
            ·
              refine ⟨2971596175183766759340887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31697025868626845432969461 2971596175183766759340887)
              ·
                refine ⟨4457394262775650139011331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2971596175183766759340887 4457394262775650139011331)
                ·
                  refine ⟨6686091394163475208516997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457394262775650139011331 6686091394163475208516997)
                  ·
                    refine ⟨1253642136405651601596937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686091394163475208516997 1253642136405651601596937)
                    ·
                      rfl

theorem cell22_3662189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_3662189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662189 prefixEnd_3662189 := by exact prefixLift 3662189
  have htrace : WordTrace (prefixWord ++ tailWord_3662189) baseStart_3662189 baseEnd_3662189 := by
    simpa [prefixWord, tailWord_3662189, baseEnd_3662189] using wordTrace_append hprefix tailTrace_3662189
  have hstable : (prefixWord ++ tailWord_3662189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662189).length < 2 ^ (prefixWord ++ tailWord_3662189).sum := by decide
  have hdescent : baseEnd_3662189 < baseStart_3662189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662234 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_3662234 : Nat := 118140960795 + 3662234 * 2 ^ 59
def prefixEnd_3662234 : Nat := 4983230072969 + 3 ^ 40 * 3662234 * 2
def baseEnd_3662234 : Nat := 1253657540825286484221799

theorem tailTrace_3662234 : CollatzResearch.WordTrace tailWord_3662234 prefixEnd_3662234 1253657540825286484221799 := by
  unfold tailWord_3662234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33393161853589788154228439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89048431609572768411275837 33393161853589788154228439)
  ·
    refine ⟨50089742780384682231342659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33393161853589788154228439 50089742780384682231342659)
    ·
      refine ⟨75134614170577023347013989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50089742780384682231342659 75134614170577023347013989)
      ·
        refine ⟨14087740156983191877565123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75134614170577023347013989 14087740156983191877565123)
        ·
          refine ⟨21131610235474787816347685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14087740156983191877565123 21131610235474787816347685)
          ·
            refine ⟨3962176919151522715565191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21131610235474787816347685 3962176919151522715565191)
            ·
              refine ⟨5943265378727284073347787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962176919151522715565191 5943265378727284073347787)
              ·
                refine ⟨8914898068090926110021681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943265378727284073347787 8914898068090926110021681)
                ·
                  refine ⟨6686173551068194582516261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8914898068090926110021681 6686173551068194582516261)
                  ·
                    refine ⟨1253657540825286484221799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686173551068194582516261 1253657540825286484221799)
                    ·
                      rfl

theorem cell22_3662234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_3662234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662234 prefixEnd_3662234 := by exact prefixLift 3662234
  have htrace : WordTrace (prefixWord ++ tailWord_3662234) baseStart_3662234 baseEnd_3662234 := by
    simpa [prefixWord, tailWord_3662234, baseEnd_3662234] using wordTrace_append hprefix tailTrace_3662234
  have hstable : (prefixWord ++ tailWord_3662234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662234).length < 2 ^ (prefixWord ++ tailWord_3662234).sum := by decide
  have hdescent : baseEnd_3662234 < baseStart_3662234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662253 : List Nat := [1, 5, 2, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3662253 : Nat := 118140960795 + 3662253 * 2 ^ 59
def prefixEnd_3662253 : Nat := 4983230072969 + 3 ^ 40 * 3662253 * 2
def baseEnd_3662253 : Nat := 1253664044913576767996741

theorem tailTrace_3662253 : CollatzResearch.WordTrace tailWord_3662253 prefixEnd_3662253 1253664044913576767996741 := by
  unfold tailWord_3662253
  simp only [CollatzResearch.WordTrace]
  refine ⟨133573340401290318861855413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89048893600860212574570275 133573340401290318861855413)
  ·
    refine ⟨12522500662620967393298945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133573340401290318861855413 12522500662620967393298945)
    ·
      refine ⟨9391875496965725544974209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12522500662620967393298945 9391875496965725544974209)
      ·
        refine ⟨7043906622724294158730657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9391875496965725544974209 7043906622724294158730657)
        ·
          refine ⟨5282929967043220619047993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7043906622724294158730657 5282929967043220619047993)
          ·
            refine ⟨3962197475282415464285995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5282929967043220619047993 3962197475282415464285995)
            ·
              refine ⟨5943296212923623196428993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962197475282415464285995 5943296212923623196428993)
              ·
                refine ⟨4457472159692717397321745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943296212923623196428993 4457472159692717397321745)
                ·
                  refine ⟨3343104119769538047991309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457472159692717397321745 3343104119769538047991309)
                  ·
                    refine ⟨1253664044913576767996741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343104119769538047991309 1253664044913576767996741)
                    ·
                      rfl

theorem cell22_3662253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3662253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662253 prefixEnd_3662253 := by exact prefixLift 3662253
  have htrace : WordTrace (prefixWord ++ tailWord_3662253) baseStart_3662253 baseEnd_3662253 := by
    simpa [prefixWord, tailWord_3662253, baseEnd_3662253] using wordTrace_append hprefix tailTrace_3662253
  have hstable : (prefixWord ++ tailWord_3662253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662253).length < 2 ^ (prefixWord ++ tailWord_3662253).sum := by decide
  have hdescent : baseEnd_3662253 < baseStart_3662253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662371 : List Nat := [1, 1, 1, 4, 4, 2, 2, 2, 2, 3]
def baseStart_3662371 : Nat := 118140960795 + 3662371 * 2 ^ 59
def prefixEnd_3662371 : Nat := 4983230072969 + 3 ^ 40 * 3662371 * 2
def baseEnd_3662371 : Nat := 1253704438725063793546379

theorem tailTrace_3662371 : CollatzResearch.WordTrace tailWord_3662371 prefixEnd_3662371 1253704438725063793546379 := by
  unfold tailWord_3662371
  simp only [CollatzResearch.WordTrace]
  refine ⟨133577644214862825014650967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89051762809908550009767311 133577644214862825014650967)
  ·
    refine ⟨200366466322294237521976451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133577644214862825014650967 200366466322294237521976451)
    ·
      refine ⟨300549699483441356282964677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200366466322294237521976451 300549699483441356282964677)
      ·
        refine ⟨56353068653145254303055877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300549699483441356282964677 56353068653145254303055877)
        ·
          refine ⟨10566200372464735181822977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56353068653145254303055877 10566200372464735181822977)
          ·
            refine ⟨7924650279348551386367233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10566200372464735181822977 7924650279348551386367233)
            ·
              refine ⟨5943487709511413539775425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924650279348551386367233 5943487709511413539775425)
              ·
                refine ⟨4457615782133560154831569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943487709511413539775425 4457615782133560154831569)
                ·
                  refine ⟨3343211836600170116123677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4457615782133560154831569 3343211836600170116123677)
                  ·
                    refine ⟨1253704438725063793546379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343211836600170116123677 1253704438725063793546379)
                    ·
                      rfl

theorem cell22_3662371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 2, 2, 3].length) (baseStart_3662371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662371 prefixEnd_3662371 := by exact prefixLift 3662371
  have htrace : WordTrace (prefixWord ++ tailWord_3662371) baseStart_3662371 baseEnd_3662371 := by
    simpa [prefixWord, tailWord_3662371, baseEnd_3662371] using wordTrace_append hprefix tailTrace_3662371
  have hstable : (prefixWord ++ tailWord_3662371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662371).length < 2 ^ (prefixWord ++ tailWord_3662371).sum := by decide
  have hdescent : baseEnd_3662371 < baseStart_3662371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662388 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3662388 : Nat := 118140960795 + 3662388 * 2 ^ 59
def prefixEnd_3662388 : Nat := 4983230072969 + 3 ^ 40 * 3662388 * 2
def baseEnd_3662388 : Nat := 1253710258172481415871327

theorem tailTrace_3662388 : CollatzResearch.WordTrace tailWord_3662388 prefixEnd_3662388 1253710258172481415871327 := by
  unfold tailWord_3662388
  simp only [CollatzResearch.WordTrace]
  refine ⟨66789132127900618459009909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89052176170534157945346545 66789132127900618459009909)
  ·
    refine ⟨6261481136990682980532179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66789132127900618459009909 6261481136990682980532179)
    ·
      refine ⟨9392221705486024470798269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6261481136990682980532179 9392221705486024470798269)
      ·
        refine ⟨3522083139557259176549351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9392221705486024470798269 3522083139557259176549351)
        ·
          refine ⟨5283124709335888764824027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522083139557259176549351 5283124709335888764824027)
          ·
            refine ⟨7924687064003833147236041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283124709335888764824027 7924687064003833147236041)
            ·
              refine ⟨5943515298002874860427031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7924687064003833147236041 5943515298002874860427031)
              ·
                refine ⟨8915272947004312290640547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5943515298002874860427031 8915272947004312290640547)
                ·
                  refine ⟨13372909420506468435960821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8915272947004312290640547 13372909420506468435960821)
                  ·
                    refine ⟨1253710258172481415871327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13372909420506468435960821 1253710258172481415871327)
                    ·
                      rfl

theorem cell22_3662388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3662388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662388 prefixEnd_3662388 := by exact prefixLift 3662388
  have htrace : WordTrace (prefixWord ++ tailWord_3662388) baseStart_3662388 baseEnd_3662388 := by
    simpa [prefixWord, tailWord_3662388, baseEnd_3662388] using wordTrace_append hprefix tailTrace_3662388
  have hstable : (prefixWord ++ tailWord_3662388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662388).length < 2 ^ (prefixWord ++ tailWord_3662388).sum := by decide
  have hdescent : baseEnd_3662388 < baseStart_3662388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662399 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 3, 3]
def baseStart_3662399 : Nat := 118140960795 + 3662399 * 2 ^ 59
def prefixEnd_3662399 : Nat := 4983230072969 + 3 ^ 40 * 3662399 * 2
def baseEnd_3662399 : Nat := 1253714023697281053846293

theorem tailTrace_3662399 : CollatzResearch.WordTrace tailWord_3662399 prefixEnd_3662399 1253714023697281053846293 := by
  unfold tailWord_3662399
  simp only [CollatzResearch.WordTrace]
  refine ⟨133578665458761385796670251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89052443639174257197780167 133578665458761385796670251)
  ·
    refine ⟨200367998188142078695005377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133578665458761385796670251 200367998188142078695005377)
    ·
      refine ⟨150275998641106559021254033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200367998188142078695005377 150275998641106559021254033)
      ·
        refine ⟨112706998980829919265940525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150275998641106559021254033 112706998980829919265940525)
        ·
          refine ⟨42265124617811219724727697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112706998980829919265940525 42265124617811219724727697)
          ·
            refine ⟨31698843463358414793545773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42265124617811219724727697 31698843463358414793545773)
            ·
              refine ⟨11887066298759405547579665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31698843463358414793545773 11887066298759405547579665)
              ·
                refine ⟨8915299724069554160684749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887066298759405547579665 8915299724069554160684749)
                ·
                  refine ⟨3343237396526082810256781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8915299724069554160684749 3343237396526082810256781)
                  ·
                    refine ⟨1253714023697281053846293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343237396526082810256781 1253714023697281053846293)
                    ·
                      rfl

theorem cell22_3662399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 3, 3].length) (baseStart_3662399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662399 prefixEnd_3662399 := by exact prefixLift 3662399
  have htrace : WordTrace (prefixWord ++ tailWord_3662399) baseStart_3662399 baseEnd_3662399 := by
    simpa [prefixWord, tailWord_3662399, baseEnd_3662399] using wordTrace_append hprefix tailTrace_3662399
  have hstable : (prefixWord ++ tailWord_3662399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662399).length < 2 ^ (prefixWord ++ tailWord_3662399).sum := by decide
  have hdescent : baseEnd_3662399 < baseStart_3662399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662412 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_3662412 : Nat := 118140960795 + 3662412 * 2 ^ 59
def prefixEnd_3662412 : Nat := 4983230072969 + 3 ^ 40 * 3662412 * 2
def baseEnd_3662412 : Nat := 417906157954317784423751

theorem tailTrace_3662412 : CollatzResearch.WordTrace tailWord_3662412 prefixEnd_3662412 417906157954317784423751 := by
  unfold tailWord_3662412
  simp only [CollatzResearch.WordTrace]
  refine ⟨66789569803857144508446745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89052759738476192677928993 66789569803857144508446745)
  ·
    refine ⟨50092177352892858381335059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66789569803857144508446745 50092177352892858381335059)
    ·
      refine ⟨75138266029339287572002589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50092177352892858381335059 75138266029339287572002589)
      ·
        refine ⟨28176849761002232839500971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75138266029339287572002589 28176849761002232839500971)
        ·
          refine ⟨42265274641503349259251457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28176849761002232839500971 42265274641503349259251457)
          ·
            refine ⟨31698955981127511944438593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42265274641503349259251457 31698955981127511944438593)
            ·
              refine ⟨23774216985845633958328945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31698955981127511944438593 23774216985845633958328945)
              ·
                refine ⟨17830662739384225468746709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23774216985845633958328945 17830662739384225468746709)
                ·
                  refine ⟨417906157954317784423751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17830662739384225468746709 417906157954317784423751)
                  ·
                    rfl

theorem cell22_3662412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_3662412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662412 prefixEnd_3662412 := by exact prefixLift 3662412
  have htrace : WordTrace (prefixWord ++ tailWord_3662412) baseStart_3662412 baseEnd_3662412 := by
    simpa [prefixWord, tailWord_3662412, baseEnd_3662412] using wordTrace_append hprefix tailTrace_3662412
  have hstable : (prefixWord ++ tailWord_3662412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662412).length < 2 ^ (prefixWord ++ tailWord_3662412).sum := by decide
  have hdescent : baseEnd_3662412 < baseStart_3662412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662489 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 4, 3]
def baseStart_3662489 : Nat := 118140960795 + 3662489 * 2 ^ 59
def prefixEnd_3662489 : Nat := 4983230072969 + 3 ^ 40 * 3662489 * 2
def baseEnd_3662489 : Nat := 1253744832536550819096017

theorem tailTrace_3662489 : CollatzResearch.WordTrace tailWord_3662489 prefixEnd_3662489 1253744832536550819096017 := by
  unfold tailWord_3662489
  simp only [CollatzResearch.WordTrace]
  refine ⟨133581948028435331167446521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89054632018956887444964347 133581948028435331167446521)
  ·
    refine ⟨100186461021326498375584891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133581948028435331167446521 100186461021326498375584891)
    ·
      refine ⟨150279691531989747563377337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100186461021326498375584891 150279691531989747563377337)
      ·
        refine ⟨112709768648992310672533003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150279691531989747563377337 112709768648992310672533003)
        ·
          refine ⟨169064652973488466008799505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112709768648992310672533003 169064652973488466008799505)
          ·
            refine ⟨126798489730116349506599629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169064652973488466008799505 126798489730116349506599629)
            ·
              refine ⟨47549433648793631064974861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126798489730116349506599629 47549433648793631064974861)
              ·
                refine ⟨17831037618297611649365573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47549433648793631064974861 17831037618297611649365573)
                ·
                  refine ⟨3343319553430802184256045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17831037618297611649365573 3343319553430802184256045)
                  ·
                    refine ⟨1253744832536550819096017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343319553430802184256045 1253744832536550819096017)
                    ·
                      rfl

theorem cell22_3662489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 3].length) (baseStart_3662489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662489 prefixEnd_3662489 := by exact prefixLift 3662489
  have htrace : WordTrace (prefixWord ++ tailWord_3662489) baseStart_3662489 baseEnd_3662489 := by
    simpa [prefixWord, tailWord_3662489, baseEnd_3662489] using wordTrace_append hprefix tailTrace_3662489
  have hstable : (prefixWord ++ tailWord_3662489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662489).length < 2 ^ (prefixWord ++ tailWord_3662489).sum := by decide
  have hdescent : baseEnd_3662489 < baseStart_3662489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662510 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3662510 : Nat := 118140960795 + 3662510 * 2 ^ 59
def prefixEnd_3662510 : Nat := 4983230072969 + 3 ^ 40 * 3662510 * 2
def baseEnd_3662510 : Nat := 1253752021265713764320953

theorem tailTrace_3662510 : CollatzResearch.WordTrace tailWord_3662510 prefixEnd_3662510 1253752021265713764320953 := by
  unfold tailWord_3662510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16697839245169906469245123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89055142640906167835973989 16697839245169906469245123)
  ·
    refine ⟨25046758867754859703867685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16697839245169906469245123 25046758867754859703867685)
    ·
      refine ⟨4696267287704036194475191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25046758867754859703867685 4696267287704036194475191)
      ·
        refine ⟨7044400931556054291712787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4696267287704036194475191 7044400931556054291712787)
        ·
          refine ⟨10566601397334081437569181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7044400931556054291712787 10566601397334081437569181)
          ·
            refine ⟨3962475524000280539088443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10566601397334081437569181 3962475524000280539088443)
            ·
              refine ⟨5943713286000420808632665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962475524000280539088443 5943713286000420808632665)
              ·
                refine ⟨4457784964500315606474499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5943713286000420808632665 4457784964500315606474499)
                ·
                  refine ⟨6686677446750473409711749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4457784964500315606474499 6686677446750473409711749)
                  ·
                    refine ⟨1253752021265713764320953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6686677446750473409711749 1253752021265713764320953)
                    ·
                      rfl

theorem cell22_3662510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3662510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662510 prefixEnd_3662510 := by exact prefixLift 3662510
  have htrace : WordTrace (prefixWord ++ tailWord_3662510) baseStart_3662510 baseEnd_3662510 := by
    simpa [prefixWord, tailWord_3662510, baseEnd_3662510] using wordTrace_append hprefix tailTrace_3662510
  have hstable : (prefixWord ++ tailWord_3662510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662510).length < 2 ^ (prefixWord ++ tailWord_3662510).sum := by decide
  have hdescent : baseEnd_3662510 < baseStart_3662510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662568 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3662568 : Nat := 118140960795 + 3662568 * 2 ^ 59
def prefixEnd_3662568 : Nat := 4983230072969 + 3 ^ 40 * 3662568 * 2
def baseEnd_3662568 : Nat := 1253771875851020946370775

theorem tailTrace_3662568 : CollatzResearch.WordTrace tailWord_3662568 prefixEnd_3662568 1253771875851020946370775 := by
  unfold tailWord_3662568
  simp only [CollatzResearch.WordTrace]
  refine ⟨66792414697574563829786179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89056552930099418439714905 66792414697574563829786179)
  ·
    refine ⟨100188622046361845744679269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66792414697574563829786179 100188622046361845744679269)
    ·
      refine ⟨18785366633692846077127363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100188622046361845744679269 18785366633692846077127363)
      ·
        refine ⟨28178049950539269115691045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18785366633692846077127363 28178049950539269115691045)
        ·
          refine ⟨5283384365726112959192071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28178049950539269115691045 5283384365726112959192071)
          ·
            refine ⟨7925076548589169438788107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283384365726112959192071 7925076548589169438788107)
            ·
              refine ⟨11887614822883754158182161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7925076548589169438788107 11887614822883754158182161)
              ·
                refine ⟨8915711117162815618636621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887614822883754158182161 8915711117162815618636621)
                ·
                  refine ⟨3343391668936055856988733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8915711117162815618636621 3343391668936055856988733)
                  ·
                    refine ⟨1253771875851020946370775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343391668936055856988733 1253771875851020946370775)
                    ·
                      rfl

theorem cell22_3662568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3662568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662568 prefixEnd_3662568 := by exact prefixLift 3662568
  have htrace : WordTrace (prefixWord ++ tailWord_3662568) baseStart_3662568 baseEnd_3662568 := by
    simpa [prefixWord, tailWord_3662568, baseEnd_3662568] using wordTrace_append hprefix tailTrace_3662568
  have hstable : (prefixWord ++ tailWord_3662568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662568).length < 2 ^ (prefixWord ++ tailWord_3662568).sum := by decide
  have hdescent : baseEnd_3662568 < baseStart_3662568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662609 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 6]
def baseStart_3662609 : Nat := 118140960795 + 3662609 * 2 ^ 59
def prefixEnd_3662609 : Nat := 4983230072969 + 3 ^ 40 * 3662609 * 2
def baseEnd_3662609 : Nat := 417928636996303502031883

theorem tailTrace_3662609 : CollatzResearch.WordTrace tailWord_3662609 prefixEnd_3662609 417928636996303502031883 := by
  unfold tailWord_3662609
  simp only [CollatzResearch.WordTrace]
  refine ⟨133586324788000591661814881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89057549858667061107876587 133586324788000591661814881)
  ·
    refine ⟨100189743591000443746361161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133586324788000591661814881 100189743591000443746361161)
    ·
      refine ⟨75142307693250332809770871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100189743591000443746361161 75142307693250332809770871)
      ·
        refine ⟨112713461539875499214656307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75142307693250332809770871 112713461539875499214656307)
        ·
          refine ⟨169070192309813248821984461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112713461539875499214656307 169070192309813248821984461)
          ·
            refine ⟨63401322116179968308244173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169070192309813248821984461 63401322116179968308244173)
            ·
              refine ⟨23775495793567488115591565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63401322116179968308244173 23775495793567488115591565)
              ·
                refine ⟨8915810922587808043346837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23775495793567488115591565 8915810922587808043346837)
                ·
                  refine ⟨417928636996303502031883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8915810922587808043346837 417928636996303502031883)
                  ·
                    rfl

theorem cell22_3662609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_3662609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662609 prefixEnd_3662609 := by exact prefixLift 3662609
  have htrace : WordTrace (prefixWord ++ tailWord_3662609) baseStart_3662609 baseEnd_3662609 := by
    simpa [prefixWord, tailWord_3662609, baseEnd_3662609] using wordTrace_append hprefix tailTrace_3662609
  have hstable : (prefixWord ++ tailWord_3662609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662609).length < 2 ^ (prefixWord ++ tailWord_3662609).sum := by decide
  have hdescent : baseEnd_3662609 < baseStart_3662609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662626 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_3662626 : Nat := 118140960795 + 3662626 * 2 ^ 59
def prefixEnd_3662626 : Nat := 4983230072969 + 3 ^ 40 * 3662626 * 2
def baseEnd_3662626 : Nat := 417930576812109376140199

theorem tailTrace_3662626 : CollatzResearch.WordTrace tailWord_3662626 prefixEnd_3662626 417930576812109376140199 := by
  unfold tailWord_3662626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33396736207234750891295933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89057963219292669043455821 33396736207234750891295933)
  ·
    refine ⟨12523776077713031584235975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33396736207234750891295933 12523776077713031584235975)
    ·
      refine ⟨18785664116569547376353963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12523776077713031584235975 18785664116569547376353963)
      ·
        refine ⟨28178496174854321064530945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18785664116569547376353963 28178496174854321064530945)
        ·
          refine ⟨21133872131140740798398209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28178496174854321064530945 21133872131140740798398209)
          ·
            refine ⟨15850404098355555598798657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21133872131140740798398209 15850404098355555598798657)
            ·
              refine ⟨11887803073766666699098993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15850404098355555598798657 11887803073766666699098993)
              ·
                refine ⟨8915852305325000024324245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11887803073766666699098993 8915852305325000024324245)
                ·
                  refine ⟨417930576812109376140199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8915852305325000024324245 417930576812109376140199)
                  ·
                    rfl

theorem cell22_3662626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_3662626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662626 prefixEnd_3662626 := by exact prefixLift 3662626
  have htrace : WordTrace (prefixWord ++ tailWord_3662626) baseStart_3662626 baseEnd_3662626 := by
    simpa [prefixWord, tailWord_3662626, baseEnd_3662626] using wordTrace_append hprefix tailTrace_3662626
  have hstable : (prefixWord ++ tailWord_3662626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662626).length < 2 ^ (prefixWord ++ tailWord_3662626).sum := by decide
  have hdescent : baseEnd_3662626 < baseStart_3662626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662641 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 6, 3]
def baseStart_3662641 : Nat := 118140960795 + 3662641 * 2 ^ 59
def prefixEnd_3662641 : Nat := 4983230072969 + 3 ^ 40 * 3662641 * 2
def baseEnd_3662641 : Nat := 1253796865242873089295551

theorem tailTrace_3662641 : CollatzResearch.WordTrace tailWord_3662641 prefixEnd_3662641 1253796865242873089295551 := by
  unfold tailWord_3662641
  simp only [CollatzResearch.WordTrace]
  refine ⟨133587491923884661126979777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89058327949256440751319851 133587491923884661126979777)
  ·
    refine ⟨100190618942913495845234833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133587491923884661126979777 100190618942913495845234833)
    ·
      refine ⟨75142964207185121883926125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100190618942913495845234833 75142964207185121883926125)
      ·
        refine ⟨28178611577694420706472297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75142964207185121883926125 28178611577694420706472297)
        ·
          refine ⟨21133958683270815529854223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28178611577694420706472297 21133958683270815529854223)
          ·
            refine ⟨31700938024906223294781335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21133958683270815529854223 31700938024906223294781335)
            ·
              refine ⟨47551407037359334942172003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31700938024906223294781335 47551407037359334942172003)
              ·
                refine ⟨71327110556039002413258005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47551407037359334942172003 71327110556039002413258005)
                ·
                  refine ⟨3343458307314328238121469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71327110556039002413258005 3343458307314328238121469)
                  ·
                    refine ⟨1253796865242873089295551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343458307314328238121469 1253796865242873089295551)
                    ·
                      rfl

theorem cell22_3662641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_3662641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662641 prefixEnd_3662641 := by exact prefixLift 3662641
  have htrace : WordTrace (prefixWord ++ tailWord_3662641) baseStart_3662641 baseEnd_3662641 := by
    simpa [prefixWord, tailWord_3662641, baseEnd_3662641] using wordTrace_append hprefix tailTrace_3662641
  have hstable : (prefixWord ++ tailWord_3662641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662641).length < 2 ^ (prefixWord ++ tailWord_3662641).sum := by decide
  have hdescent : baseEnd_3662641 < baseStart_3662641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662643 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 4]
def baseStart_3662643 : Nat := 118140960795 + 3662643 * 2 ^ 59
def prefixEnd_3662643 : Nat := 4983230072969 + 3 ^ 40 * 3662643 * 2
def baseEnd_3662643 : Nat := 417932516627915250248515

theorem tailTrace_3662643 : CollatzResearch.WordTrace tailWord_3662643 prefixEnd_3662643 417932516627915250248515 := by
  unfold tailWord_3662643
  simp only [CollatzResearch.WordTrace]
  refine ⟨133587564869877415468552583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89058376579918276979035055 133587564869877415468552583)
  ·
    refine ⟨200381347304816123202828875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133587564869877415468552583 200381347304816123202828875)
    ·
      refine ⟨300572020957224184804243313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200381347304816123202828875 300572020957224184804243313)
      ·
        refine ⟨225429015717918138603182485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300572020957224184804243313 225429015717918138603182485)
        ·
          refine ⟨10566985111777412747024179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225429015717918138603182485 10566985111777412747024179)
          ·
            refine ⟨15850477667666119120536269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10566985111777412747024179 15850477667666119120536269)
            ·
              refine ⟨5943929125374794670201101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15850477667666119120536269 5943929125374794670201101)
              ·
                refine ⟨2228973422015548001325413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5943929125374794670201101 2228973422015548001325413)
                ·
                  refine ⟨417932516627915250248515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2228973422015548001325413 417932516627915250248515)
                  ·
                    rfl

theorem cell22_3662643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 4].length) (baseStart_3662643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662643 prefixEnd_3662643 := by exact prefixLift 3662643
  have htrace : WordTrace (prefixWord ++ tailWord_3662643) baseStart_3662643 baseEnd_3662643 := by
    simpa [prefixWord, tailWord_3662643, baseEnd_3662643] using wordTrace_append hprefix tailTrace_3662643
  have hstable : (prefixWord ++ tailWord_3662643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662643).length < 2 ^ (prefixWord ++ tailWord_3662643).sum := by decide
  have hdescent : baseEnd_3662643 < baseStart_3662643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662690 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_3662690 : Nat := 118140960795 + 3662690 * 2 ^ 59
def prefixEnd_3662690 : Nat := 4983230072969 + 3 ^ 40 * 3662690 * 2
def baseEnd_3662690 : Nat := 1253813638944253294820401

theorem tailTrace_3662690 : CollatzResearch.WordTrace tailWord_3662690 prefixEnd_3662690 1253813638944253294820401 := by
  unfold tailWord_3662690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33397319775176785623878381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89059519400471428330342349 33397319775176785623878381)
  ·
    refine ⟨12523994915691294608954393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33397319775176785623878381 12523994915691294608954393)
    ·
      refine ⟨9392996186768470956715795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12523994915691294608954393 9392996186768470956715795)
      ·
        refine ⟨14089494280152706435073693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9392996186768470956715795 14089494280152706435073693)
        ·
          refine ⟨5283560355057264913152635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14089494280152706435073693 5283560355057264913152635)
          ·
            refine ⟨7925340532585897369728953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5283560355057264913152635 7925340532585897369728953)
            ·
              refine ⟨5944005399439423027296715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7925340532585897369728953 5944005399439423027296715)
              ·
                refine ⟨8916008099159134540945073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5944005399439423027296715 8916008099159134540945073)
                ·
                  refine ⟨6687006074369350905708805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8916008099159134540945073 6687006074369350905708805)
                  ·
                    refine ⟨1253813638944253294820401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687006074369350905708805 1253813638944253294820401)
                    ·
                      rfl

theorem cell22_3662690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_3662690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662690 prefixEnd_3662690 := by exact prefixLift 3662690
  have htrace : WordTrace (prefixWord ++ tailWord_3662690) baseStart_3662690 baseEnd_3662690 := by
    simpa [prefixWord, tailWord_3662690, baseEnd_3662690] using wordTrace_append hprefix tailTrace_3662690
  have hstable : (prefixWord ++ tailWord_3662690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662690).length < 2 ^ (prefixWord ++ tailWord_3662690).sum := by decide
  have hdescent : baseEnd_3662690 < baseStart_3662690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662699 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 9]
def baseStart_3662699 : Nat := 118140960795 + 3662699 * 2 ^ 59
def prefixEnd_3662699 : Nat := 4983230072969 + 3 ^ 40 * 3662699 * 2
def baseEnd_3662699 : Nat := 417938906609393423781791

theorem tailTrace_3662699 : CollatzResearch.WordTrace tailWord_3662699 prefixEnd_3662699 417938906609393423781791 := by
  unfold tailWord_3662699
  simp only [CollatzResearch.WordTrace]
  refine ⟨133589607357674537032591151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89059738238449691355060767 133589607357674537032591151)
  ·
    refine ⟨200384411036511805548886727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133589607357674537032591151 200384411036511805548886727)
    ·
      refine ⟨300576616554767708323330091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200384411036511805548886727 300576616554767708323330091)
      ·
        refine ⟨450864924832151562484995137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300576616554767708323330091 450864924832151562484995137)
        ·
          refine ⟨338148693624113671863746353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 450864924832151562484995137 338148693624113671863746353)
          ·
            refine ⟨253611520218085253897809765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338148693624113671863746353 253611520218085253897809765)
            ·
              refine ⟨47552160040890985105839331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253611520218085253897809765 47552160040890985105839331)
              ·
                refine ⟨71328240061336477658758997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47552160040890985105839331 71328240061336477658758997)
                ·
                  refine ⟨417938906609393423781791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71328240061336477658758997 417938906609393423781791)
                  ·
                    rfl

theorem cell22_3662699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_3662699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662699 prefixEnd_3662699 := by exact prefixLift 3662699
  have htrace : WordTrace (prefixWord ++ tailWord_3662699) baseStart_3662699 baseEnd_3662699 := by
    simpa [prefixWord, tailWord_3662699, baseEnd_3662699] using wordTrace_append hprefix tailTrace_3662699
  have hstable : (prefixWord ++ tailWord_3662699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662699).length < 2 ^ (prefixWord ++ tailWord_3662699).sum := by decide
  have hdescent : baseEnd_3662699 < baseStart_3662699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662722 : List Nat := [3, 4, 2, 2, 1, 2, 1, 7]
def baseStart_3662722 : Nat := 118140960795 + 3662722 * 2 ^ 59
def prefixEnd_3662722 : Nat := 4983230072969 + 3 ^ 40 * 3662722 * 2
def baseEnd_3662722 : Nat := 139313843688690653113367

theorem tailTrace_3662722 : CollatzResearch.WordTrace tailWord_3662722 prefixEnd_3662722 139313843688690653113367 := by
  unfold tailWord_3662722
  simp only [CollatzResearch.WordTrace]
  refine ⟨33397611559147802990169605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89060297491060807973785613 33397611559147802990169605)
  ·
    refine ⟨6262052167340213060656801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33397611559147802990169605 6262052167340213060656801)
    ·
      refine ⟨4696539125505159795492601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6262052167340213060656801 4696539125505159795492601)
      ·
        refine ⟨3522404344128869846619451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4696539125505159795492601 3522404344128869846619451)
        ·
          refine ⟨5283606516193304769929177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522404344128869846619451 5283606516193304769929177)
          ·
            refine ⟨3962704887144978577446883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5283606516193304769929177 3962704887144978577446883)
            ·
              refine ⟨5944057330717467866170325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3962704887144978577446883 5944057330717467866170325)
              ·
                refine ⟨139313843688690653113367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5944057330717467866170325 139313843688690653113367)
                ·
                  rfl

theorem cell22_3662722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_3662722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662722 prefixEnd_3662722 := by exact prefixLift 3662722
  have htrace : WordTrace (prefixWord ++ tailWord_3662722) baseStart_3662722 baseEnd_3662722 := by
    simpa [prefixWord, tailWord_3662722, baseEnd_3662722] using wordTrace_append hprefix tailTrace_3662722
  have hstable : (prefixWord ++ tailWord_3662722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662722).length < 2 ^ (prefixWord ++ tailWord_3662722).sum := by decide
  have hdescent : baseEnd_3662722 < baseStart_3662722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662778 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_3662778 : Nat := 118140960795 + 3662778 * 2 ^ 59
def prefixEnd_3662778 : Nat := 4983230072969 + 3 ^ 40 * 3662778 * 2
def baseEnd_3662778 : Nat := 417947921047550132873377

theorem tailTrace_3662778 : CollatzResearch.WordTrace tailWord_3662778 prefixEnd_3662778 417947921047550132873377 := by
  unfold tailWord_3662778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33398122181097083381179247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89061659149592222349811325 33398122181097083381179247)
  ·
    refine ⟨50097183271645625071768871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33398122181097083381179247 50097183271645625071768871)
    ·
      refine ⟨75145774907468437607653307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50097183271645625071768871 75145774907468437607653307)
      ·
        refine ⟨112718662361202656411479961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75145774907468437607653307 112718662361202656411479961)
        ·
          refine ⟨84538996770901992308609971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112718662361202656411479961 84538996770901992308609971)
          ·
            refine ⟨126808495156352988462914957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84538996770901992308609971 126808495156352988462914957)
            ·
              refine ⟨47553185683632370673593109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126808495156352988462914957 47553185683632370673593109)
              ·
                refine ⟨2229055578920267375324677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47553185683632370673593109 2229055578920267375324677)
                ·
                  refine ⟨417947921047550132873377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229055578920267375324677 417947921047550132873377)
                  ·
                    rfl

theorem cell22_3662778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_3662778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662778 prefixEnd_3662778 := by exact prefixLift 3662778
  have htrace : WordTrace (prefixWord ++ tailWord_3662778) baseStart_3662778 baseEnd_3662778 := by
    simpa [prefixWord, tailWord_3662778, baseEnd_3662778] using wordTrace_append hprefix tailTrace_3662778
  have hstable : (prefixWord ++ tailWord_3662778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662778).length < 2 ^ (prefixWord ++ tailWord_3662778).sum := by decide
  have hdescent : baseEnd_3662778 < baseStart_3662778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662791 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_3662791 : Nat := 118140960795 + 3662791 * 2 ^ 59
def prefixEnd_3662791 : Nat := 4983230072969 + 3 ^ 40 * 3662791 * 2
def baseEnd_3662791 : Nat := 1253848213308322698045091

theorem tailTrace_3662791 : CollatzResearch.WordTrace tailWord_3662791 prefixEnd_3662791 1253848213308322698045091 := by
  unfold tailWord_3662791
  simp only [CollatzResearch.WordTrace]
  refine ⟨133592962873341236744940227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89061975248894157829960151 133592962873341236744940227)
  ·
    refine ⟨200389444310011855117410341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133592962873341236744940227 200389444310011855117410341)
    ·
      refine ⟨37573020808127222834514439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200389444310011855117410341 37573020808127222834514439)
      ·
        refine ⟨56359531212190834251771659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37573020808127222834514439 56359531212190834251771659)
        ·
          refine ⟨84539296818286251377657489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56359531212190834251771659 84539296818286251377657489)
          ·
            refine ⟨63404472613714688533243117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84539296818286251377657489 63404472613714688533243117)
            ·
              refine ⟨23776677230143008199966169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63404472613714688533243117 23776677230143008199966169)
              ·
                refine ⟨17832507922607256149974627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23776677230143008199966169 17832507922607256149974627)
                ·
                  refine ⟨26748761883910884224961941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17832507922607256149974627 26748761883910884224961941)
                  ·
                    refine ⟨1253848213308322698045091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26748761883910884224961941 1253848213308322698045091)
                    ·
                      rfl

theorem cell22_3662791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_3662791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662791 prefixEnd_3662791 := by exact prefixLift 3662791
  have htrace : WordTrace (prefixWord ++ tailWord_3662791) baseStart_3662791 baseEnd_3662791 := by
    simpa [prefixWord, tailWord_3662791, baseEnd_3662791] using wordTrace_append hprefix tailTrace_3662791
  have hstable : (prefixWord ++ tailWord_3662791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662791).length < 2 ^ (prefixWord ++ tailWord_3662791).sum := by decide
  have hdescent : baseEnd_3662791 < baseStart_3662791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662823 : List Nat := [1, 1, 5, 2, 2, 3, 8]
def baseStart_3662823 : Nat := 118140960795 + 3662823 * 2 ^ 59
def prefixEnd_3662823 : Nat := 4983230072969 + 3 ^ 40 * 3662823 * 2
def baseEnd_3662823 : Nat := 46439228428232788194259

theorem tailTrace_3662823 : CollatzResearch.WordTrace tailWord_3662823 prefixEnd_3662823 46439228428232788194259 := by
  unfold tailWord_3662823
  simp only [CollatzResearch.WordTrace]
  refine ⟨133594130009225306210105123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89062753339483537473403415 133594130009225306210105123)
  ·
    refine ⟨200391195013837959315157685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133594130009225306210105123 200391195013837959315157685)
    ·
      refine ⟨18786674532547308685796033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200391195013837959315157685 18786674532547308685796033)
      ·
        refine ⟨14090005899410481514347025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18786674532547308685796033 14090005899410481514347025)
        ·
          refine ⟨10567504424557861135760269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14090005899410481514347025 10567504424557861135760269)
          ·
            refine ⟨3962814159209197925910101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10567504424557861135760269 3962814159209197925910101)
            ·
              refine ⟨46439228428232788194259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3962814159209197925910101 46439228428232788194259)
              ·
                rfl

theorem cell22_3662823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 8].length) (baseStart_3662823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662823 prefixEnd_3662823 := by exact prefixLift 3662823
  have htrace : WordTrace (prefixWord ++ tailWord_3662823) baseStart_3662823 baseEnd_3662823 := by
    simpa [prefixWord, tailWord_3662823, baseEnd_3662823] using wordTrace_append hprefix tailTrace_3662823
  have hstable : (prefixWord ++ tailWord_3662823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662823).length < 2 ^ (prefixWord ++ tailWord_3662823).sum := by decide
  have hdescent : baseEnd_3662823 < baseStart_3662823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662898 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_3662898 : Nat := 118140960795 + 3662898 * 2 ^ 59
def prefixEnd_3662898 : Nat := 4983230072969 + 3 ^ 40 * 3662898 * 2
def baseEnd_3662898 : Nat := 1253884841595010085619763

theorem tailTrace_3662898 : CollatzResearch.WordTrace tailWord_3662898 prefixEnd_3662898 1253884841595010085619763 := by
  unfold tailWord_3662898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33399216370988398504771337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89064576989302396012723565 33399216370988398504771337)
  ·
    refine ⟨25049412278241298878578503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33399216370988398504771337 25049412278241298878578503)
    ·
      refine ⟨37574118417361948317867755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25049412278241298878578503 37574118417361948317867755)
      ·
        refine ⟨56361177626042922476801633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37574118417361948317867755 56361177626042922476801633)
        ·
          refine ⟨42270883219532191857601225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56361177626042922476801633 42270883219532191857601225)
          ·
            refine ⟨31703162414649143893200919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42270883219532191857601225 31703162414649143893200919)
            ·
              refine ⟨47554743621973715839801379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31703162414649143893200919 47554743621973715839801379)
              ·
                refine ⟨71332115432960573759702069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47554743621973715839801379 71332115432960573759702069)
                ·
                  refine ⟨6687385821840053789972069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71332115432960573759702069 6687385821840053789972069)
                  ·
                    refine ⟨1253884841595010085619763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687385821840053789972069 1253884841595010085619763)
                    ·
                      rfl

theorem cell22_3662898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_3662898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662898 prefixEnd_3662898 := by exact prefixLift 3662898
  have htrace : WordTrace (prefixWord ++ tailWord_3662898) baseStart_3662898 baseEnd_3662898 := by
    simpa [prefixWord, tailWord_3662898, baseEnd_3662898] using wordTrace_append hprefix tailTrace_3662898
  have hstable : (prefixWord ++ tailWord_3662898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662898).length < 2 ^ (prefixWord ++ tailWord_3662898).sum := by decide
  have hdescent : baseEnd_3662898 < baseStart_3662898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662900 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3662900 : Nat := 118140960795 + 3662900 * 2 ^ 59
def prefixEnd_3662900 : Nat := 4983230072969 + 3 ^ 40 * 3662900 * 2
def baseEnd_3662900 : Nat := 1253885526235882747069757

theorem tailTrace_3662900 : CollatzResearch.WordTrace tailWord_3662900 prefixEnd_3662900 1253885526235882747069757 := by
  unfold tailWord_3662900
  simp only [CollatzResearch.WordTrace]
  refine ⟨66798469214973174180329077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89064625619964232240438769 66798469214973174180329077)
  ·
    refine ⟨6262356488903735079405851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66798469214973174180329077 6262356488903735079405851)
    ·
      refine ⟨9393534733355602619108777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6262356488903735079405851 9393534733355602619108777)
      ·
        refine ⟨7045151050016701964331583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9393534733355602619108777 7045151050016701964331583)
        ·
          refine ⟨10567726575025052946497375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7045151050016701964331583 10567726575025052946497375)
          ·
            refine ⟨15851589862537579419746063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10567726575025052946497375 15851589862537579419746063)
            ·
              refine ⟨23777384793806369129619095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15851589862537579419746063 23777384793806369129619095)
              ·
                refine ⟨35666077190709553694428643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23777384793806369129619095 35666077190709553694428643)
                ·
                  refine ⟨53499115786064330541642965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35666077190709553694428643 53499115786064330541642965)
                  ·
                    refine ⟨1253885526235882747069757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53499115786064330541642965 1253885526235882747069757)
                    ·
                      rfl

theorem cell22_3662900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3662900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662900 prefixEnd_3662900 := by exact prefixLift 3662900
  have htrace : WordTrace (prefixWord ++ tailWord_3662900) baseStart_3662900 baseEnd_3662900 := by
    simpa [prefixWord, tailWord_3662900, baseEnd_3662900] using wordTrace_append hprefix tailTrace_3662900
  have hstable : (prefixWord ++ tailWord_3662900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662900).length < 2 ^ (prefixWord ++ tailWord_3662900).sum := by decide
  have hdescent : baseEnd_3662900 < baseStart_3662900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662932 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_3662932 : Nat := 118140960795 + 3662932 * 2 ^ 59
def prefixEnd_3662932 : Nat := 4983230072969 + 3 ^ 40 * 3662932 * 2
def baseEnd_3662932 : Nat := 1253896480489845330269659

theorem tailTrace_3662932 : CollatzResearch.WordTrace tailWord_3662932 prefixEnd_3662932 1253896480489845330269659 := by
  unfold tailWord_3662932
  simp only [CollatzResearch.WordTrace]
  refine ⟨66799052782915208912911525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89065403710553611883882033 66799052782915208912911525)
  ·
    refine ⟨12524822396796601671170911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66799052782915208912911525 12524822396796601671170911)
    ·
      refine ⟨18787233595194902506756367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12524822396796601671170911 18787233595194902506756367)
      ·
        refine ⟨28180850392792353760134551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18787233595194902506756367 28180850392792353760134551)
        ·
          refine ⟨42271275589188530640201827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28180850392792353760134551 42271275589188530640201827)
          ·
            refine ⟨63406913383782795960302741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42271275589188530640201827 63406913383782795960302741)
            ·
              refine ⟨2972199064864818560639191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63406913383782795960302741 2972199064864818560639191)
              ·
                refine ⟨4458298597297227840958787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972199064864818560639191 4458298597297227840958787)
                ·
                  refine ⟨6687447895945841761438181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4458298597297227840958787 6687447895945841761438181)
                  ·
                    refine ⟨1253896480489845330269659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687447895945841761438181 1253896480489845330269659)
                    ·
                      rfl

theorem cell22_3662932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_3662932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662932 prefixEnd_3662932 := by exact prefixLift 3662932
  have htrace : WordTrace (prefixWord ++ tailWord_3662932) baseStart_3662932 baseEnd_3662932 := by
    simpa [prefixWord, tailWord_3662932, baseEnd_3662932] using wordTrace_append hprefix tailTrace_3662932
  have hstable : (prefixWord ++ tailWord_3662932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662932).length < 2 ^ (prefixWord ++ tailWord_3662932).sum := by decide
  have hdescent : baseEnd_3662932 < baseStart_3662932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662943 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_3662943 : Nat := 118140960795 + 3662943 * 2 ^ 59
def prefixEnd_3662943 : Nat := 4983230072969 + 3 ^ 40 * 3662943 * 2
def baseEnd_3662943 : Nat := 1253900246014644968244625

theorem tailTrace_3662943 : CollatzResearch.WordTrace tailWord_3662943 prefixEnd_3662943 1253900246014644968244625 := by
  unfold tailWord_3662943
  simp only [CollatzResearch.WordTrace]
  refine ⟨133598506768790566704473483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89065671179193711136315655 133598506768790566704473483)
  ·
    refine ⟨200397760153185850056710225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133598506768790566704473483 200397760153185850056710225)
    ·
      refine ⟨150298320114889387542532669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200397760153185850056710225 150298320114889387542532669)
      ·
        refine ⟨56361870043083520328449751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150298320114889387542532669 56361870043083520328449751)
        ·
          refine ⟨84542805064625280492674627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56361870043083520328449751 84542805064625280492674627)
          ·
            refine ⟨126814207596937920739011941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84542805064625280492674627 126814207596937920739011941)
            ·
              refine ⟨23777663924425860138564739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126814207596937920739011941 23777663924425860138564739)
              ·
                refine ⟨35666495886638790207847109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23777663924425860138564739 35666495886638790207847109)
                ·
                  refine ⟨6687467978744773163971333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35666495886638790207847109 6687467978744773163971333)
                  ·
                    refine ⟨1253900246014644968244625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6687467978744773163971333 1253900246014644968244625)
                    ·
                      rfl

theorem cell22_3662943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_3662943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662943 prefixEnd_3662943 := by exact prefixLift 3662943
  have htrace : WordTrace (prefixWord ++ tailWord_3662943) baseStart_3662943 baseEnd_3662943 := by
    simpa [prefixWord, tailWord_3662943, baseEnd_3662943] using wordTrace_append hprefix tailTrace_3662943
  have hstable : (prefixWord ++ tailWord_3662943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662943).length < 2 ^ (prefixWord ++ tailWord_3662943).sum := by decide
  have hdescent : baseEnd_3662943 < baseStart_3662943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3662973 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_3662973 : Nat := 118140960795 + 3662973 * 2 ^ 59
def prefixEnd_3662973 : Nat := 4983230072969 + 3 ^ 40 * 3662973 * 2
def baseEnd_3662973 : Nat := 1253910515627734889994533

theorem tailTrace_3662973 : CollatzResearch.WordTrace tailWord_3662973 prefixEnd_3662973 1253910515627734889994533 := by
  unfold tailWord_3662973
  simp only [CollatzResearch.WordTrace]
  refine ⟨133599600958681881828065573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89066400639121254552043715 133599600958681881828065573)
  ·
    refine ⟨25049925179752852842762295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133599600958681881828065573 25049925179752852842762295)
    ·
      refine ⟨37574887769629279264143443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25049925179752852842762295 37574887769629279264143443)
      ·
        refine ⟨56362331654443918896215165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37574887769629279264143443 56362331654443918896215165)
        ·
          refine ⟨21135874370416469586080687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56362331654443918896215165 21135874370416469586080687)
          ·
            refine ⟨31703811555624704379121031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21135874370416469586080687 31703811555624704379121031)
            ·
              refine ⟨47555717333437056568681547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31703811555624704379121031 47555717333437056568681547)
              ·
                refine ⟨71333576000155584853022321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47555717333437056568681547 71333576000155584853022321)
                ·
                  refine ⟨53500182000116688639766741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71333576000155584853022321 53500182000116688639766741)
                  ·
                    refine ⟨1253910515627734889994533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53500182000116688639766741 1253910515627734889994533)
                    ·
                      rfl

theorem cell22_3662973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_3662973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3662973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3662973 prefixEnd_3662973 := by exact prefixLift 3662973
  have htrace : WordTrace (prefixWord ++ tailWord_3662973) baseStart_3662973 baseEnd_3662973 := by
    simpa [prefixWord, tailWord_3662973, baseEnd_3662973] using wordTrace_append hprefix tailTrace_3662973
  have hstable : (prefixWord ++ tailWord_3662973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3662973).length < 2 ^ (prefixWord ++ tailWord_3662973).sum := by decide
  have hdescent : baseEnd_3662973 < baseStart_3662973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3662973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663144 : List Nat := [2, 1, 5, 1, 2, 3, 2, 6]
def baseStart_3663144 : Nat := 118140960795 + 3663144 * 2 ^ 59
def prefixEnd_3663144 : Nat := 4983230072969 + 3 ^ 40 * 3663144 * 2
def baseEnd_3663144 : Nat := 139329894713594160441001

theorem tailTrace_3663144 : CollatzResearch.WordTrace tailWord_3663144 prefixEnd_3663144 139329894713594160441001 := by
  unfold tailWord_3663144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66802918920531189016270243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89070558560708252021693657 66802918920531189016270243)
  ·
    refine ⟨100204378380796783524405365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66802918920531189016270243 100204378380796783524405365)
    ·
      refine ⟨9394160473199698455413003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100204378380796783524405365 9394160473199698455413003)
      ·
        refine ⟨14091240709799547683119505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9394160473199698455413003 14091240709799547683119505)
        ·
          refine ⟨10568430532349660762339629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14091240709799547683119505 10568430532349660762339629)
          ·
            refine ⟨3963161449631122785877361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10568430532349660762339629 3963161449631122785877361)
            ·
              refine ⟨2972371087223342089408021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3963161449631122785877361 2972371087223342089408021)
              ·
                refine ⟨139329894713594160441001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2972371087223342089408021 139329894713594160441001)
                ·
                  rfl

theorem cell22_3663144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_3663144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663144 prefixEnd_3663144 := by exact prefixLift 3663144
  have htrace : WordTrace (prefixWord ++ tailWord_3663144) baseStart_3663144 baseEnd_3663144 := by
    simpa [prefixWord, tailWord_3663144, baseEnd_3663144] using wordTrace_append hprefix tailTrace_3663144
  have hstable : (prefixWord ++ tailWord_3663144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663144).length < 2 ^ (prefixWord ++ tailWord_3663144).sum := by decide
  have hdescent : baseEnd_3663144 < baseStart_3663144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663155 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 7]
def baseStart_3663155 : Nat := 118140960795 + 3663155 * 2 ^ 59
def prefixEnd_3663155 : Nat := 4983230072969 + 3 ^ 40 * 3663155 * 2
def baseEnd_3663155 : Nat := 417990939315715693981325

theorem tailTrace_3663155 : CollatzResearch.WordTrace tailWord_3663155 prefixEnd_3663155 417990939315715693981325 := by
  unfold tailWord_3663155
  simp only [CollatzResearch.WordTrace]
  refine ⟨133606239044022526911190919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89070826029348351274127279 133606239044022526911190919)
  ·
    refine ⟨200409358566033790366786379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133606239044022526911190919 200409358566033790366786379)
    ·
      refine ⟨300614037849050685550179569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200409358566033790366786379 300614037849050685550179569)
      ·
        refine ⟨225460528386788014162634677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300614037849050685550179569 225460528386788014162634677)
        ·
          refine ⟨21136924536261376327747001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225460528386788014162634677 21136924536261376327747001)
          ·
            refine ⟨15852693402196032245810251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21136924536261376327747001 15852693402196032245810251)
            ·
              refine ⟨23779040103294048368715377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15852693402196032245810251 23779040103294048368715377)
              ·
                refine ⟨17834280077470536276536533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23779040103294048368715377 17834280077470536276536533)
                ·
                  refine ⟨417990939315715693981325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17834280077470536276536533 417990939315715693981325)
                  ·
                    rfl

theorem cell22_3663155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_3663155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663155 prefixEnd_3663155 := by exact prefixLift 3663155
  have htrace : WordTrace (prefixWord ++ tailWord_3663155) baseStart_3663155 baseEnd_3663155 := by
    simpa [prefixWord, tailWord_3663155, baseEnd_3663155] using wordTrace_append hprefix tailTrace_3663155
  have hstable : (prefixWord ++ tailWord_3663155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663155).length < 2 ^ (prefixWord ++ tailWord_3663155).sum := by decide
  have hdescent : baseEnd_3663155 < baseStart_3663155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663189 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 5]
def baseStart_3663189 : Nat := 118140960795 + 3663189 * 2 ^ 59
def prefixEnd_3663189 : Nat := 4983230072969 + 3 ^ 40 * 3663189 * 2
def baseEnd_3663189 : Nat := 417994818947327442197957

theorem tailTrace_3663189 : CollatzResearch.WordTrace tailWord_3663189 prefixEnd_3663189 417994818947327442197957 := by
  unfold tailWord_3663189
  simp only [CollatzResearch.WordTrace]
  refine ⟨133607479125899350717928621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89071652750599567145285747 133607479125899350717928621)
  ·
    refine ⟨50102804672212256519223233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133607479125899350717928621 50102804672212256519223233)
    ·
      refine ⟨37577103504159192389417425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50102804672212256519223233 37577103504159192389417425)
      ·
        refine ⟨28182827628119394292063069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37577103504159192389417425 28182827628119394292063069)
        ·
          refine ⟨10568560360544772859523651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28182827628119394292063069 10568560360544772859523651)
          ·
            refine ⟨15852840540817159289285477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10568560360544772859523651 15852840540817159289285477)
            ·
              refine ⟨2972407601403217366741027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15852840540817159289285477 2972407601403217366741027)
              ·
                refine ⟨4458611402104826050111541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2972407601403217366741027 4458611402104826050111541)
                ·
                  refine ⟨417994818947327442197957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458611402104826050111541 417994818947327442197957)
                  ·
                    rfl

theorem cell22_3663189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 5].length) (baseStart_3663189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663189 prefixEnd_3663189 := by exact prefixLift 3663189
  have htrace : WordTrace (prefixWord ++ tailWord_3663189) baseStart_3663189 baseEnd_3663189 := by
    simpa [prefixWord, tailWord_3663189, baseEnd_3663189] using wordTrace_append hprefix tailTrace_3663189
  have hstable : (prefixWord ++ tailWord_3663189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663189).length < 2 ^ (prefixWord ++ tailWord_3663189).sum := by decide
  have hdescent : baseEnd_3663189 < baseStart_3663189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663232 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_3663232 : Nat := 118140960795 + 3663232 * 2 ^ 59
def prefixEnd_3663232 : Nat := 4983230072969 + 3 ^ 40 * 3663232 * 2
def baseEnd_3663232 : Nat := 1253999176620744547768739

theorem tailTrace_3663232 : CollatzResearch.WordTrace tailWord_3663232 prefixEnd_3663232 1253999176620744547768739 := by
  unfold tailWord_3663232
  simp only [CollatzResearch.WordTrace]
  refine ⟨66804523732371784530871975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89072698309829046041162633 66804523732371784530871975)
  ·
    refine ⟨100206785598557676796307963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66804523732371784530871975 100206785598557676796307963)
    ·
      refine ⟨150310178397836515194461945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100206785598557676796307963 150310178397836515194461945)
      ·
        refine ⟨112732633798377386395846459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150310178397836515194461945 112732633798377386395846459)
        ·
          refine ⟨169098950697566079593769689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112732633798377386395846459 169098950697566079593769689)
          ·
            refine ⟨126824213023174559695327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169098950697566079593769689 126824213023174559695327267)
            ·
              refine ⟨190236319534761839542990901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126824213023174559695327267 190236319534761839542990901)
              ·
                refine ⟨17834654956383922457155397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190236319534761839542990901 17834654956383922457155397)
                ·
                  refine ⟨3343997804321985460716637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17834654956383922457155397 3343997804321985460716637)
                  ·
                    refine ⟨1253999176620744547768739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3343997804321985460716637 1253999176620744547768739)
                    ·
                      rfl

theorem cell22_3663232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_3663232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663232 prefixEnd_3663232 := by exact prefixLift 3663232
  have htrace : WordTrace (prefixWord ++ tailWord_3663232) baseStart_3663232 baseEnd_3663232 := by
    simpa [prefixWord, tailWord_3663232, baseEnd_3663232] using wordTrace_append hprefix tailTrace_3663232
  have hstable : (prefixWord ++ tailWord_3663232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663232).length < 2 ^ (prefixWord ++ tailWord_3663232).sum := by decide
  have hdescent : baseEnd_3663232 < baseStart_3663232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663307 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 5]
def baseStart_3663307 : Nat := 118140960795 + 3663307 * 2 ^ 59
def prefixEnd_3663307 : Nat := 4983230072969 + 3 ^ 40 * 3663307 * 2
def baseEnd_3663307 : Nat := 418008283551156450714503

theorem tailTrace_3663307 : CollatzResearch.WordTrace tailWord_3663307 prefixEnd_3663307 418008283551156450714503 := by
  unfold tailWord_3663307
  simp only [CollatzResearch.WordTrace]
  refine ⟨133611782939471856870724175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89074521959647904580482783 133611782939471856870724175)
  ·
    refine ⟨200417674409207785306086263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133611782939471856870724175 200417674409207785306086263)
    ·
      refine ⟨300626511613811677959129395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200417674409207785306086263 300626511613811677959129395)
      ·
        refine ⟨450939767420717516938694093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300626511613811677959129395 450939767420717516938694093)
        ·
          refine ⟨169102412782769068852010285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 450939767420717516938694093 169102412782769068852010285)
          ·
            refine ⟨63413404793538400819503857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169102412782769068852010285 63413404793538400819503857)
            ·
              refine ⟨47560053595153800614627893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63413404793538400819503857 47560053595153800614627893)
              ·
                refine ⟨4458755024545668807621365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47560053595153800614627893 4458755024545668807621365)
                ·
                  refine ⟨418008283551156450714503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458755024545668807621365 418008283551156450714503)
                  ·
                    rfl

theorem cell22_3663307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 5].length) (baseStart_3663307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663307 prefixEnd_3663307 := by exact prefixLift 3663307
  have htrace : WordTrace (prefixWord ++ tailWord_3663307) baseStart_3663307 baseEnd_3663307 := by
    simpa [prefixWord, tailWord_3663307, baseEnd_3663307] using wordTrace_append hprefix tailTrace_3663307
  have hstable : (prefixWord ++ tailWord_3663307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663307).length < 2 ^ (prefixWord ++ tailWord_3663307).sum := by decide
  have hdescent : baseEnd_3663307 < baseStart_3663307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663358 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3663358 : Nat := 118140960795 + 3663358 * 2 ^ 59
def prefixEnd_3663358 : Nat := 4983230072969 + 3 ^ 40 * 3663358 * 2
def baseEnd_3663358 : Nat := 418014102998574073039451

theorem tailTrace_3663358 : CollatzResearch.WordTrace tailWord_3663358 prefixEnd_3663358 418014102998574073039451 := by
  unfold tailWord_3663358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16701705382785886572603841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89075762041524728387220485 16701705382785886572603841)
  ·
    refine ⟨12526279037089414929452881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16701705382785886572603841 12526279037089414929452881)
    ·
      refine ⟨9394709277817061197089661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12526279037089414929452881 9394709277817061197089661)
      ·
        refine ⟨3523015979181397948908623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9394709277817061197089661 3523015979181397948908623)
        ·
          refine ⟨5284523968772096923362935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3523015979181397948908623 5284523968772096923362935)
          ·
            refine ⟨7926785953158145385044403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284523968772096923362935 7926785953158145385044403)
            ·
              refine ⟨11890178929737218077566605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7926785953158145385044403 11890178929737218077566605)
              ·
                refine ⟨4458817098651456779087477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11890178929737218077566605 4458817098651456779087477)
                ·
                  refine ⟨418014102998574073039451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4458817098651456779087477 418014102998574073039451)
                  ·
                    rfl

theorem cell22_3663358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3663358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663358 prefixEnd_3663358 := by exact prefixLift 3663358
  have htrace : WordTrace (prefixWord ++ tailWord_3663358) baseStart_3663358 baseEnd_3663358 := by
    simpa [prefixWord, tailWord_3663358, baseEnd_3663358] using wordTrace_append hprefix tailTrace_3663358
  have hstable : (prefixWord ++ tailWord_3663358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663358).length < 2 ^ (prefixWord ++ tailWord_3663358).sum := by decide
  have hdescent : baseEnd_3663358 < baseStart_3663358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663431 : List Nat := [1, 1, 4, 1, 5, 1, 3, 6]
def baseStart_3663431 : Nat := 118140960795 + 3663431 * 2 ^ 59
def prefixEnd_3663431 : Nat := 4983230072969 + 3 ^ 40 * 3663431 * 2
def baseEnd_3663431 : Nat := 139340810931952706893681

theorem tailTrace_3663431 : CollatzResearch.WordTrace tailWord_3663431 prefixEnd_3663431 139340810931952706893681 := by
  unfold tailWord_3663431
  simp only [CollatzResearch.WordTrace]
  refine ⟨133616305591022626048238147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89077537060681750698825431 133616305591022626048238147)
  ·
    refine ⟨200424458386533939072357221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133616305591022626048238147 200424458386533939072357221)
    ·
      refine ⟨37579585947475113576066979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200424458386533939072357221 37579585947475113576066979)
      ·
        refine ⟨56369378921212670364100469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37579585947475113576066979 56369378921212670364100469)
        ·
          refine ⟨5284629273863687846634419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56369378921212670364100469 5284629273863687846634419)
          ·
            refine ⟨7926943910795531769951629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5284629273863687846634419 7926943910795531769951629)
            ·
              refine ⟨2972603966548324413731861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7926943910795531769951629 2972603966548324413731861)
              ·
                refine ⟨139340810931952706893681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2972603966548324413731861 139340810931952706893681)
                ·
                  rfl

theorem cell22_3663431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 6].length) (baseStart_3663431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663431 prefixEnd_3663431 := by exact prefixLift 3663431
  have htrace : WordTrace (prefixWord ++ tailWord_3663431) baseStart_3663431 baseEnd_3663431 := by
    simpa [prefixWord, tailWord_3663431, baseEnd_3663431] using wordTrace_append hprefix tailTrace_3663431
  have hstable : (prefixWord ++ tailWord_3663431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663431).length < 2 ^ (prefixWord ++ tailWord_3663431).sum := by decide
  have hdescent : baseEnd_3663431 < baseStart_3663431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663459 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 7]
def baseStart_3663459 : Nat := 118140960795 + 3663459 * 2 ^ 59
def prefixEnd_3663459 : Nat := 4983230072969 + 3 ^ 40 * 3663459 * 2
def baseEnd_3663459 : Nat := 418025627786597207447681

theorem tailTrace_3663459 : CollatzResearch.WordTrace tailWord_3663459 prefixEnd_3663459 418025627786597207447681 := by
  unfold tailWord_3663459
  simp only [CollatzResearch.WordTrace]
  refine ⟨133617326834921186830257431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89078217889947457886838287 133617326834921186830257431)
  ·
    refine ⟨200425990252381780245386147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133617326834921186830257431 200425990252381780245386147)
    ·
      refine ⟨300638985378572670368079221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200425990252381780245386147 300638985378572670368079221)
      ·
        refine ⟨28184904879241187847007427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300638985378572670368079221 28184904879241187847007427)
        ·
          refine ⟨42277357318861781770511141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28184904879241187847007427 42277357318861781770511141)
          ·
            refine ⟨7927004497286584081970839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42277357318861781770511141 7927004497286584081970839)
            ·
              refine ⟨11890506745929876122956259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927004497286584081970839 11890506745929876122956259)
              ·
                refine ⟨17835760118894814184434389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11890506745929876122956259 17835760118894814184434389)
                ·
                  refine ⟨418025627786597207447681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17835760118894814184434389 418025627786597207447681)
                  ·
                    rfl

theorem cell22_3663459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_3663459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663459 prefixEnd_3663459 := by exact prefixLift 3663459
  have htrace : WordTrace (prefixWord ++ tailWord_3663459) baseStart_3663459 baseEnd_3663459 := by
    simpa [prefixWord, tailWord_3663459, baseEnd_3663459] using wordTrace_append hprefix tailTrace_3663459
  have hstable : (prefixWord ++ tailWord_3663459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663459).length < 2 ^ (prefixWord ++ tailWord_3663459).sum := by decide
  have hdescent : baseEnd_3663459 < baseStart_3663459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663463 : List Nat := [1, 1, 5, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3663463 : Nat := 118140960795 + 3663463 * 2 ^ 59
def prefixEnd_3663463 : Nat := 4983230072969 + 3 ^ 40 * 3663463 * 2
def baseEnd_3663463 : Nat := 1254078252641536945243031

theorem tailTrace_3663463 : CollatzResearch.WordTrace tailWord_3663463 prefixEnd_3663463 1254078252641536945243031 := by
  unfold tailWord_3663463
  simp only [CollatzResearch.WordTrace]
  refine ⟨133617472726906695513403043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89078315151271130342268695 133617472726906695513403043)
  ·
    refine ⟨200426209090360043270104565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133617472726906695513403043 200426209090360043270104565)
    ·
      refine ⟨18789957102221254056572303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200426209090360043270104565 18789957102221254056572303)
      ·
        refine ⟨28184935653331881084858455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18789957102221254056572303 28184935653331881084858455)
        ·
          refine ⟨42277403479997821627287683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28184935653331881084858455 42277403479997821627287683)
          ·
            refine ⟨63416105219996732440931525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42277403479997821627287683 63416105219996732440931525)
            ·
              refine ⟨11890519728749387332674661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63416105219996732440931525 11890519728749387332674661)
              ·
                refine ⟨2229472449140510124876499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11890519728749387332674661 2229472449140510124876499)
                ·
                  refine ⟨3344208673710765187314749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2229472449140510124876499 3344208673710765187314749)
                  ·
                    refine ⟨1254078252641536945243031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344208673710765187314749 1254078252641536945243031)
                    ·
                      rfl

theorem cell22_3663463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3663463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663463 prefixEnd_3663463 := by exact prefixLift 3663463
  have htrace : WordTrace (prefixWord ++ tailWord_3663463) baseStart_3663463 baseEnd_3663463 := by
    simpa [prefixWord, tailWord_3663463, baseEnd_3663463] using wordTrace_append hprefix tailTrace_3663463
  have hstable : (prefixWord ++ tailWord_3663463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663463).length < 2 ^ (prefixWord ++ tailWord_3663463).sum := by decide
  have hdescent : baseEnd_3663463 < baseStart_3663463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663521 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 6]
def baseStart_3663521 : Nat := 118140960795 + 3663521 * 2 ^ 59
def prefixEnd_3663521 : Nat := 4983230072969 + 3 ^ 40 * 3663521 * 2
def baseEnd_3663521 : Nat := 418032702408948042430951

theorem tailTrace_3663521 : CollatzResearch.WordTrace tailWord_3663521 prefixEnd_3663521 418032702408948042430951 := by
  unfold tailWord_3663521
  simp only [CollatzResearch.WordTrace]
  refine ⟨133619588160696571419014417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89079725440464380946009611 133619588160696571419014417)
  ·
    refine ⟨100214691120522428564260813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133619588160696571419014417 100214691120522428564260813)
    ·
      refine ⟨37580509170195910711597805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100214691120522428564260813 37580509170195910711597805)
      ·
        refine ⟨14092690938823466516849177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37580509170195910711597805 14092690938823466516849177)
        ·
          refine ⟨10569518204117599887636883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14092690938823466516849177 10569518204117599887636883)
          ·
            refine ⟨15854277306176399831455325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10569518204117599887636883 15854277306176399831455325)
            ·
              refine ⟨5945353989816149936795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15854277306176399831455325 5945353989816149936795747)
              ·
                refine ⟨8918030984724224905193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945353989816149936795747 8918030984724224905193621)
                ·
                  refine ⟨418032702408948042430951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8918030984724224905193621 418032702408948042430951)
                  ·
                    rfl

theorem cell22_3663521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_3663521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663521 prefixEnd_3663521 := by exact prefixLift 3663521
  have htrace : WordTrace (prefixWord ++ tailWord_3663521) baseStart_3663521 baseEnd_3663521 := by
    simpa [prefixWord, tailWord_3663521, baseEnd_3663521] using wordTrace_append hprefix tailTrace_3663521
  have hstable : (prefixWord ++ tailWord_3663521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663521).length < 2 ^ (prefixWord ++ tailWord_3663521).sum := by decide
  have hdescent : baseEnd_3663521 < baseStart_3663521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663549 : List Nat := [1, 4, 1, 2, 1, 2, 1, 10]
def baseStart_3663549 : Nat := 118140960795 + 3663549 * 2 ^ 59
def prefixEnd_3663549 : Nat := 4983230072969 + 3 ^ 40 * 3663549 * 2
def baseEnd_3663549 : Nat := 139345299133229043065863

theorem tailTrace_3663549 : CollatzResearch.WordTrace tailWord_3663549 prefixEnd_3663549 139345299133229043065863 := by
  unfold tailWord_3663549
  simp only [CollatzResearch.WordTrace]
  refine ⟨133620609404595132201033701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89080406269730088134022467 133620609404595132201033701)
  ·
    refine ⟨25053864263361587287693819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133620609404595132201033701 25053864263361587287693819)
    ·
      refine ⟨37580796395042380931540729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25053864263361587287693819 37580796395042380931540729)
      ·
        refine ⟨28185597296281785698655547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37580796395042380931540729 28185597296281785698655547)
        ·
          refine ⟨42278395944422678547983321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28185597296281785698655547 42278395944422678547983321)
          ·
            refine ⟨31708796958317008910987491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42278395944422678547983321 31708796958317008910987491)
            ·
              refine ⟨47563195437475513366481237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31708796958317008910987491 47563195437475513366481237)
              ·
                refine ⟨139345299133229043065863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47563195437475513366481237 139345299133229043065863)
                ·
                  rfl

theorem cell22_3663549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 10].length) (baseStart_3663549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663549 prefixEnd_3663549 := by exact prefixLift 3663549
  have htrace : WordTrace (prefixWord ++ tailWord_3663549) baseStart_3663549 baseEnd_3663549 := by
    simpa [prefixWord, tailWord_3663549, baseEnd_3663549] using wordTrace_append hprefix tailTrace_3663549
  have hstable : (prefixWord ++ tailWord_3663549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663549).length < 2 ^ (prefixWord ++ tailWord_3663549).sum := by decide
  have hdescent : baseEnd_3663549 < baseStart_3663549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663551 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_3663551 : Nat := 118140960795 + 3663551 * 2 ^ 59
def prefixEnd_3663551 : Nat := 4983230072969 + 3 ^ 40 * 3663551 * 2
def baseEnd_3663551 : Nat := 1254108376839934049042761

theorem tailTrace_3663551 : CollatzResearch.WordTrace tailWord_3663551 prefixEnd_3663551 1254108376839934049042761 := by
  unfold tailWord_3663551
  simp only [CollatzResearch.WordTrace]
  refine ⟨133620682350587886542606507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89080454900391924361737671 133620682350587886542606507)
  ·
    refine ⟨200431023525881829813909761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133620682350587886542606507 200431023525881829813909761)
    ·
      refine ⟨150323267644411372360432321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200431023525881829813909761 150323267644411372360432321)
      ·
        refine ⟨112742450733308529270324241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150323267644411372360432321 112742450733308529270324241)
        ·
          refine ⟨84556838049981396952743181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112742450733308529270324241 84556838049981396952743181)
          ·
            refine ⟨31708814268743023857278693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84556838049981396952743181 31708814268743023857278693)
            ·
              refine ⟨5945402675389316973239755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31708814268743023857278693 5945402675389316973239755)
              ·
                refine ⟨8918104013083975459859633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945402675389316973239755 8918104013083975459859633)
                ·
                  refine ⟨6688578009812981594894725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8918104013083975459859633 6688578009812981594894725)
                  ·
                    refine ⟨1254108376839934049042761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6688578009812981594894725 1254108376839934049042761)
                    ·
                      rfl

theorem cell22_3663551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_3663551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663551 prefixEnd_3663551 := by exact prefixLift 3663551
  have htrace : WordTrace (prefixWord ++ tailWord_3663551) baseStart_3663551 baseEnd_3663551 := by
    simpa [prefixWord, tailWord_3663551, baseEnd_3663551] using wordTrace_append hprefix tailTrace_3663551
  have hstable : (prefixWord ++ tailWord_3663551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663551).length < 2 ^ (prefixWord ++ tailWord_3663551).sum := by decide
  have hdescent : baseEnd_3663551 < baseStart_3663551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663570 : List Nat := [3, 2, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_3663570 : Nat := 118140960795 + 3663570 * 2 ^ 59
def prefixEnd_3663570 : Nat := 4983230072969 + 3 ^ 40 * 3663570 * 2
def baseEnd_3663570 : Nat := 1254114880928224332817703

theorem tailTrace_3663570 : CollatzResearch.WordTrace tailWord_3663570 prefixEnd_3663570 1254114880928224332817703 := by
  unfold tailWord_3663570
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405343834379763196887041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89080916891679368525032109 33405343834379763196887041)
  ·
    refine ⟨25054007875784822397665281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33405343834379763196887041 25054007875784822397665281)
    ·
      refine ⟨18790505906838616798248961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25054007875784822397665281 18790505906838616798248961)
      ·
        refine ⟨14092879430128962598686721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18790505906838616798248961 14092879430128962598686721)
        ·
          refine ⟨10569659572596721949015041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14092879430128962598686721 10569659572596721949015041)
          ·
            refine ⟨7927244679447541461761281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10569659572596721949015041 7927244679447541461761281)
            ·
              refine ⟨5945433509585656096320961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7927244679447541461761281 5945433509585656096320961)
              ·
                refine ⟨4459075132189242072240721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5945433509585656096320961 4459075132189242072240721)
                ·
                  refine ⟨3344306349141931554180541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4459075132189242072240721 3344306349141931554180541)
                  ·
                    refine ⟨1254114880928224332817703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344306349141931554180541 1254114880928224332817703)
                    ·
                      rfl

theorem cell22_3663570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_3663570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663570 prefixEnd_3663570 := by exact prefixLift 3663570
  have htrace : WordTrace (prefixWord ++ tailWord_3663570) baseStart_3663570 baseEnd_3663570 := by
    simpa [prefixWord, tailWord_3663570, baseEnd_3663570] using wordTrace_append hprefix tailTrace_3663570
  have hstable : (prefixWord ++ tailWord_3663570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663570).length < 2 ^ (prefixWord ++ tailWord_3663570).sum := by decide
  have hdescent : baseEnd_3663570 < baseStart_3663570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663572 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 4]
def baseStart_3663572 : Nat := 118140960795 + 3663572 * 2 ^ 59
def prefixEnd_3663572 : Nat := 4983230072969 + 3 ^ 40 * 3663572 * 2
def baseEnd_3663572 : Nat := 418038521856365664755899

theorem tailTrace_3663572 : CollatzResearch.WordTrace tailWord_3663572 prefixEnd_3663572 418038521856365664755899 := by
  unfold tailWord_3663572
  simp only [CollatzResearch.WordTrace]
  refine ⟨66810724141755903564560485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89080965522341204752747313 66810724141755903564560485)
  ·
    refine ⟨12527010776579231918355091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66810724141755903564560485 12527010776579231918355091)
    ·
      refine ⟨18790516164868847877532637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12527010776579231918355091 18790516164868847877532637)
      ·
        refine ⟨7046443561825817954074739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18790516164868847877532637 7046443561825817954074739)
        ·
          refine ⟨10569665342738726931112109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7046443561825817954074739 10569665342738726931112109)
          ·
            refine ⟨3963624503527022599167041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10569665342738726931112109 3963624503527022599167041)
            ·
              refine ⟨2972718377645266949375281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3963624503527022599167041 2972718377645266949375281)
              ·
                refine ⟨2229538783233950212031461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972718377645266949375281 2229538783233950212031461)
                ·
                  refine ⟨418038521856365664755899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229538783233950212031461 418038521856365664755899)
                  ·
                    rfl

theorem cell22_3663572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_3663572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663572 prefixEnd_3663572 := by exact prefixLift 3663572
  have htrace : WordTrace (prefixWord ++ tailWord_3663572) baseStart_3663572 baseEnd_3663572 := by
    simpa [prefixWord, tailWord_3663572, baseEnd_3663572] using wordTrace_append hprefix tailTrace_3663572
  have hstable : (prefixWord ++ tailWord_3663572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663572).length < 2 ^ (prefixWord ++ tailWord_3663572).sum := by decide
  have hdescent : baseEnd_3663572 < baseStart_3663572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663598 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3663598 : Nat := 118140960795 + 3663598 * 2 ^ 59
def prefixEnd_3663598 : Nat := 4983230072969 + 3 ^ 40 * 3663598 * 2
def baseEnd_3663598 : Nat := 1254124465900441593117617

theorem tailTrace_3663598 : CollatzResearch.WordTrace tailWord_3663598 prefixEnd_3663598 1254124465900441593117617 := by
  unfold tailWord_3663598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16702799572677201696195931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89081597720945075713044965 16702799572677201696195931)
  ·
    refine ⟨25054199359015802544293897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16702799572677201696195931 25054199359015802544293897)
    ·
      refine ⟨18790649519261851908220423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25054199359015802544293897 18790649519261851908220423)
      ·
        refine ⟨28185974278892777862330635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18790649519261851908220423 28185974278892777862330635)
        ·
          refine ⟨42278961418339166793495953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28185974278892777862330635 42278961418339166793495953)
          ·
            refine ⟨31709221063754375095121965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42278961418339166793495953 31709221063754375095121965)
            ·
              refine ⟨11890957898907890660670737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31709221063754375095121965 11890957898907890660670737)
              ·
                refine ⟨8918218424180917995503053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11890957898907890660670737 8918218424180917995503053)
                ·
                  refine ⟨3344331909067844248313645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8918218424180917995503053 3344331909067844248313645)
                  ·
                    refine ⟨1254124465900441593117617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344331909067844248313645 1254124465900441593117617)
                    ·
                      rfl

theorem cell22_3663598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3663598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663598 prefixEnd_3663598 := by exact prefixLift 3663598
  have htrace : WordTrace (prefixWord ++ tailWord_3663598) baseStart_3663598 baseEnd_3663598 := by
    simpa [prefixWord, tailWord_3663598, baseEnd_3663598] using wordTrace_append hprefix tailTrace_3663598
  have hstable : (prefixWord ++ tailWord_3663598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663598).length < 2 ^ (prefixWord ++ tailWord_3663598).sum := by decide
  have hdescent : baseEnd_3663598 < baseStart_3663598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663626 : List Nat := [3, 1, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_3663626 : Nat := 118140960795 + 3663626 * 2 ^ 59
def prefixEnd_3663626 : Nat := 4983230072969 + 3 ^ 40 * 3663626 * 2
def baseEnd_3663626 : Nat := 1254134050872658853417531

theorem tailTrace_3663626 : CollatzResearch.WordTrace tailWord_3663626 prefixEnd_3663626 1254134050872658853417531 := by
  unfold tailWord_3663626
  simp only [CollatzResearch.WordTrace]
  refine ⟨33405854456329043587896683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89082278550210782901057821 33405854456329043587896683)
  ·
    refine ⟨50108781684493565381845025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33405854456329043587896683 50108781684493565381845025)
    ·
      refine ⟨37581586263370174036383769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50108781684493565381845025 37581586263370174036383769)
      ·
        refine ⟨28186189697527630527287827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37581586263370174036383769 28186189697527630527287827)
        ·
          refine ⟨42279284546291445790931741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28186189697527630527287827 42279284546291445790931741)
          ·
            refine ⟨15854731704859292171599403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42279284546291445790931741 15854731704859292171599403)
            ·
              refine ⟨23782097557288938257399105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15854731704859292171599403 23782097557288938257399105)
              ·
                refine ⟨17836573167966703693049329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23782097557288938257399105 17836573167966703693049329)
                ·
                  refine ⟨13377429875975027769786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17836573167966703693049329 13377429875975027769786997)
                  ·
                    refine ⟨1254134050872658853417531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13377429875975027769786997 1254134050872658853417531)
                    ·
                      rfl

theorem cell22_3663626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_3663626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663626 prefixEnd_3663626 := by exact prefixLift 3663626
  have htrace : WordTrace (prefixWord ++ tailWord_3663626) baseStart_3663626 baseEnd_3663626 := by
    simpa [prefixWord, tailWord_3663626, baseEnd_3663626] using wordTrace_append hprefix tailTrace_3663626
  have hstable : (prefixWord ++ tailWord_3663626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663626).length < 2 ^ (prefixWord ++ tailWord_3663626).sum := by decide
  have hdescent : baseEnd_3663626 < baseStart_3663626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663688 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_3663688 : Nat := 118140960795 + 3663688 * 2 ^ 59
def prefixEnd_3663688 : Nat := 4983230072969 + 3 ^ 40 * 3663688 * 2
def baseEnd_3663688 : Nat := 1254155274739711358367341

theorem tailTrace_3663688 : CollatzResearch.WordTrace tailWord_3663688 prefixEnd_3663688 1254155274739711358367341 := by
  unfold tailWord_3663688
  simp only [CollatzResearch.WordTrace]
  refine ⟨66812839575545779470171859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89083786100727705960229145 66812839575545779470171859)
  ·
    refine ⟨100219259363318669205257789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66812839575545779470171859 100219259363318669205257789)
    ·
      refine ⟨37582222261244500951971671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100219259363318669205257789 37582222261244500951971671)
      ·
        refine ⟨56373333391866751427957507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37582222261244500951971671 56373333391866751427957507)
        ·
          refine ⟨84560000087800127141936261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56373333391866751427957507 84560000087800127141936261)
          ·
            refine ⟨15855000016462523839113049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84560000087800127141936261 15855000016462523839113049)
            ·
              refine ⟨11891250012346892879334787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15855000016462523839113049 11891250012346892879334787)
              ·
                refine ⟨17836875018520339319002181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891250012346892879334787 17836875018520339319002181)
                ·
                  refine ⟨3344414065972563622312909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17836875018520339319002181 3344414065972563622312909)
                  ·
                    refine ⟨1254155274739711358367341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3344414065972563622312909 1254155274739711358367341)
                    ·
                      rfl

theorem cell22_3663688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_3663688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663688 prefixEnd_3663688 := by exact prefixLift 3663688
  have htrace : WordTrace (prefixWord ++ tailWord_3663688) baseStart_3663688 baseEnd_3663688 := by
    simpa [prefixWord, tailWord_3663688, baseEnd_3663688] using wordTrace_append hprefix tailTrace_3663688
  have hstable : (prefixWord ++ tailWord_3663688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663688).length < 2 ^ (prefixWord ++ tailWord_3663688).sum := by decide
  have hdescent : baseEnd_3663688 < baseStart_3663688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663690 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_3663690 : Nat := 118140960795 + 3663690 * 2 ^ 59
def prefixEnd_3663690 : Nat := 4983230072969 + 3 ^ 40 * 3663690 * 2
def baseEnd_3663690 : Nat := 418051986460194673272445

theorem tailTrace_3663690 : CollatzResearch.WordTrace tailWord_3663690 prefixEnd_3663690 418051986460194673272445 := by
  unfold tailWord_3663690
  simp only [CollatzResearch.WordTrace]
  refine ⟨33406438024271078320479131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89083834731389542187944349 33406438024271078320479131)
  ·
    refine ⟨50109657036406617480718697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33406438024271078320479131 50109657036406617480718697)
    ·
      refine ⟨37582242777304963110539023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50109657036406617480718697 37582242777304963110539023)
      ·
        refine ⟨56373364165957444665808535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37582242777304963110539023 56373364165957444665808535)
        ·
          refine ⟨84560046248936166998712803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56373364165957444665808535 84560046248936166998712803)
          ·
            refine ⟨126840069373404250498069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84560046248936166998712803 126840069373404250498069205)
            ·
              refine ⟨2972814125939162121048497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 126840069373404250498069205 2972814125939162121048497)
              ·
                refine ⟨2229610594454371590786373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2972814125939162121048497 2229610594454371590786373)
                ·
                  refine ⟨418051986460194673272445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2229610594454371590786373 418051986460194673272445)
                  ·
                    rfl

theorem cell22_3663690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_3663690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663690 prefixEnd_3663690 := by exact prefixLift 3663690
  have htrace : WordTrace (prefixWord ++ tailWord_3663690) baseStart_3663690 baseEnd_3663690 := by
    simpa [prefixWord, tailWord_3663690, baseEnd_3663690] using wordTrace_append hprefix tailTrace_3663690
  have hstable : (prefixWord ++ tailWord_3663690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663690).length < 2 ^ (prefixWord ++ tailWord_3663690).sum := by decide
  have hdescent : baseEnd_3663690 < baseStart_3663690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663701 : List Nat := [1, 3, 2, 2, 2, 2, 1, 9]
def baseStart_3663701 : Nat := 118140960795 + 3663701 * 2 ^ 59
def prefixEnd_3663701 : Nat := 4983230072969 + 3 ^ 40 * 3663701 * 2
def baseEnd_3663701 : Nat := 139351080545042628643589

theorem tailTrace_3663701 : CollatzResearch.WordTrace tailWord_3663701 prefixEnd_3663701 139351080545042628643589 := by
  unfold tailWord_3663701
  simp only [CollatzResearch.WordTrace]
  refine ⟨133626153300044462160566957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89084102200029641440377971 133626153300044462160566957)
  ·
    refine ⟨50109807487516673310212609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133626153300044462160566957 50109807487516673310212609)
    ·
      refine ⟨37582355615637504982659457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50109807487516673310212609 37582355615637504982659457)
      ·
        refine ⟨28186766711728128736994593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37582355615637504982659457 28186766711728128736994593)
        ·
          refine ⟨21140075033796096552745945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28186766711728128736994593 21140075033796096552745945)
          ·
            refine ⟨15855056275347072414559459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21140075033796096552745945 15855056275347072414559459)
            ·
              refine ⟨23782584413020608621839189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15855056275347072414559459 23782584413020608621839189)
              ·
                refine ⟨139351080545042628643589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23782584413020608621839189 139351080545042628643589)
                ·
                  rfl

theorem cell22_3663701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 9].length) (baseStart_3663701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663701 prefixEnd_3663701 := by exact prefixLift 3663701
  have htrace : WordTrace (prefixWord ++ tailWord_3663701) baseStart_3663701 baseEnd_3663701 := by
    simpa [prefixWord, tailWord_3663701, baseEnd_3663701] using wordTrace_append hprefix tailTrace_3663701
  have hstable : (prefixWord ++ tailWord_3663701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663701).length < 2 ^ (prefixWord ++ tailWord_3663701).sum := by decide
  have hdescent : baseEnd_3663701 < baseStart_3663701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663761 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 1, 7]
def baseStart_3663761 : Nat := 118140960795 + 3663761 * 2 ^ 59
def prefixEnd_3663761 : Nat := 4983230072969 + 3 ^ 40 * 3663761 * 2
def baseEnd_3663761 : Nat := 1254180264131563501292117

theorem tailTrace_3663761 : CollatzResearch.WordTrace tailWord_3663761 prefixEnd_3663761 1254180264131563501292117 := by
  unfold tailWord_3663761
  simp only [CollatzResearch.WordTrace]
  refine ⟨133628341679827092407751137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89085561119884728271834091 133628341679827092407751137)
  ·
    refine ⟨100221256259870319305813353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133628341679827092407751137 100221256259870319305813353)
    ·
      refine ⟨75165942194902739479360015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100221256259870319305813353 75165942194902739479360015)
      ·
        refine ⟨112748913292354109219040023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75165942194902739479360015 112748913292354109219040023)
        ·
          refine ⟨169123369938531163828560035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112748913292354109219040023 169123369938531163828560035)
          ·
            refine ⟨253685054907796745742840053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169123369938531163828560035 253685054907796745742840053)
            ·
              refine ⟨23782973897605944913391255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253685054907796745742840053 23782973897605944913391255)
              ·
                refine ⟨35674460846408917370086883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23782973897605944913391255 35674460846408917370086883)
                ·
                  refine ⟨53511691269613376055130325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35674460846408917370086883 53511691269613376055130325)
                  ·
                    refine ⟨1254180264131563501292117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53511691269613376055130325 1254180264131563501292117)
                    ·
                      rfl

theorem cell22_3663761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_3663761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663761 prefixEnd_3663761 := by exact prefixLift 3663761
  have htrace : WordTrace (prefixWord ++ tailWord_3663761) baseStart_3663761 baseEnd_3663761 := by
    simpa [prefixWord, tailWord_3663761, baseEnd_3663761] using wordTrace_append hprefix tailTrace_3663761
  have hstable : (prefixWord ++ tailWord_3663761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663761).length < 2 ^ (prefixWord ++ tailWord_3663761).sum := by decide
  have hdescent : baseEnd_3663761 < baseStart_3663761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663791 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 8]
def baseStart_3663791 : Nat := 118140960795 + 3663791 * 2 ^ 59
def prefixEnd_3663791 : Nat := 4983230072969 + 3 ^ 40 * 3663791 * 2
def baseEnd_3663791 : Nat := 418063511248217807680675

theorem tailTrace_3663791 : CollatzResearch.WordTrace tailWord_3663791 prefixEnd_3663791 418063511248217807680675 := by
  unfold tailWord_3663791
  simp only [CollatzResearch.WordTrace]
  refine ⟨133629435869718407531343227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89086290579812271687562151 133629435869718407531343227)
  ·
    refine ⟨200444153804577611297014841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133629435869718407531343227 200444153804577611297014841)
    ·
      refine ⟨150333115353433208472761131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200444153804577611297014841 150333115353433208472761131)
      ·
        refine ⟨225499673030149812709141697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150333115353433208472761131 225499673030149812709141697)
        ·
          refine ⟨169124754772612359531856273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225499673030149812709141697 169124754772612359531856273)
          ·
            refine ⟨126843566079459269648892205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169124754772612359531856273 126843566079459269648892205)
            ·
              refine ⟨47566337279797226118334577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126843566079459269648892205 47566337279797226118334577)
              ·
                refine ⟨35674752959847919588750933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47566337279797226118334577 35674752959847919588750933)
                ·
                  refine ⟨418063511248217807680675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35674752959847919588750933 418063511248217807680675)
                  ·
                    rfl

theorem cell22_3663791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 8].length) (baseStart_3663791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663791 prefixEnd_3663791 := by exact prefixLift 3663791
  have htrace : WordTrace (prefixWord ++ tailWord_3663791) baseStart_3663791 baseEnd_3663791 := by
    simpa [prefixWord, tailWord_3663791, baseEnd_3663791] using wordTrace_append hprefix tailTrace_3663791
  have hstable : (prefixWord ++ tailWord_3663791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663791).length < 2 ^ (prefixWord ++ tailWord_3663791).sum := by decide
  have hdescent : baseEnd_3663791 < baseStart_3663791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3663808 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 6]
def baseStart_3663808 : Nat := 118140960795 + 3663808 * 2 ^ 59
def prefixEnd_3663808 : Nat := 4983230072969 + 3 ^ 40 * 3663808 * 2
def baseEnd_3663808 : Nat := 418065451064023681788991

theorem tailTrace_3663808 : CollatzResearch.WordTrace tailWord_3663808 prefixEnd_3663808 418065451064023681788991 := by
  unfold tailWord_3663808
  simp only [CollatzResearch.WordTrace]
  refine ⟨66815027955328409717356039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89086703940437879623141385 66815027955328409717356039)
  ·
    refine ⟨100222541932992614576034059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66815027955328409717356039 100222541932992614576034059)
    ·
      refine ⟨150333812899488921864051089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100222541932992614576034059 150333812899488921864051089)
      ·
        refine ⟨112750359674616691398038317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150333812899488921864051089 112750359674616691398038317)
        ·
          refine ⟨42281384877981259274264369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112750359674616691398038317 42281384877981259274264369)
          ·
            refine ⟨31711038658485944455698277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42281384877981259274264369 31711038658485944455698277)
            ·
              refine ⟨5945819748466114585443427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31711038658485944455698277 5945819748466114585443427)
              ·
                refine ⟨8918729622699171878165141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945819748466114585443427 8918729622699171878165141)
                ·
                  refine ⟨418065451064023681788991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8918729622699171878165141 418065451064023681788991)
                  ·
                    rfl

theorem cell22_3663808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_3663808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3663808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3663808 prefixEnd_3663808 := by exact prefixLift 3663808
  have htrace : WordTrace (prefixWord ++ tailWord_3663808) baseStart_3663808 baseEnd_3663808 := by
    simpa [prefixWord, tailWord_3663808, baseEnd_3663808] using wordTrace_append hprefix tailTrace_3663808
  have hstable : (prefixWord ++ tailWord_3663808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3663808).length < 2 ^ (prefixWord ++ tailWord_3663808).sum := by decide
  have hdescent : baseEnd_3663808 < baseStart_3663808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3663808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
