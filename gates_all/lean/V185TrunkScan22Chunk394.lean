import V185TrunkScan22Chunk393

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3514930 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_3514930 : Nat := 118140960795 + 3514930 * 2 ^ 59
def prefixEnd_3514930 : Nat := 4983230072969 + 3 ^ 40 * 3514930 * 2
def baseEnd_3514930 : Nat := 1203232371272025369273425

theorem tailTrace_3514930 : CollatzResearch.WordTrace tailWord_3514930 prefixEnd_3514930 1203232371272025369273425 := by
  unfold tailWord_3514930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050007289004096774151561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85466686104010924731070829 32050007289004096774151561)
  ·
    refine ⟨24037505466753072580613671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32050007289004096774151561 24037505466753072580613671)
    ·
      refine ⟨36056258200129608870920507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24037505466753072580613671 36056258200129608870920507)
      ·
        refine ⟨54084387300194413306380761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36056258200129608870920507 54084387300194413306380761)
        ·
          refine ⟨40563290475145809979785571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54084387300194413306380761 40563290475145809979785571)
          ·
            refine ⟨60844935712718714969678357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40563290475145809979785571 60844935712718714969678357)
            ·
              refine ⟨2852106361533689764203673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60844935712718714969678357 2852106361533689764203673)
              ·
                refine ⟨2139079771150267323152755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852106361533689764203673 2139079771150267323152755)
                ·
                  refine ⟨3208619656725400984729133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139079771150267323152755 3208619656725400984729133)
                  ·
                    refine ⟨1203232371272025369273425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208619656725400984729133 1203232371272025369273425)
                    ·
                      rfl

theorem cell22_3514930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_3514930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514930 prefixEnd_3514930 := by exact prefixLift 3514930
  have htrace : WordTrace (prefixWord ++ tailWord_3514930) baseStart_3514930 baseEnd_3514930 := by
    simpa [prefixWord, tailWord_3514930, baseEnd_3514930] using wordTrace_append hprefix tailTrace_3514930
  have hstable : (prefixWord ++ tailWord_3514930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514930).length < 2 ^ (prefixWord ++ tailWord_3514930).sum := by decide
  have hdescent : baseEnd_3514930 < baseStart_3514930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514941 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_3514941 : Nat := 118140960795 + 3514941 * 2 ^ 59
def prefixEnd_3514941 : Nat := 4983230072969 + 3 ^ 40 * 3514941 * 2
def baseEnd_3514941 : Nat := 1203236136796825007248391

theorem tailTrace_3514941 : CollatzResearch.WordTrace tailWord_3514941 prefixEnd_3514941 1203236136796825007248391 := by
  unfold tailWord_3514941
  simp only [CollatzResearch.WordTrace]
  refine ⟨128200430358976535975256677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85466953572651023983504451 128200430358976535975256677)
  ·
    refine ⟨24037580692308100495360627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128200430358976535975256677 24037580692308100495360627)
    ·
      refine ⟨36056371038462150743040941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24037580692308100495360627 36056371038462150743040941)
      ·
        refine ⟨13521139139423306528640353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36056371038462150743040941 13521139139423306528640353)
        ·
          refine ⟨10140854354567479896480265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13521139139423306528640353 10140854354567479896480265)
          ·
            refine ⟨7605640765925609922360199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10140854354567479896480265 7605640765925609922360199)
            ·
              refine ⟨11408461148888414883540299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7605640765925609922360199 11408461148888414883540299)
              ·
                refine ⟨17112691723332622325310449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11408461148888414883540299 17112691723332622325310449)
                ·
                  refine ⟨12834518792499466743982837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17112691723332622325310449 12834518792499466743982837)
                  ·
                    refine ⟨1203236136796825007248391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12834518792499466743982837 1203236136796825007248391)
                    ·
                      rfl

theorem cell22_3514941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_3514941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514941 prefixEnd_3514941 := by exact prefixLift 3514941
  have htrace : WordTrace (prefixWord ++ tailWord_3514941) baseStart_3514941 baseEnd_3514941 := by
    simpa [prefixWord, tailWord_3514941, baseEnd_3514941] using wordTrace_append hprefix tailTrace_3514941
  have hstable : (prefixWord ++ tailWord_3514941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514941).length < 2 ^ (prefixWord ++ tailWord_3514941).sum := by decide
  have hdescent : baseEnd_3514941 < baseStart_3514941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514954 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3514954 : Nat := 118140960795 + 3514954 * 2 ^ 59
def prefixEnd_3514954 : Nat := 4983230072969 + 3 ^ 40 * 3514954 * 2
def baseEnd_3514954 : Nat := 401080195654165768891117

theorem tailTrace_3514954 : CollatzResearch.WordTrace tailWord_3514954 prefixEnd_3514954 401080195654165768891117 := by
  unfold tailWord_3514954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050226126982359798869979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85467269671952959463653277 32050226126982359798869979)
  ·
    refine ⟨48075339190473539698304969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32050226126982359798869979 48075339190473539698304969)
    ·
      refine ⟨36056504392855154773728727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48075339190473539698304969 36056504392855154773728727)
      ·
        refine ⟨54084756589282732160593091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36056504392855154773728727 54084756589282732160593091)
        ·
          refine ⟨81127134883924098240889637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54084756589282732160593091 81127134883924098240889637)
          ·
            refine ⟨15211337790735768420166807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81127134883924098240889637 15211337790735768420166807)
            ·
              refine ⟨22817006686103652630250211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15211337790735768420166807 22817006686103652630250211)
              ·
                refine ⟨34225510029155478945375317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22817006686103652630250211 34225510029155478945375317)
                ·
                  refine ⟨401080195654165768891117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34225510029155478945375317 401080195654165768891117)
                  ·
                    rfl

theorem cell22_3514954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3514954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514954 prefixEnd_3514954 := by exact prefixLift 3514954
  have htrace : WordTrace (prefixWord ++ tailWord_3514954) baseStart_3514954 baseEnd_3514954 := by
    simpa [prefixWord, tailWord_3514954, baseEnd_3514954] using wordTrace_append hprefix tailTrace_3514954
  have hstable : (prefixWord ++ tailWord_3514954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514954).length < 2 ^ (prefixWord ++ tailWord_3514954).sum := by decide
  have hdescent : baseEnd_3514954 < baseStart_3514954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3514956 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 1, 4]
def baseStart_3514956 : Nat := 118140960795 + 3514956 * 2 ^ 59
def prefixEnd_3514956 : Nat := 4983230072969 + 3 ^ 40 * 3514956 * 2
def baseEnd_3514956 : Nat := 1203241271603369968123345

theorem tailTrace_3514956 : CollatzResearch.WordTrace tailWord_3514956 prefixEnd_3514956 1203241271603369968123345 := by
  unfold tailWord_3514956
  simp only [CollatzResearch.WordTrace]
  refine ⟨64100488726961096768526361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85467318302614795691368481 64100488726961096768526361)
  ·
    refine ⟨48075366545220822576394771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64100488726961096768526361 48075366545220822576394771)
    ·
      refine ⟨72113049817831233864592157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48075366545220822576394771 72113049817831233864592157)
      ·
        refine ⟨27042393681686712699222059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72113049817831233864592157 27042393681686712699222059)
        ·
          refine ⟨40563590522530069048833089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27042393681686712699222059 40563590522530069048833089)
          ·
            refine ⟨30422692891897551786624817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40563590522530069048833089 30422692891897551786624817)
            ·
              refine ⟨22817019668923163839968613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30422692891897551786624817 22817019668923163839968613)
              ·
                refine ⟨4278191187923093219994115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22817019668923163839968613 4278191187923093219994115)
                ·
                  refine ⟨6417286781884639829991173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4278191187923093219994115 6417286781884639829991173)
                  ·
                    refine ⟨1203241271603369968123345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6417286781884639829991173 1203241271603369968123345)
                    ·
                      rfl

theorem cell22_3514956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_3514956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3514956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3514956 prefixEnd_3514956 := by exact prefixLift 3514956
  have htrace : WordTrace (prefixWord ++ tailWord_3514956) baseStart_3514956 baseEnd_3514956 := by
    simpa [prefixWord, tailWord_3514956, baseEnd_3514956] using wordTrace_append hprefix tailTrace_3514956
  have hstable : (prefixWord ++ tailWord_3514956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3514956).length < 2 ^ (prefixWord ++ tailWord_3514956).sum := by decide
  have hdescent : baseEnd_3514956 < baseStart_3514956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3514956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515029 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3515029 : Nat := 118140960795 + 3515029 * 2 ^ 59
def prefixEnd_3515029 : Nat := 4983230072969 + 3 ^ 40 * 3515029 * 2
def baseEnd_3515029 : Nat := 1203266260995222111048121

theorem tailTrace_3515029 : CollatzResearch.WordTrace tailWord_3515029 prefixEnd_3515029 1203266260995222111048121 := by
  unfold tailWord_3515029
  simp only [CollatzResearch.WordTrace]
  refine ⟨128203639982657727004460141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85469093321771818002973427 128203639982657727004460141)
  ·
    refine ⟨48076364993496647626672553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128203639982657727004460141 48076364993496647626672553)
    ·
      refine ⟨36057273745122485720004415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48076364993496647626672553 36057273745122485720004415)
      ·
        refine ⟨54085910617683728580006623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36057273745122485720004415 54085910617683728580006623)
        ·
          refine ⟨81128865926525592870009935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54085910617683728580006623 81128865926525592870009935)
          ·
            refine ⟨121693298889788389305014903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81128865926525592870009935 121693298889788389305014903)
            ·
              refine ⟨182539948334682583957522355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121693298889788389305014903 182539948334682583957522355)
              ·
                refine ⟨273809922502023875936283533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182539948334682583957522355 273809922502023875936283533)
                ·
                  refine ⟨102678720938258953476106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273809922502023875936283533 102678720938258953476106325)
                  ·
                    refine ⟨1203266260995222111048121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102678720938258953476106325 1203266260995222111048121)
                    ·
                      rfl

theorem cell22_3515029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3515029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515029 prefixEnd_3515029 := by exact prefixLift 3515029
  have htrace : WordTrace (prefixWord ++ tailWord_3515029) baseStart_3515029 baseEnd_3515029 := by
    simpa [prefixWord, tailWord_3515029, baseEnd_3515029] using wordTrace_append hprefix tailTrace_3515029
  have hstable : (prefixWord ++ tailWord_3515029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515029).length < 2 ^ (prefixWord ++ tailWord_3515029).sum := by decide
  have hdescent : baseEnd_3515029 < baseStart_3515029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515050 : List Nat := [3, 1, 5, 2, 1, 1, 2, 7]
def baseStart_3515050 : Nat := 118140960795 + 3515050 * 2 ^ 59
def prefixEnd_3515050 : Nat := 4983230072969 + 3 ^ 40 * 3515050 * 2
def baseEnd_3515050 : Nat := 133697049969376117363673

theorem tailTrace_3515050 : CollatzResearch.WordTrace tailWord_3515050 prefixEnd_3515050 133697049969376117363673 := by
  unfold tailWord_3515050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32051101478895411897743651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85469603943721098393983069 32051101478895411897743651)
  ·
    refine ⟨48076652218343117846615477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32051101478895411897743651 48076652218343117846615477)
    ·
      refine ⟨4507186145469667298120201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48076652218343117846615477 4507186145469667298120201)
      ·
        refine ⟨3380389609102250473590151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4507186145469667298120201 3380389609102250473590151)
        ·
          refine ⟨5070584413653375710385227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3380389609102250473590151 5070584413653375710385227)
          ·
            refine ⟨7605876620480063565577841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5070584413653375710385227 7605876620480063565577841)
            ·
              refine ⟨5704407465360047674183381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7605876620480063565577841 5704407465360047674183381)
              ·
                refine ⟨133697049969376117363673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5704407465360047674183381 133697049969376117363673)
                ·
                  rfl

theorem cell22_3515050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_3515050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515050 prefixEnd_3515050 := by exact prefixLift 3515050
  have htrace : WordTrace (prefixWord ++ tailWord_3515050) baseStart_3515050 baseEnd_3515050 := by
    simpa [prefixWord, tailWord_3515050, baseEnd_3515050] using wordTrace_append hprefix tailTrace_3515050
  have hstable : (prefixWord ++ tailWord_3515050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515050).length < 2 ^ (prefixWord ++ tailWord_3515050).sum := by decide
  have hdescent : baseEnd_3515050 < baseStart_3515050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515054 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3515054 : Nat := 118140960795 + 3515054 * 2 ^ 59
def prefixEnd_3515054 : Nat := 4983230072969 + 3 ^ 40 * 3515054 * 2
def baseEnd_3515054 : Nat := 1203274819006130379173045

theorem tailTrace_3515054 : CollatzResearch.WordTrace tailWord_3515054 prefixEnd_3515054 1203274819006130379173045 := by
  unfold tailWord_3515054
  simp only [CollatzResearch.WordTrace]
  refine ⟨16025568975945894534265027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85469701205044770849413477 16025568975945894534265027)
  ·
    refine ⟨24038353463918841801397541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16025568975945894534265027 24038353463918841801397541)
    ·
      refine ⟨4507191274484782837762039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24038353463918841801397541 4507191274484782837762039)
      ·
        refine ⟨6760786911727174256643059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507191274484782837762039 6760786911727174256643059)
        ·
          refine ⟨10141180367590761384964589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760786911727174256643059 10141180367590761384964589)
          ·
            refine ⟨3802942637846535519361721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10141180367590761384964589 3802942637846535519361721)
            ·
              refine ⟨2852206978384901639521291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3802942637846535519361721 2852206978384901639521291)
              ·
                refine ⟨4278310467577352459281937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852206978384901639521291 4278310467577352459281937)
                ·
                  refine ⟨3208732850683014344461453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4278310467577352459281937 3208732850683014344461453)
                  ·
                    refine ⟨1203274819006130379173045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208732850683014344461453 1203274819006130379173045)
                    ·
                      rfl

theorem cell22_3515054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3515054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515054 prefixEnd_3515054 := by exact prefixLift 3515054
  have htrace : WordTrace (prefixWord ++ tailWord_3515054) baseStart_3515054 baseEnd_3515054 := by
    simpa [prefixWord, tailWord_3515054, baseEnd_3515054] using wordTrace_append hprefix tailTrace_3515054
  have hstable : (prefixWord ++ tailWord_3515054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515054).length < 2 ^ (prefixWord ++ tailWord_3515054).sum := by decide
  have hdescent : baseEnd_3515054 < baseStart_3515054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515140 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3515140 : Nat := 118140960795 + 3515140 * 2 ^ 59
def prefixEnd_3515140 : Nat := 4983230072969 + 3 ^ 40 * 3515140 * 2
def baseEnd_3515140 : Nat := 401101419521218273840927

theorem tailTrace_3515140 : CollatzResearch.WordTrace tailWord_3515140 prefixEnd_3515140 401101419521218273840927 := by
  unfold tailWord_3515140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64103844242627796480875437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85471792323503728641167249 64103844242627796480875437)
  ·
    refine ⟨24038941590985423680328289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64103844242627796480875437 24038941590985423680328289)
    ·
      refine ⟨18029206193239067760246217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24038941590985423680328289 18029206193239067760246217)
      ·
        refine ⟨13521904644929300820184663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18029206193239067760246217 13521904644929300820184663)
        ·
          refine ⟨20282856967393951230276995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13521904644929300820184663 20282856967393951230276995)
          ·
            refine ⟨30424285451090926845415493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20282856967393951230276995 30424285451090926845415493)
            ·
              refine ⟨5704553522079548783515405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30424285451090926845415493 5704553522079548783515405)
              ·
                refine ⟨2139207570779830793818277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5704553522079548783515405 2139207570779830793818277)
                ·
                  refine ⟨401101419521218273840927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139207570779830793818277 401101419521218273840927)
                  ·
                    rfl

theorem cell22_3515140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3515140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515140 prefixEnd_3515140 := by exact prefixLift 3515140
  have htrace : WordTrace (prefixWord ++ tailWord_3515140) baseStart_3515140 baseEnd_3515140 := by
    simpa [prefixWord, tailWord_3515140, baseEnd_3515140] using wordTrace_append hprefix tailTrace_3515140
  have hstable : (prefixWord ++ tailWord_3515140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515140).length < 2 ^ (prefixWord ++ tailWord_3515140).sum := by decide
  have hdescent : baseEnd_3515140 < baseStart_3515140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515172 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 5]
def baseStart_3515172 : Nat := 118140960795 + 3515172 * 2 ^ 59
def prefixEnd_3515172 : Nat := 4983230072969 + 3 ^ 40 * 3515172 * 2
def baseEnd_3515172 : Nat := 1203315212817617404722683

theorem tailTrace_3515172 : CollatzResearch.WordTrace tailWord_3515172 prefixEnd_3515172 1203315212817617404722683 := by
  unfold tailWord_3515172
  simp only [CollatzResearch.WordTrace]
  refine ⟨64104427810569831213457885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85472570414093108284610513 64104427810569831213457885)
  ·
    refine ⟨24039160428963686705046707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64104427810569831213457885 24039160428963686705046707)
    ·
      refine ⟨36058740643445530057570061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24039160428963686705046707 36058740643445530057570061)
      ·
        refine ⟨13522027741292073771588773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36058740643445530057570061 13522027741292073771588773)
        ·
          refine ⟨2535380201492263832172895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13522027741292073771588773 2535380201492263832172895)
          ·
            refine ⟨3803070302238395748259343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535380201492263832172895 3803070302238395748259343)
            ·
              refine ⟨5704605453357593622389015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803070302238395748259343 5704605453357593622389015)
              ·
                refine ⟨8556908180036390433583523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704605453357593622389015 8556908180036390433583523)
                ·
                  refine ⟨12835362270054585650375285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8556908180036390433583523 12835362270054585650375285)
                  ·
                    refine ⟨1203315212817617404722683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12835362270054585650375285 1203315212817617404722683)
                    ·
                      rfl

theorem cell22_3515172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_3515172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515172 prefixEnd_3515172 := by exact prefixLift 3515172
  have htrace : WordTrace (prefixWord ++ tailWord_3515172) baseStart_3515172 baseEnd_3515172 := by
    simpa [prefixWord, tailWord_3515172, baseEnd_3515172] using wordTrace_append hprefix tailTrace_3515172
  have hstable : (prefixWord ++ tailWord_3515172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515172).length < 2 ^ (prefixWord ++ tailWord_3515172).sum := by decide
  have hdescent : baseEnd_3515172 < baseStart_3515172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515217 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 3, 3]
def baseStart_3515217 : Nat := 118140960795 + 3515217 * 2 ^ 59
def prefixEnd_3515217 : Nat := 4983230072969 + 3 ^ 40 * 3515217 * 2
def baseEnd_3515217 : Nat := 1203330617237252287347545

theorem tailTrace_3515217 : CollatzResearch.WordTrace tailWord_3515217 prefixEnd_3515217 1203330617237252287347545 := by
  unfold tailWord_3515217
  simp only [CollatzResearch.WordTrace]
  refine ⟨128210496905976635112303905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85473664603984423408202603 128210496905976635112303905)
  ·
    refine ⟨96157872679482476334227929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128210496905976635112303905 96157872679482476334227929)
    ·
      refine ⟨72118404509611857250670947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96157872679482476334227929 72118404509611857250670947)
      ·
        refine ⟨108177606764417785876006421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72118404509611857250670947 108177606764417785876006421)
        ·
          refine ⟨5070825317082083712937801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108177606764417785876006421 5070825317082083712937801)
          ·
            refine ⟨3803118987811562784703351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5070825317082083712937801 3803118987811562784703351)
            ·
              refine ⟨5704678481717344177055027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803118987811562784703351 5704678481717344177055027)
              ·
                refine ⟨8557017722576016265582541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5704678481717344177055027 8557017722576016265582541)
                ·
                  refine ⟨3208881645966006099593453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8557017722576016265582541 3208881645966006099593453)
                  ·
                    refine ⟨1203330617237252287347545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208881645966006099593453 1203330617237252287347545)
                    ·
                      rfl

theorem cell22_3515217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_3515217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515217 prefixEnd_3515217 := by exact prefixLift 3515217
  have htrace : WordTrace (prefixWord ++ tailWord_3515217) baseStart_3515217 baseEnd_3515217 := by
    simpa [prefixWord, tailWord_3515217, baseEnd_3515217] using wordTrace_append hprefix tailTrace_3515217
  have hstable : (prefixWord ++ tailWord_3515217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515217).length < 2 ^ (prefixWord ++ tailWord_3515217).sum := by decide
  have hdescent : baseEnd_3515217 < baseStart_3515217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515335 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 3, 3]
def baseStart_3515335 : Nat := 118140960795 + 3515335 * 2 ^ 59
def prefixEnd_3515335 : Nat := 4983230072969 + 3 ^ 40 * 3515335 * 2
def baseEnd_3515335 : Nat := 1203371011048739312897183

theorem tailTrace_3515335 : CollatzResearch.WordTrace tailWord_3515335 prefixEnd_3515335 1203371011048739312897183 := by
  unfold tailWord_3515335
  simp only [CollatzResearch.WordTrace]
  refine ⟨128214800719549141265099459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85476533813032760843399639 128214800719549141265099459)
  ·
    refine ⟨192322201079323711897649189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128214800719549141265099459 192322201079323711897649189)
    ·
      refine ⟨36060412702373195980809223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192322201079323711897649189 36060412702373195980809223)
      ·
        refine ⟨54090619053559793971213835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36060412702373195980809223 54090619053559793971213835)
        ·
          refine ⟨81135928580339690956820753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54090619053559793971213835 81135928580339690956820753)
          ·
            refine ⟨60851946435254768217615565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81135928580339690956820753 60851946435254768217615565)
            ·
              refine ⟨22819479913220538081605837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60851946435254768217615565 22819479913220538081605837)
              ·
                refine ⟨8557304967457701780602189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22819479913220538081605837 8557304967457701780602189)
                ·
                  refine ⟨3208989362796638167725821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8557304967457701780602189 3208989362796638167725821)
                  ·
                    refine ⟨1203371011048739312897183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3208989362796638167725821 1203371011048739312897183)
                    ·
                      rfl

theorem cell22_3515335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_3515335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515335 prefixEnd_3515335 := by exact prefixLift 3515335
  have htrace : WordTrace (prefixWord ++ tailWord_3515335) baseStart_3515335 baseEnd_3515335 := by
    simpa [prefixWord, tailWord_3515335, baseEnd_3515335] using wordTrace_append hprefix tailTrace_3515335
  have hstable : (prefixWord ++ tailWord_3515335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515335).length < 2 ^ (prefixWord ++ tailWord_3515335).sum := by decide
  have hdescent : baseEnd_3515335 < baseStart_3515335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515425 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_3515425 : Nat := 118140960795 + 3515425 * 2 ^ 59
def prefixEnd_3515425 : Nat := 4983230072969 + 3 ^ 40 * 3515425 * 2
def baseEnd_3515425 : Nat := 1203401819888009078146907

theorem tailTrace_3515425 : CollatzResearch.WordTrace tailWord_3515425 prefixEnd_3515425 1203401819888009078146907 := by
  unfold tailWord_3515425
  simp only [CollatzResearch.WordTrace]
  refine ⟨128218083289223086635875729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85478722192815391090583819 128218083289223086635875729)
  ·
    refine ⟨96163562466917314976906797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128218083289223086635875729 96163562466917314976906797)
    ·
      refine ⟨36061335925093993116340049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96163562466917314976906797 36061335925093993116340049)
      ·
        refine ⟨27046001943820494837255037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36061335925093993116340049 27046001943820494837255037)
        ·
          refine ⟨10142250728932685563970639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27046001943820494837255037 10142250728932685563970639)
          ·
            refine ⟨15213376093399028345955959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142250728932685563970639 15213376093399028345955959)
            ·
              refine ⟨22820064140098542518933939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15213376093399028345955959 22820064140098542518933939)
              ·
                refine ⟨34230096210147813778400909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22820064140098542518933939 34230096210147813778400909)
                ·
                  refine ⟨12836286078805430166900341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34230096210147813778400909 12836286078805430166900341)
                  ·
                    refine ⟨1203401819888009078146907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12836286078805430166900341 1203401819888009078146907)
                    ·
                      rfl

theorem cell22_3515425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_3515425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515425 prefixEnd_3515425 := by exact prefixLift 3515425
  have htrace : WordTrace (prefixWord ++ tailWord_3515425) baseStart_3515425 baseEnd_3515425 := by
    simpa [prefixWord, tailWord_3515425, baseEnd_3515425] using wordTrace_append hprefix tailTrace_3515425
  have hstable : (prefixWord ++ tailWord_3515425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515425).length < 2 ^ (prefixWord ++ tailWord_3515425).sum := by decide
  have hdescent : baseEnd_3515425 < baseStart_3515425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515440 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 2, 4]
def baseStart_3515440 : Nat := 118140960795 + 3515440 * 2 ^ 59
def prefixEnd_3515440 : Nat := 4983230072969 + 3 ^ 40 * 3515440 * 2
def baseEnd_3515440 : Nat := 1203406954694554039021861

theorem tailTrace_3515440 : CollatzResearch.WordTrace tailWord_3515440 prefixEnd_3515440 1203406954694554039021861 := by
  unfold tailWord_3515440
  simp only [CollatzResearch.WordTrace]
  refine ⟨64109315192084372098835887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85479086922779162798447849 64109315192084372098835887)
  ·
    refine ⟨96163972788126558148253831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64109315192084372098835887 96163972788126558148253831)
    ·
      refine ⟨144245959182189837222380747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96163972788126558148253831 144245959182189837222380747)
      ·
        refine ⟨216368938773284755833571121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144245959182189837222380747 216368938773284755833571121)
        ·
          refine ⟨162276704079963566875178341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216368938773284755833571121 162276704079963566875178341)
          ·
            refine ⟨30426882014993168789095939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162276704079963566875178341 30426882014993168789095939)
            ·
              refine ⟨45640323022489753183643909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30426882014993168789095939 45640323022489753183643909)
              ·
                refine ⟨8557560566716828721933233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45640323022489753183643909 8557560566716828721933233)
                ·
                  refine ⟨6418170425037621541449925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557560566716828721933233 6418170425037621541449925)
                  ·
                    refine ⟨1203406954694554039021861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418170425037621541449925 1203406954694554039021861)
                    ·
                      rfl

theorem cell22_3515440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_3515440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515440 prefixEnd_3515440 := by exact prefixLift 3515440
  have htrace : WordTrace (prefixWord ++ tailWord_3515440) baseStart_3515440 baseEnd_3515440 := by
    simpa [prefixWord, tailWord_3515440, baseEnd_3515440] using wordTrace_append hprefix tailTrace_3515440
  have hstable : (prefixWord ++ tailWord_3515440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515440).length < 2 ^ (prefixWord ++ tailWord_3515440).sum := by decide
  have hdescent : baseEnd_3515440 < baseStart_3515440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515474 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_3515474 : Nat := 118140960795 + 3515474 * 2 ^ 59
def prefixEnd_3515474 : Nat := 4983230072969 + 3 ^ 40 * 3515474 * 2
def baseEnd_3515474 : Nat := 1203418593589389283671757

theorem tailTrace_3515474 : CollatzResearch.WordTrace tailWord_3515474 prefixEnd_3515474 1203418593589389283671757 := by
  unfold tailWord_3515474
  simp only [CollatzResearch.WordTrace]
  refine ⟨32054967616511392001102369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85479913644030378669606317 32054967616511392001102369)
  ·
    refine ⟨24041225712383544000826777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32054967616511392001102369 24041225712383544000826777)
    ·
      refine ⟨18030919284287658000620083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24041225712383544000826777 18030919284287658000620083)
      ·
        refine ⟨27046378926431487000930125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18030919284287658000620083 27046378926431487000930125)
        ·
          refine ⟨10142392097411807625348797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27046378926431487000930125 10142392097411807625348797)
          ·
            refine ⟨3803397036529427859505799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10142392097411807625348797 3803397036529427859505799)
            ·
              refine ⟨5705095554794141789258699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803397036529427859505799 5705095554794141789258699)
              ·
                refine ⟨8557643332191212683888049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705095554794141789258699 8557643332191212683888049)
                ·
                  refine ⟨6418232499143409512916037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557643332191212683888049 6418232499143409512916037)
                  ·
                    refine ⟨1203418593589389283671757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418232499143409512916037 1203418593589389283671757)
                    ·
                      rfl

theorem cell22_3515474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_3515474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515474 prefixEnd_3515474 := by exact prefixLift 3515474
  have htrace : WordTrace (prefixWord ++ tailWord_3515474) baseStart_3515474 baseEnd_3515474 := by
    simpa [prefixWord, tailWord_3515474, baseEnd_3515474] using wordTrace_append hprefix tailTrace_3515474
  have hstable : (prefixWord ++ tailWord_3515474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515474).length < 2 ^ (prefixWord ++ tailWord_3515474).sum := by decide
  have hdescent : baseEnd_3515474 < baseStart_3515474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515478 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_3515478 : Nat := 118140960795 + 3515478 * 2 ^ 59
def prefixEnd_3515478 : Nat := 4983230072969 + 3 ^ 40 * 3515478 * 2
def baseEnd_3515478 : Nat := 401139987623711535523915

theorem tailTrace_3515478 : CollatzResearch.WordTrace tailWord_3515478 prefixEnd_3515478 401139987623711535523915 := by
  unfold tailWord_3515478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013751022376942292972193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85480010905354051125036725 8013751022376942292972193)
  ·
    refine ⟨6010313266782706719729145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8013751022376942292972193 6010313266782706719729145)
    ·
      refine ⟨4507734950087030039796859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6010313266782706719729145 4507734950087030039796859)
      ·
        refine ⟨6761602425130545059695289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507734950087030039796859 6761602425130545059695289)
        ·
          refine ⟨5071201818847908794771467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6761602425130545059695289 5071201818847908794771467)
          ·
            refine ⟨7606802728271863192157201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5071201818847908794771467 7606802728271863192157201)
            ·
              refine ⟨5705102046203897394117901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7606802728271863192157201 5705102046203897394117901)
              ·
                refine ⟨2139413267326461522794213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5705102046203897394117901 2139413267326461522794213)
                ·
                  refine ⟨401139987623711535523915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139413267326461522794213 401139987623711535523915)
                  ·
                    rfl

theorem cell22_3515478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_3515478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515478 prefixEnd_3515478 := by exact prefixLift 3515478
  have htrace : WordTrace (prefixWord ++ tailWord_3515478) baseStart_3515478 baseEnd_3515478 := by
    simpa [prefixWord, tailWord_3515478, baseEnd_3515478] using wordTrace_append hprefix tailTrace_3515478
  have hstable : (prefixWord ++ tailWord_3515478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515478).length < 2 ^ (prefixWord ++ tailWord_3515478).sum := by decide
  have hdescent : baseEnd_3515478 < baseStart_3515478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515500 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_3515500 : Nat := 118140960795 + 3515500 * 2 ^ 59
def prefixEnd_3515500 : Nat := 4983230072969 + 3 ^ 40 * 3515500 * 2
def baseEnd_3515500 : Nat := 401142497973577960840559

theorem tailTrace_3515500 : CollatzResearch.WordTrace tailWord_3515500 prefixEnd_3515500 401142497973577960840559 := by
  unfold tailWord_3515500
  simp only [CollatzResearch.WordTrace]
  refine ⟨64110409381975687222427977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85480545842634249629903969 64110409381975687222427977)
  ·
    refine ⟨48082807036481765416820983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64110409381975687222427977 48082807036481765416820983)
    ·
      refine ⟨72124210554722648125231475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48082807036481765416820983 72124210554722648125231475)
      ·
        refine ⟨108186315832083972187847213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72124210554722648125231475 108186315832083972187847213)
        ·
          refine ⟨40569868437031489570442705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108186315832083972187847213 40569868437031489570442705)
          ·
            refine ⟨30427401327773617177832029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40569868437031489570442705 30427401327773617177832029)
            ·
              refine ⟨11410275497915106441687011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30427401327773617177832029 11410275497915106441687011)
              ·
                refine ⟨17115413246872659662530517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11410275497915106441687011 17115413246872659662530517)
                ·
                  refine ⟨401142497973577960840559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17115413246872659662530517 401142497973577960840559)
                  ·
                    rfl

theorem cell22_3515500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_3515500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515500 prefixEnd_3515500 := by exact prefixLift 3515500
  have htrace : WordTrace (prefixWord ++ tailWord_3515500) baseStart_3515500 baseEnd_3515500 := by
    simpa [prefixWord, tailWord_3515500, baseEnd_3515500] using wordTrace_append hprefix tailTrace_3515500
  have hstable : (prefixWord ++ tailWord_3515500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515500).length < 2 ^ (prefixWord ++ tailWord_3515500).sum := by decide
  have hdescent : baseEnd_3515500 < baseStart_3515500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515504 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_3515504 : Nat := 118140960795 + 3515504 * 2 ^ 59
def prefixEnd_3515504 : Nat := 4983230072969 + 3 ^ 40 * 3515504 * 2
def baseEnd_3515504 : Nat := 1203428863202479205421665

theorem tailTrace_3515504 : CollatzResearch.WordTrace tailWord_3515504 prefixEnd_3515504 1203428863202479205421665 := by
  unfold tailWord_3515504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64110482327968441564000783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85480643103957922085334377 64110482327968441564000783)
  ·
    refine ⟨96165723491952662346001175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64110482327968441564000783 96165723491952662346001175)
    ·
      refine ⟨144248585237928993519001763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96165723491952662346001175 144248585237928993519001763)
      ·
        refine ⟨216372877856893490278502645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144248585237928993519001763 216372877856893490278502645)
        ·
          refine ⟨20284957299083764713609623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216372877856893490278502645 20284957299083764713609623)
          ·
            refine ⟨30427435948625647070414435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20284957299083764713609623 30427435948625647070414435)
            ·
              refine ⟨45641153922938470605621653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30427435948625647070414435 45641153922938470605621653)
              ·
                refine ⟨2139429090137740809638515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45641153922938470605621653 2139429090137740809638515)
                ·
                  refine ⟨3209143635206611214457773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139429090137740809638515 3209143635206611214457773)
                  ·
                    refine ⟨1203428863202479205421665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209143635206611214457773 1203428863202479205421665)
                    ·
                      rfl

theorem cell22_3515504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_3515504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515504 prefixEnd_3515504 := by exact prefixLift 3515504
  have htrace : WordTrace (prefixWord ++ tailWord_3515504) baseStart_3515504 baseEnd_3515504 := by
    simpa [prefixWord, tailWord_3515504, baseEnd_3515504] using wordTrace_append hprefix tailTrace_3515504
  have hstable : (prefixWord ++ tailWord_3515504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515504).length < 2 ^ (prefixWord ++ tailWord_3515504).sum := by decide
  have hdescent : baseEnd_3515504 < baseStart_3515504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515538 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 1, 3]
def baseStart_3515538 : Nat := 118140960795 + 3515538 * 2 ^ 59
def prefixEnd_3515538 : Nat := 4983230072969 + 3 ^ 40 * 3515538 * 2
def baseEnd_3515538 : Nat := 1203440502097314450071561

theorem tailTrace_3515538 : CollatzResearch.WordTrace tailWord_3515538 prefixEnd_3515538 1203440502097314450071561 := by
  unfold tailWord_3515538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055551184453426733684817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85481469825209137956492845 32055551184453426733684817)
  ·
    refine ⟨24041663388340070050263613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32055551184453426733684817 24041663388340070050263613)
    ·
      refine ⟨9015623770627526268848855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24041663388340070050263613 9015623770627526268848855)
      ·
        refine ⟨13523435655941289403273283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015623770627526268848855 13523435655941289403273283)
        ·
          refine ⟨20285153483911934104909925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13523435655941289403273283 20285153483911934104909925)
          ·
            refine ⟨3803466278233487644670611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20285153483911934104909925 3803466278233487644670611)
            ·
              refine ⟨5705199417350231467005917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3803466278233487644670611 5705199417350231467005917)
              ·
                refine ⟨2139449781506336800127219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5705199417350231467005917 2139449781506336800127219)
                ·
                  refine ⟨3209174672259505200190829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139449781506336800127219 3209174672259505200190829)
                  ·
                    refine ⟨1203440502097314450071561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209174672259505200190829 1203440502097314450071561)
                    ·
                      rfl

theorem cell22_3515538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_3515538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515538 prefixEnd_3515538 := by exact prefixLift 3515538
  have htrace : WordTrace (prefixWord ++ tailWord_3515538) baseStart_3515538 baseEnd_3515538 := by
    simpa [prefixWord, tailWord_3515538, baseEnd_3515538] using wordTrace_append hprefix tailTrace_3515538
  have hstable : (prefixWord ++ tailWord_3515538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515538).length < 2 ^ (prefixWord ++ tailWord_3515538).sum := by decide
  have hdescent : baseEnd_3515538 < baseStart_3515538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515592 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 2, 4]
def baseStart_3515592 : Nat := 118140960795 + 3515592 * 2 ^ 59
def prefixEnd_3515592 : Nat := 4983230072969 + 3 ^ 40 * 3515592 * 2
def baseEnd_3515592 : Nat := 1203458987400876309221395

theorem tailTrace_3515592 : CollatzResearch.WordTrace tailWord_3515592 prefixEnd_3515592 1203458987400876309221395 := by
  unfold tailWord_3515592
  simp only [CollatzResearch.WordTrace]
  refine ⟨64112087139809037078602515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85482782853078716104803353 64112087139809037078602515)
  ·
    refine ⟨96168130709713555617903773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64112087139809037078602515 96168130709713555617903773)
    ·
      refine ⟨36063049016142583356713915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96168130709713555617903773 36063049016142583356713915)
      ·
        refine ⟨54094573524213875035070873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36063049016142583356713915 54094573524213875035070873)
        ·
          refine ⟨40570930143160406276303155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54094573524213875035070873 40570930143160406276303155)
          ·
            refine ⟨60856395214740609414454733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40570930143160406276303155 60856395214740609414454733)
            ·
              refine ⟨22821148205527728530420525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60856395214740609414454733 22821148205527728530420525)
              ·
                refine ⟨8557930577072898198907697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22821148205527728530420525 8557930577072898198907697)
                ·
                  refine ⟨6418447932804673649180773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8557930577072898198907697 6418447932804673649180773)
                  ·
                    refine ⟨1203458987400876309221395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418447932804673649180773 1203458987400876309221395)
                    ·
                      rfl

theorem cell22_3515592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_3515592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515592 prefixEnd_3515592 := by exact prefixLift 3515592
  have htrace : WordTrace (prefixWord ++ tailWord_3515592) baseStart_3515592 baseEnd_3515592 := by
    simpa [prefixWord, tailWord_3515592, baseEnd_3515592] using wordTrace_append hprefix tailTrace_3515592
  have hstable : (prefixWord ++ tailWord_3515592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515592).length < 2 ^ (prefixWord ++ tailWord_3515592).sum := by decide
  have hdescent : baseEnd_3515592 < baseStart_3515592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515699 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 1, 4]
def baseStart_3515699 : Nat := 118140960795 + 3515699 * 2 ^ 59
def prefixEnd_3515699 : Nat := 4983230072969 + 3 ^ 40 * 3515699 * 2
def baseEnd_3515699 : Nat := 1203495615687563696796067

theorem tailTrace_3515699 : CollatzResearch.WordTrace tailWord_3515699 prefixEnd_3515699 1203495615687563696796067 := by
  unfold tailWord_3515699
  simp only [CollatzResearch.WordTrace]
  refine ⟨128228076890230431431350151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85485384593486954287566767 128228076890230431431350151)
  ·
    refine ⟨192342115335345647147025227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128228076890230431431350151 192342115335345647147025227)
    ·
      refine ⟨288513173003018470720537841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192342115335345647147025227 288513173003018470720537841)
      ·
        refine ⟨216384879752263853040403381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288513173003018470720537841 216384879752263853040403381)
        ·
          refine ⟨20286082476774736222537817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216384879752263853040403381 20286082476774736222537817)
          ·
            refine ⟨15214561857581052166903363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20286082476774736222537817 15214561857581052166903363)
            ·
              refine ⟨22821842786371578250355045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15214561857581052166903363 22821842786371578250355045)
              ·
                refine ⟨4279095522444670921941571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22821842786371578250355045 4279095522444670921941571)
                ·
                  refine ⟨6418643283667006382912357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279095522444670921941571 6418643283667006382912357)
                  ·
                    refine ⟨1203495615687563696796067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418643283667006382912357 1203495615687563696796067)
                    ·
                      rfl

theorem cell22_3515699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 4].length) (baseStart_3515699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515699 prefixEnd_3515699 := by exact prefixLift 3515699
  have htrace : WordTrace (prefixWord ++ tailWord_3515699) baseStart_3515699 baseEnd_3515699 := by
    simpa [prefixWord, tailWord_3515699, baseEnd_3515699] using wordTrace_append hprefix tailTrace_3515699
  have hstable : (prefixWord ++ tailWord_3515699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515699).length < 2 ^ (prefixWord ++ tailWord_3515699).sum := by decide
  have hdescent : baseEnd_3515699 < baseStart_3515699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515712 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 5]
def baseStart_3515712 : Nat := 118140960795 + 3515712 * 2 ^ 59
def prefixEnd_3515712 : Nat := 4983230072969 + 3 ^ 40 * 3515712 * 2
def baseEnd_3515712 : Nat := 1203500065853235996221027

theorem tailTrace_3515712 : CollatzResearch.WordTrace tailWord_3515712 prefixEnd_3515712 1203500065853235996221027 := by
  unfold tailWord_3515712
  simp only [CollatzResearch.WordTrace]
  refine ⟨64114275519591667325786695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85485700692788889767715593 64114275519591667325786695)
  ·
    refine ⟨96171413279387500988680043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64114275519591667325786695 96171413279387500988680043)
    ·
      refine ⟨144257119919081251483020065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96171413279387500988680043 144257119919081251483020065)
      ·
        refine ⟨108192839939310938612265049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144257119919081251483020065 108192839939310938612265049)
        ·
          refine ⟨81144629954483203959198787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108192839939310938612265049 81144629954483203959198787)
          ·
            refine ⟨121716944931724805938798181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81144629954483203959198787 121716944931724805938798181)
            ·
              refine ⟨22821927174698401113524659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121716944931724805938798181 22821927174698401113524659)
              ·
                refine ⟨34232890762047601670286989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22821927174698401113524659 34232890762047601670286989)
                ·
                  refine ⟨12837334035767850626357621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34232890762047601670286989 12837334035767850626357621)
                  ·
                    refine ⟨1203500065853235996221027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12837334035767850626357621 1203500065853235996221027)
                    ·
                      rfl

theorem cell22_3515712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_3515712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515712 prefixEnd_3515712 := by exact prefixLift 3515712
  have htrace : WordTrace (prefixWord ++ tailWord_3515712) baseStart_3515712 baseEnd_3515712 := by
    simpa [prefixWord, tailWord_3515712, baseEnd_3515712] using wordTrace_append hprefix tailTrace_3515712
  have hstable : (prefixWord ++ tailWord_3515712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515712).length < 2 ^ (prefixWord ++ tailWord_3515712).sum := by decide
  have hdescent : baseEnd_3515712 < baseStart_3515712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515729 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 4, 3]
def baseStart_3515729 : Nat := 118140960795 + 3515729 * 2 ^ 59
def prefixEnd_3515729 : Nat := 4983230072969 + 3 ^ 40 * 3515729 * 2
def baseEnd_3515729 : Nat := 1203505885300653618545975

theorem tailTrace_3515729 : CollatzResearch.WordTrace tailWord_3515729 prefixEnd_3515729 1203505885300653618545975 := by
  unfold tailWord_3515729
  simp only [CollatzResearch.WordTrace]
  refine ⟨128229171080121746554942241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85486114053414497703294827 128229171080121746554942241)
  ·
    refine ⟨96171878310091309916206681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128229171080121746554942241 96171878310091309916206681)
    ·
      refine ⟨72128908732568482437155011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96171878310091309916206681 72128908732568482437155011)
      ·
        refine ⟨108193363098852723655732517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72128908732568482437155011 108193363098852723655732517)
        ·
          refine ⟨20286255581034885685449847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108193363098852723655732517 20286255581034885685449847)
          ·
            refine ⟨30429383371552328528174771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20286255581034885685449847 30429383371552328528174771)
            ·
              refine ⟨45644075057328492792262157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30429383371552328528174771 45644075057328492792262157)
              ·
                refine ⟨17116528146498184797098309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45644075057328492792262157 17116528146498184797098309)
                ·
                  refine ⟨3209349027468409649455933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17116528146498184797098309 3209349027468409649455933)
                  ·
                    refine ⟨1203505885300653618545975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209349027468409649455933 1203505885300653618545975)
                    ·
                      rfl

theorem cell22_3515729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_3515729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515729 prefixEnd_3515729 := by exact prefixLift 3515729
  have htrace : WordTrace (prefixWord ++ tailWord_3515729) baseStart_3515729 baseEnd_3515729 := by
    simpa [prefixWord, tailWord_3515729, baseEnd_3515729] using wordTrace_append hprefix tailTrace_3515729
  have hstable : (prefixWord ++ tailWord_3515729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515729).length < 2 ^ (prefixWord ++ tailWord_3515729).sum := by decide
  have hdescent : baseEnd_3515729 < baseStart_3515729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515731 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 4]
def baseStart_3515731 : Nat := 118140960795 + 3515731 * 2 ^ 59
def prefixEnd_3515731 : Nat := 4983230072969 + 3 ^ 40 * 3515731 * 2
def baseEnd_3515731 : Nat := 401168856647175426665323

theorem tailTrace_3515731 : CollatzResearch.WordTrace tailWord_3515731 prefixEnd_3515731 401168856647175426665323 := by
  unfold tailWord_3515731
  simp only [CollatzResearch.WordTrace]
  refine ⟨128229244026114500896515047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85486162684076333931010031 128229244026114500896515047)
  ·
    refine ⟨192343866039171751344772571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128229244026114500896515047 192343866039171751344772571)
    ·
      refine ⟨288515799058757627017158857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192343866039171751344772571 288515799058757627017158857)
      ·
        refine ⟨216386849294068220262869143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288515799058757627017158857 216386849294068220262869143)
        ·
          refine ⟨324580273941102330394303715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216386849294068220262869143 324580273941102330394303715)
          ·
            refine ⟨486870410911653495591455573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324580273941102330394303715 486870410911653495591455573)
            ·
              refine ⟨2852756313935469700731185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 486870410911653495591455573 2852756313935469700731185)
              ·
                refine ⟨2139567235451602275548389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2852756313935469700731185 2139567235451602275548389)
                ·
                  refine ⟨401168856647175426665323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139567235451602275548389 401168856647175426665323)
                  ·
                    rfl

theorem cell22_3515731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 4].length) (baseStart_3515731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515731 prefixEnd_3515731 := by exact prefixLift 3515731
  have htrace : WordTrace (prefixWord ++ tailWord_3515731) baseStart_3515731 baseEnd_3515731 := by
    simpa [prefixWord, tailWord_3515731, baseEnd_3515731] using wordTrace_append hprefix tailTrace_3515731
  have hstable : (prefixWord ++ tailWord_3515731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515731).length < 2 ^ (prefixWord ++ tailWord_3515731).sum := by decide
  have hdescent : baseEnd_3515731 < baseStart_3515731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515778 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3515778 : Nat := 118140960795 + 3515778 * 2 ^ 59
def prefixEnd_3515778 : Nat := 4983230072969 + 3 ^ 40 * 3515778 * 2
def baseEnd_3515778 : Nat := 1203522659002033824070825

theorem tailTrace_3515778 : CollatzResearch.WordTrace tailWord_3515778 prefixEnd_3515778 1203522659002033824070825 := by
  unfold tailWord_3515778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32057739564236056980868997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85487305504629485282317325 32057739564236056980868997)
  ·
    refine ⟨6010826168294260683912937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32057739564236056980868997 6010826168294260683912937)
    ·
      refine ⟨4508119626220695512934703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6010826168294260683912937 4508119626220695512934703)
      ·
        refine ⟨6762179439331043269402055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4508119626220695512934703 6762179439331043269402055)
        ·
          refine ⟨10143269158996564904103083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6762179439331043269402055 10143269158996564904103083)
          ·
            refine ⟨15214903738494847356154625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10143269158996564904103083 15214903738494847356154625)
            ·
              refine ⟨11411177803871135517115969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15214903738494847356154625 11411177803871135517115969)
              ·
                refine ⟨8558383352903351637836977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411177803871135517115969 8558383352903351637836977)
                ·
                  refine ⟨6418787514677513728377733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558383352903351637836977 6418787514677513728377733)
                  ·
                    refine ⟨1203522659002033824070825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6418787514677513728377733 1203522659002033824070825)
                    ·
                      rfl

theorem cell22_3515778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3515778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515778 prefixEnd_3515778 := by exact prefixLift 3515778
  have htrace : WordTrace (prefixWord ++ tailWord_3515778) baseStart_3515778 baseEnd_3515778 := by
    simpa [prefixWord, tailWord_3515778, baseEnd_3515778] using wordTrace_append hprefix tailTrace_3515778
  have hstable : (prefixWord ++ tailWord_3515778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515778).length < 2 ^ (prefixWord ++ tailWord_3515778).sum := by decide
  have hdescent : baseEnd_3515778 < baseStart_3515778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515896 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 2, 4]
def baseStart_3515896 : Nat := 118140960795 + 3515896 * 2 ^ 59
def prefixEnd_3515896 : Nat := 4983230072969 + 3 ^ 40 * 3515896 * 2
def baseEnd_3515896 : Nat := 1203563052813520849620463

theorem tailTrace_3515896 : CollatzResearch.WordTrace tailWord_3515896 prefixEnd_3515896 1203563052813520849620463 := by
  unfold tailWord_3515896
  simp only [CollatzResearch.WordTrace]
  refine ⟨64117631035258367038135771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85490174713677822717514361 64117631035258367038135771)
  ·
    refine ⟨96176446552887550557203657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64117631035258367038135771 96176446552887550557203657)
    ·
      refine ⟨72132334914665662917902743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96176446552887550557203657 72132334914665662917902743)
      ·
        refine ⟨108198502371998494376854115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72132334914665662917902743 108198502371998494376854115)
        ·
          refine ⟨162297753557997741565281173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108198502371998494376854115 162297753557997741565281173)
          ·
            refine ⟨7607707198031144135872555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162297753557997741565281173 7607707198031144135872555)
            ·
              refine ⟨11411560797046716203808833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607707198031144135872555 11411560797046716203808833)
              ·
                refine ⟨8558670597785037152856625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11411560797046716203808833 8558670597785037152856625)
                ·
                  refine ⟨6419002948338777864642469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8558670597785037152856625 6419002948338777864642469)
                  ·
                    refine ⟨1203563052813520849620463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419002948338777864642469 1203563052813520849620463)
                    ·
                      rfl

theorem cell22_3515896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_3515896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515896 prefixEnd_3515896 := by exact prefixLift 3515896
  have htrace : WordTrace (prefixWord ++ tailWord_3515896) baseStart_3515896 baseEnd_3515896 := by
    simpa [prefixWord, tailWord_3515896, baseEnd_3515896] using wordTrace_append hprefix tailTrace_3515896
  have hstable : (prefixWord ++ tailWord_3515896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515896).length < 2 ^ (prefixWord ++ tailWord_3515896).sum := by decide
  have hdescent : baseEnd_3515896 < baseStart_3515896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515911 : List Nat := [1, 1, 4, 3, 2, 2, 2, 7]
def baseStart_3515911 : Nat := 118140960795 + 3515911 * 2 ^ 59
def prefixEnd_3515911 : Nat := 4983230072969 + 3 ^ 40 * 3515911 * 2
def baseEnd_3515911 : Nat := 133729798624451756721713

theorem tailTrace_3515911 : CollatzResearch.WordTrace tailWord_3515911 prefixEnd_3515911 133729798624451756721713 := by
  unfold tailWord_3515911
  simp only [CollatzResearch.WordTrace]
  refine ⟨128235809165462391638067587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85490539443641594425378391 128235809165462391638067587)
  ·
    refine ⟨192353713748193587457101381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128235809165462391638067587 192353713748193587457101381)
    ·
      refine ⟨36066321327786297648206509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192353713748193587457101381 36066321327786297648206509)
      ·
        refine ⟨13524870497919861618077441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36066321327786297648206509 13524870497919861618077441)
        ·
          refine ⟨10143652873439896213558081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13524870497919861618077441 10143652873439896213558081)
          ·
            refine ⟨7607739655079922160168561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10143652873439896213558081 7607739655079922160168561)
            ·
              refine ⟨5705804741309941620126421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607739655079922160168561 5705804741309941620126421)
              ·
                refine ⟨133729798624451756721713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5705804741309941620126421 133729798624451756721713)
                ·
                  rfl

theorem cell22_3515911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 7].length) (baseStart_3515911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515911 prefixEnd_3515911 := by exact prefixLift 3515911
  have htrace : WordTrace (prefixWord ++ tailWord_3515911) baseStart_3515911 baseEnd_3515911 := by
    simpa [prefixWord, tailWord_3515911, baseEnd_3515911] using wordTrace_append hprefix tailTrace_3515911
  have hstable : (prefixWord ++ tailWord_3515911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515911).length < 2 ^ (prefixWord ++ tailWord_3515911).sum := by decide
  have hdescent : baseEnd_3515911 < baseStart_3515911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3515960 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_3515960 : Nat := 118140960795 + 3515960 * 2 ^ 59
def prefixEnd_3515960 : Nat := 4983230072969 + 3 ^ 40 * 3515960 * 2
def baseEnd_3515960 : Nat := 1203584961321446016020267

theorem tailTrace_3515960 : CollatzResearch.WordTrace tailWord_3515960 prefixEnd_3515960 1203584961321446016020267 := by
  unfold tailWord_3515960
  simp only [CollatzResearch.WordTrace]
  refine ⟨64118798171142436503300667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85491730894856582004400889 64118798171142436503300667)
  ·
    refine ⟨96178197256713654754951001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64118798171142436503300667 96178197256713654754951001)
    ·
      refine ⟨72133647942535241066213251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96178197256713654754951001 72133647942535241066213251)
      ·
        refine ⟨108200471913802861599319877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72133647942535241066213251 108200471913802861599319877)
        ·
          refine ⟨20287588483838036549872477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108200471913802861599319877 20287588483838036549872477)
          ·
            refine ⟨7607845681439263706202179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20287588483838036549872477 7607845681439263706202179)
            ·
              refine ⟨11411768522158895559303269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607845681439263706202179 11411768522158895559303269)
              ·
                refine ⟨2139706597904792917369363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11411768522158895559303269 2139706597904792917369363)
                ·
                  refine ⟨3209559896857189376054045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139706597904792917369363 3209559896857189376054045)
                  ·
                    refine ⟨1203584961321446016020267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209559896857189376054045 1203584961321446016020267)
                    ·
                      rfl

theorem cell22_3515960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_3515960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3515960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3515960 prefixEnd_3515960 := by exact prefixLift 3515960
  have htrace : WordTrace (prefixWord ++ tailWord_3515960) baseStart_3515960 baseEnd_3515960 := by
    simpa [prefixWord, tailWord_3515960, baseEnd_3515960] using wordTrace_append hprefix tailTrace_3515960
  have hstable : (prefixWord ++ tailWord_3515960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3515960).length < 2 ^ (prefixWord ++ tailWord_3515960).sum := by decide
  have hdescent : baseEnd_3515960 < baseStart_3515960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3515960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516003 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 1, 4]
def baseStart_3516003 : Nat := 118140960795 + 3516003 * 2 ^ 59
def prefixEnd_3516003 : Nat := 4983230072969 + 3 ^ 40 * 3516003 * 2
def baseEnd_3516003 : Nat := 1203599681100208237195135

theorem tailTrace_3516003 : CollatzResearch.WordTrace tailWord_3516003 prefixEnd_3516003 1203599681100208237195135 := by
  unfold tailWord_3516003
  simp only [CollatzResearch.WordTrace]
  refine ⟨128239164681129091350416663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85492776454086060900277775 128239164681129091350416663)
  ·
    refine ⟨192358747021693637025624995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128239164681129091350416663 192358747021693637025624995)
    ·
      refine ⟨288538120532540455538437493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192358747021693637025624995 288538120532540455538437493)
      ·
        refine ⟨27050448799925667706728515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 288538120532540455538437493 27050448799925667706728515)
        ·
          refine ⟨40575673199888501560092773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27050448799925667706728515 40575673199888501560092773)
          ·
            refine ⟨7607938724979094042517395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40575673199888501560092773 7607938724979094042517395)
            ·
              refine ⟨11411908087468641063776093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7607938724979094042517395 11411908087468641063776093)
              ·
                refine ⟨4279465532800740398916035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11411908087468641063776093 4279465532800740398916035)
                ·
                  refine ⟨6419198299201110598374053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4279465532800740398916035 6419198299201110598374053)
                  ·
                    refine ⟨1203599681100208237195135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419198299201110598374053 1203599681100208237195135)
                    ·
                      rfl

theorem cell22_3516003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 4].length) (baseStart_3516003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516003 prefixEnd_3516003 := by exact prefixLift 3516003
  have htrace : WordTrace (prefixWord ++ tailWord_3516003) baseStart_3516003 baseEnd_3516003 := by
    simpa [prefixWord, tailWord_3516003, baseEnd_3516003] using wordTrace_append hprefix tailTrace_3516003
  have hstable : (prefixWord ++ tailWord_3516003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516003).length < 2 ^ (prefixWord ++ tailWord_3516003).sum := by decide
  have hdescent : baseEnd_3516003 < baseStart_3516003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516018 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3516018 : Nat := 118140960795 + 3516018 * 2 ^ 59
def prefixEnd_3516018 : Nat := 4983230072969 + 3 ^ 40 * 3516018 * 2
def baseEnd_3516018 : Nat := 401201605302251066023363

theorem tailTrace_3516018 : CollatzResearch.WordTrace tailWord_3516018 prefixEnd_3516018 401201605302251066023363 := by
  unfold tailWord_3516018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32059927944018687228053177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85493141184049832608141805 32059927944018687228053177)
  ·
    refine ⟨24044945958014015421039883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32059927944018687228053177 24044945958014015421039883)
    ·
      refine ⟨36067418937021023131559825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24044945958014015421039883 36067418937021023131559825)
      ·
        refine ⟨27050564202765767348669869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36067418937021023131559825 27050564202765767348669869)
        ·
          refine ⟨10143961576037162755751201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27050564202765767348669869 10143961576037162755751201)
          ·
            refine ⟨7607971182027872066813401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10143961576037162755751201 7607971182027872066813401)
            ·
              refine ⟨5705978386520904050110051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7607971182027872066813401 5705978386520904050110051)
              ·
                refine ⟨8558967579781356075165077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5705978386520904050110051 8558967579781356075165077)
                ·
                  refine ⟨401201605302251066023363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8558967579781356075165077 401201605302251066023363)
                  ·
                    rfl

theorem cell22_3516018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3516018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516018 prefixEnd_3516018 := by exact prefixLift 3516018
  have htrace : WordTrace (prefixWord ++ tailWord_3516018) baseStart_3516018 baseEnd_3516018 := by
    simpa [prefixWord, tailWord_3516018, baseEnd_3516018] using wordTrace_append hprefix tailTrace_3516018
  have hstable : (prefixWord ++ tailWord_3516018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516018).length < 2 ^ (prefixWord ++ tailWord_3516018).sum := by decide
  have hdescent : baseEnd_3516018 < baseStart_3516018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516033 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3516033 : Nat := 118140960795 + 3516033 * 2 ^ 59
def prefixEnd_3516033 : Nat := 4983230072969 + 3 ^ 40 * 3516033 * 2
def baseEnd_3516033 : Nat := 1203609950713298158945043

theorem tailTrace_3516033 : CollatzResearch.WordTrace tailWord_3516033 prefixEnd_3516033 1203609950713298158945043 := by
  unfold tailWord_3516033
  simp only [CollatzResearch.WordTrace]
  refine ⟨128240258871020406474008753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85493505914013604316005835 128240258871020406474008753)
  ·
    refine ⟨96180194153265304855506565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128240258871020406474008753 96180194153265304855506565)
    ·
      refine ⟨18033786403737244660407481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96180194153265304855506565 18033786403737244660407481)
      ·
        refine ⟨13525339802802933495305611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18033786403737244660407481 13525339802802933495305611)
        ·
          refine ⟨20288009704204400242958417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13525339802802933495305611 20288009704204400242958417)
          ·
            refine ⟨15216007278153300182218813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20288009704204400242958417 15216007278153300182218813)
            ·
              refine ⟨5706002729307487568332055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15216007278153300182218813 5706002729307487568332055)
              ·
                refine ⟨8559004093961231352498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706002729307487568332055 8559004093961231352498083)
                ·
                  refine ⟨12838506140941847028747125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559004093961231352498083 12838506140941847028747125)
                  ·
                    refine ⟨1203609950713298158945043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12838506140941847028747125 1203609950713298158945043)
                    ·
                      rfl

theorem cell22_3516033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3516033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516033 prefixEnd_3516033 := by exact prefixLift 3516033
  have htrace : WordTrace (prefixWord ++ tailWord_3516033) baseStart_3516033 baseEnd_3516033 := by
    simpa [prefixWord, tailWord_3516033, baseEnd_3516033] using wordTrace_append hprefix tailTrace_3516033
  have hstable : (prefixWord ++ tailWord_3516033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516033).length < 2 ^ (prefixWord ++ tailWord_3516033).sum := by decide
  have hdescent : baseEnd_3516033 < baseStart_3516033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516138 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3516138 : Nat := 118140960795 + 3516138 * 2 ^ 59
def prefixEnd_3516138 : Nat := 4983230072969 + 3 ^ 40 * 3516138 * 2
def baseEnd_3516138 : Nat := 1203645894359112885069721

theorem tailTrace_3516138 : CollatzResearch.WordTrace tailWord_3516138 prefixEnd_3516138 1203645894359112885069721 := by
  unfold tailWord_3516138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32061022133910002351645267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85496059023760006271054045 32061022133910002351645267)
  ·
    refine ⟨48091533200865003527467901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32061022133910002351645267 48091533200865003527467901)
    ·
      refine ⟨18034324950324376322800463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48091533200865003527467901 18034324950324376322800463)
      ·
        refine ⟨27051487425486564484200695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18034324950324376322800463 27051487425486564484200695)
        ·
          refine ⟨40577231138229846726301043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27051487425486564484200695 40577231138229846726301043)
          ·
            refine ⟨60865846707344770089451565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40577231138229846726301043 60865846707344770089451565)
            ·
              refine ⟨22824692515254288783544337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60865846707344770089451565 22824692515254288783544337)
              ·
                refine ⟨17118519386440716587658253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22824692515254288783544337 17118519386440716587658253)
                ·
                  refine ⟨6419444769915268720371845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17118519386440716587658253 6419444769915268720371845)
                  ·
                    refine ⟨1203645894359112885069721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419444769915268720371845 1203645894359112885069721)
                    ·
                      rfl

theorem cell22_3516138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3516138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516138 prefixEnd_3516138 := by exact prefixLift 3516138
  have htrace : WordTrace (prefixWord ++ tailWord_3516138) baseStart_3516138 baseEnd_3516138 := by
    simpa [prefixWord, tailWord_3516138, baseEnd_3516138] using wordTrace_append hprefix tailTrace_3516138
  have hstable : (prefixWord ++ tailWord_3516138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516138).length < 2 ^ (prefixWord ++ tailWord_3516138).sum := by decide
  have hdescent : baseEnd_3516138 < baseStart_3516138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516168 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 5]
def baseStart_3516168 : Nat := 118140960795 + 3516168 * 2 ^ 59
def prefixEnd_3516168 : Nat := 4983230072969 + 3 ^ 40 * 3516168 * 2
def baseEnd_3516168 : Nat := 1203656163972202806819629

theorem tailTrace_3516168 : CollatzResearch.WordTrace tailWord_3516168 prefixEnd_3516168 1203656163972202806819629 := by
  unfold tailWord_3516168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64122591362765662265086579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85496788483687549686782105 64122591362765662265086579)
  ·
    refine ⟨96183887044148493397629869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64122591362765662265086579 96183887044148493397629869)
    ·
      refine ⟨36068957641555685024111201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96183887044148493397629869 36068957641555685024111201)
      ·
        refine ⟨27051718231166763768083401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36068957641555685024111201 27051718231166763768083401)
        ·
          refine ⟨20288788673375072826062551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27051718231166763768083401 20288788673375072826062551)
          ·
            refine ⟨30433183010062609239093827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20288788673375072826062551 30433183010062609239093827)
            ·
              refine ⟨45649774515093913858640741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30433183010062609239093827 45649774515093913858640741)
              ·
                refine ⟨8559332721580108848495139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45649774515093913858640741 8559332721580108848495139)
                ·
                  refine ⟨12838999082370163272742709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8559332721580108848495139 12838999082370163272742709)
                  ·
                    refine ⟨1203656163972202806819629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12838999082370163272742709 1203656163972202806819629)
                    ·
                      rfl

theorem cell22_3516168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_3516168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516168 prefixEnd_3516168 := by exact prefixLift 3516168
  have htrace : WordTrace (prefixWord ++ tailWord_3516168) baseStart_3516168 baseEnd_3516168 := by
    simpa [prefixWord, tailWord_3516168, baseEnd_3516168] using wordTrace_append hprefix tailTrace_3516168
  have hstable : (prefixWord ++ tailWord_3516168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516168).length < 2 ^ (prefixWord ++ tailWord_3516168).sum := by decide
  have hdescent : baseEnd_3516168 < baseStart_3516168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516170 : List Nat := [3, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_3516170 : Nat := 118140960795 + 3516170 * 2 ^ 59
def prefixEnd_3516170 : Nat := 4983230072969 + 3 ^ 40 * 3516170 * 2
def baseEnd_3516170 : Nat := 401218949537691822756541

theorem tailTrace_3516170 : CollatzResearch.WordTrace tailWord_3516170 prefixEnd_3516170 401218949537691822756541 := by
  unfold tailWord_3516170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32061313917881019717936491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85496837114349385914497309 32061313917881019717936491)
  ·
    refine ⟨48091970876821529576904737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32061313917881019717936491 48091970876821529576904737)
    ·
      refine ⟨36068978157616147182678553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48091970876821529576904737 36068978157616147182678553)
      ·
        refine ⟨27051733618212110387008915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36068978157616147182678553 27051733618212110387008915)
        ·
          refine ⟨40577600427318165580513373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27051733618212110387008915 40577600427318165580513373)
          ·
            refine ⟨15216600160244312092692515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40577600427318165580513373 15216600160244312092692515)
            ·
              refine ⟨22824900240366468139038773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15216600160244312092692515 22824900240366468139038773)
              ·
                refine ⟨2139834397534356388034885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22824900240366468139038773 2139834397534356388034885)
                ·
                  refine ⟨401218949537691822756541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139834397534356388034885 401218949537691822756541)
                  ·
                    rfl

theorem cell22_3516170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_3516170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516170 prefixEnd_3516170 := by exact prefixLift 3516170
  have htrace : WordTrace (prefixWord ++ tailWord_3516170) baseStart_3516170 baseEnd_3516170 := by
    simpa [prefixWord, tailWord_3516170, baseEnd_3516170] using wordTrace_append hprefix tailTrace_3516170
  have hstable : (prefixWord ++ tailWord_3516170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516170).length < 2 ^ (prefixWord ++ tailWord_3516170).sum := by decide
  have hdescent : baseEnd_3516170 < baseStart_3516170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516298 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 1, 3]
def baseStart_3516298 : Nat := 118140960795 + 3516298 * 2 ^ 59
def prefixEnd_3516298 : Nat := 4983230072969 + 3 ^ 40 * 3516298 * 2
def baseEnd_3516298 : Nat := 1203700665628925801069231

theorem tailTrace_3516298 : CollatzResearch.WordTrace tailWord_3516298 prefixEnd_3516298 1203700665628925801069231 := by
  unfold tailWord_3516298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32062481053765089183101387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85499949476706904488270365 32062481053765089183101387)
  ·
    refine ⟨48093721580647633774652081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32062481053765089183101387 48093721580647633774652081)
    ·
      refine ⟨36070291185485725330989061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48093721580647633774652081 36070291185485725330989061)
      ·
        refine ⟨6763179597278573499560449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36070291185485725330989061 6763179597278573499560449)
        ·
          refine ⟨5072384697958930124670337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6763179597278573499560449 5072384697958930124670337)
          ·
            refine ⟨3804288523469197593502753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5072384697958930124670337 3804288523469197593502753)
            ·
              refine ⟨2853216392601898195127065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3804288523469197593502753 2853216392601898195127065)
              ·
                refine ⟨2139912294451423646345299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853216392601898195127065 2139912294451423646345299)
                ·
                  refine ⟨3209868441677135469517949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2139912294451423646345299 3209868441677135469517949)
                  ·
                    refine ⟨1203700665628925801069231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209868441677135469517949 1203700665628925801069231)
                    ·
                      rfl

theorem cell22_3516298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_3516298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516298 prefixEnd_3516298 := by exact prefixLift 3516298
  have htrace : WordTrace (prefixWord ++ tailWord_3516298) baseStart_3516298 baseEnd_3516298 := by
    simpa [prefixWord, tailWord_3516298, baseEnd_3516298] using wordTrace_append hprefix tailTrace_3516298
  have hstable : (prefixWord ++ tailWord_3516298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516298).length < 2 ^ (prefixWord ++ tailWord_3516298).sum := by decide
  have hdescent : baseEnd_3516298 < baseStart_3516298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516320 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_3516320 : Nat := 118140960795 + 3516320 * 2 ^ 59
def prefixEnd_3516320 : Nat := 4983230072969 + 3 ^ 40 * 3516320 * 2
def baseEnd_3516320 : Nat := 1203708196678525077019163

theorem tailTrace_3516320 : CollatzResearch.WordTrace tailWord_3516320 prefixEnd_3516320 1203708196678525077019163 := by
  unfold tailWord_3516320
  simp only [CollatzResearch.WordTrace]
  refine ⟨64125363310490327244853207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85500484413987102993137609 64125363310490327244853207)
  ·
    refine ⟨96188044965735490867279811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64125363310490327244853207 96188044965735490867279811)
    ·
      refine ⟨144282067448603236300919717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96188044965735490867279811 144282067448603236300919717)
      ·
        refine ⟨27052887646613106806422447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144282067448603236300919717 27052887646613106806422447)
        ·
          refine ⟨40579331469919660209633671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27052887646613106806422447 40579331469919660209633671)
          ·
            refine ⟨60868997204879490314450507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40579331469919660209633671 60868997204879490314450507)
            ·
              refine ⟨91303495807319235471675761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60868997204879490314450507 91303495807319235471675761)
              ·
                refine ⟨68477621855489426603756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91303495807319235471675761 68477621855489426603756821)
                ·
                  refine ⟨3209888524476066872051101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68477621855489426603756821 3209888524476066872051101)
                  ·
                    refine ⟨1203708196678525077019163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3209888524476066872051101 1203708196678525077019163)
                    ·
                      rfl

theorem cell22_3516320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_3516320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516320 prefixEnd_3516320 := by exact prefixLift 3516320
  have htrace : WordTrace (prefixWord ++ tailWord_3516320) baseStart_3516320 baseEnd_3516320 := by
    simpa [prefixWord, tailWord_3516320, baseEnd_3516320] using wordTrace_append hprefix tailTrace_3516320
  have hstable : (prefixWord ++ tailWord_3516320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516320).length < 2 ^ (prefixWord ++ tailWord_3516320).sum := by decide
  have hdescent : baseEnd_3516320 < baseStart_3516320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516322 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3516322 : Nat := 118140960795 + 3516322 * 2 ^ 59
def prefixEnd_3516322 : Nat := 4983230072969 + 3 ^ 40 * 3516322 * 2
def baseEnd_3516322 : Nat := 401236293773132579489719

theorem tailTrace_3516322 : CollatzResearch.WordTrace tailWord_3516322 prefixEnd_3516322 401236293773132579489719 := by
  unfold tailWord_3516322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32062699891743352207819805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85500533044648939220852813 32062699891743352207819805)
  ·
    refine ⟨12023512459403757077932427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32062699891743352207819805 12023512459403757077932427)
    ·
      refine ⟨18035268689105635616898641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12023512459403757077932427 18035268689105635616898641)
      ·
        refine ⟨13526451516829226712673981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18035268689105635616898641 13526451516829226712673981)
        ·
          refine ⟨5072419318810960017252743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13526451516829226712673981 5072419318810960017252743)
          ·
            refine ⟨7608628978216440025879115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072419318810960017252743 7608628978216440025879115)
            ·
              refine ⟨11412943467324660038818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608628978216440025879115 11412943467324660038818673)
              ·
                refine ⟨8559707600493495029114005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11412943467324660038818673 8559707600493495029114005)
                ·
                  refine ⟨401236293773132579489719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8559707600493495029114005 401236293773132579489719)
                  ·
                    rfl

theorem cell22_3516322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3516322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516322 prefixEnd_3516322 := by exact prefixLift 3516322
  have htrace : WordTrace (prefixWord ++ tailWord_3516322) baseStart_3516322 baseEnd_3516322 := by
    simpa [prefixWord, tailWord_3516322, baseEnd_3516322] using wordTrace_append hprefix tailTrace_3516322
  have hstable : (prefixWord ++ tailWord_3516322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516322).length < 2 ^ (prefixWord ++ tailWord_3516322).sum := by decide
  have hdescent : baseEnd_3516322 < baseStart_3516322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516350 : List Nat := [4, 2, 1, 1, 1, 4, 9]
def baseStart_3516350 : Nat := 118140960795 + 3516350 * 2 ^ 59
def prefixEnd_3516350 : Nat := 4983230072969 + 3 ^ 40 * 3516350 * 2
def baseEnd_3516350 : Nat := 44582165418207962917373

theorem tailTrace_3516350 : CollatzResearch.WordTrace tailWord_3516350 prefixEnd_3516350 44582165418207962917373 := by
  unfold tailWord_3516350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031477601358996201662313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85501213873914646408865669 16031477601358996201662313)
  ·
    refine ⟨12023608201019247151246735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16031477601358996201662313 12023608201019247151246735)
    ·
      refine ⟨18035412301528870726870103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12023608201019247151246735 18035412301528870726870103)
      ·
        refine ⟨27053118452293306090305155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18035412301528870726870103 27053118452293306090305155)
        ·
          refine ⟨40579677678439959135457733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27053118452293306090305155 40579677678439959135457733)
          ·
            refine ⟨7608689564707492337898325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40579677678439959135457733 7608689564707492337898325)
            ·
              refine ⟨44582165418207962917373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7608689564707492337898325 44582165418207962917373)
              ·
                rfl

theorem cell22_3516350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 9].length) (baseStart_3516350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516350 prefixEnd_3516350 := by exact prefixLift 3516350
  have htrace : WordTrace (prefixWord ++ tailWord_3516350) baseStart_3516350 baseEnd_3516350 := by
    simpa [prefixWord, tailWord_3516350, baseEnd_3516350] using wordTrace_append hprefix tailTrace_3516350
  have hstable : (prefixWord ++ tailWord_3516350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516350).length < 2 ^ (prefixWord ++ tailWord_3516350).sum := by decide
  have hdescent : baseEnd_3516350 < baseStart_3516350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516440 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_3516440 : Nat := 118140960795 + 3516440 * 2 ^ 59
def prefixEnd_3516440 : Nat := 4983230072969 + 3 ^ 40 * 3516440 * 2
def baseEnd_3516440 : Nat := 401249758376961588006265

theorem tailTrace_3516440 : CollatzResearch.WordTrace tailWord_3516440 prefixEnd_3516440 401249758376961588006265 := by
  unfold tailWord_3516440
  simp only [CollatzResearch.WordTrace]
  refine ⟨64127551690272957492037387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85503402253697276656049849 64127551690272957492037387)
  ·
    refine ⟨96191327535409436238056081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64127551690272957492037387 96191327535409436238056081)
    ·
      refine ⟨72143495651557077178542061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96191327535409436238056081 72143495651557077178542061)
      ·
        refine ⟨27053810869333903941953273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72143495651557077178542061 27053810869333903941953273)
        ·
          refine ⟨20290358152000427956464955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27053810869333903941953273 20290358152000427956464955)
          ·
            refine ⟨30435537228000641934697433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20290358152000427956464955 30435537228000641934697433)
            ·
              refine ⟨22826652921000481451023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30435537228000641934697433 22826652921000481451023075)
              ·
                refine ⟨34239979381500722176534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22826652921000481451023075 34239979381500722176534613)
                ·
                  refine ⟨401249758376961588006265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34239979381500722176534613 401249758376961588006265)
                  ·
                    rfl

theorem cell22_3516440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_3516440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516440 prefixEnd_3516440 := by exact prefixLift 3516440
  have htrace : WordTrace (prefixWord ++ tailWord_3516440) baseStart_3516440 baseEnd_3516440 := by
    simpa [prefixWord, tailWord_3516440, baseEnd_3516440] using wordTrace_append hprefix tailTrace_3516440
  have hstable : (prefixWord ++ tailWord_3516440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516440).length < 2 ^ (prefixWord ++ tailWord_3516440).sum := by decide
  have hdescent : baseEnd_3516440 < baseStart_3516440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516442 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 3, 4]
def baseStart_3516442 : Nat := 118140960795 + 3516442 * 2 ^ 59
def prefixEnd_3516442 : Nat := 4983230072969 + 3 ^ 40 * 3516442 * 2
def baseEnd_3516442 : Nat := 1203749959771757425468789

theorem tailTrace_3516442 : CollatzResearch.WordTrace tailWord_3516442 prefixEnd_3516442 1203749959771757425468789 := by
  unfold tailWord_3516442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32063794081634667331411895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85503450884359112883765053 32063794081634667331411895)
  ·
    refine ⟨48095691122452000997117843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32063794081634667331411895 48095691122452000997117843)
    ·
      refine ⟨72143536683678001495676765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48095691122452000997117843 72143536683678001495676765)
      ·
        refine ⟨27053826256379250560878787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72143536683678001495676765 27053826256379250560878787)
        ·
          refine ⟨40580739384568875841318181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27053826256379250560878787 40580739384568875841318181)
          ·
            refine ⟨7608888634606664220247159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40580739384568875841318181 7608888634606664220247159)
            ·
              refine ⟨11413332951909996330370739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608888634606664220247159 11413332951909996330370739)
              ·
                refine ⟨17119999427864994495556109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11413332951909996330370739 17119999427864994495556109)
                ·
                  refine ⟨6419999785449372935833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17119999427864994495556109 6419999785449372935833541)
                  ·
                    refine ⟨1203749959771757425468789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6419999785449372935833541 1203749959771757425468789)
                    ·
                      rfl

theorem cell22_3516442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_3516442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516442 prefixEnd_3516442 := by exact prefixLift 3516442
  have htrace : WordTrace (prefixWord ++ tailWord_3516442) baseStart_3516442 baseEnd_3516442 := by
    simpa [prefixWord, tailWord_3516442, baseEnd_3516442] using wordTrace_append hprefix tailTrace_3516442
  have hstable : (prefixWord ++ tailWord_3516442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516442).length < 2 ^ (prefixWord ++ tailWord_3516442).sum := by decide
  have hdescent : baseEnd_3516442 < baseStart_3516442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516504 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 2, 4]
def baseStart_3516504 : Nat := 118140960795 + 3516504 * 2 ^ 59
def prefixEnd_3516504 : Nat := 4983230072969 + 3 ^ 40 * 3516504 * 2
def baseEnd_3516504 : Nat := 1203771183638809930418599

theorem tailTrace_3516504 : CollatzResearch.WordTrace tailWord_3516504 prefixEnd_3516504 1203771183638809930418599 := by
  unfold tailWord_3516504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64128718826157026957202283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85504958434876035942936377 64128718826157026957202283)
  ·
    refine ⟨96193078239235540435803425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64128718826157026957202283 96193078239235540435803425)
    ·
      refine ⟨72144808679426655326852569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96193078239235540435803425 72144808679426655326852569)
      ·
        refine ⟨54108606509569991495139427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72144808679426655326852569 54108606509569991495139427)
        ·
          refine ⟨81162909764354987242709141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54108606509569991495139427 81162909764354987242709141)
          ·
            refine ⟨3804511395204140027001991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81162909764354987242709141 3804511395204140027001991)
            ·
              refine ⟨5706767092806210040502987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804511395204140027001991 5706767092806210040502987)
              ·
                refine ⟨8560150639209315060754481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5706767092806210040502987 8560150639209315060754481)
                ·
                  refine ⟨6420112979406986295565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8560150639209315060754481 6420112979406986295565861)
                  ·
                    refine ⟨1203771183638809930418599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420112979406986295565861 1203771183638809930418599)
                    ·
                      rfl

theorem cell22_3516504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_3516504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516504 prefixEnd_3516504 := by exact prefixLift 3516504
  have htrace : WordTrace (prefixWord ++ tailWord_3516504) baseStart_3516504 baseEnd_3516504 := by
    simpa [prefixWord, tailWord_3516504, baseEnd_3516504] using wordTrace_append hprefix tailTrace_3516504
  have hstable : (prefixWord ++ tailWord_3516504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516504).length < 2 ^ (prefixWord ++ tailWord_3516504).sum := by decide
  have hdescent : baseEnd_3516504 < baseStart_3516504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516607 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 5]
def baseStart_3516607 : Nat := 118140960795 + 3516607 * 2 ^ 59
def prefixEnd_3516607 : Nat := 4983230072969 + 3 ^ 40 * 3516607 * 2
def baseEnd_3516607 : Nat := 1203806442643751995093283

theorem tailTrace_3516607 : CollatzResearch.WordTrace tailWord_3516607 prefixEnd_3516607 1203806442643751995093283 := by
  unfold tailWord_3516607
  simp only [CollatzResearch.WordTrace]
  refine ⟨128261194370940902505404075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85507462913960601670269383 128261194370940902505404075)
  ·
    refine ⟨192391791556411353758106113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128261194370940902505404075 192391791556411353758106113)
    ·
      refine ⟨144293843667308515318579585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192391791556411353758106113 144293843667308515318579585)
      ·
        refine ⟨108220382750481386488934689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144293843667308515318579585 108220382750481386488934689)
        ·
          refine ⟨81165287062861039866701017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108220382750481386488934689 81165287062861039866701017)
          ·
            refine ⟨60873965297145779900025763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81165287062861039866701017 60873965297145779900025763)
            ·
              refine ⟨91310947945718669850038645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60873965297145779900025763 91310947945718669850038645)
              ·
                refine ⟨8560401369911125298441123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91310947945718669850038645 8560401369911125298441123)
                ·
                  refine ⟨12840602054866687947661685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8560401369911125298441123 12840602054866687947661685)
                  ·
                    refine ⟨1203806442643751995093283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12840602054866687947661685 1203806442643751995093283)
                    ·
                      rfl

theorem cell22_3516607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_3516607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516607 prefixEnd_3516607 := by exact prefixLift 3516607
  have htrace : WordTrace (prefixWord ++ tailWord_3516607) baseStart_3516607 baseEnd_3516607 := by
    simpa [prefixWord, tailWord_3516607, baseEnd_3516607] using wordTrace_append hprefix tailTrace_3516607
  have hstable : (prefixWord ++ tailWord_3516607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516607).length < 2 ^ (prefixWord ++ tailWord_3516607).sum := by decide
  have hdescent : baseEnd_3516607 < baseStart_3516607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516641 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3516641 : Nat := 118140960795 + 3516641 * 2 ^ 59
def prefixEnd_3516641 : Nat := 4983230072969 + 3 ^ 40 * 3516641 * 2
def baseEnd_3516641 : Nat := 1203818081538587239743179

theorem tailTrace_3516641 : CollatzResearch.WordTrace tailWord_3516641 prefixEnd_3516641 1203818081538587239743179 := by
  unfold tailWord_3516641
  simp only [CollatzResearch.WordTrace]
  refine ⟨128262434452817726312141777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85508289635211817541427851 128262434452817726312141777)
  ·
    refine ⟨96196825839613294734106333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128262434452817726312141777 96196825839613294734106333)
    ·
      refine ⟨36073809689854985525289875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96196825839613294734106333 36073809689854985525289875)
      ·
        refine ⟨54110714534782478287934813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36073809689854985525289875 54110714534782478287934813)
        ·
          refine ⟨20291517950543429357975555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54110714534782478287934813 20291517950543429357975555)
          ·
            refine ⟨30437276925815144036963333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20291517950543429357975555 30437276925815144036963333)
            ·
              refine ⟨5706989423590339506930625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30437276925815144036963333 5706989423590339506930625)
              ·
                refine ⟨4280242067692754630197969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5706989423590339506930625 4280242067692754630197969)
                ·
                  refine ⟨3210181550769565972648477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4280242067692754630197969 3210181550769565972648477)
                  ·
                    refine ⟨1203818081538587239743179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210181550769565972648477 1203818081538587239743179)
                    ·
                      rfl

theorem cell22_3516641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3516641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516641 prefixEnd_3516641 := by exact prefixLift 3516641
  have htrace : WordTrace (prefixWord ++ tailWord_3516641) baseStart_3516641 baseEnd_3516641 := by
    simpa [prefixWord, tailWord_3516641, baseEnd_3516641] using wordTrace_append hprefix tailTrace_3516641
  have hstable : (prefixWord ++ tailWord_3516641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516641).length < 2 ^ (prefixWord ++ tailWord_3516641).sum := by decide
  have hdescent : baseEnd_3516641 < baseStart_3516641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516643 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 4]
def baseStart_3516643 : Nat := 118140960795 + 3516643 * 2 ^ 59
def prefixEnd_3516643 : Nat := 4983230072969 + 3 ^ 40 * 3516643 * 2
def baseEnd_3516643 : Nat := 401272922059819967064391

theorem tailTrace_3516643 : CollatzResearch.WordTrace tailWord_3516643 prefixEnd_3516643 401272922059819967064391 := by
  unfold tailWord_3516643
  simp only [CollatzResearch.WordTrace]
  refine ⟨128262507398810480653714583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85508338265873653769143055 128262507398810480653714583)
  ·
    refine ⟨192393761098215720980571875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128262507398810480653714583 192393761098215720980571875)
    ·
      refine ⟨288590641647323581470857813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192393761098215720980571875 288590641647323581470857813)
      ·
        refine ⟨3381921581804573220361615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 288590641647323581470857813 3381921581804573220361615)
        ·
          refine ⟨5072882372706859830542423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381921581804573220361615 5072882372706859830542423)
          ·
            refine ⟨7609323559060289745813635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072882372706859830542423 7609323559060289745813635)
            ·
              refine ⟨11413985338590434618720453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609323559060289745813635 11413985338590434618720453)
              ·
                refine ⟨2140122250985706491010085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11413985338590434618720453 2140122250985706491010085)
                ·
                  refine ⟨401272922059819967064391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140122250985706491010085 401272922059819967064391)
                  ·
                    rfl

theorem cell22_3516643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 4].length) (baseStart_3516643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516643 prefixEnd_3516643 := by exact prefixLift 3516643
  have htrace : WordTrace (prefixWord ++ tailWord_3516643) baseStart_3516643 baseEnd_3516643 := by
    simpa [prefixWord, tailWord_3516643, baseEnd_3516643] using wordTrace_append hprefix tailTrace_3516643
  have hstable : (prefixWord ++ tailWord_3516643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516643).length < 2 ^ (prefixWord ++ tailWord_3516643).sum := by decide
  have hdescent : baseEnd_3516643 < baseStart_3516643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516699 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 5]
def baseStart_3516699 : Nat := 118140960795 + 3516699 * 2 ^ 59
def prefixEnd_3516699 : Nat := 4983230072969 + 3 ^ 40 * 3516699 * 2
def baseEnd_3516699 : Nat := 401279312041298140597667

theorem tailTrace_3516699 : CollatzResearch.WordTrace tailWord_3516699 prefixEnd_3516699 401279312041298140597667 := by
  unfold tailWord_3516699
  simp only [CollatzResearch.WordTrace]
  refine ⟨128264549886607602217753151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85509699924405068145168767 128264549886607602217753151)
  ·
    refine ⟨192396824829911403326629727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128264549886607602217753151 192396824829911403326629727)
    ·
      refine ⟨288595237244867104989944591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192396824829911403326629727 288595237244867104989944591)
      ·
        refine ⟨432892855867300657484916887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288595237244867104989944591 432892855867300657484916887)
        ·
          refine ⟨649339283800950986227375331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432892855867300657484916887 649339283800950986227375331)
          ·
            refine ⟨974008925701426479341062997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649339283800950986227375331 974008925701426479341062997)
            ·
              refine ⟨5707083549031795777389041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 974008925701426479341062997 5707083549031795777389041)
              ·
                refine ⟨4280312661773846833041781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707083549031795777389041 4280312661773846833041781)
                ·
                  refine ⟨401279312041298140597667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280312661773846833041781 401279312041298140597667)
                  ·
                    rfl

theorem cell22_3516699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 5].length) (baseStart_3516699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516699 prefixEnd_3516699 := by exact prefixLift 3516699
  have htrace : WordTrace (prefixWord ++ tailWord_3516699) baseStart_3516699 baseEnd_3516699 := by
    simpa [prefixWord, tailWord_3516699, baseEnd_3516699] using wordTrace_append hprefix tailTrace_3516699
  have hstable : (prefixWord ++ tailWord_3516699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516699).length < 2 ^ (prefixWord ++ tailWord_3516699).sum := by decide
  have hdescent : baseEnd_3516699 < baseStart_3516699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516703 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 1, 3]
def baseStart_3516703 : Nat := 118140960795 + 3516703 * 2 ^ 59
def prefixEnd_3516703 : Nat := 4983230072969 + 3 ^ 40 * 3516703 * 2
def baseEnd_3516703 : Nat := 1203839305405639744692989

theorem tailTrace_3516703 : CollatzResearch.WordTrace tailWord_3516703 prefixEnd_3516703 1203839305405639744692989 := by
  unfold tailWord_3516703
  simp only [CollatzResearch.WordTrace]
  refine ⟨128264695778593110900898763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85509797185728740600599175 128264695778593110900898763)
  ·
    refine ⟨192397043667889666351348145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128264695778593110900898763 192397043667889666351348145)
    ·
      refine ⟨144297782750917249763511109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192397043667889666351348145 144297782750917249763511109)
      ·
        refine ⟨27055834265796984330658333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144297782750917249763511109 27055834265796984330658333)
        ·
          refine ⟨10145937849673869123996875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27055834265796984330658333 10145937849673869123996875)
          ·
            refine ⟨15218906774510803685995313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10145937849673869123996875 15218906774510803685995313)
            ·
              refine ⟨11414180080883102764496485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15218906774510803685995313 11414180080883102764496485)
              ·
                refine ⟨2140158765165581768343091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11414180080883102764496485 2140158765165581768343091)
                ·
                  refine ⟨3210238147748372652514637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140158765165581768343091 3210238147748372652514637)
                  ·
                    refine ⟨1203839305405639744692989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210238147748372652514637 1203839305405639744692989)
                    ·
                      rfl

theorem cell22_3516703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 3].length) (baseStart_3516703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516703 prefixEnd_3516703 := by exact prefixLift 3516703
  have htrace : WordTrace (prefixWord ++ tailWord_3516703) baseStart_3516703 baseEnd_3516703 := by
    simpa [prefixWord, tailWord_3516703, baseEnd_3516703] using wordTrace_append hprefix tailTrace_3516703
  have hstable : (prefixWord ++ tailWord_3516703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516703).length < 2 ^ (prefixWord ++ tailWord_3516703).sum := by decide
  have hdescent : baseEnd_3516703 < baseStart_3516703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516737 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3516737 : Nat := 118140960795 + 3516737 * 2 ^ 59
def prefixEnd_3516737 : Nat := 4983230072969 + 3 ^ 40 * 3516737 * 2
def baseEnd_3516737 : Nat := 1203850944300474989342885

theorem tailTrace_3516737 : CollatzResearch.WordTrace tailWord_3516737 prefixEnd_3516737 1203850944300474989342885 := by
  unfold tailWord_3516737
  simp only [CollatzResearch.WordTrace]
  refine ⟨128265935860469934707636465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85510623906979956471757643 128265935860469934707636465)
  ·
    refine ⟨96199451895352451030727349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128265935860469934707636465 96199451895352451030727349)
    ·
      refine ⟨9018698615189292284130689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96199451895352451030727349 9018698615189292284130689)
      ·
        refine ⟨6764023961391969213098017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9018698615189292284130689 6764023961391969213098017)
        ·
          refine ⟨5073017971043976909823513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764023961391969213098017 5073017971043976909823513)
          ·
            refine ⟨3804763478282982682367635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5073017971043976909823513 3804763478282982682367635)
            ·
              refine ⟨5707145217424474023551453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804763478282982682367635 5707145217424474023551453)
              ·
                refine ⟨2140179456534177758831795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5707145217424474023551453 2140179456534177758831795)
                ·
                  refine ⟨3210269184801266638247693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140179456534177758831795 3210269184801266638247693)
                  ·
                    refine ⟨1203850944300474989342885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210269184801266638247693 1203850944300474989342885)
                    ·
                      rfl

theorem cell22_3516737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3516737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516737 prefixEnd_3516737 := by exact prefixLift 3516737
  have htrace : WordTrace (prefixWord ++ tailWord_3516737) baseStart_3516737 baseEnd_3516737 := by
    simpa [prefixWord, tailWord_3516737, baseEnd_3516737] using wordTrace_append hprefix tailTrace_3516737
  have hstable : (prefixWord ++ tailWord_3516737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516737).length < 2 ^ (prefixWord ++ tailWord_3516737).sum := by decide
  have hdescent : baseEnd_3516737 < baseStart_3516737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516780 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 1, 4]
def baseStart_3516780 : Nat := 118140960795 + 3516780 * 2 ^ 59
def prefixEnd_3516780 : Nat := 4983230072969 + 3 ^ 40 * 3516780 * 2
def baseEnd_3516780 : Nat := 1203865664079237210517753

theorem tailTrace_3516780 : CollatzResearch.WordTrace tailWord_3516780 prefixEnd_3516780 1203865664079237210517753 := by
  unfold tailWord_3516780
  simp only [CollatzResearch.WordTrace]
  refine ⟨64133752099657076525725897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85511669466209435367634529 64133752099657076525725897)
  ·
    refine ⟨48100314074742807394294423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64133752099657076525725897 48100314074742807394294423)
    ·
      refine ⟨72150471112114211091441635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48100314074742807394294423 72150471112114211091441635)
      ·
        refine ⟨108225706668171316637162453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72150471112114211091441635 108225706668171316637162453)
        ·
          refine ⟨2536540000035265233683495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 108225706668171316637162453 2536540000035265233683495)
          ·
            refine ⟨3804810000052897850525243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2536540000035265233683495 3804810000052897850525243)
            ·
              refine ⟨5707215000079346775787865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3804810000052897850525243 5707215000079346775787865)
              ·
                refine ⟨4280411250059510081840899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707215000079346775787865 4280411250059510081840899)
                ·
                  refine ⟨6420616875089265122761349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280411250059510081840899 6420616875089265122761349)
                  ·
                    refine ⟨1203865664079237210517753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420616875089265122761349 1203865664079237210517753)
                    ·
                      rfl

theorem cell22_3516780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_3516780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516780 prefixEnd_3516780 := by exact prefixLift 3516780
  have htrace : WordTrace (prefixWord ++ tailWord_3516780) baseStart_3516780 baseEnd_3516780 := by
    simpa [prefixWord, tailWord_3516780, baseEnd_3516780] using wordTrace_append hprefix tailTrace_3516780
  have hstable : (prefixWord ++ tailWord_3516780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516780).length < 2 ^ (prefixWord ++ tailWord_3516780).sum := by decide
  have hdescent : baseEnd_3516780 < baseStart_3516780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516821 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 3, 3]
def baseStart_3516821 : Nat := 118140960795 + 3516821 * 2 ^ 59
def prefixEnd_3516821 : Nat := 4983230072969 + 3 ^ 40 * 3516821 * 2
def baseEnd_3516821 : Nat := 1203879699217126770242627

theorem tailTrace_3516821 : CollatzResearch.WordTrace tailWord_3516821 prefixEnd_3516821 1203879699217126770242627 := by
  unfold tailWord_3516821
  simp only [CollatzResearch.WordTrace]
  refine ⟨128268999592165617053694317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85512666394777078035796211 128268999592165617053694317)
  ·
    refine ⟨48100874847062106395135369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128268999592165617053694317 48100874847062106395135369)
    ·
      refine ⟨36075656135296579796351527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48100874847062106395135369 36075656135296579796351527)
      ·
        refine ⟨54113484202944869694527291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36075656135296579796351527 54113484202944869694527291)
        ·
          refine ⟨81170226304417304541790937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54113484202944869694527291 81170226304417304541790937)
          ·
            refine ⟨60877669728312978406343203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81170226304417304541790937 60877669728312978406343203)
            ·
              refine ⟨91316504592469467609514805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60877669728312978406343203 91316504592469467609514805)
              ·
                refine ⟨8560922305544012588392013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91316504592469467609514805 8560922305544012588392013)
                ·
                  refine ⟨3210345864579004720647005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8560922305544012588392013 3210345864579004720647005)
                  ·
                    refine ⟨1203879699217126770242627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210345864579004720647005 1203879699217126770242627)
                    ·
                      rfl

theorem cell22_3516821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_3516821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516821 prefixEnd_3516821 := by exact prefixLift 3516821
  have htrace : WordTrace (prefixWord ++ tailWord_3516821) baseStart_3516821 baseEnd_3516821 := by
    simpa [prefixWord, tailWord_3516821, baseEnd_3516821] using wordTrace_append hprefix tailTrace_3516821
  have hstable : (prefixWord ++ tailWord_3516821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516821).length < 2 ^ (prefixWord ++ tailWord_3516821).sum := by decide
  have hdescent : baseEnd_3516821 < baseStart_3516821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516855 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 1, 3]
def baseStart_3516855 : Nat := 118140960795 + 3516855 * 2 ^ 59
def prefixEnd_3516855 : Nat := 4983230072969 + 3 ^ 40 * 3516855 * 2
def baseEnd_3516855 : Nat := 1203891338111962014892523

theorem tailTrace_3516855 : CollatzResearch.WordTrace tailWord_3516855 prefixEnd_3516855 1203891338111962014892523 := by
  unfold tailWord_3516855
  simp only [CollatzResearch.WordTrace]
  refine ⟨128270239674042440860432019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85513493116028293906954679 128270239674042440860432019)
  ·
    refine ⟨192405359511063661290648029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128270239674042440860432019 192405359511063661290648029)
    ·
      refine ⟨72152009816648872983993011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192405359511063661290648029 72152009816648872983993011)
      ·
        refine ⟨108228014724973309475989517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72152009816648872983993011 108228014724973309475989517)
        ·
          refine ⟨40585505521864991053496069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108228014724973309475989517 40585505521864991053496069)
          ·
            refine ⟨7609782285349685822530513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40585505521864991053496069 7609782285349685822530513)
            ·
              refine ⟨5707336714012264366897885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7609782285349685822530513 5707336714012264366897885)
              ·
                refine ⟨2140251267754599137586707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5707336714012264366897885 2140251267754599137586707)
                ·
                  refine ⟨3210376901631898706380061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2140251267754599137586707 3210376901631898706380061)
                  ·
                    refine ⟨1203891338111962014892523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210376901631898706380061 1203891338111962014892523)
                    ·
                      rfl

theorem cell22_3516855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_3516855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516855 prefixEnd_3516855 := by exact prefixLift 3516855
  have htrace : WordTrace (prefixWord ++ tailWord_3516855) baseStart_3516855 baseEnd_3516855 := by
    simpa [prefixWord, tailWord_3516855, baseEnd_3516855] using wordTrace_append hprefix tailTrace_3516855
  have hstable : (prefixWord ++ tailWord_3516855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516855).length < 2 ^ (prefixWord ++ tailWord_3516855).sum := by decide
  have hdescent : baseEnd_3516855 < baseStart_3516855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516868 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3516868 : Nat := 118140960795 + 3516868 * 2 ^ 59
def prefixEnd_3516868 : Nat := 4983230072969 + 3 ^ 40 * 3516868 * 2
def baseEnd_3516868 : Nat := 401298596092544771439161

theorem tailTrace_3516868 : CollatzResearch.WordTrace tailWord_3516868 prefixEnd_3516868 401298596092544771439161 := by
  unfold tailWord_3516868
  simp only [CollatzResearch.WordTrace]
  refine ⟨64135356911497672040327629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85513809215330229387103505 64135356911497672040327629)
  ·
    refine ⟨24050758841811627015122861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64135356911497672040327629 24050758841811627015122861)
    ·
      refine ⟨9019034565679360130671073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24050758841811627015122861 9019034565679360130671073)
      ·
        refine ⟨6764275924259520098003305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9019034565679360130671073 6764275924259520098003305)
        ·
          refine ⟨5073206943194640073502479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764275924259520098003305 5073206943194640073502479)
          ·
            refine ⟨7609810414791960110253719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073206943194640073502479 7609810414791960110253719)
            ·
              refine ⟨11414715622187940165380579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7609810414791960110253719 11414715622187940165380579)
              ·
                refine ⟨17122073433281910248070869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11414715622187940165380579 17122073433281910248070869)
                ·
                  refine ⟨401298596092544771439161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17122073433281910248070869 401298596092544771439161)
                  ·
                    rfl

theorem cell22_3516868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3516868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516868 prefixEnd_3516868 := by exact prefixLift 3516868
  have htrace : WordTrace (prefixWord ++ tailWord_3516868) baseStart_3516868 baseEnd_3516868 := by
    simpa [prefixWord, tailWord_3516868, baseEnd_3516868] using wordTrace_append hprefix tailTrace_3516868
  have hstable : (prefixWord ++ tailWord_3516868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516868).length < 2 ^ (prefixWord ++ tailWord_3516868).sum := by decide
  have hdescent : baseEnd_3516868 < baseStart_3516868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3516960 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_3516960 : Nat := 118140960795 + 3516960 * 2 ^ 59
def prefixEnd_3516960 : Nat := 4983230072969 + 3 ^ 40 * 3516960 * 2
def baseEnd_3516960 : Nat := 1203927281757776741017201

theorem tailTrace_3516960 : CollatzResearch.WordTrace tailWord_3516960 prefixEnd_3516960 1203927281757776741017201 := by
  unfold tailWord_3516960
  simp only [CollatzResearch.WordTrace]
  refine ⟨64137034669331021896502167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85516046225774695862002889 64137034669331021896502167)
  ·
    refine ⟨96205552003996532844753251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64137034669331021896502167 96205552003996532844753251)
    ·
      refine ⟨144308328005994799267129877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96205552003996532844753251 144308328005994799267129877)
      ·
        refine ⟨6764452875281006215646713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144308328005994799267129877 6764452875281006215646713)
        ·
          refine ⟨5073339656460754661735035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6764452875281006215646713 5073339656460754661735035)
          ·
            refine ⟨7610009484691131992602553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073339656460754661735035 7610009484691131992602553)
            ·
              refine ⟨5707507113518348994451915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610009484691131992602553 5707507113518348994451915)
              ·
                refine ⟨8561260670277523491677873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5707507113518348994451915 8561260670277523491677873)
                ·
                  refine ⟨6420945502708142618758405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8561260670277523491677873 6420945502708142618758405)
                  ·
                    refine ⟨1203927281757776741017201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6420945502708142618758405 1203927281757776741017201)
                    ·
                      rfl

theorem cell22_3516960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_3516960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3516960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3516960 prefixEnd_3516960 := by exact prefixLift 3516960
  have htrace : WordTrace (prefixWord ++ tailWord_3516960) baseStart_3516960 baseEnd_3516960 := by
    simpa [prefixWord, tailWord_3516960, baseEnd_3516960] using wordTrace_append hprefix tailTrace_3516960
  have hstable : (prefixWord ++ tailWord_3516960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3516960).length < 2 ^ (prefixWord ++ tailWord_3516960).sum := by decide
  have hdescent : baseEnd_3516960 < baseStart_3516960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3516960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517031 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 10]
def baseStart_3517031 : Nat := 118140960795 + 3517031 * 2 ^ 59
def prefixEnd_3517031 : Nat := 4983230072969 + 3 ^ 40 * 3517031 * 2
def baseEnd_3517031 : Nat := 401317195502918740830661

theorem tailTrace_3517031 : CollatzResearch.WordTrace tailWord_3517031 prefixEnd_3517031 401317195502918740830661 := by
  unfold tailWord_3517031
  simp only [CollatzResearch.WordTrace]
  refine ⟨128276658921404822918838947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85517772614269881945892631 128276658921404822918838947)
  ·
    refine ⟨192414988382107234378258421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128276658921404822918838947 192414988382107234378258421)
    ·
      refine ⟨18038905160822553222961727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 192414988382107234378258421 18038905160822553222961727)
      ·
        refine ⟨27058357741233829834442591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18038905160822553222961727 27058357741233829834442591)
        ·
          refine ⟨40587536611850744751663887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27058357741233829834442591 40587536611850744751663887)
          ·
            refine ⟨60881304917776117127495831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40587536611850744751663887 60881304917776117127495831)
            ·
              refine ⟨91321957376664175691243747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60881304917776117127495831 91321957376664175691243747)
              ·
                refine ⟨136982936064996263536865621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91321957376664175691243747 136982936064996263536865621)
                ·
                  refine ⟨401317195502918740830661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 136982936064996263536865621 401317195502918740830661)
                  ·
                    rfl

theorem cell22_3517031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 10].length) (baseStart_3517031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517031 prefixEnd_3517031 := by exact prefixLift 3517031
  have htrace : WordTrace (prefixWord ++ tailWord_3517031) baseStart_3517031 baseEnd_3517031 := by
    simpa [prefixWord, tailWord_3517031, baseEnd_3517031] using wordTrace_append hprefix tailTrace_3517031
  have hstable : (prefixWord ++ tailWord_3517031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517031).length < 2 ^ (prefixWord ++ tailWord_3517031).sum := by decide
  have hdescent : baseEnd_3517031 < baseStart_3517031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517155 : List Nat := [1, 1, 1, 7, 1, 1, 1, 4, 5]
def baseStart_3517155 : Nat := 118140960795 + 3517155 * 2 ^ 59
def prefixEnd_3517155 : Nat := 4983230072969 + 3 ^ 40 * 3517155 * 2
def baseEnd_3517155 : Nat := 401331344747620410797201

theorem tailTrace_3517155 : CollatzResearch.WordTrace tailWord_3517155 prefixEnd_3517155 401331344747620410797201 := by
  unfold tailWord_3517155
  simp only [CollatzResearch.WordTrace]
  refine ⟨128281181572955592096352919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85520787715303728064235279 128281181572955592096352919)
  ·
    refine ⟨192421772359433388144529379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128281181572955592096352919 192421772359433388144529379)
    ·
      refine ⟨288632658539150082216794069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192421772359433388144529379 288632658539150082216794069)
      ·
        refine ⟨6764827934511330051956111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 288632658539150082216794069 6764827934511330051956111)
        ·
          refine ⟨10147241901766995077934167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764827934511330051956111 10147241901766995077934167)
          ·
            refine ⟨15220862852650492616901251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10147241901766995077934167 15220862852650492616901251)
            ·
              refine ⟨22831294278975738925351877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15220862852650492616901251 22831294278975738925351877)
              ·
                refine ⟨4280867677307951048503477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22831294278975738925351877 4280867677307951048503477)
                ·
                  refine ⟨401331344747620410797201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280867677307951048503477 401331344747620410797201)
                  ·
                    rfl

theorem cell22_3517155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 5].length) (baseStart_3517155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517155 prefixEnd_3517155 := by exact prefixLift 3517155
  have htrace : WordTrace (prefixWord ++ tailWord_3517155) baseStart_3517155 baseEnd_3517155 := by
    simpa [prefixWord, tailWord_3517155, baseEnd_3517155] using wordTrace_append hprefix tailTrace_3517155
  have hstable : (prefixWord ++ tailWord_3517155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517155).length < 2 ^ (prefixWord ++ tailWord_3517155).sum := by decide
  have hdescent : baseEnd_3517155 < baseStart_3517155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517168 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_3517168 : Nat := 118140960795 + 3517168 * 2 ^ 59
def prefixEnd_3517168 : Nat := 4983230072969 + 3 ^ 40 * 3517168 * 2
def baseEnd_3517168 : Nat := 1203998484408533531816563

theorem tailTrace_3517168 : CollatzResearch.WordTrace tailWord_3517168 prefixEnd_3517168 1203998484408533531816563 := by
  unfold tailWord_3517168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64140827860954247658288079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85521103814605663544384105 64140827860954247658288079)
  ·
    refine ⟨96211241791431371487432119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64140827860954247658288079 96211241791431371487432119)
    ·
      refine ⟨144316862687147057231148179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96211241791431371487432119 144316862687147057231148179)
      ·
        refine ⟨216475294030720585846722269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144316862687147057231148179 216475294030720585846722269)
        ·
          refine ⟨81178235261520219692520851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216475294030720585846722269 81178235261520219692520851)
          ·
            refine ⟨121767352892280329538781277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81178235261520219692520851 121767352892280329538781277)
            ·
              refine ⟨45662757334605123577042979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121767352892280329538781277 45662757334605123577042979)
              ·
                refine ⟨68494136001907685365564469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45662757334605123577042979 68494136001907685365564469)
                ·
                  refine ⟨6421325250178845503021669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68494136001907685365564469 6421325250178845503021669)
                  ·
                    refine ⟨1203998484408533531816563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421325250178845503021669 1203998484408533531816563)
                    ·
                      rfl

theorem cell22_3517168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_3517168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517168 prefixEnd_3517168 := by exact prefixLift 3517168
  have htrace : WordTrace (prefixWord ++ tailWord_3517168) baseStart_3517168 baseEnd_3517168 := by
    simpa [prefixWord, tailWord_3517168, baseEnd_3517168] using wordTrace_append hprefix tailTrace_3517168
  have hstable : (prefixWord ++ tailWord_3517168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517168).length < 2 ^ (prefixWord ++ tailWord_3517168).sum := by decide
  have hdescent : baseEnd_3517168 < baseStart_3517168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517170 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 5]
def baseStart_3517170 : Nat := 118140960795 + 3517170 * 2 ^ 59
def prefixEnd_3517170 : Nat := 4983230072969 + 3 ^ 40 * 3517170 * 2
def baseEnd_3517170 : Nat := 1203999169049406193266557

theorem tailTrace_3517170 : CollatzResearch.WordTrace tailWord_3517170 prefixEnd_3517170 1203999169049406193266557 := by
  unfold tailWord_3517170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070432166975312414537241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85521152445267499772099309 32070432166975312414537241)
  ·
    refine ⟨24052824125231484310902931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32070432166975312414537241 24052824125231484310902931)
    ·
      refine ⟨36079236187847226466354397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24052824125231484310902931 36079236187847226466354397)
      ·
        refine ⟨13529713570442709924882899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36079236187847226466354397 13529713570442709924882899)
        ·
          refine ⟨20294570355664064887324349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13529713570442709924882899 20294570355664064887324349)
          ·
            refine ⟨7610463883374024332746631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20294570355664064887324349 7610463883374024332746631)
            ·
              refine ⟨11415695825061036499119947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610463883374024332746631 11415695825061036499119947)
              ·
                refine ⟨17123543737591554748679921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11415695825061036499119947 17123543737591554748679921)
                ·
                  refine ⟨12842657803193666061509941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17123543737591554748679921 12842657803193666061509941)
                  ·
                    refine ⟨1203999169049406193266557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12842657803193666061509941 1203999169049406193266557)
                    ·
                      rfl

theorem cell22_3517170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_3517170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517170 prefixEnd_3517170 := by exact prefixLift 3517170
  have htrace : WordTrace (prefixWord ++ tailWord_3517170) baseStart_3517170 baseEnd_3517170 := by
    simpa [prefixWord, tailWord_3517170, baseEnd_3517170] using wordTrace_append hprefix tailTrace_3517170
  have hstable : (prefixWord ++ tailWord_3517170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517170).length < 2 ^ (prefixWord ++ tailWord_3517170).sum := by decide
  have hdescent : baseEnd_3517170 < baseStart_3517170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517185 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3517185 : Nat := 118140960795 + 3517185 * 2 ^ 59
def prefixEnd_3517185 : Nat := 4983230072969 + 3 ^ 40 * 3517185 * 2
def baseEnd_3517185 : Nat := 1204004303855951154141511

theorem tailTrace_3517185 : CollatzResearch.WordTrace tailWord_3517185 prefixEnd_3517185 1204004303855951154141511 := by
  unfold tailWord_3517185
  simp only [CollatzResearch.WordTrace]
  refine ⟨128282275762846907219945009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85521517175231271479963339 128282275762846907219945009)
  ·
    refine ⟨96211706822135180414958757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128282275762846907219945009 96211706822135180414958757)
    ·
      refine ⟨18039695029150346327804767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96211706822135180414958757 18039695029150346327804767)
      ·
        refine ⟨27059542543725519491707151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18039695029150346327804767 27059542543725519491707151)
        ·
          refine ⟨40589313815588279237560727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27059542543725519491707151 40589313815588279237560727)
          ·
            refine ⟨60883970723382418856341091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40589313815588279237560727 60883970723382418856341091)
            ·
              refine ⟨91325956085073628284511637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60883970723382418856341091 91325956085073628284511637)
              ·
                refine ⟨4280904191487826325836483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91325956085073628284511637 4280904191487826325836483)
                ·
                  refine ⟨6421356287231739488754725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4280904191487826325836483 6421356287231739488754725)
                  ·
                    refine ⟨1204004303855951154141511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6421356287231739488754725 1204004303855951154141511)
                    ·
                      rfl

theorem cell22_3517185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3517185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517185 prefixEnd_3517185 := by exact prefixLift 3517185
  have htrace : WordTrace (prefixWord ++ tailWord_3517185) baseStart_3517185 baseEnd_3517185 := by
    simpa [prefixWord, tailWord_3517185, baseEnd_3517185] using wordTrace_append hprefix tailTrace_3517185
  have hstable : (prefixWord ++ tailWord_3517185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517185).length < 2 ^ (prefixWord ++ tailWord_3517185).sum := by decide
  have hdescent : baseEnd_3517185 < baseStart_3517185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517228 : List Nat := [2, 2, 1, 1, 1, 4, 2, 9]
def baseStart_3517228 : Nat := 118140960795 + 3517228 * 2 ^ 59
def prefixEnd_3517228 : Nat := 4983230072969 + 3 ^ 40 * 3517228 * 2
def baseEnd_3517228 : Nat := 133779891514968152812931

theorem tailTrace_3517228 : CollatzResearch.WordTrace tailWord_3517228 prefixEnd_3517228 133779891514968152812931 := by
  unfold tailWord_3517228
  simp only [CollatzResearch.WordTrace]
  refine ⟨64141922050845562781880169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85522562734460750375840225 64141922050845562781880169)
  ·
    refine ⟨48106441538134172086410127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64141922050845562781880169 48106441538134172086410127)
    ·
      refine ⟨72159662307201258129615191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48106441538134172086410127 72159662307201258129615191)
      ·
        refine ⟨108239493460801887194422787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72159662307201258129615191 108239493460801887194422787)
        ·
          refine ⟨162359240191202830791634181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108239493460801887194422787 162359240191202830791634181)
          ·
            refine ⟨30442357535850530773431409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162359240191202830791634181 30442357535850530773431409)
            ·
              refine ⟨22831768151887898080073557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30442357535850530773431409 22831768151887898080073557)
              ·
                refine ⟨133779891514968152812931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22831768151887898080073557 133779891514968152812931)
                ·
                  rfl

theorem cell22_3517228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_3517228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517228 prefixEnd_3517228 := by exact prefixLift 3517228
  have htrace : WordTrace (prefixWord ++ tailWord_3517228) baseStart_3517228 baseEnd_3517228 := by
    simpa [prefixWord, tailWord_3517228, baseEnd_3517228] using wordTrace_append hprefix tailTrace_3517228
  have hstable : (prefixWord ++ tailWord_3517228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517228).length < 2 ^ (prefixWord ++ tailWord_3517228).sum := by decide
  have hdescent : baseEnd_3517228 < baseStart_3517228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517335 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 6]
def baseStart_3517335 : Nat := 118140960795 + 3517335 * 2 ^ 59
def prefixEnd_3517335 : Nat := 4983230072969 + 3 ^ 40 * 3517335 * 2
def baseEnd_3517335 : Nat := 401351883973800254297017

theorem tailTrace_3517335 : CollatzResearch.WordTrace tailWord_3517335 prefixEnd_3517335 401351883973800254297017 := by
  unfold tailWord_3517335
  simp only [CollatzResearch.WordTrace]
  refine ⟨128287746712303482837905459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85525164474868988558603639 128287746712303482837905459)
  ·
    refine ⟨192431620068455224256858189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128287746712303482837905459 192431620068455224256858189)
    ·
      refine ⟨72161857525670709096321821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192431620068455224256858189 72161857525670709096321821)
      ·
        refine ⟨27060696572126515911120683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72161857525670709096321821 27060696572126515911120683)
        ·
          refine ⟨40591044858189773866681025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27060696572126515911120683 40591044858189773866681025)
          ·
            refine ⟨30443283643642330400010769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40591044858189773866681025 30443283643642330400010769)
            ·
              refine ⟨22832462732731747800008077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30443283643642330400010769 22832462732731747800008077)
              ·
                refine ⟨8562173524774405425003029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22832462732731747800008077 8562173524774405425003029)
                ·
                  refine ⟨401351883973800254297017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8562173524774405425003029 401351883973800254297017)
                  ·
                    rfl

theorem cell22_3517335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 6].length) (baseStart_3517335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517335 prefixEnd_3517335 := by exact prefixLift 3517335
  have htrace : WordTrace (prefixWord ++ tailWord_3517335) baseStart_3517335 baseEnd_3517335 := by
    simpa [prefixWord, tailWord_3517335, baseEnd_3517335] using wordTrace_append hprefix tailTrace_3517335
  have hstable : (prefixWord ++ tailWord_3517335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517335).length < 2 ^ (prefixWord ++ tailWord_3517335).sum := by decide
  have hdescent : baseEnd_3517335 < baseStart_3517335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517369 : List Nat := [1, 2, 1, 4, 2, 3, 2, 3, 4]
def baseStart_3517369 : Nat := 118140960795 + 3517369 * 2 ^ 59
def prefixEnd_3517369 : Nat := 4983230072969 + 3 ^ 40 * 3517369 * 2
def baseEnd_3517369 : Nat := 401355763605412002513649

theorem tailTrace_3517369 : CollatzResearch.WordTrace tailWord_3517369 prefixEnd_3517369 401355763605412002513649 := by
  unfold tailWord_3517369
  simp only [CollatzResearch.WordTrace]
  refine ⟨128288986794180306644643161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85525991196120204429762107 128288986794180306644643161)
  ·
    refine ⟨96216740095635229983482371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128288986794180306644643161 96216740095635229983482371)
    ·
      refine ⟨144325110143452844975223557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96216740095635229983482371 144325110143452844975223557)
      ·
        refine ⟨27060958151897408432854417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144325110143452844975223557 27060958151897408432854417)
        ·
          refine ⟨20295718613923056324640813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27060958151897408432854417 20295718613923056324640813)
          ·
            refine ⟨7610894480221146121740305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20295718613923056324640813 7610894480221146121740305)
            ·
              refine ⟨5708170860165859591305229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610894480221146121740305 5708170860165859591305229)
              ·
                refine ⟨2140564072562197346739461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708170860165859591305229 2140564072562197346739461)
                ·
                  refine ⟨401355763605412002513649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140564072562197346739461 401355763605412002513649)
                  ·
                    rfl

theorem cell22_3517369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 4].length) (baseStart_3517369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517369 prefixEnd_3517369 := by exact prefixLift 3517369
  have htrace : WordTrace (prefixWord ++ tailWord_3517369) baseStart_3517369 baseEnd_3517369 := by
    simpa [prefixWord, tailWord_3517369, baseEnd_3517369] using wordTrace_append hprefix tailTrace_3517369
  have hstable : (prefixWord ++ tailWord_3517369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517369).length < 2 ^ (prefixWord ++ tailWord_3517369).sum := by decide
  have hdescent : baseEnd_3517369 < baseStart_3517369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517384 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_3517384 : Nat := 118140960795 + 3517384 * 2 ^ 59
def prefixEnd_3517384 : Nat := 4983230072969 + 3 ^ 40 * 3517384 * 2
def baseEnd_3517384 : Nat := 1204072425622780968415901

theorem tailTrace_3517384 : CollatzResearch.WordTrace tailWord_3517384 prefixEnd_3517384 1204072425622780968415901 := by
  unfold tailWord_3517384
  simp only [CollatzResearch.WordTrace]
  refine ⟨64144766944562982103219603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85526355926083976137626137 64144766944562982103219603)
  ·
    refine ⟨96217150416844473154829405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64144766944562982103219603 96217150416844473154829405)
    ·
      refine ⟨36081431406316677433061027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96217150416844473154829405 36081431406316677433061027)
      ·
        refine ⟨54122147109475016149591541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36081431406316677433061027 54122147109475016149591541)
        ·
          refine ⟨5073951291513282764024207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54122147109475016149591541 5073951291513282764024207)
          ·
            refine ⟨7610926937269924146036311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073951291513282764024207 7610926937269924146036311)
            ·
              refine ⟨11416390405904886219054467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7610926937269924146036311 11416390405904886219054467)
              ·
                refine ⟨17124585608857329328581701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11416390405904886219054467 17124585608857329328581701)
                ·
                  refine ⟨3210859801660749249109069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17124585608857329328581701 3210859801660749249109069)
                  ·
                    refine ⟨1204072425622780968415901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210859801660749249109069 1204072425622780968415901)
                    ·
                      rfl

theorem cell22_3517384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_3517384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517384 prefixEnd_3517384 := by exact prefixLift 3517384
  have htrace : WordTrace (prefixWord ++ tailWord_3517384) baseStart_3517384 baseEnd_3517384 := by
    simpa [prefixWord, tailWord_3517384, baseEnd_3517384] using wordTrace_append hprefix tailTrace_3517384
  have hstable : (prefixWord ++ tailWord_3517384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517384).length < 2 ^ (prefixWord ++ tailWord_3517384).sum := by decide
  have hdescent : baseEnd_3517384 < baseStart_3517384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517401 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 2, 3]
def baseStart_3517401 : Nat := 118140960795 + 3517401 * 2 ^ 59
def prefixEnd_3517401 : Nat := 4983230072969 + 3 ^ 40 * 3517401 * 2
def baseEnd_3517401 : Nat := 1204078245070198590740849

theorem tailTrace_3517401 : CollatzResearch.WordTrace tailWord_3517401 prefixEnd_3517401 1204078245070198590740849 := by
  unfold tailWord_3517401
  simp only [CollatzResearch.WordTrace]
  refine ⟨128290153930064376109808057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85526769286709584073205371 128290153930064376109808057)
  ·
    refine ⟨96217615447548282082356043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128290153930064376109808057 96217615447548282082356043)
    ·
      refine ⟨144326423171322423123534065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96217615447548282082356043 144326423171322423123534065)
      ·
        refine ⟨108244817378491817342650549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144326423171322423123534065 108244817378491817342650549)
        ·
          refine ⟨10147951629233607875873489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108244817378491817342650549 10147951629233607875873489)
          ·
            refine ⟨7610963721925205906905117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147951629233607875873489 7610963721925205906905117)
            ·
              refine ⟨2854111395721952215089419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7610963721925205906905117 2854111395721952215089419)
              ·
                refine ⟨4281167093582928322634129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854111395721952215089419 4281167093582928322634129)
                ·
                  refine ⟨3210875320187196241975597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4281167093582928322634129 3210875320187196241975597)
                  ·
                    refine ⟨1204078245070198590740849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210875320187196241975597 1204078245070198590740849)
                    ·
                      rfl

theorem cell22_3517401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_3517401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517401 prefixEnd_3517401 := by exact prefixLift 3517401
  have htrace : WordTrace (prefixWord ++ tailWord_3517401) baseStart_3517401 baseEnd_3517401 := by
    simpa [prefixWord, tailWord_3517401, baseEnd_3517401] using wordTrace_append hprefix tailTrace_3517401
  have hstable : (prefixWord ++ tailWord_3517401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517401).length < 2 ^ (prefixWord ++ tailWord_3517401).sum := by decide
  have hdescent : baseEnd_3517401 < baseStart_3517401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517412 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_3517412 : Nat := 118140960795 + 3517412 * 2 ^ 59
def prefixEnd_3517412 : Nat := 4983230072969 + 3 ^ 40 * 3517412 * 2
def baseEnd_3517412 : Nat := 1204082010594998228715815

theorem tailTrace_3517412 : CollatzResearch.WordTrace tailWord_3517412 prefixEnd_3517412 1204082010594998228715815 := by
  unfold tailWord_3517412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64145277566512262494229245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85527036755349683325638993 64145277566512262494229245)
  ·
    refine ⟨24054479087442098435335967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64145277566512262494229245 24054479087442098435335967)
    ·
      refine ⟨36081718631163147653003951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24054479087442098435335967 36081718631163147653003951)
      ·
        refine ⟨54122577946744721479505927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36081718631163147653003951 54122577946744721479505927)
        ·
          refine ⟨81183866920117082219258891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54122577946744721479505927 81183866920117082219258891)
          ·
            refine ⟨121775800380175623328888337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81183866920117082219258891 121775800380175623328888337)
            ·
              refine ⟨91331850285131717496666253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121775800380175623328888337 91331850285131717496666253)
              ·
                refine ⟨34249443856924394061249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91331850285131717496666253 34249443856924394061249845)
                ·
                  refine ⟨3210885361586661943242173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34249443856924394061249845 3210885361586661943242173)
                  ·
                    refine ⟨1204082010594998228715815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3210885361586661943242173 1204082010594998228715815)
                    ·
                      rfl

theorem cell22_3517412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_3517412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517412 prefixEnd_3517412 := by exact prefixLift 3517412
  have htrace : WordTrace (prefixWord ++ tailWord_3517412) baseStart_3517412 baseEnd_3517412 := by
    simpa [prefixWord, tailWord_3517412, baseEnd_3517412] using wordTrace_append hprefix tailTrace_3517412
  have hstable : (prefixWord ++ tailWord_3517412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517412).length < 2 ^ (prefixWord ++ tailWord_3517412).sum := by decide
  have hdescent : baseEnd_3517412 < baseStart_3517412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517504 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_3517504 : Nat := 118140960795 + 3517504 * 2 ^ 59
def prefixEnd_3517504 : Nat := 4983230072969 + 3 ^ 40 * 3517504 * 2
def baseEnd_3517504 : Nat := 401371168025046885138511

theorem tailTrace_3517504 : CollatzResearch.WordTrace tailWord_3517504 prefixEnd_3517504 401371168025046885138511 := by
  unfold tailWord_3517504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64146955324345612350403783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85529273765794149800538377 64146955324345612350403783)
  ·
    refine ⟨96220432986518418525605675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64146955324345612350403783 96220432986518418525605675)
    ·
      refine ⟨144330649479777627788408513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96220432986518418525605675 144330649479777627788408513)
      ·
        refine ⟨108247987109833220841306385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144330649479777627788408513 108247987109833220841306385)
        ·
          refine ⟨81185990332374915630979789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108247987109833220841306385 81185990332374915630979789)
          ·
            refine ⟨30444746374640593361617421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81185990332374915630979789 30444746374640593361617421)
            ·
              refine ⟨11416779890490222510606533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30444746374640593361617421 11416779890490222510606533)
              ·
                refine ⟨2140646229466916720738725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11416779890490222510606533 2140646229466916720738725)
                ·
                  refine ⟨401371168025046885138511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140646229466916720738725 401371168025046885138511)
                  ·
                    rfl

theorem cell22_3517504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_3517504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517504 prefixEnd_3517504 := by exact prefixLift 3517504
  have htrace : WordTrace (prefixWord ++ tailWord_3517504) baseStart_3517504 baseEnd_3517504 := by
    simpa [prefixWord, tailWord_3517504, baseEnd_3517504] using wordTrace_append hprefix tailTrace_3517504
  have hstable : (prefixWord ++ tailWord_3517504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517504).length < 2 ^ (prefixWord ++ tailWord_3517504).sum := by decide
  have hdescent : baseEnd_3517504 < baseStart_3517504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517538 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_3517538 : Nat := 118140960795 + 3517538 * 2 ^ 59
def prefixEnd_3517538 : Nat := 4983230072969 + 3 ^ 40 * 3517538 * 2
def baseEnd_3517538 : Nat := 401375047656658633355143

theorem tailTrace_3517538 : CollatzResearch.WordTrace tailWord_3517538 prefixEnd_3517538 401375047656658633355143 := by
  unfold tailWord_3517538
  simp only [CollatzResearch.WordTrace]
  refine ⟨32073787682642012126886317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85530100487045365671696845 32073787682642012126886317)
  ·
    refine ⟨12027670380990754547582369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32073787682642012126886317 12027670380990754547582369)
    ·
      refine ⟨9020752785743065910686777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12027670380990754547582369 9020752785743065910686777)
      ·
        refine ⟨6765564589307299433015083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9020752785743065910686777 6765564589307299433015083)
        ·
          refine ⟨10148346883960949149522625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765564589307299433015083 10148346883960949149522625)
          ·
            refine ⟨7611260162970711862141969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148346883960949149522625 7611260162970711862141969)
            ·
              refine ⟨5708445122228033896606477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611260162970711862141969 5708445122228033896606477)
              ·
                refine ⟨2140666920835512711227429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5708445122228033896606477 2140666920835512711227429)
                ·
                  refine ⟨401375047656658633355143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140666920835512711227429 401375047656658633355143)
                  ·
                    rfl

theorem cell22_3517538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_3517538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517538 prefixEnd_3517538 := by exact prefixLift 3517538
  have htrace : WordTrace (prefixWord ++ tailWord_3517538) baseStart_3517538 baseEnd_3517538 := by
    simpa [prefixWord, tailWord_3517538, baseEnd_3517538] using wordTrace_append hprefix tailTrace_3517538
  have hstable : (prefixWord ++ tailWord_3517538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517538).length < 2 ^ (prefixWord ++ tailWord_3517538).sum := by decide
  have hdescent : baseEnd_3517538 < baseStart_3517538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517594 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3517594 : Nat := 118140960795 + 3517594 * 2 ^ 59
def prefixEnd_3517594 : Nat := 4983230072969 + 3 ^ 40 * 3517594 * 2
def baseEnd_3517594 : Nat := 401381437638136806888419

theorem tailTrace_3517594 : CollatzResearch.WordTrace tailWord_3517594 prefixEnd_3517594 401381437638136806888419 := by
  unfold tailWord_3517594
  simp only [CollatzResearch.WordTrace]
  refine ⟨32074298304591292517895959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85531462145576780047722557 32074298304591292517895959)
  ·
    refine ⟨48111447456886938776843939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32074298304591292517895959 48111447456886938776843939)
    ·
      refine ⟨72167171185330408165265909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48111447456886938776843939 72167171185330408165265909)
      ·
        refine ⟨6765672298624725765493679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72167171185330408165265909 6765672298624725765493679)
        ·
          refine ⟨10148508447937088648240519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6765672298624725765493679 10148508447937088648240519)
          ·
            refine ⟨15222762671905632972360779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10148508447937088648240519 15222762671905632972360779)
            ·
              refine ⟨22834144007858449458541169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15222762671905632972360779 22834144007858449458541169)
              ·
                refine ⟨17125608005893837093905877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22834144007858449458541169 17125608005893837093905877)
                ·
                  refine ⟨401381437638136806888419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17125608005893837093905877 401381437638136806888419)
                  ·
                    rfl

theorem cell22_3517594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3517594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517594 prefixEnd_3517594 := by exact prefixLift 3517594
  have htrace : WordTrace (prefixWord ++ tailWord_3517594) baseStart_3517594 baseEnd_3517594 := by
    simpa [prefixWord, tailWord_3517594, baseEnd_3517594] using wordTrace_append hprefix tailTrace_3517594
  have hstable : (prefixWord ++ tailWord_3517594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517594).length < 2 ^ (prefixWord ++ tailWord_3517594).sum := by decide
  have hdescent : baseEnd_3517594 < baseStart_3517594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517628 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_3517628 : Nat := 118140960795 + 3517628 * 2 ^ 59
def prefixEnd_3517628 : Nat := 4983230072969 + 3 ^ 40 * 3517628 * 2
def baseEnd_3517628 : Nat := 401385317269748555105051

theorem tailTrace_3517628 : CollatzResearch.WordTrace tailWord_3517628 prefixEnd_3517628 401385317269748555105051 := by
  unfold tailWord_3517628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64149216650120996939160769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85532288866827995918881025 64149216650120996939160769)
  ·
    refine ⟨48111912487590747704370577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64149216650120996939160769 48111912487590747704370577)
    ·
      refine ⟨36083934365693060778277933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48111912487590747704370577 36083934365693060778277933)
      ·
        refine ⟨13531475387134897791854225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36083934365693060778277933 13531475387134897791854225)
        ·
          refine ⟨10148606540351173343890669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13531475387134897791854225 10148606540351173343890669)
          ·
            refine ⟨3805727452631690003959001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10148606540351173343890669 3805727452631690003959001)
            ·
              refine ⟨2854295589473767502969251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3805727452631690003959001 2854295589473767502969251)
              ·
                refine ⟨4281443384210651254453877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2854295589473767502969251 4281443384210651254453877)
                ·
                  refine ⟨401385317269748555105051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4281443384210651254453877 401385317269748555105051)
                  ·
                    rfl

theorem cell22_3517628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_3517628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517628 prefixEnd_3517628 := by exact prefixLift 3517628
  have htrace : WordTrace (prefixWord ++ tailWord_3517628) baseStart_3517628 baseEnd_3517628 := by
    simpa [prefixWord, tailWord_3517628, baseEnd_3517628] using wordTrace_append hprefix tailTrace_3517628
  have hstable : (prefixWord ++ tailWord_3517628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517628).length < 2 ^ (prefixWord ++ tailWord_3517628).sum := by decide
  have hdescent : baseEnd_3517628 < baseStart_3517628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517667 : List Nat := [1, 1, 1, 19]
def baseStart_3517667 : Nat := 118140960795 + 3517667 * 2 ^ 59
def prefixEnd_3517667 : Nat := 4983230072969 + 3 ^ 40 * 3517667 * 2
def baseEnd_3517667 : Nat := 1651809742532596109177

theorem tailTrace_3517667 : CollatzResearch.WordTrace tailWord_3517667 prefixEnd_3517667 1651809742532596109177 := by
  unfold tailWord_3517667
  simp only [CollatzResearch.WordTrace]
  refine ⟨128299855747100703538991255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85533237164733802359327503 128299855747100703538991255)
  ·
    refine ⟨192449783620651055308486883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128299855747100703538991255 192449783620651055308486883)
    ·
      refine ⟨288674675430976582962730325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192449783620651055308486883 288674675430976582962730325)
      ·
        refine ⟨1651809742532596109177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 19 288674675430976582962730325 1651809742532596109177)
        ·
          rfl

theorem cell22_3517667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 19].length) (baseStart_3517667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517667 prefixEnd_3517667 := by exact prefixLift 3517667
  have htrace : WordTrace (prefixWord ++ tailWord_3517667) baseStart_3517667 baseEnd_3517667 := by
    simpa [prefixWord, tailWord_3517667, baseEnd_3517667] using wordTrace_append hprefix tailTrace_3517667
  have hstable : (prefixWord ++ tailWord_3517667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517667).length < 2 ^ (prefixWord ++ tailWord_3517667).sum := by decide
  have hdescent : baseEnd_3517667 < baseStart_3517667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517733 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 3, 3]
def baseStart_3517733 : Nat := 118140960795 + 3517733 * 2 ^ 59
def prefixEnd_3517733 : Nat := 4983230072969 + 3 ^ 40 * 3517733 * 2
def baseEnd_3517733 : Nat := 1204191895455060391439831

theorem tailTrace_3517733 : CollatzResearch.WordTrace tailWord_3517733 prefixEnd_3517733 1204191895455060391439831 := by
  unfold tailWord_3517733
  simp only [CollatzResearch.WordTrace]
  refine ⟨128302262964861596810893853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85534841976574397873929235 128302262964861596810893853)
  ·
    refine ⟨48113348611823098804085195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128302262964861596810893853 48113348611823098804085195)
    ·
      refine ⟨72170022917734648206127793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48113348611823098804085195 72170022917734648206127793)
      ·
        refine ⟨54127517188300986154595845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72170022917734648206127793 54127517188300986154595845)
        ·
          refine ⟨10148909472806434903986721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54127517188300986154595845 10148909472806434903986721)
          ·
            refine ⟨7611682104604826177990041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10148909472806434903986721 7611682104604826177990041)
            ·
              refine ⟨5708761578453619633492531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7611682104604826177990041 5708761578453619633492531)
              ·
                refine ⟨8563142367680429450238797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5708761578453619633492531 8563142367680429450238797)
                ·
                  refine ⟨3211178387880161043839549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8563142367680429450238797 3211178387880161043839549)
                  ·
                    refine ⟨1204191895455060391439831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211178387880161043839549 1204191895455060391439831)
                    ·
                      rfl

theorem cell22_3517733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_3517733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517733 prefixEnd_3517733 := by exact prefixLift 3517733
  have htrace : WordTrace (prefixWord ++ tailWord_3517733) baseStart_3517733 baseEnd_3517733 := by
    simpa [prefixWord, tailWord_3517733, baseEnd_3517733] using wordTrace_append hprefix tailTrace_3517733
  have hstable : (prefixWord ++ tailWord_3517733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517733).length < 2 ^ (prefixWord ++ tailWord_3517733).sum := by decide
  have hdescent : baseEnd_3517733 < baseStart_3517733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517744 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_3517744 : Nat := 118140960795 + 3517744 * 2 ^ 59
def prefixEnd_3517744 : Nat := 4983230072969 + 3 ^ 40 * 3517744 * 2
def baseEnd_3517744 : Nat := 1204195660979860029414797

theorem tailTrace_3517744 : CollatzResearch.WordTrace tailWord_3517744 prefixEnd_3517744 1204195660979860029414797 := by
  unfold tailWord_3517744
  simp only [CollatzResearch.WordTrace]
  refine ⟨64151332083910872844772143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85535109445214497126362857 64151332083910872844772143)
  ·
    refine ⟨96226998125866309267158215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64151332083910872844772143 96226998125866309267158215)
    ·
      refine ⟨144340497188799463900737323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96226998125866309267158215 144340497188799463900737323)
      ·
        refine ⟨216510745783199195851105985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144340497188799463900737323 216510745783199195851105985)
        ·
          refine ⟨162383059337399396888329489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216510745783199195851105985 162383059337399396888329489)
          ·
            refine ⟨121787294503049547666247117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162383059337399396888329489 121787294503049547666247117)
            ·
              refine ⟨45670235438643580374842669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121787294503049547666247117 45670235438643580374842669)
              ·
                refine ⟨17126338289491342640566001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45670235438643580374842669 17126338289491342640566001)
                ·
                  refine ⟨12844753717118506980424501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17126338289491342640566001 12844753717118506980424501)
                  ·
                    refine ⟨1204195660979860029414797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12844753717118506980424501 1204195660979860029414797)
                    ·
                      rfl

theorem cell22_3517744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_3517744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517744 prefixEnd_3517744 := by exact prefixLift 3517744
  have htrace : WordTrace (prefixWord ++ tailWord_3517744) baseStart_3517744 baseEnd_3517744 := by
    simpa [prefixWord, tailWord_3517744, baseEnd_3517744] using wordTrace_append hprefix tailTrace_3517744
  have hstable : (prefixWord ++ tailWord_3517744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517744).length < 2 ^ (prefixWord ++ tailWord_3517744).sum := by decide
  have hdescent : baseEnd_3517744 < baseStart_3517744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517776 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_3517776 : Nat := 118140960795 + 3517776 * 2 ^ 59
def prefixEnd_3517776 : Nat := 4983230072969 + 3 ^ 40 * 3517776 * 2
def baseEnd_3517776 : Nat := 1204206615233822612614699

theorem tailTrace_3517776 : CollatzResearch.WordTrace tailWord_3517776 prefixEnd_3517776 1204206615233822612614699 := by
  unfold tailWord_3517776
  simp only [CollatzResearch.WordTrace]
  refine ⟨64151915651852907577354591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85535887535803876769806121 64151915651852907577354591)
  ·
    refine ⟨96227873477779361366031887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64151915651852907577354591 96227873477779361366031887)
    ·
      refine ⟨144341810216669042049047831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96227873477779361366031887 144341810216669042049047831)
      ·
        refine ⟨216512715325003563073571747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144341810216669042049047831 216512715325003563073571747)
        ·
          refine ⟨324769072987505344610357621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216512715325003563073571747 324769072987505344610357621)
          ·
            refine ⟨30447100592578626057221027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 324769072987505344610357621 30447100592578626057221027)
            ·
              refine ⟨45670650888867939085831541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30447100592578626057221027 45670650888867939085831541)
              ·
                refine ⟨4281623520831369289296707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45670650888867939085831541 4281623520831369289296707)
                ·
                  refine ⟨6422435281247053933945061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4281623520831369289296707 6422435281247053933945061)
                  ·
                    refine ⟨1204206615233822612614699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422435281247053933945061 1204206615233822612614699)
                    ·
                      rfl

theorem cell22_3517776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_3517776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517776 prefixEnd_3517776 := by exact prefixLift 3517776
  have htrace : WordTrace (prefixWord ++ tailWord_3517776) baseStart_3517776 baseEnd_3517776 := by
    simpa [prefixWord, tailWord_3517776, baseEnd_3517776] using wordTrace_append hprefix tailTrace_3517776
  have hstable : (prefixWord ++ tailWord_3517776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517776).length < 2 ^ (prefixWord ++ tailWord_3517776).sum := by decide
  have hdescent : baseEnd_3517776 < baseStart_3517776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517819 : List Nat := [1, 1, 1, 1, 1, 6, 1, 10]
def baseStart_3517819 : Nat := 118140960795 + 3517819 * 2 ^ 59
def prefixEnd_3517819 : Nat := 4983230072969 + 3 ^ 40 * 3517819 * 2
def baseEnd_3517819 : Nat := 133802370556953870421063

theorem tailTrace_3517819 : CollatzResearch.WordTrace tailWord_3517819 prefixEnd_3517819 133802370556953870421063 := by
  unfold tailWord_3517819
  simp only [CollatzResearch.WordTrace]
  refine ⟨128305399642550033498524511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85536933095033355665683007 128305399642550033498524511)
  ·
    refine ⟨192458099463825050247786767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128305399642550033498524511 192458099463825050247786767)
    ·
      refine ⟨288687149195737575371680151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192458099463825050247786767 288687149195737575371680151)
      ·
        refine ⟨433030723793606363057520227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288687149195737575371680151 433030723793606363057520227)
        ·
          refine ⟨649546085690409544586280341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433030723793606363057520227 649546085690409544586280341)
          ·
            refine ⟨30447472766737947402481891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 649546085690409544586280341 30447472766737947402481891)
            ·
              refine ⟨45671209150106921103722837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30447472766737947402481891 45671209150106921103722837)
              ·
                refine ⟨133802370556953870421063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45671209150106921103722837 133802370556953870421063)
                ·
                  rfl

theorem cell22_3517819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_3517819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517819 prefixEnd_3517819 := by exact prefixLift 3517819
  have htrace : WordTrace (prefixWord ++ tailWord_3517819) baseStart_3517819 baseEnd_3517819 := by
    simpa [prefixWord, tailWord_3517819, baseEnd_3517819] using wordTrace_append hprefix tailTrace_3517819
  have hstable : (prefixWord ++ tailWord_3517819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517819).length < 2 ^ (prefixWord ++ tailWord_3517819).sum := by decide
  have hdescent : baseEnd_3517819 < baseStart_3517819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517842 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3517842 : Nat := 118140960795 + 3517842 * 2 ^ 59
def prefixEnd_3517842 : Nat := 4983230072969 + 3 ^ 40 * 3517842 * 2
def baseEnd_3517842 : Nat := 401409736127540146821499

theorem tailTrace_3517842 : CollatzResearch.WordTrace tailWord_3517842 prefixEnd_3517842 401409736127540146821499 := by
  unfold tailWord_3517842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32076559630366677106652945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85537492347644472284407853 32076559630366677106652945)
  ·
    refine ⟨24057419722775007829989709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32076559630366677106652945 24057419722775007829989709)
    ·
      refine ⟨9021532396040627936246141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24057419722775007829989709 9021532396040627936246141)
      ·
        refine ⟨3383074648515235476092303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9021532396040627936246141 3383074648515235476092303)
        ·
          refine ⟨5074611972772853214138455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3383074648515235476092303 5074611972772853214138455)
          ·
            refine ⟨7611917959159279821207683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5074611972772853214138455 7611917959159279821207683)
            ·
              refine ⟨11417876938738919731811525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7611917959159279821207683 11417876938738919731811525)
              ·
                refine ⟨2140851926013547449714661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11417876938738919731811525 2140851926013547449714661)
                ·
                  refine ⟨401409736127540146821499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140851926013547449714661 401409736127540146821499)
                  ·
                    rfl

theorem cell22_3517842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3517842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517842 prefixEnd_3517842 := by exact prefixLift 3517842
  have htrace : WordTrace (prefixWord ++ tailWord_3517842) baseStart_3517842 baseEnd_3517842 := by
    simpa [prefixWord, tailWord_3517842, baseEnd_3517842] using wordTrace_append hprefix tailTrace_3517842
  have hstable : (prefixWord ++ tailWord_3517842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517842).length < 2 ^ (prefixWord ++ tailWord_3517842).sum := by decide
  have hdescent : baseEnd_3517842 < baseStart_3517842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517853 : List Nat := [1, 4, 2, 1, 3, 3, 1, 7]
def baseStart_3517853 : Nat := 118140960795 + 3517853 * 2 ^ 59
def prefixEnd_3517853 : Nat := 4983230072969 + 3 ^ 40 * 3517853 * 2
def baseEnd_3517853 : Nat := 133803663767491119826607

theorem tailTrace_3517853 : CollatzResearch.WordTrace tailWord_3517853 prefixEnd_3517853 133803663767491119826607 := by
  unfold tailWord_3517853
  simp only [CollatzResearch.WordTrace]
  refine ⟨128306639724426857305262213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85537759816284571536841475 128306639724426857305262213)
  ·
    refine ⟨24057494948330035744736665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128306639724426857305262213 24057494948330035744736665)
    ·
      refine ⟨18043121211247526808552499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24057494948330035744736665 18043121211247526808552499)
      ·
        refine ⟨27064681816871290212828749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18043121211247526808552499 27064681816871290212828749)
        ·
          refine ⟨10149255681326733829810781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27064681816871290212828749 10149255681326733829810781)
          ·
            refine ⟨3805970880497525186179043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10149255681326733829810781 3805970880497525186179043)
            ·
              refine ⟨5708956320746287779268565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3805970880497525186179043 5708956320746287779268565)
              ·
                refine ⟨133803663767491119826607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5708956320746287779268565 133803663767491119826607)
                ·
                  rfl

theorem cell22_3517853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 7].length) (baseStart_3517853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517853 prefixEnd_3517853 := by exact prefixLift 3517853
  have htrace : WordTrace (prefixWord ++ tailWord_3517853) baseStart_3517853 baseEnd_3517853 := by
    simpa [prefixWord, tailWord_3517853, baseEnd_3517853] using wordTrace_append hprefix tailTrace_3517853
  have hstable : (prefixWord ++ tailWord_3517853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517853).length < 2 ^ (prefixWord ++ tailWord_3517853).sum := by decide
  have hdescent : baseEnd_3517853 < baseStart_3517853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517896 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3517896 : Nat := 118140960795 + 3517896 * 2 ^ 59
def prefixEnd_3517896 : Nat := 4983230072969 + 3 ^ 40 * 3517896 * 2
def baseEnd_3517896 : Nat := 1204247693686182299614331

theorem tailTrace_3517896 : CollatzResearch.WordTrace tailWord_3517896 prefixEnd_3517896 1204247693686182299614331 := by
  unfold tailWord_3517896
  simp only [CollatzResearch.WordTrace]
  refine ⟨64154104031635537824538771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85538805375514050432718361 64154104031635537824538771)
  ·
    refine ⟨96231156047453306736808157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64154104031635537824538771 96231156047453306736808157)
    ·
      refine ⟨36086683517794990026303059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96231156047453306736808157 36086683517794990026303059)
      ·
        refine ⟨54130025276692485039454589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36086683517794990026303059 54130025276692485039454589)
        ·
          refine ⟨20298759478759681889795471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54130025276692485039454589 20298759478759681889795471)
          ·
            refine ⟨30448139218139522834693207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20298759478759681889795471 30448139218139522834693207)
            ·
              refine ⟨45672208827209284252039811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30448139218139522834693207 45672208827209284252039811)
              ·
                refine ⟨68508313240813926378059717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45672208827209284252039811 68508313240813926378059717)
                ·
                  refine ⟨12845308732652611195886197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68508313240813926378059717 12845308732652611195886197)
                  ·
                    refine ⟨1204247693686182299614331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12845308732652611195886197 1204247693686182299614331)
                    ·
                      rfl

theorem cell22_3517896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3517896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517896 prefixEnd_3517896 := by exact prefixLift 3517896
  have htrace : WordTrace (prefixWord ++ tailWord_3517896) baseStart_3517896 baseEnd_3517896 := by
    simpa [prefixWord, tailWord_3517896, baseEnd_3517896] using wordTrace_append hprefix tailTrace_3517896
  have hstable : (prefixWord ++ tailWord_3517896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517896).length < 2 ^ (prefixWord ++ tailWord_3517896).sum := by decide
  have hdescent : baseEnd_3517896 < baseStart_3517896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517898 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_3517898 : Nat := 118140960795 + 3517898 * 2 ^ 59
def prefixEnd_3517898 : Nat := 4983230072969 + 3 ^ 40 * 3517898 * 2
def baseEnd_3517898 : Nat := 401416126109018320354775

theorem tailTrace_3517898 : CollatzResearch.WordTrace tailWord_3517898 prefixEnd_3517898 401416126109018320354775 := by
  unfold tailWord_3517898
  simp only [CollatzResearch.WordTrace]
  refine ⟨32077070252315957497662587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85538854006175886660433565 32077070252315957497662587)
  ·
    refine ⟨48115605378473936246493881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32077070252315957497662587 48115605378473936246493881)
    ·
      refine ⟨36086704033855452184870411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48115605378473936246493881 36086704033855452184870411)
      ·
        refine ⟨54130056050783178277305617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36086704033855452184870411 54130056050783178277305617)
        ·
          refine ⟨40597542038087383707979213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54130056050783178277305617 40597542038087383707979213)
          ·
            refine ⟨15224078264282768890492205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40597542038087383707979213 15224078264282768890492205)
            ·
              refine ⟨5709029349106038333934577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15224078264282768890492205 5709029349106038333934577)
              ·
                refine ⟨4281772011829528750450933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5709029349106038333934577 4281772011829528750450933)
                ·
                  refine ⟨401416126109018320354775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4281772011829528750450933 401416126109018320354775)
                  ·
                    rfl

theorem cell22_3517898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_3517898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517898 prefixEnd_3517898 := by exact prefixLift 3517898
  have htrace : WordTrace (prefixWord ++ tailWord_3517898) baseStart_3517898 baseEnd_3517898 := by
    simpa [prefixWord, tailWord_3517898, baseEnd_3517898] using wordTrace_append hprefix tailTrace_3517898
  have hstable : (prefixWord ++ tailWord_3517898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517898).length < 2 ^ (prefixWord ++ tailWord_3517898).sum := by decide
  have hdescent : baseEnd_3517898 < baseStart_3517898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517911 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3517911 : Nat := 118140960795 + 3517911 * 2 ^ 59
def prefixEnd_3517911 : Nat := 4983230072969 + 3 ^ 40 * 3517911 * 2
def baseEnd_3517911 : Nat := 1204252828492727260489285

theorem tailTrace_3517911 : CollatzResearch.WordTrace tailWord_3517911 prefixEnd_3517911 1204252828492727260489285 := by
  unfold tailWord_3517911
  simp only [CollatzResearch.WordTrace]
  refine ⟨128308755158216733210873587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85539170105477822140582391 128308755158216733210873587)
  ·
    refine ⟨192463132737325099816310381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128308755158216733210873587 192463132737325099816310381)
    ·
      refine ⟨72173674776496912431116393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192463132737325099816310381 72173674776496912431116393)
      ·
        refine ⟨54130256082372684323337295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72173674776496912431116393 54130256082372684323337295)
        ·
          refine ⟨81195384123559026485005943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54130256082372684323337295 81195384123559026485005943)
          ·
            refine ⟨121793076185338539727508915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81195384123559026485005943 121793076185338539727508915)
            ·
              refine ⟨182689614278007809591263373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121793076185338539727508915 182689614278007809591263373)
              ·
                refine ⟨68508605354252928596723765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182689614278007809591263373 68508605354252928596723765)
                ·
                  refine ⟨6422681751961212055942853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68508605354252928596723765 6422681751961212055942853)
                  ·
                    refine ⟨1204252828492727260489285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6422681751961212055942853 1204252828492727260489285)
                    ·
                      rfl

theorem cell22_3517911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3517911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517911 prefixEnd_3517911 := by exact prefixLift 3517911
  have htrace : WordTrace (prefixWord ++ tailWord_3517911) baseStart_3517911 baseEnd_3517911 := by
    simpa [prefixWord, tailWord_3517911, baseEnd_3517911] using wordTrace_append hprefix tailTrace_3517911
  have hstable : (prefixWord ++ tailWord_3517911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517911).length < 2 ^ (prefixWord ++ tailWord_3517911).sum := by decide
  have hdescent : baseEnd_3517911 < baseStart_3517911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517943 : List Nat := [1, 1, 3, 1, 1, 1, 1, 9, 4]
def baseStart_3517943 : Nat := 118140960795 + 3517943 * 2 ^ 59
def prefixEnd_3517943 : Nat := 4983230072969 + 3 ^ 40 * 3517943 * 2
def baseEnd_3517943 : Nat := 401421260915563281229729

theorem tailTrace_3517943 : CollatzResearch.WordTrace tailWord_3517943 prefixEnd_3517943 401421260915563281229729 := by
  unfold tailWord_3517943
  simp only [CollatzResearch.WordTrace]
  refine ⟨128309922294100802676038483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85539948196067201784025655 128309922294100802676038483)
  ·
    refine ⟨192464883441151204014057725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128309922294100802676038483 192464883441151204014057725)
    ·
      refine ⟨72174331290431701505271647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192464883441151204014057725 72174331290431701505271647)
      ·
        refine ⟨108261496935647552257907471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72174331290431701505271647 108261496935647552257907471)
        ·
          refine ⟨162392245403471328386861207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108261496935647552257907471 162392245403471328386861207)
          ·
            refine ⟨243588368105206992580291811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162392245403471328386861207 243588368105206992580291811)
            ·
              refine ⟨365382552157810488870437717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243588368105206992580291811 365382552157810488870437717)
              ·
                refine ⟨2140913391549670833225221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 365382552157810488870437717 2140913391549670833225221)
                ·
                  refine ⟨401421260915563281229729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140913391549670833225221 401421260915563281229729)
                  ·
                    rfl

theorem cell22_3517943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 9, 4].length) (baseStart_3517943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517943 prefixEnd_3517943 := by exact prefixLift 3517943
  have htrace : WordTrace (prefixWord ++ tailWord_3517943) baseStart_3517943 baseEnd_3517943 := by
    simpa [prefixWord, tailWord_3517943, baseEnd_3517943] using wordTrace_append hprefix tailTrace_3517943
  have hstable : (prefixWord ++ tailWord_3517943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517943).length < 2 ^ (prefixWord ++ tailWord_3517943).sum := by decide
  have hdescent : baseEnd_3517943 < baseStart_3517943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3517971 : List Nat := [1, 1, 1, 2, 1, 6, 1, 9]
def baseStart_3517971 : Nat := 118140960795 + 3517971 * 2 ^ 59
def prefixEnd_3517971 : Nat := 4983230072969 + 3 ^ 40 * 3517971 * 2
def baseEnd_3517971 : Nat := 133808151968767455998789

theorem tailTrace_3517971 : CollatzResearch.WordTrace tailWord_3517971 prefixEnd_3517971 133808151968767455998789 := by
  unfold tailWord_3517971
  simp only [CollatzResearch.WordTrace]
  refine ⟨128310943537999363458057767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85540629025332908972038511 128310943537999363458057767)
  ·
    refine ⟨192466415306999045187086651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128310943537999363458057767 192466415306999045187086651)
    ·
      refine ⟨288699622960498567780629977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192466415306999045187086651 288699622960498567780629977)
      ·
        refine ⟨216524717220373925835472483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288699622960498567780629977 216524717220373925835472483)
        ·
          refine ⟨324787075830560888753208725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216524717220373925835472483 324787075830560888753208725)
          ·
            refine ⟨15224394179557541660306659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 324787075830560888753208725 15224394179557541660306659)
            ·
              refine ⟨22836591269336312490459989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15224394179557541660306659 22836591269336312490459989)
              ·
                refine ⟨133808151968767455998789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22836591269336312490459989 133808151968767455998789)
                ·
                  rfl

theorem cell22_3517971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_3517971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3517971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3517971 prefixEnd_3517971 := by exact prefixLift 3517971
  have htrace : WordTrace (prefixWord ++ tailWord_3517971) baseStart_3517971 baseEnd_3517971 := by
    simpa [prefixWord, tailWord_3517971, baseEnd_3517971] using wordTrace_append hprefix tailTrace_3517971
  have hstable : (prefixWord ++ tailWord_3517971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3517971).length < 2 ^ (prefixWord ++ tailWord_3517971).sum := by decide
  have hdescent : baseEnd_3517971 < baseStart_3517971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3517971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518033 : List Nat := [1, 2, 2, 1, 3, 2, 1, 5, 5]
def baseStart_3518033 : Nat := 118140960795 + 3518033 * 2 ^ 59
def prefixEnd_3518033 : Nat := 4983230072969 + 3 ^ 40 * 3518033 * 2
def baseEnd_3518033 : Nat := 401431530528653202979637

theorem tailTrace_3518033 : CollatzResearch.WordTrace tailWord_3518033 prefixEnd_3518033 401431530528653202979637 := by
  unfold tailWord_3518033
  simp only [CollatzResearch.WordTrace]
  refine ⟨128313204863774748046814753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85542136575849832031209835 128313204863774748046814753)
  ·
    refine ⟨96234903647831061035111065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128313204863774748046814753 96234903647831061035111065)
    ·
      refine ⟨72176177735873295776333299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96234903647831061035111065 72176177735873295776333299)
      ·
        refine ⟨108264266603809943664499949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72176177735873295776333299 108264266603809943664499949)
        ·
          refine ⟨40599099976428728874187481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108264266603809943664499949 40599099976428728874187481)
          ·
            refine ⟨30449324982321546655640611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40599099976428728874187481 30449324982321546655640611)
            ·
              refine ⟨45673987473482319983460917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30449324982321546655640611 45673987473482319983460917)
              ·
                refine ⟨4281936325638967498449461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45673987473482319983460917 4281936325638967498449461)
                ·
                  refine ⟨401431530528653202979637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4281936325638967498449461 401431530528653202979637)
                  ·
                    rfl

theorem cell22_3518033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_3518033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518033 prefixEnd_3518033 := by exact prefixLift 3518033
  have htrace : WordTrace (prefixWord ++ tailWord_3518033) baseStart_3518033 baseEnd_3518033 := by
    simpa [prefixWord, tailWord_3518033, baseEnd_3518033] using wordTrace_append hprefix tailTrace_3518033
  have hstable : (prefixWord ++ tailWord_3518033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518033).length < 2 ^ (prefixWord ++ tailWord_3518033).sum := by decide
  have hdescent : baseEnd_3518033 < baseStart_3518033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518112 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_3518112 : Nat := 118140960795 + 3518112 * 2 ^ 59
def prefixEnd_3518112 : Nat := 4983230072969 + 3 ^ 40 * 3518112 * 2
def baseEnd_3518112 : Nat := 401440544966809912071223

theorem tailTrace_3518112 : CollatzResearch.WordTrace tailWord_3518112 prefixEnd_3518112 401440544966809912071223 := by
  unfold tailWord_3518112
  simp only [CollatzResearch.WordTrace]
  refine ⟨64158043115244272269470295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85544057486992363025960393 64158043115244272269470295)
  ·
    refine ⟨96237064672866408404205443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64158043115244272269470295 96237064672866408404205443)
    ·
      refine ⟨144355597009299612606308165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96237064672866408404205443 144355597009299612606308165)
      ·
        refine ⟨27066674439243677363682781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144355597009299612606308165 27066674439243677363682781)
        ·
          refine ⟨10150002914716379011381043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27066674439243677363682781 10150002914716379011381043)
          ·
            refine ⟨15225004372074568517071565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10150002914716379011381043 15225004372074568517071565)
            ·
              refine ⟨5709376639527963193901837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15225004372074568517071565 5709376639527963193901837)
              ·
                refine ⟨2141016239822986197713189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5709376639527963193901837 2141016239822986197713189)
                ·
                  refine ⟨401440544966809912071223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141016239822986197713189 401440544966809912071223)
                  ·
                    rfl

theorem cell22_3518112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_3518112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518112 prefixEnd_3518112 := by exact prefixLift 3518112
  have htrace : WordTrace (prefixWord ++ tailWord_3518112) baseStart_3518112 baseEnd_3518112 := by
    simpa [prefixWord, tailWord_3518112, baseEnd_3518112] using wordTrace_append hprefix tailTrace_3518112
  have hstable : (prefixWord ++ tailWord_3518112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518112).length < 2 ^ (prefixWord ++ tailWord_3518112).sum := by decide
  have hdescent : baseEnd_3518112 < baseStart_3518112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518140 : List Nat := [2, 2, 2, 3, 1, 3, 2, 7]
def baseStart_3518140 : Nat := 118140960795 + 3518140 * 2 ^ 59
def prefixEnd_3518140 : Nat := 4983230072969 + 3 ^ 40 * 3518140 * 2
def baseEnd_3518140 : Nat := 133814579985849666279287

theorem tailTrace_3518140 : CollatzResearch.WordTrace tailWord_3518140 prefixEnd_3518140 133814579985849666279287 := by
  unfold tailWord_3518140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64158553737193552660479937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85544738316258070213973249 64158553737193552660479937)
  ·
    refine ⟨48118915302895164495359953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64158553737193552660479937 48118915302895164495359953)
    ·
      refine ⟨36089186477171373371519965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48118915302895164495359953 36089186477171373371519965)
      ·
        refine ⟨13533444928939265014319987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36089186477171373371519965 13533444928939265014319987)
        ·
          refine ⟨20300167393408897521479981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13533444928939265014319987 20300167393408897521479981)
          ·
            refine ⟨7612562772528336570554993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20300167393408897521479981 7612562772528336570554993)
            ·
              refine ⟨5709422079396252427916245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7612562772528336570554993 5709422079396252427916245)
              ·
                refine ⟨133814579985849666279287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5709422079396252427916245 133814579985849666279287)
                ·
                  rfl

theorem cell22_3518140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_3518140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518140 prefixEnd_3518140 := by exact prefixLift 3518140
  have htrace : WordTrace (prefixWord ++ tailWord_3518140) baseStart_3518140 baseEnd_3518140 := by
    simpa [prefixWord, tailWord_3518140, baseEnd_3518140] using wordTrace_append hprefix tailTrace_3518140
  have hstable : (prefixWord ++ tailWord_3518140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518140).length < 2 ^ (prefixWord ++ tailWord_3518140).sum := by decide
  have hdescent : baseEnd_3518140 < baseStart_3518140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518155 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 3, 3]
def baseStart_3518155 : Nat := 118140960795 + 3518155 * 2 ^ 59
def prefixEnd_3518155 : Nat := 4983230072969 + 3 ^ 40 * 3518155 * 2
def baseEnd_3518155 : Nat := 1204336354679191957388537

theorem tailTrace_3518155 : CollatzResearch.WordTrace tailWord_3518155 prefixEnd_3518155 1204336354679191957388537 := by
  unfold tailWord_3518155
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317654569332762882755919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85545103046221841921837279 128317654569332762882755919)
  ·
    refine ⟨192476481853999144324133879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128317654569332762882755919 192476481853999144324133879)
    ·
      refine ⟨288714722780998716486200819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192476481853999144324133879 288714722780998716486200819)
      ·
        refine ⟨433072084171498074729301229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288714722780998716486200819 433072084171498074729301229)
        ·
          refine ⟨162402031564311778023487961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433072084171498074729301229 162402031564311778023487961)
          ·
            refine ⟨121801523673233833517615971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162402031564311778023487961 121801523673233833517615971)
            ·
              refine ⟨182702285509850750276423957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121801523673233833517615971 182702285509850750276423957)
              ·
                refine ⟨8564169633274253919207373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182702285509850750276423957 8564169633274253919207373)
                ·
                  refine ⟨3211563612477845219702765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8564169633274253919207373 3211563612477845219702765)
                  ·
                    refine ⟨1204336354679191957388537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211563612477845219702765 1204336354679191957388537)
                    ·
                      rfl

theorem cell22_3518155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 3].length) (baseStart_3518155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518155 prefixEnd_3518155 := by exact prefixLift 3518155
  have htrace : WordTrace (prefixWord ++ tailWord_3518155) baseStart_3518155 baseEnd_3518155 := by
    simpa [prefixWord, tailWord_3518155, baseEnd_3518155] using wordTrace_append hprefix tailTrace_3518155
  have hstable : (prefixWord ++ tailWord_3518155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518155).length < 2 ^ (prefixWord ++ tailWord_3518155).sum := by decide
  have hdescent : baseEnd_3518155 < baseStart_3518155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518157 : List Nat := [1, 6, 2, 1, 1, 1, 2, 8]
def baseStart_3518157 : Nat := 118140960795 + 3518157 * 2 ^ 59
def prefixEnd_3518157 : Nat := 4983230072969 + 3 ^ 40 * 3518157 * 2
def baseEnd_3518157 : Nat := 133815226591118290982059

theorem tailTrace_3518157 : CollatzResearch.WordTrace tailWord_3518157 prefixEnd_3518157 133815226591118290982059 := by
  unfold tailWord_3518157
  simp only [CollatzResearch.WordTrace]
  refine ⟨128317727515325517224328725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85545151676883678149552483 128317727515325517224328725)
  ·
    refine ⟨6014893477280883619890409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128317727515325517224328725 6014893477280883619890409)
    ·
      refine ⟨4511170107960662714917807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6014893477280883619890409 4511170107960662714917807)
      ·
        refine ⟨6766755161940994072376711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4511170107960662714917807 6766755161940994072376711)
        ·
          refine ⟨10150132742911491108565067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6766755161940994072376711 10150132742911491108565067)
          ·
            refine ⟨15225199114367236662847601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10150132742911491108565067 15225199114367236662847601)
            ·
              refine ⟨11418899335775427497135701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15225199114367236662847601 11418899335775427497135701)
              ·
                refine ⟨133815226591118290982059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11418899335775427497135701 133815226591118290982059)
                ·
                  rfl

theorem cell22_3518157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 8].length) (baseStart_3518157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518157 prefixEnd_3518157 := by exact prefixLift 3518157
  have htrace : WordTrace (prefixWord ++ tailWord_3518157) baseStart_3518157 baseEnd_3518157 := by
    simpa [prefixWord, tailWord_3518157, baseEnd_3518157] using wordTrace_append hprefix tailTrace_3518157
  have hstable : (prefixWord ++ tailWord_3518157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518157).length < 2 ^ (prefixWord ++ tailWord_3518157).sum := by decide
  have hdescent : baseEnd_3518157 < baseStart_3518157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518275 : List Nat := [1, 1, 1, 3, 1, 6, 1, 8]
def baseStart_3518275 : Nat := 118140960795 + 3518275 * 2 ^ 59
def prefixEnd_3518275 : Nat := 4983230072969 + 3 ^ 40 * 3518275 * 2
def baseEnd_3518275 : Nat := 133819714792394627154241

theorem tailTrace_3518275 : CollatzResearch.WordTrace tailWord_3518275 prefixEnd_3518275 133819714792394627154241 := by
  unfold tailWord_3518275
  simp only [CollatzResearch.WordTrace]
  refine ⟨128322031328898023377124279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85548020885932015584749519 128322031328898023377124279)
  ·
    refine ⟨192483046993347035065686419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128322031328898023377124279 192483046993347035065686419)
    ·
      refine ⟨288724570490020552598529629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192483046993347035065686419 288724570490020552598529629)
      ·
        refine ⟨108271713933757707224448611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288724570490020552598529629 108271713933757707224448611)
        ·
          refine ⟨162407570900636560836672917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108271713933757707224448611 162407570900636560836672917)
          ·
            refine ⟨7612854885967338789219043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 162407570900636560836672917 7612854885967338789219043)
            ·
              refine ⟨11419282328951008183828565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7612854885967338789219043 11419282328951008183828565)
              ·
                refine ⟨133819714792394627154241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11419282328951008183828565 133819714792394627154241)
                ·
                  rfl

theorem cell22_3518275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_3518275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518275 prefixEnd_3518275 := by exact prefixLift 3518275
  have htrace : WordTrace (prefixWord ++ tailWord_3518275) baseStart_3518275 baseEnd_3518275 := by
    simpa [prefixWord, tailWord_3518275, baseEnd_3518275] using wordTrace_append hprefix tailTrace_3518275
  have hstable : (prefixWord ++ tailWord_3518275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518275).length < 2 ^ (prefixWord ++ tailWord_3518275).sum := by decide
  have hdescent : baseEnd_3518275 < baseStart_3518275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518292 : List Nat := [2, 4, 1, 1, 3, 3, 8]
def baseStart_3518292 : Nat := 118140960795 + 3518292 * 2 ^ 59
def prefixEnd_3518292 : Nat := 4983230072969 + 3 ^ 40 * 3518292 * 2
def baseEnd_3518292 : Nat := 44606787132554417285671

theorem tailTrace_3518292 : CollatzResearch.WordTrace tailWord_3518292 prefixEnd_3518292 44606787132554417285671 := by
  unfold tailWord_3518292
  simp only [CollatzResearch.WordTrace]
  refine ⟨64161325684918217640246565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85548434246557623520328753 64161325684918217640246565)
  ·
    refine ⟨12030248565922165807546231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64161325684918217640246565 12030248565922165807546231)
    ·
      refine ⟨18045372848883248711319347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12030248565922165807546231 18045372848883248711319347)
      ·
        refine ⟨27068059273324873066979021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18045372848883248711319347 27068059273324873066979021)
        ·
          refine ⟨10150522227496827400117133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27068059273324873066979021 10150522227496827400117133)
          ·
            refine ⟨3806445835311310275043925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10150522227496827400117133 3806445835311310275043925)
            ·
              refine ⟨44606787132554417285671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3806445835311310275043925 44606787132554417285671)
              ·
                rfl

theorem cell22_3518292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 8].length) (baseStart_3518292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518292 prefixEnd_3518292 := by exact prefixLift 3518292
  have htrace : WordTrace (prefixWord ++ tailWord_3518292) baseStart_3518292 baseEnd_3518292 := by
    simpa [prefixWord, tailWord_3518292, baseEnd_3518292] using wordTrace_append hprefix tailTrace_3518292
  have hstable : (prefixWord ++ tailWord_3518292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518292).length < 2 ^ (prefixWord ++ tailWord_3518292).sum := by decide
  have hdescent : baseEnd_3518292 < baseStart_3518292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518305 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3518305 : Nat := 118140960795 + 3518305 * 2 ^ 59
def prefixEnd_3518305 : Nat := 4983230072969 + 3 ^ 40 * 3518305 * 2
def baseEnd_3518305 : Nat := 1204387702744641566138077

theorem tailTrace_3518305 : CollatzResearch.WordTrace tailWord_3518305 prefixEnd_3518305 1204387702744641566138077 := by
  unfold tailWord_3518305
  simp only [CollatzResearch.WordTrace]
  refine ⟨128323125518789338500716369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85548750345859559000477579 128323125518789338500716369)
  ·
    refine ⟨96242344139092003875537277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128323125518789338500716369 96242344139092003875537277)
    ·
      refine ⟨36090879052159501453326479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96242344139092003875537277 36090879052159501453326479)
      ·
        refine ⟨54136318578239252179989719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36090879052159501453326479 54136318578239252179989719)
        ·
          refine ⟨81204477867358878269984579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54136318578239252179989719 81204477867358878269984579)
          ·
            refine ⟨121806716801038317404976869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81204477867358878269984579 121806716801038317404976869)
            ·
              refine ⟨22838759400194684513433163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121806716801038317404976869 22838759400194684513433163)
              ·
                refine ⟨34258139100292026770149745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22838759400194684513433163 34258139100292026770149745)
                ·
                  refine ⟨25693604325219020077612309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34258139100292026770149745 25693604325219020077612309)
                  ·
                    refine ⟨1204387702744641566138077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25693604325219020077612309 1204387702744641566138077)
                    ·
                      rfl

theorem cell22_3518305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3518305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518305 prefixEnd_3518305 := by exact prefixLift 3518305
  have htrace : WordTrace (prefixWord ++ tailWord_3518305) baseStart_3518305 baseEnd_3518305 := by
    simpa [prefixWord, tailWord_3518305, baseEnd_3518305] using wordTrace_append hprefix tailTrace_3518305
  have hstable : (prefixWord ++ tailWord_3518305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518305).length < 2 ^ (prefixWord ++ tailWord_3518305).sum := by decide
  have hdescent : baseEnd_3518305 < baseStart_3518305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518335 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_3518335 : Nat := 118140960795 + 3518335 * 2 ^ 59
def prefixEnd_3518335 : Nat := 4983230072969 + 3 ^ 40 * 3518335 * 2
def baseEnd_3518335 : Nat := 1204397972357731487887985

theorem tailTrace_3518335 : CollatzResearch.WordTrace tailWord_3518335 prefixEnd_3518335 1204397972357731487887985 := by
  unfold tailWord_3518335
  simp only [CollatzResearch.WordTrace]
  refine ⟨128324219708680653624308459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85549479805787102416205639 128324219708680653624308459)
  ·
    refine ⟨192486329563020980436462689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128324219708680653624308459 192486329563020980436462689)
    ·
      refine ⟨144364747172265735327347017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192486329563020980436462689 144364747172265735327347017)
      ·
        refine ⟨108273560379199301495510263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144364747172265735327347017 108273560379199301495510263)
        ·
          refine ⟨162410340568798952243265395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108273560379199301495510263 162410340568798952243265395)
          ·
            refine ⟨243615510853198428364898093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162410340568798952243265395 243615510853198428364898093)
            ·
              refine ⟨91355816569949410636836785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243615510853198428364898093 91355816569949410636836785)
              ·
                refine ⟨68516862427462057977627589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91355816569949410636836785 68516862427462057977627589)
                ·
                  refine ⟨12846911705149135870805173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 68516862427462057977627589 12846911705149135870805173)
                  ·
                    refine ⟨1204397972357731487887985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12846911705149135870805173 1204397972357731487887985)
                    ·
                      rfl

theorem cell22_3518335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_3518335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518335 prefixEnd_3518335 := by exact prefixLift 3518335
  have htrace : WordTrace (prefixWord ++ tailWord_3518335) baseStart_3518335 baseEnd_3518335 := by
    simpa [prefixWord, tailWord_3518335, baseEnd_3518335] using wordTrace_append hprefix tailTrace_3518335
  have hstable : (prefixWord ++ tailWord_3518335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518335).length < 2 ^ (prefixWord ++ tailWord_3518335).sum := by decide
  have hdescent : baseEnd_3518335 < baseStart_3518335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518354 : List Nat := [3, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_3518354 : Nat := 118140960795 + 3518354 * 2 ^ 59
def prefixEnd_3518354 : Nat := 4983230072969 + 3 ^ 40 * 3518354 * 2
def baseEnd_3518354 : Nat := 401468158815340590554309

theorem tailTrace_3518354 : CollatzResearch.WordTrace tailWord_3518354 prefixEnd_3518354 401468158815340590554309 := by
  unfold tailWord_3518354
  simp only [CollatzResearch.WordTrace]
  refine ⟨32081228173902954967312529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85549941797074546579500077 32081228173902954967312529)
  ·
    refine ⟨24060921130427216225484397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32081228173902954967312529 24060921130427216225484397)
    ·
      refine ⟨9022845423910206084556649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24060921130427216225484397 9022845423910206084556649)
      ·
        refine ⟨6767134067932654563417487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9022845423910206084556649 6767134067932654563417487)
        ·
          refine ⟨10150701101898981845126231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6767134067932654563417487 10150701101898981845126231)
          ·
            refine ⟨15226051652848472767689347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10150701101898981845126231 15226051652848472767689347)
            ·
              refine ⟨22839077479272709151534021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226051652848472767689347 22839077479272709151534021)
              ·
                refine ⟨4282327027363632965912629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22839077479272709151534021 4282327027363632965912629)
                ·
                  refine ⟨401468158815340590554309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4282327027363632965912629 401468158815340590554309)
                  ·
                    rfl

theorem cell22_3518354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_3518354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518354 prefixEnd_3518354 := by exact prefixLift 3518354
  have htrace : WordTrace (prefixWord ++ tailWord_3518354) baseStart_3518354 baseEnd_3518354 := by
    simpa [prefixWord, tailWord_3518354, baseEnd_3518354] using wordTrace_append hprefix tailTrace_3518354
  have hstable : (prefixWord ++ tailWord_3518354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518354).length < 2 ^ (prefixWord ++ tailWord_3518354).sum := by decide
  have hdescent : baseEnd_3518354 < baseStart_3518354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518369 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3518369 : Nat := 118140960795 + 3518369 * 2 ^ 59
def prefixEnd_3518369 : Nat := 4983230072969 + 3 ^ 40 * 3518369 * 2
def baseEnd_3518369 : Nat := 1204409611252566732537881

theorem tailTrace_3518369 : CollatzResearch.WordTrace tailWord_3518369 prefixEnd_3518369 1204409611252566732537881 := by
  unfold tailWord_3518369
  simp only [CollatzResearch.WordTrace]
  refine ⟨128325459790557477431046161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85550306527038318287364107 128325459790557477431046161)
  ·
    refine ⟨96244094842918108073284621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128325459790557477431046161 96244094842918108073284621)
    ·
      refine ⟨36091535566094290527481733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96244094842918108073284621 36091535566094290527481733)
      ·
        refine ⟨6767162918642679473902825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36091535566094290527481733 6767162918642679473902825)
        ·
          refine ⟨5075372188982009605427119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6767162918642679473902825 5075372188982009605427119)
          ·
            refine ⟨7613058283473014408140679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5075372188982009605427119 7613058283473014408140679)
            ·
              refine ⟨11419587425209521612211019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613058283473014408140679 11419587425209521612211019)
              ·
                refine ⟨17129381137814282418316529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11419587425209521612211019 17129381137814282418316529)
                ·
                  refine ⟨12847035853360711813737397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17129381137814282418316529 12847035853360711813737397)
                  ·
                    refine ⟨1204409611252566732537881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12847035853360711813737397 1204409611252566732537881)
                    ·
                      rfl

theorem cell22_3518369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3518369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518369 prefixEnd_3518369 := by exact prefixLift 3518369
  have htrace : WordTrace (prefixWord ++ tailWord_3518369) baseStart_3518369 baseEnd_3518369 := by
    simpa [prefixWord, tailWord_3518369, baseEnd_3518369] using wordTrace_append hprefix tailTrace_3518369
  have hstable : (prefixWord ++ tailWord_3518369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518369).length < 2 ^ (prefixWord ++ tailWord_3518369).sum := by decide
  have hdescent : baseEnd_3518369 < baseStart_3518369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518399 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 4]
def baseStart_3518399 : Nat := 118140960795 + 3518399 * 2 ^ 59
def prefixEnd_3518399 : Nat := 4983230072969 + 3 ^ 40 * 3518399 * 2
def baseEnd_3518399 : Nat := 401473293621885551429263

theorem tailTrace_3518399 : CollatzResearch.WordTrace tailWord_3518399 prefixEnd_3518399 401473293621885551429263 := by
  unfold tailWord_3518399
  simp only [CollatzResearch.WordTrace]
  refine ⟨128326553980448792554638251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85551035986965861703092167 128326553980448792554638251)
  ·
    refine ⟨192489830970673188831957377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128326553980448792554638251 192489830970673188831957377)
    ·
      refine ⟨144367373228004891623968033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192489830970673188831957377 144367373228004891623968033)
      ·
        refine ⟨108275529921003668717976025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144367373228004891623968033 108275529921003668717976025)
        ·
          refine ⟨81206647440752751538482019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108275529921003668717976025 81206647440752751538482019)
          ·
            refine ⟨121809971161129127307723029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81206647440752751538482019 121809971161129127307723029)
            ·
              refine ⟨5709842398177927842549517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121809971161129127307723029 5709842398177927842549517)
              ·
                refine ⟨2141190899316722940956069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5709842398177927842549517 2141190899316722940956069)
                ·
                  refine ⟨401473293621885551429263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141190899316722940956069 401473293621885551429263)
                  ·
                    rfl

theorem cell22_3518399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 4].length) (baseStart_3518399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518399 prefixEnd_3518399 := by exact prefixLift 3518399
  have htrace : WordTrace (prefixWord ++ tailWord_3518399) baseStart_3518399 baseEnd_3518399 := by
    simpa [prefixWord, tailWord_3518399, baseEnd_3518399] using wordTrace_append hprefix tailTrace_3518399
  have hstable : (prefixWord ++ tailWord_3518399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518399).length < 2 ^ (prefixWord ++ tailWord_3518399).sum := by decide
  have hdescent : baseEnd_3518399 < baseStart_3518399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518414 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3518414 : Nat := 118140960795 + 3518414 * 2 ^ 59
def prefixEnd_3518414 : Nat := 4983230072969 + 3 ^ 40 * 3518414 * 2
def baseEnd_3518414 : Nat := 1204425015672201615162743

theorem tailTrace_3518414 : CollatzResearch.WordTrace tailWord_3518414 prefixEnd_3518414 1204425015672201615162743 := by
  unfold tailWord_3518414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040887634424306264554287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85551400716929633410956197 16040887634424306264554287)
  ·
    refine ⟨24061331451636459396831431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040887634424306264554287 24061331451636459396831431)
    ·
      refine ⟨36091997177454689095247147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24061331451636459396831431 36091997177454689095247147)
      ·
        refine ⟨54137995766182033642870721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36091997177454689095247147 54137995766182033642870721)
        ·
          refine ⟨40603496824636525232153041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54137995766182033642870721 40603496824636525232153041)
          ·
            refine ⟨30452622618477393924114781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40603496824636525232153041 30452622618477393924114781)
            ·
              refine ⟨11419733481929022721543043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30452622618477393924114781 11419733481929022721543043)
              ·
                refine ⟨17129600222893534082314565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11419733481929022721543043 17129600222893534082314565)
                ·
                  refine ⟨3211800041792537640433981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17129600222893534082314565 3211800041792537640433981)
                  ·
                    refine ⟨1204425015672201615162743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211800041792537640433981 1204425015672201615162743)
                    ·
                      rfl

theorem cell22_3518414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3518414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518414 prefixEnd_3518414 := by exact prefixLift 3518414
  have htrace : WordTrace (prefixWord ++ tailWord_3518414) baseStart_3518414 baseEnd_3518414 := by
    simpa [prefixWord, tailWord_3518414, baseEnd_3518414] using wordTrace_append hprefix tailTrace_3518414
  have hstable : (prefixWord ++ tailWord_3518414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518414).length < 2 ^ (prefixWord ++ tailWord_3518414).sum := by decide
  have hdescent : baseEnd_3518414 < baseStart_3518414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518442 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3518442 : Nat := 118140960795 + 3518442 * 2 ^ 59
def prefixEnd_3518442 : Nat := 4983230072969 + 3 ^ 40 * 3518442 * 2
def baseEnd_3518442 : Nat := 1204434600644418875462657

theorem tailTrace_3518442 : CollatzResearch.WordTrace tailWord_3518442 prefixEnd_3518442 1204434600644418875462657 := by
  unfold tailWord_3518442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32082030579823252724613395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85552081546195340598969053 32082030579823252724613395)
  ·
    refine ⟨48123045869734879086920093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32082030579823252724613395 48123045869734879086920093)
    ·
      refine ⟨18046142201150579657595035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48123045869734879086920093 18046142201150579657595035)
      ·
        refine ⟨27069213301725869486392553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18046142201150579657595035 27069213301725869486392553)
        ·
          refine ⟨20301909976294402114794415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27069213301725869486392553 20301909976294402114794415)
          ·
            refine ⟨30452864964441603172191623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20301909976294402114794415 30452864964441603172191623)
            ·
              refine ⟨45679297446662404758287435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30452864964441603172191623 45679297446662404758287435)
              ·
                refine ⟨68518946169993607137431153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45679297446662404758287435 68518946169993607137431153)
                ·
                  refine ⟨51389209627495205353073365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68518946169993607137431153 51389209627495205353073365)
                  ·
                    refine ⟨1204434600644418875462657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51389209627495205353073365 1204434600644418875462657)
                    ·
                      rfl

theorem cell22_3518442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3518442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518442 prefixEnd_3518442 := by exact prefixLift 3518442
  have htrace : WordTrace (prefixWord ++ tailWord_3518442) baseStart_3518442 baseEnd_3518442 := by
    simpa [prefixWord, tailWord_3518442, baseEnd_3518442] using wordTrace_append hprefix tailTrace_3518442
  have hstable : (prefixWord ++ tailWord_3518442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518442).length < 2 ^ (prefixWord ++ tailWord_3518442).sum := by decide
  have hdescent : baseEnd_3518442 < baseStart_3518442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518472 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_3518472 : Nat := 118140960795 + 3518472 * 2 ^ 59
def prefixEnd_3518472 : Nat := 4983230072969 + 3 ^ 40 * 3518472 * 2
def baseEnd_3518472 : Nat := 401481623419169599070855

theorem tailTrace_3518472 : CollatzResearch.WordTrace tailWord_3518472 prefixEnd_3518472 401481623419169599070855 := by
  unfold tailWord_3518472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64164608254592163011022835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85552811006122884014697113 64164608254592163011022835)
  ·
    refine ⟨96246912381888244516534253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64164608254592163011022835 96246912381888244516534253)
    ·
      refine ⟨36092592143208091693700345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96246912381888244516534253 36092592143208091693700345)
      ·
        refine ⟨27069444107406068770275259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36092592143208091693700345 27069444107406068770275259)
        ·
          refine ⟨40604166161109103155412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27069444107406068770275259 40604166161109103155412889)
          ·
            refine ⟨30453124620831827366559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40604166161109103155412889 30453124620831827366559667)
            ·
              refine ⟨45679686931247741049839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30453124620831827366559667 45679686931247741049839501)
              ·
                refine ⟨17129882599217902893689813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45679686931247741049839501 17129882599217902893689813)
                ·
                  refine ⟨401481623419169599070855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17129882599217902893689813 401481623419169599070855)
                  ·
                    rfl

theorem cell22_3518472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_3518472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518472 prefixEnd_3518472 := by exact prefixLift 3518472
  have htrace : WordTrace (prefixWord ++ tailWord_3518472) baseStart_3518472 baseEnd_3518472 := by
    simpa [prefixWord, tailWord_3518472, baseEnd_3518472] using wordTrace_append hprefix tailTrace_3518472
  have hstable : (prefixWord ++ tailWord_3518472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518472).length < 2 ^ (prefixWord ++ tailWord_3518472).sum := by decide
  have hdescent : baseEnd_3518472 < baseStart_3518472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518519 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 1, 4]
def baseStart_3518519 : Nat := 118140960795 + 3518519 * 2 ^ 59
def prefixEnd_3518519 : Nat := 4983230072969 + 3 ^ 40 * 3518519 * 2
def baseEnd_3518519 : Nat := 1204460959318016341287421

theorem tailTrace_3518519 : CollatzResearch.WordTrace tailWord_3518519 prefixEnd_3518519 1204460959318016341287421 := by
  unfold tailWord_3518519
  simp only [CollatzResearch.WordTrace]
  refine ⟨128330930740014053049006611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85553953826676035366004407 128330930740014053049006611)
  ·
    refine ⟨192496396110021079573509917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128330930740014053049006611 192496396110021079573509917)
    ·
      refine ⟨72186148541257904840066219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192496396110021079573509917 72186148541257904840066219)
      ·
        refine ⟨108279222811886857260099329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72186148541257904840066219 108279222811886857260099329)
        ·
          refine ⟨81209417108915142945074497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108279222811886857260099329 81209417108915142945074497)
          ·
            refine ⟨60907062831686357208805873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81209417108915142945074497 60907062831686357208805873)
            ·
              refine ⟨45680297123764767906604405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60907062831686357208805873 45680297123764767906604405)
              ·
                refine ⟨4282527855352946991244163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45680297123764767906604405 4282527855352946991244163)
                ·
                  refine ⟨6423791783029420486866245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282527855352946991244163 6423791783029420486866245)
                  ·
                    refine ⟨1204460959318016341287421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423791783029420486866245 1204460959318016341287421)
                    ·
                      rfl

theorem cell22_3518519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_3518519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518519 prefixEnd_3518519 := by exact prefixLift 3518519
  have htrace : WordTrace (prefixWord ++ tailWord_3518519) baseStart_3518519 baseEnd_3518519 := by
    simpa [prefixWord, tailWord_3518519, baseEnd_3518519] using wordTrace_append hprefix tailTrace_3518519
  have hstable : (prefixWord ++ tailWord_3518519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518519).length < 2 ^ (prefixWord ++ tailWord_3518519).sum := by decide
  have hdescent : baseEnd_3518519 < baseStart_3518519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518549 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3518549 : Nat := 118140960795 + 3518549 * 2 ^ 59
def prefixEnd_3518549 : Nat := 4983230072969 + 3 ^ 40 * 3518549 * 2
def baseEnd_3518549 : Nat := 1204471228931106263037329

theorem tailTrace_3518549 : CollatzResearch.WordTrace tailWord_3518549 prefixEnd_3518549 1204471228931106263037329 := by
  unfold tailWord_3518549
  simp only [CollatzResearch.WordTrace]
  refine ⟨128332024929905368172598701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85554683286603578781732467 128332024929905368172598701)
  ·
    refine ⟨48124509348714513064724513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128332024929905368172598701 48124509348714513064724513)
    ·
      refine ⟨36093382011535884798543385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48124509348714513064724513 36093382011535884798543385)
      ·
        refine ⟨27070036508651913598907539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36093382011535884798543385 27070036508651913598907539)
        ·
          refine ⟨40605054762977870398361309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27070036508651913598907539 40605054762977870398361309)
          ·
            refine ⟨15226895536116701399385491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40605054762977870398361309 15226895536116701399385491)
            ·
              refine ⟨22840343304175052099078237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226895536116701399385491 22840343304175052099078237)
              ·
                refine ⟨8565128739065644537154339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22840343304175052099078237 8565128739065644537154339)
                ·
                  refine ⟨12847693108598466805731509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565128739065644537154339 12847693108598466805731509)
                  ·
                    refine ⟨1204471228931106263037329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12847693108598466805731509 1204471228931106263037329)
                    ·
                      rfl

theorem cell22_3518549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3518549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518549 prefixEnd_3518549 := by exact prefixLift 3518549
  have htrace : WordTrace (prefixWord ++ tailWord_3518549) baseStart_3518549 baseEnd_3518549 := by
    simpa [prefixWord, tailWord_3518549, baseEnd_3518549] using wordTrace_append hprefix tailTrace_3518549
  have hstable : (prefixWord ++ tailWord_3518549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518549).length < 2 ^ (prefixWord ++ tailWord_3518549).sum := by decide
  have hdescent : baseEnd_3518549 < baseStart_3518549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518570 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_3518570 : Nat := 118140960795 + 3518570 * 2 ^ 59
def prefixEnd_3518570 : Nat := 4983230072969 + 3 ^ 40 * 3518570 * 2
def baseEnd_3518570 : Nat := 1204478417660269208262265

theorem tailTrace_3518570 : CollatzResearch.WordTrace tailWord_3518570 prefixEnd_3518570 1204478417660269208262265 := by
  unfold tailWord_3518570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32083197715707322189778291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85555193908552859172742109 32083197715707322189778291)
  ·
    refine ⟨48124796573560983284667437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32083197715707322189778291 48124796573560983284667437)
    ·
      refine ⟨18046798715085368731750289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48124796573560983284667437 18046798715085368731750289)
      ·
        refine ⟨13535099036314026548812717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18046798715085368731750289 13535099036314026548812717)
        ·
          refine ⟨5075662138617759955804769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13535099036314026548812717 5075662138617759955804769)
          ·
            refine ⟨3806746603963319966853577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5075662138617759955804769 3806746603963319966853577)
            ·
              refine ⟨2855059952972489975140183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3806746603963319966853577 2855059952972489975140183)
              ·
                refine ⟨4282589929458734962710275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855059952972489975140183 4282589929458734962710275)
                ·
                  refine ⟨6423884894188102444065413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282589929458734962710275 6423884894188102444065413)
                  ·
                    refine ⟨1204478417660269208262265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6423884894188102444065413 1204478417660269208262265)
                    ·
                      rfl

theorem cell22_3518570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_3518570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518570 prefixEnd_3518570 := by exact prefixLift 3518570
  have htrace : WordTrace (prefixWord ++ tailWord_3518570) baseStart_3518570 baseEnd_3518570 := by
    simpa [prefixWord, tailWord_3518570, baseEnd_3518570] using wordTrace_append hprefix tailTrace_3518570
  have hstable : (prefixWord ++ tailWord_3518570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518570).length < 2 ^ (prefixWord ++ tailWord_3518570).sum := by decide
  have hdescent : baseEnd_3518570 < baseStart_3518570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518583 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 2, 3]
def baseStart_3518583 : Nat := 118140960795 + 3518583 * 2 ^ 59
def prefixEnd_3518583 : Nat := 4983230072969 + 3 ^ 40 * 3518583 * 2
def baseEnd_3518583 : Nat := 1204482867825941507687225

theorem tailTrace_3518583 : CollatzResearch.WordTrace tailWord_3518583 prefixEnd_3518583 1204482867825941507687225 := by
  unfold tailWord_3518583
  simp only [CollatzResearch.WordTrace]
  refine ⟨128333265011782191979336403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85555510007854794652890935 128333265011782191979336403)
  ·
    refine ⟨192499897517673287969004605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128333265011782191979336403 192499897517673287969004605)
    ·
      refine ⟨72187461569127482988376727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192499897517673287969004605 72187461569127482988376727)
      ·
        refine ⟨108281192353691224482565091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72187461569127482988376727 108281192353691224482565091)
        ·
          refine ⟨162421788530536836723847637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108281192353691224482565091 162421788530536836723847637)
          ·
            refine ⟨3806760668684457110715179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 162421788530536836723847637 3806760668684457110715179)
            ·
              refine ⟨5710141003026685666072769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3806760668684457110715179 5710141003026685666072769)
              ·
                refine ⟨4282605752270014249554577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5710141003026685666072769 4282605752270014249554577)
                ·
                  refine ⟨3211954314202510687165933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282605752270014249554577 3211954314202510687165933)
                  ·
                    refine ⟨1204482867825941507687225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211954314202510687165933 1204482867825941507687225)
                    ·
                      rfl

theorem cell22_3518583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_3518583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518583 prefixEnd_3518583 := by exact prefixLift 3518583
  have htrace : WordTrace (prefixWord ++ tailWord_3518583) baseStart_3518583 baseEnd_3518583 := by
    simpa [prefixWord, tailWord_3518583, baseEnd_3518583] using wordTrace_append hprefix tailTrace_3518583
  have hstable : (prefixWord ++ tailWord_3518583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518583).length < 2 ^ (prefixWord ++ tailWord_3518583).sum := by decide
  have hdescent : baseEnd_3518583 < baseStart_3518583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518600 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_3518600 : Nat := 118140960795 + 3518600 * 2 ^ 59
def prefixEnd_3518600 : Nat := 4983230072969 + 3 ^ 40 * 3518600 * 2
def baseEnd_3518600 : Nat := 1204488687273359130012173

theorem tailTrace_3518600 : CollatzResearch.WordTrace tailWord_3518600 prefixEnd_3518600 1204488687273359130012173 := by
  unfold tailWord_3518600
  simp only [CollatzResearch.WordTrace]
  refine ⟨64166942526360301941352627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85555923368480402588470169 64166942526360301941352627)
  ·
    refine ⟨96250413789540452912028941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64166942526360301941352627 96250413789540452912028941)
    ·
      refine ⟨36093905171077669842010853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96250413789540452912028941 36093905171077669842010853)
      ·
        refine ⟨6767607219577063095377035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36093905171077669842010853 6767607219577063095377035)
        ·
          refine ⟨10151410829365594643065553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6767607219577063095377035 10151410829365594643065553)
          ·
            refine ⟨7613558122024195982299165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10151410829365594643065553 7613558122024195982299165)
            ·
              refine ⟨2855084295759073493362187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7613558122024195982299165 2855084295759073493362187)
              ·
                refine ⟨4282626443638610240043281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855084295759073493362187 4282626443638610240043281)
                ·
                  refine ⟨3211969832728957680032461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4282626443638610240043281 3211969832728957680032461)
                  ·
                    refine ⟨1204488687273359130012173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3211969832728957680032461 1204488687273359130012173)
                    ·
                      rfl

theorem cell22_3518600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_3518600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518600 prefixEnd_3518600 := by exact prefixLift 3518600
  have htrace : WordTrace (prefixWord ++ tailWord_3518600) baseStart_3518600 baseEnd_3518600 := by
    simpa [prefixWord, tailWord_3518600, baseEnd_3518600] using wordTrace_append hprefix tailTrace_3518600
  have hstable : (prefixWord ++ tailWord_3518600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518600).length < 2 ^ (prefixWord ++ tailWord_3518600).sum := by decide
  have hdescent : baseEnd_3518600 < baseStart_3518600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518624 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_3518624 : Nat := 118140960795 + 3518624 * 2 ^ 59
def prefixEnd_3518624 : Nat := 4983230072969 + 3 ^ 40 * 3518624 * 2
def baseEnd_3518624 : Nat := 401498967654610355804033

theorem tailTrace_3518624 : CollatzResearch.WordTrace tailWord_3518624 prefixEnd_3518624 401498967654610355804033 := by
  unfold tailWord_3518624
  simp only [CollatzResearch.WordTrace]
  refine ⟨64167380202316827990789463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85556506936422437321052617 64167380202316827990789463)
  ·
    refine ⟨96251070303475241986184195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64167380202316827990789463 96251070303475241986184195)
    ·
      refine ⟨144376605455212862979276293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96251070303475241986184195 144376605455212862979276293)
      ·
        refine ⟨27070613522852411808614305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144376605455212862979276293 27070613522852411808614305)
        ·
          refine ⟨20302960142139308856460729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27070613522852411808614305 20302960142139308856460729)
          ·
            refine ⟨15227220106604481642345547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20302960142139308856460729 15227220106604481642345547)
            ·
              refine ⟨22840830159906722463518321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15227220106604481642345547 22840830159906722463518321)
              ·
                refine ⟨17130622619930041847638741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22840830159906722463518321 17130622619930041847638741)
                ·
                  refine ⟨401498967654610355804033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17130622619930041847638741 401498967654610355804033)
                  ·
                    rfl

theorem cell22_3518624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_3518624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518624 prefixEnd_3518624 := by exact prefixLift 3518624
  have htrace : WordTrace (prefixWord ++ tailWord_3518624) baseStart_3518624 baseEnd_3518624 := by
    simpa [prefixWord, tailWord_3518624, baseEnd_3518624] using wordTrace_append hprefix tailTrace_3518624
  have hstable : (prefixWord ++ tailWord_3518624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518624).length < 2 ^ (prefixWord ++ tailWord_3518624).sum := by decide
  have hdescent : baseEnd_3518624 < baseStart_3518624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518688 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_3518688 : Nat := 118140960795 + 3518688 * 2 ^ 59
def prefixEnd_3518688 : Nat := 4983230072969 + 3 ^ 40 * 3518688 * 2
def baseEnd_3518688 : Nat := 1204518811471756233811903

theorem tailTrace_3518688 : CollatzResearch.WordTrace tailWord_3518688 prefixEnd_3518688 1204518811471756233811903 := by
  unfold tailWord_3518688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64168547338200897455954359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85558063117601196607939145 64168547338200897455954359)
  ·
    refine ⟨96252821007301346183931539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64168547338200897455954359 96252821007301346183931539)
    ·
      refine ⟨144379231510952019275897309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96252821007301346183931539 144379231510952019275897309)
      ·
        refine ⟨54142211816607007228461491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144379231510952019275897309 54142211816607007228461491)
        ·
          refine ⟨81213317724910510842692237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54142211816607007228461491 81213317724910510842692237)
          ·
            refine ⟨30454994146841441566009589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81213317724910510842692237 30454994146841441566009589)
            ·
              refine ⟨2855155701266385146813399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30454994146841441566009589 2855155701266385146813399)
              ·
                refine ⟨4282733551899577720220099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855155701266385146813399 4282733551899577720220099)
                ·
                  refine ⟨6424100327849366580330149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4282733551899577720220099 6424100327849366580330149)
                  ·
                    refine ⟨1204518811471756233811903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424100327849366580330149 1204518811471756233811903)
                    ·
                      rfl

theorem cell22_3518688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_3518688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518688 prefixEnd_3518688 := by exact prefixLift 3518688
  have htrace : WordTrace (prefixWord ++ tailWord_3518688) baseStart_3518688 baseEnd_3518688 := by
    simpa [prefixWord, tailWord_3518688, baseEnd_3518688] using wordTrace_append hprefix tailTrace_3518688
  have hstable : (prefixWord ++ tailWord_3518688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518688).length < 2 ^ (prefixWord ++ tailWord_3518688).sum := by decide
  have hdescent : baseEnd_3518688 < baseStart_3518688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518703 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 4]
def baseStart_3518703 : Nat := 118140960795 + 3518703 * 2 ^ 59
def prefixEnd_3518703 : Nat := 4983230072969 + 3 ^ 40 * 3518703 * 2
def baseEnd_3518703 : Nat := 401507982092767064895619

theorem tailTrace_3518703 : CollatzResearch.WordTrace tailWord_3518703 prefixEnd_3518703 401507982092767064895619 := by
  unfold tailWord_3518703
  simp only [CollatzResearch.WordTrace]
  refine ⟨128337641771347452473704763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85558427847564968315803175 128337641771347452473704763)
  ·
    refine ⟨192506462657021178710557145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128337641771347452473704763 192506462657021178710557145)
    ·
      refine ⟨144379846992765884032917859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192506462657021178710557145 144379846992765884032917859)
      ·
        refine ⟨216569770489148826049376789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144379846992765884032917859 216569770489148826049376789)
        ·
          refine ⟨10151707991678851221064537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 216569770489148826049376789 10151707991678851221064537)
          ·
            refine ⟨7613780993759138415798403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10151707991678851221064537 7613780993759138415798403)
            ·
              refine ⟨11420671490638707623697605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7613780993759138415798403 11420671490638707623697605)
              ·
                refine ⟨2141375904494757679443301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11420671490638707623697605 2141375904494757679443301)
                ·
                  refine ⟨401507982092767064895619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141375904494757679443301 401507982092767064895619)
                  ·
                    rfl

theorem cell22_3518703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 4].length) (baseStart_3518703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518703 prefixEnd_3518703 := by exact prefixLift 3518703
  have htrace : WordTrace (prefixWord ++ tailWord_3518703) baseStart_3518703 baseEnd_3518703 := by
    simpa [prefixWord, tailWord_3518703, baseEnd_3518703] using wordTrace_append hprefix tailTrace_3518703
  have hstable : (prefixWord ++ tailWord_3518703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518703).length < 2 ^ (prefixWord ++ tailWord_3518703).sum := by decide
  have hdescent : baseEnd_3518703 < baseStart_3518703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518718 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_3518718 : Nat := 118140960795 + 3518718 * 2 ^ 59
def prefixEnd_3518718 : Nat := 4983230072969 + 3 ^ 40 * 3518718 * 2
def baseEnd_3518718 : Nat := 1204529081084846155561811

theorem tailTrace_3518718 : CollatzResearch.WordTrace tailWord_3518718 prefixEnd_3518718 1204529081084846155561811 := by
  unfold tailWord_3518718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16042273608286638754437601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85558792577528740023667205 16042273608286638754437601)
  ·
    refine ⟨12031705206214979065828201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16042273608286638754437601 12031705206214979065828201)
    ·
      refine ⟨9023778904661234299371151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12031705206214979065828201 9023778904661234299371151)
      ·
        refine ⟨13535668356991851449056727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9023778904661234299371151 13535668356991851449056727)
        ·
          refine ⟨20303502535487777173585091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13535668356991851449056727 20303502535487777173585091)
          ·
            refine ⟨30455253803231665760377637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20303502535487777173585091 30455253803231665760377637)
            ·
              refine ⟨5710360088105937330070807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30455253803231665760377637 5710360088105937330070807)
              ·
                refine ⟨8565540132158905995106211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710360088105937330070807 8565540132158905995106211)
                ·
                  refine ⟨12848310198238358992659317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8565540132158905995106211 12848310198238358992659317)
                  ·
                    refine ⟨1204529081084846155561811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12848310198238358992659317 1204529081084846155561811)
                    ·
                      rfl

theorem cell22_3518718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_3518718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518718 prefixEnd_3518718 := by exact prefixLift 3518718
  have htrace : WordTrace (prefixWord ++ tailWord_3518718) baseStart_3518718 baseEnd_3518718 := by
    simpa [prefixWord, tailWord_3518718, baseEnd_3518718] using wordTrace_append hprefix tailTrace_3518718
  have hstable : (prefixWord ++ tailWord_3518718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518718).length < 2 ^ (prefixWord ++ tailWord_3518718).sum := by decide
  have hdescent : baseEnd_3518718 < baseStart_3518718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518731 : List Nat := [1, 1, 1, 1, 5, 2, 5, 6]
def baseStart_3518731 : Nat := 118140960795 + 3518731 * 2 ^ 59
def prefixEnd_3518731 : Nat := 4983230072969 + 3 ^ 40 * 3518731 * 2
def baseEnd_3518731 : Nat := 133837059027835383887419

theorem tailTrace_3518731 : CollatzResearch.WordTrace tailWord_3518731 prefixEnd_3518731 133837059027835383887419 := by
  unfold tailWord_3518731
  simp only [CollatzResearch.WordTrace]
  refine ⟨128338663015246013255724047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85559108676830675503816031 128338663015246013255724047)
  ·
    refine ⟨192507994522869019883586071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128338663015246013255724047 192507994522869019883586071)
    ·
      refine ⟨288761991784303529825379107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192507994522869019883586071 288761991784303529825379107)
      ·
        refine ⟨433142987676455294738068661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288761991784303529825379107 433142987676455294738068661)
        ·
          refine ⟨40607155094667683881693937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 433142987676455294738068661 40607155094667683881693937)
          ·
            refine ⟨30455366321000762911270453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40607155094667683881693937 30455366321000762911270453)
            ·
              refine ⟨2855190592593821522931605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30455366321000762911270453 2855190592593821522931605)
              ·
                refine ⟨133837059027835383887419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2855190592593821522931605 133837059027835383887419)
                ·
                  rfl

theorem cell22_3518731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 6].length) (baseStart_3518731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518731 prefixEnd_3518731 := by exact prefixLift 3518731
  have htrace : WordTrace (prefixWord ++ tailWord_3518731) baseStart_3518731 baseEnd_3518731 := by
    simpa [prefixWord, tailWord_3518731, baseEnd_3518731] using wordTrace_append hprefix tailTrace_3518731
  have hstable : (prefixWord ++ tailWord_3518731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518731).length < 2 ^ (prefixWord ++ tailWord_3518731).sum := by decide
  have hdescent : baseEnd_3518731 < baseStart_3518731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518776 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_3518776 : Nat := 118140960795 + 3518776 * 2 ^ 59
def prefixEnd_3518776 : Nat := 4983230072969 + 3 ^ 40 * 3518776 * 2
def baseEnd_3518776 : Nat := 401516311890051112537211

theorem tailTrace_3518776 : CollatzResearch.WordTrace tailWord_3518776 prefixEnd_3518776 401516311890051112537211 := by
  unfold tailWord_3518776
  simp only [CollatzResearch.WordTrace]
  refine ⟨64170152150041492970556091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85560202866721990627408121 64170152150041492970556091)
  ·
    refine ⟨96255228225062239455834137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64170152150041492970556091 96255228225062239455834137)
    ·
      refine ⟨72191421168796679591875603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96255228225062239455834137 72191421168796679591875603)
      ·
        refine ⟨108287131753195019387813405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72191421168796679591875603 108287131753195019387813405)
        ·
          refine ⟨40607674407448132270430027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108287131753195019387813405 40607674407448132270430027)
          ·
            refine ⟨60911511611172198405645041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40607674407448132270430027 60911511611172198405645041)
            ·
              refine ⟨45683633708379148804233781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60911511611172198405645041 45683633708379148804233781)
              ·
                refine ⟨4282840660160545200396917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45683633708379148804233781 4282840660160545200396917)
                ·
                  refine ⟨401516311890051112537211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4282840660160545200396917 401516311890051112537211)
                  ·
                    rfl

theorem cell22_3518776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_3518776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518776 prefixEnd_3518776 := by exact prefixLift 3518776
  have htrace : WordTrace (prefixWord ++ tailWord_3518776) baseStart_3518776 baseEnd_3518776 := by
    simpa [prefixWord, tailWord_3518776, baseEnd_3518776] using wordTrace_append hprefix tailTrace_3518776
  have hstable : (prefixWord ++ tailWord_3518776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518776).length < 2 ^ (prefixWord ++ tailWord_3518776).sum := by decide
  have hdescent : baseEnd_3518776 < baseStart_3518776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518866 : List Nat := [3, 2, 3, 14]
def baseStart_3518866 : Nat := 118140960795 + 3518866 * 2 ^ 59
def prefixEnd_3518866 : Nat := 4983230072969 + 3 ^ 40 * 3518866 * 2
def baseEnd_3518866 : Nat := 1652372763387411663733

theorem tailTrace_3518866 : CollatzResearch.WordTrace tailWord_3518866 prefixEnd_3518866 1652372763387411663733 := by
  unfold tailWord_3518866
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085896717439232827972113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85562391246504620874592301 32085896717439232827972113)
  ·
    refine ⟨24064422538079424620979085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32085896717439232827972113 24064422538079424620979085)
    ·
      refine ⟨9024158451779784232867157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24064422538079424620979085 9024158451779784232867157)
      ·
        refine ⟨1652372763387411663733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9024158451779784232867157 1652372763387411663733)
        ·
          rfl

theorem cell22_3518866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 14].length) (baseStart_3518866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518866 prefixEnd_3518866 := by exact prefixLift 3518866
  have htrace : WordTrace (prefixWord ++ tailWord_3518866) baseStart_3518866 baseEnd_3518866 := by
    simpa [prefixWord, tailWord_3518866, baseEnd_3518866] using wordTrace_append hprefix tailTrace_3518866
  have hstable : (prefixWord ++ tailWord_3518866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518866).length < 2 ^ (prefixWord ++ tailWord_3518866).sum := by decide
  have hdescent : baseEnd_3518866 < baseStart_3518866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518872 : List Nat := [2, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_3518872 : Nat := 118140960795 + 3518872 * 2 ^ 59
def prefixEnd_3518872 : Nat := 4983230072969 + 3 ^ 40 * 3518872 * 2
def baseEnd_3518872 : Nat := 401527266144013695737113

theorem tailTrace_3518872 : CollatzResearch.WordTrace tailWord_3518872 prefixEnd_3518872 401527266144013695737113 := by
  unfold tailWord_3518872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64171902853867597168303435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85562537138490129557737913 64171902853867597168303435)
  ·
    refine ⟨96257854280801395752455153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64171902853867597168303435 96257854280801395752455153)
    ·
      refine ⟨72193390710601046814341365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96257854280801395752455153 72193390710601046814341365)
      ·
        refine ⟨6768130379118848138844503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72193390710601046814341365 6768130379118848138844503)
        ·
          refine ⟨10152195568678272208266755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768130379118848138844503 10152195568678272208266755)
          ·
            refine ⟨15228293353017408312400133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152195568678272208266755 15228293353017408312400133)
            ·
              refine ⟨2855305003690764058575025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15228293353017408312400133 2855305003690764058575025)
              ·
                refine ⟨2141478752768073043931269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855305003690764058575025 2141478752768073043931269)
                ·
                  refine ⟨401527266144013695737113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141478752768073043931269 401527266144013695737113)
                  ·
                    rfl

theorem cell22_3518872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_3518872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518872 prefixEnd_3518872 := by exact prefixLift 3518872
  have htrace : WordTrace (prefixWord ++ tailWord_3518872) baseStart_3518872 baseEnd_3518872 := by
    simpa [prefixWord, tailWord_3518872, baseEnd_3518872] using wordTrace_append hprefix tailTrace_3518872
  have hstable : (prefixWord ++ tailWord_3518872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518872).length < 2 ^ (prefixWord ++ tailWord_3518872).sum := by decide
  have hdescent : baseEnd_3518872 < baseStart_3518872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518883 : List Nat := [1, 1, 1, 4, 1, 6, 1, 7]
def baseStart_3518883 : Nat := 118140960795 + 3518883 * 2 ^ 59
def prefixEnd_3518883 : Nat := 4983230072969 + 3 ^ 40 * 3518883 * 2
def baseEnd_3518883 : Nat := 133842840439648969465145

theorem tailTrace_3518883 : CollatzResearch.WordTrace tailWord_3518883 prefixEnd_3518883 133842840439648969465145 := by
  unfold tailWord_3518883
  simp only [CollatzResearch.WordTrace]
  refine ⟨128344206910695343215257303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85562804607130228810171535 128344206910695343215257303)
  ·
    refine ⟨192516310366043014822885955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128344206910695343215257303 192516310366043014822885955)
    ·
      refine ⟨288774465549064522234328933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192516310366043014822885955 288774465549064522234328933)
      ·
        refine ⟨54145212290449597918936675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 288774465549064522234328933 54145212290449597918936675)
        ·
          refine ⟨81217818435674396878405013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54145212290449597918936675 81217818435674396878405013)
          ·
            refine ⟨3807085239172237353675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81217818435674396878405013 3807085239172237353675235)
            ·
              refine ⟨5710627858758356030512853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807085239172237353675235 5710627858758356030512853)
              ·
                refine ⟨133842840439648969465145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5710627858758356030512853 133842840439648969465145)
                ·
                  rfl

theorem cell22_3518883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 7].length) (baseStart_3518883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518883 prefixEnd_3518883 := by exact prefixLift 3518883
  have htrace : WordTrace (prefixWord ++ tailWord_3518883) baseStart_3518883 baseEnd_3518883 := by
    simpa [prefixWord, tailWord_3518883, baseEnd_3518883] using wordTrace_append hprefix tailTrace_3518883
  have hstable : (prefixWord ++ tailWord_3518883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518883).length < 2 ^ (prefixWord ++ tailWord_3518883).sum := by decide
  have hdescent : baseEnd_3518883 < baseStart_3518883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518932 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3518932 : Nat := 118140960795 + 3518932 * 2 ^ 59
def prefixEnd_3518932 : Nat := 4983230072969 + 3 ^ 40 * 3518932 * 2
def baseEnd_3518932 : Nat := 1204602337658220930711155

theorem tailTrace_3518932 : CollatzResearch.WordTrace tailWord_3518932 prefixEnd_3518932 1204602337658220930711155 := by
  unfold tailWord_3518932
  simp only [CollatzResearch.WordTrace]
  refine ⟨64172997043758912291895525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85563996058345216389194033 64172997043758912291895525)
  ·
    refine ⟨12032436945704796054730411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64172997043758912291895525 12032436945704796054730411)
    ·
      refine ⟨18048655418557194082095617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032436945704796054730411 18048655418557194082095617)
      ·
        refine ⟨13536491563917895561571713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18048655418557194082095617 13536491563917895561571713)
        ·
          refine ⟨10152368672938421671178785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13536491563917895561571713 10152368672938421671178785)
          ·
            refine ⟨7614276504703816253384089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10152368672938421671178785 7614276504703816253384089)
            ·
              refine ⟨5710707378527862190038067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7614276504703816253384089 5710707378527862190038067)
              ·
                refine ⟨8566061067791793285057101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710707378527862190038067 8566061067791793285057101)
                ·
                  refine ⟨3212272900421922481896413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8566061067791793285057101 3212272900421922481896413)
                  ·
                    refine ⟨1204602337658220930711155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212272900421922481896413 1204602337658220930711155)
                    ·
                      rfl

theorem cell22_3518932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3518932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518932 prefixEnd_3518932 := by exact prefixLift 3518932
  have htrace : WordTrace (prefixWord ++ tailWord_3518932) baseStart_3518932 baseEnd_3518932 := by
    simpa [prefixWord, tailWord_3518932, baseEnd_3518932] using wordTrace_append hprefix tailTrace_3518932
  have hstable : (prefixWord ++ tailWord_3518932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518932).length < 2 ^ (prefixWord ++ tailWord_3518932).sum := by decide
  have hdescent : baseEnd_3518932 < baseStart_3518932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518943 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_3518943 : Nat := 118140960795 + 3518943 * 2 ^ 59
def prefixEnd_3518943 : Nat := 4983230072969 + 3 ^ 40 * 3518943 * 2
def baseEnd_3518943 : Nat := 1204606103183020568686121

theorem tailTrace_3518943 : CollatzResearch.WordTrace tailWord_3518943 prefixEnd_3518943 1204606103183020568686121 := by
  unfold tailWord_3518943
  simp only [CollatzResearch.WordTrace]
  refine ⟨128346395290477973462441483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85564263526985315641627655 128346395290477973462441483)
  ·
    refine ⟨192519592935716960193662225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128346395290477973462441483 192519592935716960193662225)
    ·
      refine ⟨144389694701787720145246669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192519592935716960193662225 144389694701787720145246669)
      ·
        refine ⟨54146135513170395054467501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144389694701787720145246669 54146135513170395054467501)
        ·
          refine ⟨20304800817438898145425313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54146135513170395054467501 20304800817438898145425313)
          ·
            refine ⟨15228600613079173609068985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20304800817438898145425313 15228600613079173609068985)
            ·
              refine ⟨11421450459809380206801739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15228600613079173609068985 11421450459809380206801739)
              ·
                refine ⟨17132175689714070310202609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11421450459809380206801739 17132175689714070310202609)
                ·
                  refine ⟨12849131767285552732651957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17132175689714070310202609 12849131767285552732651957)
                  ·
                    refine ⟨1204606103183020568686121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849131767285552732651957 1204606103183020568686121)
                    ·
                      rfl

theorem cell22_3518943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_3518943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518943 prefixEnd_3518943 := by exact prefixLift 3518943
  have htrace : WordTrace (prefixWord ++ tailWord_3518943) baseStart_3518943 baseEnd_3518943 := by
    simpa [prefixWord, tailWord_3518943, baseEnd_3518943] using wordTrace_append hprefix tailTrace_3518943
  have hstable : (prefixWord ++ tailWord_3518943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518943).length < 2 ^ (prefixWord ++ tailWord_3518943).sum := by decide
  have hdescent : baseEnd_3518943 < baseStart_3518943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518945 : List Nat := [1, 2, 3, 1, 2, 2, 5, 1, 5]
def baseStart_3518945 : Nat := 118140960795 + 3518945 * 2 ^ 59
def prefixEnd_3518945 : Nat := 4983230072969 + 3 ^ 40 * 3518945 * 2
def baseEnd_3518945 : Nat := 401535595941297743378705

theorem tailTrace_3518945 : CollatzResearch.WordTrace tailWord_3518945 prefixEnd_3518945 401535595941297743378705 := by
  unfold tailWord_3518945
  simp only [CollatzResearch.WordTrace]
  refine ⟨128346468236470727804014289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85564312157647151869342859 128346468236470727804014289)
  ·
    refine ⟨96259851177353045853010717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128346468236470727804014289 96259851177353045853010717)
    ·
      refine ⟨36097444191507392194879019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96259851177353045853010717 36097444191507392194879019)
      ·
        refine ⟨54146166287261088292318529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36097444191507392194879019 54146166287261088292318529)
        ·
          refine ⟨40609624715445816219238897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54146166287261088292318529 40609624715445816219238897)
          ·
            refine ⟨30457218536584362164429173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40609624715445816219238897 30457218536584362164429173)
            ·
              refine ⟨2855364237804783952915235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30457218536584362164429173 2855364237804783952915235)
              ·
                refine ⟨4283046356707175929372853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855364237804783952915235 4283046356707175929372853)
                ·
                  refine ⟨401535595941297743378705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283046356707175929372853 401535595941297743378705)
                  ·
                    rfl

theorem cell22_3518945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 1, 5].length) (baseStart_3518945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518945 prefixEnd_3518945 := by exact prefixLift 3518945
  have htrace : WordTrace (prefixWord ++ tailWord_3518945) baseStart_3518945 baseEnd_3518945 := by
    simpa [prefixWord, tailWord_3518945, baseEnd_3518945] using wordTrace_append hprefix tailTrace_3518945
  have hstable : (prefixWord ++ tailWord_3518945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518945).length < 2 ^ (prefixWord ++ tailWord_3518945).sum := by decide
  have hdescent : baseEnd_3518945 < baseStart_3518945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3518990 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_3518990 : Nat := 118140960795 + 3518990 * 2 ^ 59
def prefixEnd_3518990 : Nat := 4983230072969 + 3 ^ 40 * 3518990 * 2
def baseEnd_3518990 : Nat := 401540730747842704253659

theorem tailTrace_3518990 : CollatzResearch.WordTrace tailWord_3518990 prefixEnd_3518990 401540730747842704253659 := by
  unfold tailWord_3518990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043513690163462561175303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85565406347538466992934949 16043513690163462561175303)
  ·
    refine ⟨24065270535245193841762955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043513690163462561175303 24065270535245193841762955)
    ·
      refine ⟨36097905802867790762644433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24065270535245193841762955 36097905802867790762644433)
      ·
        refine ⟨27073429352150843071983325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36097905802867790762644433 27073429352150843071983325)
        ·
          refine ⟨10152536007056566151993747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27073429352150843071983325 10152536007056566151993747)
          ·
            refine ⟨15228804010584849227990621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152536007056566151993747 15228804010584849227990621)
            ·
              refine ⟨5710801503969318460496483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15228804010584849227990621 5710801503969318460496483)
              ·
                refine ⟨8566202255953977690744725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5710801503969318460496483 8566202255953977690744725)
                ·
                  refine ⟨401540730747842704253659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8566202255953977690744725 401540730747842704253659)
                  ·
                    rfl

theorem cell22_3518990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_3518990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3518990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3518990 prefixEnd_3518990 := by exact prefixLift 3518990
  have htrace : WordTrace (prefixWord ++ tailWord_3518990) baseStart_3518990 baseEnd_3518990 := by
    simpa [prefixWord, tailWord_3518990, baseEnd_3518990] using wordTrace_append hprefix tailTrace_3518990
  have hstable : (prefixWord ++ tailWord_3518990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3518990).length < 2 ^ (prefixWord ++ tailWord_3518990).sum := by decide
  have hdescent : baseEnd_3518990 < baseStart_3518990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3518990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519022 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3519022 : Nat := 118140960795 + 3519022 * 2 ^ 59
def prefixEnd_3519022 : Nat := 4983230072969 + 3 ^ 40 * 3519022 * 2
def baseEnd_3519022 : Nat := 1204633146497490695960879

theorem tailTrace_3519022 : CollatzResearch.WordTrace tailWord_3519022 prefixEnd_3519022 1204633146497490695960879 := by
  unfold tailWord_3519022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043659582148971244320915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85566184438127846636378213 16043659582148971244320915)
  ·
    refine ⟨24065489373223456866481373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16043659582148971244320915 24065489373223456866481373)
    ·
      refine ⟨9024558514958796324930515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24065489373223456866481373 9024558514958796324930515)
      ·
        refine ⟨13536837772438194487395773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024558514958796324930515 13536837772438194487395773)
        ·
          refine ⟨5076314164664322932773415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13536837772438194487395773 5076314164664322932773415)
          ·
            refine ⟨7614471246996484399160123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076314164664322932773415 7614471246996484399160123)
            ·
              refine ⟨11421706870494726598740185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7614471246996484399160123 11421706870494726598740185)
              ·
                refine ⟨8566280152871044949055139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11421706870494726598740185 8566280152871044949055139)
                ·
                  refine ⟨12849420229306567423582709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8566280152871044949055139 12849420229306567423582709)
                  ·
                    refine ⟨1204633146497490695960879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849420229306567423582709 1204633146497490695960879)
                    ·
                      rfl

theorem cell22_3519022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3519022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519022 prefixEnd_3519022 := by exact prefixLift 3519022
  have htrace : WordTrace (prefixWord ++ tailWord_3519022) baseStart_3519022 baseEnd_3519022 := by
    simpa [prefixWord, tailWord_3519022, baseEnd_3519022] using wordTrace_append hprefix tailTrace_3519022
  have hstable : (prefixWord ++ tailWord_3519022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519022).length < 2 ^ (prefixWord ++ tailWord_3519022).sum := by decide
  have hdescent : baseEnd_3519022 < baseStart_3519022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519097 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 5]
def baseStart_3519097 : Nat := 118140960795 + 3519097 * 2 ^ 59
def prefixEnd_3519097 : Nat := 4983230072969 + 3 ^ 40 * 3519097 * 2
def baseEnd_3519097 : Nat := 401552940176738500111883

theorem tailTrace_3519097 : CollatzResearch.WordTrace tailWord_3519097 prefixEnd_3519097 401552940176738500111883 := by
  unfold tailWord_3519097
  simp only [CollatzResearch.WordTrace]
  refine ⟨128352012131920057763547545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85568008087946705175698363 128352012131920057763547545)
  ·
    refine ⟨96264009098940043322660659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128352012131920057763547545 96264009098940043322660659)
    ·
      refine ⟨144396013648410064983990989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96264009098940043322660659 144396013648410064983990989)
      ·
        refine ⟨54148505118153774368996621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144396013648410064983990989 54148505118153774368996621)
        ·
          refine ⟨20305689419307665388373733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54148505118153774368996621 20305689419307665388373733)
          ·
            refine ⟨3807316766120187260320075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20305689419307665388373733 3807316766120187260320075)
            ·
              refine ⟨5710975149180280890480113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807316766120187260320075 5710975149180280890480113)
              ·
                refine ⟨4283231361885210667860085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5710975149180280890480113 4283231361885210667860085)
                ·
                  refine ⟨401552940176738500111883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283231361885210667860085 401552940176738500111883)
                  ·
                    rfl

theorem cell22_3519097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 5].length) (baseStart_3519097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519097 prefixEnd_3519097 := by exact prefixLift 3519097
  have htrace : WordTrace (prefixWord ++ tailWord_3519097) baseStart_3519097 baseEnd_3519097 := by
    simpa [prefixWord, tailWord_3519097, baseEnd_3519097] using wordTrace_append hprefix tailTrace_3519097
  have hstable : (prefixWord ++ tailWord_3519097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519097).length < 2 ^ (prefixWord ++ tailWord_3519097).sum := by decide
  have hdescent : baseEnd_3519097 < baseStart_3519097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519114 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_3519114 : Nat := 118140960795 + 3519114 * 2 ^ 59
def prefixEnd_3519114 : Nat := 4983230072969 + 3 ^ 40 * 3519114 * 2
def baseEnd_3519114 : Nat := 401554879992544374220199

theorem tailTrace_3519114 : CollatzResearch.WordTrace tailWord_3519114 prefixEnd_3519114 401554879992544374220199 := by
  unfold tailWord_3519114
  simp only [CollatzResearch.WordTrace]
  refine ⟨32088158043214617416729099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85568421448572313111277597 32088158043214617416729099)
  ·
    refine ⟨48132237064821926125093649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32088158043214617416729099 48132237064821926125093649)
    ·
      refine ⟨36099177798616444593820237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48132237064821926125093649 36099177798616444593820237)
      ·
        refine ⟨13537191674481166722682589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36099177798616444593820237 13537191674481166722682589)
        ·
          refine ⟨5076446877930437521005971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13537191674481166722682589 5076446877930437521005971)
          ·
            refine ⟨7614670316895656281508957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076446877930437521005971 7614670316895656281508957)
            ·
              refine ⟨2855501368835871105565859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7614670316895656281508957 2855501368835871105565859)
              ·
                refine ⟨4283252053253806658348789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855501368835871105565859 4283252053253806658348789)
                ·
                  refine ⟨401554879992544374220199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283252053253806658348789 401554879992544374220199)
                  ·
                    rfl

theorem cell22_3519114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_3519114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519114 prefixEnd_3519114 := by exact prefixLift 3519114
  have htrace : WordTrace (prefixWord ++ tailWord_3519114) baseStart_3519114 baseEnd_3519114 := by
    simpa [prefixWord, tailWord_3519114, baseEnd_3519114] using wordTrace_append hprefix tailTrace_3519114
  have hstable : (prefixWord ++ tailWord_3519114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519114).length < 2 ^ (prefixWord ++ tailWord_3519114).sum := by decide
  have hdescent : baseEnd_3519114 < baseStart_3519114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519127 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 1, 4]
def baseStart_3519127 : Nat := 118140960795 + 3519127 * 2 ^ 59
def prefixEnd_3519127 : Nat := 4983230072969 + 3 ^ 40 * 3519127 * 2
def baseEnd_3519127 : Nat := 1204669090143305422085557

theorem tailTrace_3519127 : CollatzResearch.WordTrace tailWord_3519127 prefixEnd_3519127 1204669090143305422085557 := by
  unfold tailWord_3519127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128353106321811372887139635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85568737547874248591426423 128353106321811372887139635)
  ·
    refine ⟨192529659482717059330709453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128353106321811372887139635 192529659482717059330709453)
    ·
      refine ⟨72198622306018897249016045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192529659482717059330709453 72198622306018897249016045)
      ·
        refine ⟨27074483364757086468381017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72198622306018897249016045 27074483364757086468381017)
        ·
          refine ⟨20305862523567814851285763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27074483364757086468381017 20305862523567814851285763)
          ·
            refine ⟨30458793785351722276928645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20305862523567814851285763 30458793785351722276928645)
            ·
              refine ⟨5711023834753447926924121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30458793785351722276928645 5711023834753447926924121)
              ·
                refine ⟨4283267876065085945193091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5711023834753447926924121 4283267876065085945193091)
                ·
                  refine ⟨6424901814097628917789637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283267876065085945193091 6424901814097628917789637)
                  ·
                    refine ⟨1204669090143305422085557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424901814097628917789637 1204669090143305422085557)
                    ·
                      rfl

theorem cell22_3519127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_3519127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519127 prefixEnd_3519127 := by exact prefixLift 3519127
  have htrace : WordTrace (prefixWord ++ tailWord_3519127) baseStart_3519127 baseEnd_3519127 := by
    simpa [prefixWord, tailWord_3519127, baseEnd_3519127] using wordTrace_append hprefix tailTrace_3519127
  have hstable : (prefixWord ++ tailWord_3519127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519127).length < 2 ^ (prefixWord ++ tailWord_3519127).sum := by decide
  have hdescent : baseEnd_3519127 < baseStart_3519127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519140 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3519140 : Nat := 118140960795 + 3519140 * 2 ^ 59
def prefixEnd_3519140 : Nat := 4983230072969 + 3 ^ 40 * 3519140 * 2
def baseEnd_3519140 : Nat := 1204673540308977721510517

theorem tailTrace_3519140 : CollatzResearch.WordTrace tailWord_3519140 prefixEnd_3519140 1204673540308977721510517 := by
  unfold tailWord_3519140
  simp only [CollatzResearch.WordTrace]
  refine ⟨64176790235382138053681437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85569053647176184071575249 64176790235382138053681437)
  ·
    refine ⟨24066296338268301770130539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64176790235382138053681437 24066296338268301770130539)
    ·
      refine ⟨36099444507402452655195809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24066296338268301770130539 36099444507402452655195809)
      ·
        refine ⟨27074583380551839491396857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36099444507402452655195809 27074583380551839491396857)
        ·
          refine ⟨20305937535413879618547643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27074583380551839491396857 20305937535413879618547643)
          ·
            refine ⟨30458906303120819427821465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20305937535413879618547643 30458906303120819427821465)
            ·
              refine ⟨22844179727340614570866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30458906303120819427821465 22844179727340614570866099)
              ·
                refine ⟨34266269591010921856299149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22844179727340614570866099 34266269591010921856299149)
                ·
                  refine ⟨12849851096629095696112181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34266269591010921856299149 12849851096629095696112181)
                  ·
                    refine ⟨1204673540308977721510517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12849851096629095696112181 1204673540308977721510517)
                    ·
                      rfl

theorem cell22_3519140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3519140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519140 prefixEnd_3519140 := by exact prefixLift 3519140
  have htrace : WordTrace (prefixWord ++ tailWord_3519140) baseStart_3519140 baseEnd_3519140 := by
    simpa [prefixWord, tailWord_3519140, baseEnd_3519140] using wordTrace_append hprefix tailTrace_3519140
  have hstable : (prefixWord ++ tailWord_3519140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519140).length < 2 ^ (prefixWord ++ tailWord_3519140).sum := by decide
  have hdescent : baseEnd_3519140 < baseStart_3519140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519155 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_3519155 : Nat := 118140960795 + 3519155 * 2 ^ 59
def prefixEnd_3519155 : Nat := 4983230072969 + 3 ^ 40 * 3519155 * 2
def baseEnd_3519155 : Nat := 1204678675115522682385471

theorem tailTrace_3519155 : CollatzResearch.WordTrace tailWord_3519155 prefixEnd_3519155 1204678675115522682385471 := by
  unfold tailWord_3519155
  simp only [CollatzResearch.WordTrace]
  refine ⟨128354127565709933669158919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85569418377139955779439279 128354127565709933669158919)
  ·
    refine ⟨192531191348564900503738379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128354127565709933669158919 192531191348564900503738379)
    ·
      refine ⟨288796787022847350755607569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192531191348564900503738379 288796787022847350755607569)
      ·
        refine ⟨216597590267135513066705677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288796787022847350755607569 216597590267135513066705677)
        ·
          refine ⟨81224096350175817400014629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216597590267135513066705677 81224096350175817400014629)
          ·
            refine ⟨15229518065657965762502743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81224096350175817400014629 15229518065657965762502743)
            ·
              refine ⟨22844277098486948643754115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15229518065657965762502743 22844277098486948643754115)
              ·
                refine ⟨34266415647730422965631173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22844277098486948643754115 34266415647730422965631173)
                ·
                  refine ⟨6424952933949454306055845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34266415647730422965631173 6424952933949454306055845)
                  ·
                    refine ⟨1204678675115522682385471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6424952933949454306055845 1204678675115522682385471)
                    ·
                      rfl

theorem cell22_3519155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_3519155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519155 prefixEnd_3519155 := by exact prefixLift 3519155
  have htrace : WordTrace (prefixWord ++ tailWord_3519155) baseStart_3519155 baseEnd_3519155 := by
    simpa [prefixWord, tailWord_3519155, baseEnd_3519155] using wordTrace_append hprefix tailTrace_3519155
  have hstable : (prefixWord ++ tailWord_3519155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519155).length < 2 ^ (prefixWord ++ tailWord_3519155).sum := by decide
  have hdescent : baseEnd_3519155 < baseStart_3519155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519159 : List Nat := [1, 1, 3, 1, 7, 1, 1, 1, 6]
def baseStart_3519159 : Nat := 118140960795 + 3519159 * 2 ^ 59
def prefixEnd_3519159 : Nat := 4983230072969 + 3 ^ 40 * 3519159 * 2
def baseEnd_3519159 : Nat := 401560014799089335095153

theorem tailTrace_3519159 : CollatzResearch.WordTrace tailWord_3519159 prefixEnd_3519159 401560014799089335095153 := by
  unfold tailWord_3519159
  simp only [CollatzResearch.WordTrace]
  refine ⟨128354273457695442352304531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85569515638463628234869687 128354273457695442352304531)
  ·
    refine ⟨192531410186543163528456797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128354273457695442352304531 192531410186543163528456797)
    ·
      refine ⟨72199278819953686323171299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192531410186543163528456797 72199278819953686323171299)
      ·
        refine ⟨108298918229930529484756949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72199278819953686323171299 108298918229930529484756949)
        ·
          refine ⟨2538255896013996784798991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 108298918229930529484756949 2538255896013996784798991)
          ·
            refine ⟨3807383844020995177198487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538255896013996784798991 3807383844020995177198487)
            ·
              refine ⟨5711075766031492765797731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807383844020995177198487 5711075766031492765797731)
              ·
                refine ⟨8566613649047239148696597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711075766031492765797731 8566613649047239148696597)
                ·
                  refine ⟨401560014799089335095153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8566613649047239148696597 401560014799089335095153)
                  ·
                    rfl

theorem cell22_3519159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 6].length) (baseStart_3519159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519159 prefixEnd_3519159 := by exact prefixLift 3519159
  have htrace : WordTrace (prefixWord ++ tailWord_3519159) baseStart_3519159 baseEnd_3519159 := by
    simpa [prefixWord, tailWord_3519159, baseEnd_3519159] using wordTrace_append hprefix tailTrace_3519159
  have hstable : (prefixWord ++ tailWord_3519159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519159).length < 2 ^ (prefixWord ++ tailWord_3519159).sum := by decide
  have hdescent : baseEnd_3519159 < baseStart_3519159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519275 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_3519275 : Nat := 118140960795 + 3519275 * 2 ^ 59
def prefixEnd_3519275 : Nat := 4983230072969 + 3 ^ 40 * 3519275 * 2
def baseEnd_3519275 : Nat := 1204719753567882369385103

theorem tailTrace_3519275 : CollatzResearch.WordTrace tailWord_3519275 prefixEnd_3519275 1204719753567882369385103 := by
  unfold tailWord_3519275
  simp only [CollatzResearch.WordTrace]
  refine ⟨128358504325275194163527279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85572336216850129442351519 128358504325275194163527279)
  ·
    refine ⟨192537756487912791245290919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128358504325275194163527279 192537756487912791245290919)
    ·
      refine ⟨288806634731869186867936379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192537756487912791245290919 288806634731869186867936379)
      ·
        refine ⟨433209952097803780301904569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288806634731869186867936379 433209952097803780301904569)
        ·
          refine ⟨324907464073352835226428427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433209952097803780301904569 324907464073352835226428427)
          ·
            refine ⟨487361196110029252839642641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324907464073352835226428427 487361196110029252839642641)
            ·
              refine ⟨365520897082521939629731981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487361196110029252839642641 365520897082521939629731981)
              ·
                refine ⟨137070336405945727361149493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365520897082521939629731981 137070336405945727361149493)
                ·
                  refine ⟨12850344038057411940107765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 137070336405945727361149493 12850344038057411940107765)
                  ·
                    refine ⟨1204719753567882369385103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12850344038057411940107765 1204719753567882369385103)
                    ·
                      rfl

theorem cell22_3519275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_3519275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519275 prefixEnd_3519275 := by exact prefixLift 3519275
  have htrace : WordTrace (prefixWord ++ tailWord_3519275) baseStart_3519275 baseEnd_3519275 := by
    simpa [prefixWord, tailWord_3519275, baseEnd_3519275] using wordTrace_append hprefix tailTrace_3519275
  have hstable : (prefixWord ++ tailWord_3519275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519275).length < 2 ^ (prefixWord ++ tailWord_3519275).sum := by decide
  have hdescent : baseEnd_3519275 < baseStart_3519275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519322 : List Nat := [3, 1, 1, 2, 1, 6, 8]
def baseStart_3519322 : Nat := 118140960795 + 3519322 * 2 ^ 59
def prefixEnd_3519322 : Nat := 4983230072969 + 3 ^ 40 * 3519322 * 2
def baseEnd_3519322 : Nat := 44619846023273700498517

theorem tailTrace_3519322 : CollatzResearch.WordTrace tailWord_3519322 prefixEnd_3519322 44619846023273700498517 := by
  unfold tailWord_3519322
  simp only [CollatzResearch.WordTrace]
  refine ⟨32090054639026230297622055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85573479037403280793658813 32090054639026230297622055)
  ·
    refine ⟨48135081958539345446433083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32090054639026230297622055 48135081958539345446433083)
    ·
      refine ⟨72202622937809018169649625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48135081958539345446433083 72202622937809018169649625)
      ·
        refine ⟨54151967203356763627237219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72202622937809018169649625 54151967203356763627237219)
        ·
          refine ⟨81227950805035145440855829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54151967203356763627237219 81227950805035145440855829)
          ·
            refine ⟨3807560193986022442540117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81227950805035145440855829 3807560193986022442540117)
            ·
              refine ⟨44619846023273700498517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3807560193986022442540117 44619846023273700498517)
              ·
                rfl

theorem cell22_3519322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 8].length) (baseStart_3519322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519322 prefixEnd_3519322 := by exact prefixLift 3519322
  have htrace : WordTrace (prefixWord ++ tailWord_3519322) baseStart_3519322 baseEnd_3519322 := by
    simpa [prefixWord, tailWord_3519322, baseEnd_3519322] using wordTrace_append hprefix tailTrace_3519322
  have hstable : (prefixWord ++ tailWord_3519322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519322).length < 2 ^ (prefixWord ++ tailWord_3519322).sum := by decide
  have hdescent : baseEnd_3519322 < baseStart_3519322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519324 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_3519324 : Nat := 118140960795 + 3519324 * 2 ^ 59
def prefixEnd_3519324 : Nat := 4983230072969 + 3 ^ 40 * 3519324 * 2
def baseEnd_3519324 : Nat := 1204736527269262574909953

theorem tailTrace_3519324 : CollatzResearch.WordTrace tailWord_3519324 prefixEnd_3519324 1204736527269262574909953 := by
  unfold tailWord_3519324
  simp only [CollatzResearch.WordTrace]
  refine ⟨64180145751048837766030513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85573527668065117021374017 64180145751048837766030513)
  ·
    refine ⟨48135109313286628324522885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64180145751048837766030513 48135109313286628324522885)
    ·
      refine ⟨9025332996241242810848041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48135109313286628324522885 9025332996241242810848041)
      ·
        refine ⟨6768999747180932108136031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9025332996241242810848041 6768999747180932108136031)
        ·
          refine ⟨10153499620771398162204047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768999747180932108136031 10153499620771398162204047)
          ·
            refine ⟨15230249431157097243306071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153499620771398162204047 15230249431157097243306071)
            ·
              refine ⟨22845374146735645864959107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230249431157097243306071 22845374146735645864959107)
              ·
                refine ⟨34268061220103468797438661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22845374146735645864959107 34268061220103468797438661)
                ·
                  refine ⟨6425261478769400399519749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34268061220103468797438661 6425261478769400399519749)
                  ·
                    refine ⟨1204736527269262574909953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425261478769400399519749 1204736527269262574909953)
                    ·
                      rfl

theorem cell22_3519324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_3519324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519324 prefixEnd_3519324 := by exact prefixLift 3519324
  have htrace : WordTrace (prefixWord ++ tailWord_3519324) baseStart_3519324 baseEnd_3519324 := by
    simpa [prefixWord, tailWord_3519324, baseEnd_3519324] using wordTrace_append hprefix tailTrace_3519324
  have hstable : (prefixWord ++ tailWord_3519324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519324).length < 2 ^ (prefixWord ++ tailWord_3519324).sum := by decide
  have hdescent : baseEnd_3519324 < baseStart_3519324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519358 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3519358 : Nat := 118140960795 + 3519358 * 2 ^ 59
def prefixEnd_3519358 : Nat := 4983230072969 + 3 ^ 40 * 3519358 * 2
def baseEnd_3519358 : Nat := 1204748166164097819559849

theorem tailTrace_3519358 : CollatzResearch.WordTrace tailWord_3519358 prefixEnd_3519358 1204748166164097819559849 := by
  unfold tailWord_3519358
  simp only [CollatzResearch.WordTrace]
  refine ⟨16045191447996812417349841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85574354389316332892532485 16045191447996812417349841)
  ·
    refine ⟨12033893585997609313012381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16045191447996812417349841 12033893585997609313012381)
    ·
      refine ⟨4512710094749103492379643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12033893585997609313012381 4512710094749103492379643)
      ·
        refine ⟨6769065142123655238569465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4512710094749103492379643 6769065142123655238569465)
        ·
          refine ⟨5076798856592741428927099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6769065142123655238569465 5076798856592741428927099)
          ·
            refine ⟨7615198284889112143390649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076798856592741428927099 7615198284889112143390649)
            ·
              refine ⟨5711398713666834107542987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7615198284889112143390649 5711398713666834107542987)
              ·
                refine ⟨8567098070500251161314481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5711398713666834107542987 8567098070500251161314481)
                ·
                  refine ⟨6425323552875188370985861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8567098070500251161314481 6425323552875188370985861)
                  ·
                    refine ⟨1204748166164097819559849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425323552875188370985861 1204748166164097819559849)
                    ·
                      rfl

theorem cell22_3519358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3519358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519358 prefixEnd_3519358 := by exact prefixLift 3519358
  have htrace : WordTrace (prefixWord ++ tailWord_3519358) baseStart_3519358 baseEnd_3519358 := by
    simpa [prefixWord, tailWord_3519358, baseEnd_3519358] using wordTrace_append hprefix tailTrace_3519358
  have hstable : (prefixWord ++ tailWord_3519358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519358).length < 2 ^ (prefixWord ++ tailWord_3519358).sum := by decide
  have hdescent : baseEnd_3519358 < baseStart_3519358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519431 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 1, 4]
def baseStart_3519431 : Nat := 118140960795 + 3519431 * 2 ^ 59
def prefixEnd_3519431 : Nat := 4983230072969 + 3 ^ 40 * 3519431 * 2
def baseEnd_3519431 : Nat := 1204773155555949962484625

theorem tailTrace_3519431 : CollatzResearch.WordTrace tailWord_3519431 prefixEnd_3519431 1204773155555949962484625 := by
  unfold tailWord_3519431
  simp only [CollatzResearch.WordTrace]
  refine ⟨128364194112710032806206147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85576129408473355204137431 128364194112710032806206147)
  ·
    refine ⟨192546291169065049209309221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128364194112710032806206147 192546291169065049209309221)
    ·
      refine ⟨36102429594199696726745479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192546291169065049209309221 36102429594199696726745479)
      ·
        refine ⟨54153644391299545090118219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36102429594199696726745479 54153644391299545090118219)
        ·
          refine ⟨81230466586949317635177329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54153644391299545090118219 81230466586949317635177329)
          ·
            refine ⟨60922849940211988226382997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81230466586949317635177329 60922849940211988226382997)
            ·
              refine ⟨2855758590947436948111703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60922849940211988226382997 2855758590947436948111703)
              ·
                refine ⟨4283637886421155422167555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855758590947436948111703 4283637886421155422167555)
                ·
                  refine ⟨6425456829631733133251333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4283637886421155422167555 6425456829631733133251333)
                  ·
                    refine ⟨1204773155555949962484625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6425456829631733133251333 1204773155555949962484625)
                    ·
                      rfl

theorem cell22_3519431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_3519431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519431 prefixEnd_3519431 := by exact prefixLift 3519431
  have htrace : WordTrace (prefixWord ++ tailWord_3519431) baseStart_3519431 baseEnd_3519431 := by
    simpa [prefixWord, tailWord_3519431, baseEnd_3519431] using wordTrace_append hprefix tailTrace_3519431
  have hstable : (prefixWord ++ tailWord_3519431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519431).length < 2 ^ (prefixWord ++ tailWord_3519431).sum := by decide
  have hdescent : baseEnd_3519431 < baseStart_3519431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519446 : List Nat := [5, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_3519446 : Nat := 118140960795 + 3519446 * 2 ^ 59
def prefixEnd_3519446 : Nat := 4983230072969 + 3 ^ 40 * 3519446 * 2
def baseEnd_3519446 : Nat := 401592763454164974453193

theorem tailTrace_3519446 : CollatzResearch.WordTrace tailWord_3519446 prefixEnd_3519446 401592763454164974453193 := by
  unfold tailWord_3519446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022796325478480648000137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85576494138437126912001461 8022796325478480648000137)
  ·
    refine ⟨6017097244108860486000103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8022796325478480648000137 6017097244108860486000103)
    ·
      refine ⟨9025645866163290729000155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6017097244108860486000103 9025645866163290729000155)
      ·
        refine ⟨13538468799244936093500233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025645866163290729000155 13538468799244936093500233)
        ·
          refine ⟨10153851599433702070125175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13538468799244936093500233 10153851599433702070125175)
          ·
            refine ⟨15230777399150553105187763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153851599433702070125175 15230777399150553105187763)
            ·
              refine ⟨22846166098725829657781645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15230777399150553105187763 22846166098725829657781645)
              ·
                refine ⟨8567312287022186121668117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22846166098725829657781645 8567312287022186121668117)
                ·
                  refine ⟨401592763454164974453193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8567312287022186121668117 401592763454164974453193)
                  ·
                    rfl

theorem cell22_3519446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_3519446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519446 prefixEnd_3519446 := by exact prefixLift 3519446
  have htrace : WordTrace (prefixWord ++ tailWord_3519446) baseStart_3519446 baseEnd_3519446 := by
    simpa [prefixWord, tailWord_3519446, baseEnd_3519446] using wordTrace_append hprefix tailTrace_3519446
  have hstable : (prefixWord ++ tailWord_3519446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519446).length < 2 ^ (prefixWord ++ tailWord_3519446).sum := by decide
  have hdescent : baseEnd_3519446 < baseStart_3519446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519457 : List Nat := [1, 2, 3, 1, 2, 1, 1, 11]
def baseStart_3519457 : Nat := 118140960795 + 3519457 * 2 ^ 59
def prefixEnd_3519457 : Nat := 4983230072969 + 3 ^ 40 * 3519457 * 2
def baseEnd_3519457 : Nat := 133864672876366062370505

theorem tailTrace_3519457 : CollatzResearch.WordTrace tailWord_3519457 prefixEnd_3519457 133864672876366062370505 := by
  unfold tailWord_3519457
  simp only [CollatzResearch.WordTrace]
  refine ⟨128365142410615839246652625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85576761607077226164435083 128365142410615839246652625)
  ·
    refine ⟨96273856807961879434989469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128365142410615839246652625 96273856807961879434989469)
    ·
      refine ⟨36102696302985704788121051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96273856807961879434989469 36102696302985704788121051)
      ·
        refine ⟨54154044454478557182181577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36102696302985704788121051 54154044454478557182181577)
        ·
          refine ⟨40615533340858917886636183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54154044454478557182181577 40615533340858917886636183)
          ·
            refine ⟨60923300011288376829954275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40615533340858917886636183 60923300011288376829954275)
            ·
              refine ⟨91384950016932565244931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60923300011288376829954275 91384950016932565244931413)
              ·
                refine ⟨133864672876366062370505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 91384950016932565244931413 133864672876366062370505)
                ·
                  rfl

theorem cell22_3519457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 11].length) (baseStart_3519457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519457 prefixEnd_3519457 := by exact prefixLift 3519457
  have htrace : WordTrace (prefixWord ++ tailWord_3519457) baseStart_3519457 baseEnd_3519457 := by
    simpa [prefixWord, tailWord_3519457, baseEnd_3519457] using wordTrace_append hprefix tailTrace_3519457
  have hstable : (prefixWord ++ tailWord_3519457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519457).length < 2 ^ (prefixWord ++ tailWord_3519457).sum := by decide
  have hdescent : baseEnd_3519457 < baseStart_3519457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519472 : List Nat := [2, 1, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_3519472 : Nat := 118140960795 + 3519472 * 2 ^ 59
def prefixEnd_3519472 : Nat := 4983230072969 + 3 ^ 40 * 3519472 * 2
def baseEnd_3519472 : Nat := 1204787190693839522209499

theorem tailTrace_3519472 : CollatzResearch.WordTrace tailWord_3519472 prefixEnd_3519472 1204787190693839522209499 := by
  unfold tailWord_3519472
  simp only [CollatzResearch.WordTrace]
  refine ⟨64182844752780748404224335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85577126337040997872299113 64182844752780748404224335)
  ·
    refine ⟨96274267129171122606336503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64182844752780748404224335 96274267129171122606336503)
    ·
      refine ⟨144411400693756683909504755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96274267129171122606336503 144411400693756683909504755)
      ·
        refine ⟨216617101040635025864257133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144411400693756683909504755 216617101040635025864257133)
        ·
          refine ⟨81231412890238134699096425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216617101040635025864257133 81231412890238134699096425)
          ·
            refine ⟨60923559667678601024322319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81231412890238134699096425 60923559667678601024322319)
            ·
              refine ⟨91385339501517901536483479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60923559667678601024322319 91385339501517901536483479)
              ·
                refine ⟨137078009252276852304725219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91385339501517901536483479 137078009252276852304725219)
                ·
                  refine ⟨205617013878415278457087829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137078009252276852304725219 205617013878415278457087829)
                  ·
                    refine ⟨1204787190693839522209499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205617013878415278457087829 1204787190693839522209499)
                    ·
                      rfl

theorem cell22_3519472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_3519472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519472 prefixEnd_3519472 := by exact prefixLift 3519472
  have htrace : WordTrace (prefixWord ++ tailWord_3519472) baseStart_3519472 baseEnd_3519472 := by
    simpa [prefixWord, tailWord_3519472, baseEnd_3519472] using wordTrace_append hprefix tailTrace_3519472
  have hstable : (prefixWord ++ tailWord_3519472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519472).length < 2 ^ (prefixWord ++ tailWord_3519472).sum := by decide
  have hdescent : baseEnd_3519472 < baseStart_3519472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519487 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_3519487 : Nat := 118140960795 + 3519487 * 2 ^ 59
def prefixEnd_3519487 : Nat := 4983230072969 + 3 ^ 40 * 3519487 * 2
def baseEnd_3519487 : Nat := 1204792325500384483084453

theorem tailTrace_3519487 : CollatzResearch.WordTrace tailWord_3519487 prefixEnd_3519487 1204792325500384483084453 := by
  unfold tailWord_3519487
  simp only [CollatzResearch.WordTrace]
  refine ⟨128366236600507154370244715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85577491067004769580163143 128366236600507154370244715)
  ·
    refine ⟨192549354900760731555367073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128366236600507154370244715 192549354900760731555367073)
    ·
      refine ⟨144412016175570548666525305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192549354900760731555367073 144412016175570548666525305)
      ·
        refine ⟨108309012131677911499893979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144412016175570548666525305 108309012131677911499893979)
        ·
          refine ⟨162463518197516867249840969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108309012131677911499893979 162463518197516867249840969)
          ·
            refine ⟨121847638648137650437380727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162463518197516867249840969 121847638648137650437380727)
            ·
              refine ⟨182771457972206475656071091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121847638648137650437380727 182771457972206475656071091)
              ·
                refine ⟨274157186958309713484106637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182771457972206475656071091 274157186958309713484106637)
                ·
                  refine ⟨102808945109366142556539989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274157186958309713484106637 102808945109366142556539989)
                  ·
                    refine ⟨1204792325500384483084453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102808945109366142556539989 1204792325500384483084453)
                    ·
                      rfl

theorem cell22_3519487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_3519487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519487 prefixEnd_3519487 := by exact prefixLift 3519487
  have htrace : WordTrace (prefixWord ++ tailWord_3519487) baseStart_3519487 baseEnd_3519487 := by
    simpa [prefixWord, tailWord_3519487, baseEnd_3519487] using wordTrace_append hprefix tailTrace_3519487
  have hstable : (prefixWord ++ tailWord_3519487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519487).length < 2 ^ (prefixWord ++ tailWord_3519487).sum := by decide
  have hdescent : baseEnd_3519487 < baseStart_3519487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519553 : List Nat := [1, 2, 5, 1, 3, 1, 2, 2, 5]
def baseStart_3519553 : Nat := 118140960795 + 3519553 * 2 ^ 59
def prefixEnd_3519553 : Nat := 4983230072969 + 3 ^ 40 * 3519553 * 2
def baseEnd_3519553 : Nat := 401604972883060770311417

theorem tailTrace_3519553 : CollatzResearch.WordTrace tailWord_3519553 prefixEnd_3519553 401604972883060770311417 := by
  unfold tailWord_3519553
  simp only [CollatzResearch.WordTrace]
  refine ⟨128368643818268047642147313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85579095878845365094764875 128368643818268047642147313)
  ·
    refine ⟨96276482863701035731610485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128368643818268047642147313 96276482863701035731610485)
    ·
      refine ⟨9025920268471972099838483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96276482863701035731610485 9025920268471972099838483)
      ·
        refine ⟨13538880402707958149757725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025920268471972099838483 13538880402707958149757725)
        ·
          refine ⟨5077080151015484306159147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13538880402707958149757725 5077080151015484306159147)
          ·
            refine ⟨7615620226523226459238721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077080151015484306159147 7615620226523226459238721)
            ·
              refine ⟨5711715169892419844429041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7615620226523226459238721 5711715169892419844429041)
              ·
                refine ⟨4283786377419314883321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5711715169892419844429041 4283786377419314883321781)
                ·
                  refine ⟨401604972883060770311417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283786377419314883321781 401604972883060770311417)
                  ·
                    rfl

theorem cell22_3519553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_3519553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519553 prefixEnd_3519553 := by exact prefixLift 3519553
  have htrace : WordTrace (prefixWord ++ tailWord_3519553) baseStart_3519553 baseEnd_3519553 := by
    simpa [prefixWord, tailWord_3519553, baseEnd_3519553] using wordTrace_append hprefix tailTrace_3519553
  have hstable : (prefixWord ++ tailWord_3519553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519553).length < 2 ^ (prefixWord ++ tailWord_3519553).sum := by decide
  have hdescent : baseEnd_3519553 < baseStart_3519553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519564 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_3519564 : Nat := 118140960795 + 3519564 * 2 ^ 59
def prefixEnd_3519564 : Nat := 4983230072969 + 3 ^ 40 * 3519564 * 2
def baseEnd_3519564 : Nat := 401606228057993982969739

theorem tailTrace_3519564 : CollatzResearch.WordTrace tailWord_3519564 prefixEnd_3519564 401606228057993982969739 := by
  unfold tailWord_3519564
  simp only [CollatzResearch.WordTrace]
  refine ⟨64184522510614098260398873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85579363347485464347198497 64184522510614098260398873)
  ·
    refine ⟨48138391882960573695299155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64184522510614098260398873 48138391882960573695299155)
    ·
      refine ⟨72207587824440860542948733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48138391882960573695299155 72207587824440860542948733)
      ·
        refine ⟨27077845434165322703605775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72207587824440860542948733 27077845434165322703605775)
        ·
          refine ⟨40616768151247984055408663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27077845434165322703605775 40616768151247984055408663)
          ·
            refine ⟨60925152226871976083112995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40616768151247984055408663 60925152226871976083112995)
            ·
              refine ⟨91387728340307964124669493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60925152226871976083112995 91387728340307964124669493)
              ·
                refine ⟨8567599531903871636687765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91387728340307964124669493 8567599531903871636687765)
                ·
                  refine ⟨401606228057993982969739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8567599531903871636687765 401606228057993982969739)
                  ·
                    rfl

theorem cell22_3519564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_3519564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519564 prefixEnd_3519564 := by exact prefixLift 3519564
  have htrace : WordTrace (prefixWord ++ tailWord_3519564) baseStart_3519564 baseEnd_3519564 := by
    simpa [prefixWord, tailWord_3519564, baseEnd_3519564] using wordTrace_append hprefix tailTrace_3519564
  have hstable : (prefixWord ++ tailWord_3519564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519564).length < 2 ^ (prefixWord ++ tailWord_3519564).sum := by decide
  have hdescent : baseEnd_3519564 < baseStart_3519564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519596 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_3519596 : Nat := 118140960795 + 3519596 * 2 ^ 59
def prefixEnd_3519596 : Nat := 4983230072969 + 3 ^ 40 * 3519596 * 2
def baseEnd_3519596 : Nat := 1204829638427944532109119

theorem tailTrace_3519596 : CollatzResearch.WordTrace tailWord_3519596 prefixEnd_3519596 1204829638427944532109119 := by
  unfold tailWord_3519596
  simp only [CollatzResearch.WordTrace]
  refine ⟨64185106078556132992981321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85580141438074843990641761 64185106078556132992981321)
  ·
    refine ⟨48138829558917099744735991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64185106078556132992981321 48138829558917099744735991)
    ·
      refine ⟨72208244338375649617103987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48138829558917099744735991 72208244338375649617103987)
      ·
        refine ⟨108312366507563474425655981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72208244338375649617103987 108312366507563474425655981)
        ·
          refine ⟨40617137440336302909620993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108312366507563474425655981 40617137440336302909620993)
          ·
            refine ⟨30462853080252227182215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40617137440336302909620993 30462853080252227182215745)
            ·
              refine ⟨22847139810189170386661809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30462853080252227182215745 22847139810189170386661809)
              ·
                refine ⟨17135354857641877789996357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22847139810189170386661809 17135354857641877789996357)
                ·
                  refine ⟨3212879035807852085624317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17135354857641877789996357 3212879035807852085624317)
                  ·
                    refine ⟨1204829638427944532109119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3212879035807852085624317 1204829638427944532109119)
                    ·
                      rfl

theorem cell22_3519596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_3519596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519596 prefixEnd_3519596 := by exact prefixLift 3519596
  have htrace : WordTrace (prefixWord ++ tailWord_3519596) baseStart_3519596 baseEnd_3519596 := by
    simpa [prefixWord, tailWord_3519596, baseEnd_3519596] using wordTrace_append hprefix tailTrace_3519596
  have hstable : (prefixWord ++ tailWord_3519596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519596).length < 2 ^ (prefixWord ++ tailWord_3519596).sum := by decide
  have hdescent : baseEnd_3519596 < baseStart_3519596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519598 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3519598 : Nat := 118140960795 + 3519598 * 2 ^ 59
def prefixEnd_3519598 : Nat := 4983230072969 + 3 ^ 40 * 3519598 * 2
def baseEnd_3519598 : Nat := 401610107689605731186371

theorem tailTrace_3519598 : CollatzResearch.WordTrace tailWord_3519598 prefixEnd_3519598 401610107689605731186371 := by
  unfold tailWord_3519598
  simp only [CollatzResearch.WordTrace]
  refine ⟨16046285637888127540941931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85580190068736680218356965 16046285637888127540941931)
  ·
    refine ⟨24069428456832191311412897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16046285637888127540941931 24069428456832191311412897)
    ·
      refine ⟨18052071342624143483559673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24069428456832191311412897 18052071342624143483559673)
      ·
        refine ⟨13539053506968107612669755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18052071342624143483559673 13539053506968107612669755)
        ·
          refine ⟨20308580260452161419004633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13539053506968107612669755 20308580260452161419004633)
          ·
            refine ⟨15231435195339121064253475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20308580260452161419004633 15231435195339121064253475)
            ·
              refine ⟨22847152793008681596380213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15231435195339121064253475 22847152793008681596380213)
              ·
                refine ⟨2141920574344563899660645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22847152793008681596380213 2141920574344563899660645)
                ·
                  refine ⟨401610107689605731186371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141920574344563899660645 401610107689605731186371)
                  ·
                    rfl

theorem cell22_3519598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3519598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519598 prefixEnd_3519598 := by exact prefixLift 3519598
  have htrace : WordTrace (prefixWord ++ tailWord_3519598) baseStart_3519598 baseEnd_3519598 := by
    simpa [prefixWord, tailWord_3519598, baseEnd_3519598] using wordTrace_append hprefix tailTrace_3519598
  have hstable : (prefixWord ++ tailWord_3519598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519598).length < 2 ^ (prefixWord ++ tailWord_3519598).sum := by decide
  have hdescent : baseEnd_3519598 < baseStart_3519598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519671 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 5]
def baseStart_3519671 : Nat := 118140960795 + 3519671 * 2 ^ 59
def prefixEnd_3519671 : Nat := 4983230072969 + 3 ^ 40 * 3519671 * 2
def baseEnd_3519671 : Nat := 401618437486889778827963

theorem tailTrace_3519671 : CollatzResearch.WordTrace tailWord_3519671 prefixEnd_3519671 401618437486889778827963 := by
  unfold tailWord_3519671
  simp only [CollatzResearch.WordTrace]
  refine ⟨128372947631840553794942867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85581965087893702529961911 128372947631840553794942867)
  ·
    refine ⟨192559421447760830692414301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128372947631840553794942867 192559421447760830692414301)
    ·
      refine ⟨72209783042910311509655363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192559421447760830692414301 72209783042910311509655363)
      ·
        refine ⟨108314674564365467264483045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72209783042910311509655363 108314674564365467264483045)
        ·
          refine ⟨20309001480818525112090571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108314674564365467264483045 20309001480818525112090571)
          ·
            refine ⟨30463502221227787668135857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20309001480818525112090571 30463502221227787668135857)
            ·
              refine ⟨22847626665920840751101893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30463502221227787668135857 22847626665920840751101893)
              ·
                refine ⟨4283929999860157640831605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22847626665920840751101893 4283929999860157640831605)
                ·
                  refine ⟨401618437486889778827963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283929999860157640831605 401618437486889778827963)
                  ·
                    rfl

theorem cell22_3519671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 5].length) (baseStart_3519671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519671 prefixEnd_3519671 := by exact prefixLift 3519671
  have htrace : WordTrace (prefixWord ++ tailWord_3519671) baseStart_3519671 baseEnd_3519671 := by
    simpa [prefixWord, tailWord_3519671, baseEnd_3519671] using wordTrace_append hprefix tailTrace_3519671
  have hstable : (prefixWord ++ tailWord_3519671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519671).length < 2 ^ (prefixWord ++ tailWord_3519671).sum := by decide
  have hdescent : baseEnd_3519671 < baseStart_3519671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519688 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_3519688 : Nat := 118140960795 + 3519688 * 2 ^ 59
def prefixEnd_3519688 : Nat := 4983230072969 + 3 ^ 40 * 3519688 * 2
def baseEnd_3519688 : Nat := 401620377302695652936279

theorem tailTrace_3519688 : CollatzResearch.WordTrace tailWord_3519688 prefixEnd_3519688 401620377302695652936279 := by
  unfold tailWord_3519688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64186783836389482849155859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85582378448519310465541145 64186783836389482849155859)
  ·
    refine ⟨96280175754584224273733789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64186783836389482849155859 96280175754584224273733789)
    ·
      refine ⟨36105065907969084102650171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96280175754584224273733789 36105065907969084102650171)
      ·
        refine ⟨54157598861953626153975257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36105065907969084102650171 54157598861953626153975257)
        ·
          refine ⟨40618199146465219615481443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54157598861953626153975257 40618199146465219615481443)
          ·
            refine ⟨60927298719697829423222165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40618199146465219615481443 60927298719697829423222165)
            ·
              refine ⟨2855967127485835754213539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60927298719697829423222165 2855967127485835754213539)
              ·
                refine ⟨4283950691228753631320309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2855967127485835754213539 4283950691228753631320309)
                ·
                  refine ⟨401620377302695652936279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4283950691228753631320309 401620377302695652936279)
                  ·
                    rfl

theorem cell22_3519688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_3519688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519688 prefixEnd_3519688 := by exact prefixLift 3519688
  have htrace : WordTrace (prefixWord ++ tailWord_3519688) baseStart_3519688 baseEnd_3519688 := by
    simpa [prefixWord, tailWord_3519688, baseEnd_3519688] using wordTrace_append hprefix tailTrace_3519688
  have hstable : (prefixWord ++ tailWord_3519688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519688).length < 2 ^ (prefixWord ++ tailWord_3519688).sum := by decide
  have hdescent : baseEnd_3519688 < baseStart_3519688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519748 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3519748 : Nat := 118140960795 + 3519748 * 2 ^ 59
def prefixEnd_3519748 : Nat := 4983230072969 + 3 ^ 40 * 3519748 * 2
def baseEnd_3519748 : Nat := 1204881671134266802308653

theorem tailTrace_3519748 : CollatzResearch.WordTrace tailWord_3519748 prefixEnd_3519748 1204881671134266802308653 := by
  unfold tailWord_3519748
  simp only [CollatzResearch.WordTrace]
  refine ⟨64187878026280797972747949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85583837368374397296997265 64187878026280797972747949)
  ·
    refine ⟨24070454259855299239780481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64187878026280797972747949 24070454259855299239780481)
    ·
      refine ⟨18052840694891474429835361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24070454259855299239780481 18052840694891474429835361)
      ·
        refine ⟨13539630521168605822376521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18052840694891474429835361 13539630521168605822376521)
        ·
          refine ⟨10154722890876454366782391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13539630521168605822376521 10154722890876454366782391)
          ·
            refine ⟨15232084336314681550173587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10154722890876454366782391 15232084336314681550173587)
            ·
              refine ⟨22848126504472022325260381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15232084336314681550173587 22848126504472022325260381)
              ·
                refine ⟨8568047439177008371972643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22848126504472022325260381 8568047439177008371972643)
                ·
                  refine ⟨12852071158765512557958965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568047439177008371972643 12852071158765512557958965)
                  ·
                    refine ⟨1204881671134266802308653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12852071158765512557958965 1204881671134266802308653)
                    ·
                      rfl

theorem cell22_3519748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3519748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519748 prefixEnd_3519748 := by exact prefixLift 3519748
  have htrace : WordTrace (prefixWord ++ tailWord_3519748) baseStart_3519748 baseEnd_3519748 := by
    simpa [prefixWord, tailWord_3519748, baseEnd_3519748] using wordTrace_append hprefix tailTrace_3519748
  have hstable : (prefixWord ++ tailWord_3519748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519748).length < 2 ^ (prefixWord ++ tailWord_3519748).sum := by decide
  have hdescent : baseEnd_3519748 < baseStart_3519748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519778 : List Nat := [3, 3, 1, 1, 4, 1, 9]
def baseStart_3519778 : Nat := 118140960795 + 3519778 * 2 ^ 59
def prefixEnd_3519778 : Nat := 4983230072969 + 3 ^ 40 * 3519778 * 2
def baseEnd_3519778 : Nat := 44625627435087286076243

theorem tailTrace_3519778 : CollatzResearch.WordTrace tailWord_3519778 prefixEnd_3519778 44625627435087286076243 := by
  unfold tailWord_3519778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32094212560613227767271997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85584566828301940712725325 32094212560613227767271997)
  ·
    refine ⟨12035329710229960412726999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32094212560613227767271997 12035329710229960412726999)
    ·
      refine ⟨18052994565344940619090499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12035329710229960412726999 18052994565344940619090499)
      ·
        refine ⟨27079491848017410928635749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18052994565344940619090499 27079491848017410928635749)
        ·
          refine ⟨5077404721503264549119203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27079491848017410928635749 5077404721503264549119203)
          ·
            refine ⟨7616107082254896823678805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077404721503264549119203 7616107082254896823678805)
            ·
              refine ⟨44625627435087286076243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7616107082254896823678805 44625627435087286076243)
              ·
                rfl

theorem cell22_3519778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 9].length) (baseStart_3519778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519778 prefixEnd_3519778 := by exact prefixLift 3519778
  have htrace : WordTrace (prefixWord ++ tailWord_3519778) baseStart_3519778 baseEnd_3519778 := by
    simpa [prefixWord, tailWord_3519778, baseEnd_3519778] using wordTrace_append hprefix tailTrace_3519778
  have hstable : (prefixWord ++ tailWord_3519778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519778).length < 2 ^ (prefixWord ++ tailWord_3519778).sum := by decide
  have hdescent : baseEnd_3519778 < baseStart_3519778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519812 : List Nat := [2, 3, 4, 1, 1, 3, 2, 6]
def baseStart_3519812 : Nat := 118140960795 + 3519812 * 2 ^ 59
def prefixEnd_3519812 : Nat := 4983230072969 + 3 ^ 40 * 3519812 * 2
def baseEnd_3519812 : Nat := 133878175515799107634273

theorem tailTrace_3519812 : CollatzResearch.WordTrace tailWord_3519812 prefixEnd_3519812 133878175515799107634273 := by
  unfold tailWord_3519812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64189045162164867437912845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85585393549553156583883793 64189045162164867437912845)
  ·
    refine ⟨24070891935811825289217317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64189045162164867437912845 24070891935811825289217317)
    ·
      refine ⟨4513292237964717241728247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24070891935811825289217317 4513292237964717241728247)
      ·
        refine ⟨6769938356947075862592371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513292237964717241728247 6769938356947075862592371)
        ·
          refine ⟨10154907535420613793888557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6769938356947075862592371 10154907535420613793888557)
          ·
            refine ⟨3808090325782730172708209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10154907535420613793888557 3808090325782730172708209)
            ·
              refine ⟨2856067744337047629531157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808090325782730172708209 2856067744337047629531157)
              ·
                refine ⟨133878175515799107634273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2856067744337047629531157 133878175515799107634273)
                ·
                  rfl

theorem cell22_3519812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_3519812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519812 prefixEnd_3519812 := by exact prefixLift 3519812
  have htrace : WordTrace (prefixWord ++ tailWord_3519812) baseStart_3519812 baseEnd_3519812 := by
    simpa [prefixWord, tailWord_3519812, baseEnd_3519812] using wordTrace_append hprefix tailTrace_3519812
  have hstable : (prefixWord ++ tailWord_3519812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519812).length < 2 ^ (prefixWord ++ tailWord_3519812).sum := by decide
  have hdescent : baseEnd_3519812 < baseStart_3519812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519844 : List Nat := [2, 3, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3519844 : Nat := 118140960795 + 3519844 * 2 ^ 59
def prefixEnd_3519844 : Nat := 4983230072969 + 3 ^ 40 * 3519844 * 2
def baseEnd_3519844 : Nat := 1204914533896154551908359

theorem tailTrace_3519844 : CollatzResearch.WordTrace tailWord_3519844 prefixEnd_3519844 1204914533896154551908359 := by
  unfold tailWord_3519844
  simp only [CollatzResearch.WordTrace]
  refine ⟨64189628730106902170495293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85586171640142536227327057 64189628730106902170495293)
  ·
    refine ⟨24071110773790088313935735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64189628730106902170495293 24071110773790088313935735)
    ·
      refine ⟨36106666160685132470903603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24071110773790088313935735 36106666160685132470903603)
      ·
        refine ⟨54159999241027698706355405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36106666160685132470903603 54159999241027698706355405)
        ·
          refine ⟨20309999715385387014883277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54159999241027698706355405 20309999715385387014883277)
          ·
            refine ⟨7616249893269520130581229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20309999715385387014883277 7616249893269520130581229)
            ·
              refine ⟨2856093709976070048967961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7616249893269520130581229 2856093709976070048967961)
              ·
                refine ⟨2142070282482052536725971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856093709976070048967961 2142070282482052536725971)
                ·
                  refine ⟨3213105423723078805088957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142070282482052536725971 3213105423723078805088957)
                  ·
                    refine ⟨1204914533896154551908359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213105423723078805088957 1204914533896154551908359)
                    ·
                      rfl

theorem cell22_3519844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3519844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519844 prefixEnd_3519844 := by exact prefixLift 3519844
  have htrace : WordTrace (prefixWord ++ tailWord_3519844) baseStart_3519844 baseEnd_3519844 := by
    simpa [prefixWord, tailWord_3519844, baseEnd_3519844] using wordTrace_append hprefix tailTrace_3519844
  have hstable : (prefixWord ++ tailWord_3519844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519844).length < 2 ^ (prefixWord ++ tailWord_3519844).sum := by decide
  have hdescent : baseEnd_3519844 < baseStart_3519844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519883 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_3519883 : Nat := 118140960795 + 3519883 * 2 ^ 59
def prefixEnd_3519883 : Nat := 4983230072969 + 3 ^ 40 * 3519883 * 2
def baseEnd_3519883 : Nat := 1204927884393171450183239

theorem tailTrace_3519883 : CollatzResearch.WordTrace tailWord_3519883 prefixEnd_3519883 1204927884393171450183239 := by
  unfold tailWord_3519883
  simp only [CollatzResearch.WordTrace]
  refine ⟨128380679907072514001660303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85587119938048342667773535 128380679907072514001660303)
  ·
    refine ⟨192571019860608771002490455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128380679907072514001660303 192571019860608771002490455)
    ·
      refine ⟨288856529790913156503735683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192571019860608771002490455 288856529790913156503735683)
      ·
        refine ⟨433284794686369734755603525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288856529790913156503735683 433284794686369734755603525)
        ·
          refine ⟨81240899003694325266675661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433284794686369734755603525 81240899003694325266675661)
          ·
            refine ⟨30465337126385371975003373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81240899003694325266675661 30465337126385371975003373)
            ·
              refine ⟨11424501422394514490626265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30465337126385371975003373 11424501422394514490626265)
              ·
                refine ⟨8568376066795885867969699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11424501422394514490626265 8568376066795885867969699)
                ·
                  refine ⟨12852564100193828801954549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568376066795885867969699 12852564100193828801954549)
                  ·
                    refine ⟨1204927884393171450183239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12852564100193828801954549 1204927884393171450183239)
                    ·
                      rfl

theorem cell22_3519883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_3519883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519883 prefixEnd_3519883 := by exact prefixLift 3519883
  have htrace : WordTrace (prefixWord ++ tailWord_3519883) baseStart_3519883 baseEnd_3519883 := by
    simpa [prefixWord, tailWord_3519883, baseEnd_3519883] using wordTrace_append hprefix tailTrace_3519883
  have hstable : (prefixWord ++ tailWord_3519883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519883).length < 2 ^ (prefixWord ++ tailWord_3519883).sum := by decide
  have hdescent : baseEnd_3519883 < baseStart_3519883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519917 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_3519917 : Nat := 118140960795 + 3519917 * 2 ^ 59
def prefixEnd_3519917 : Nat := 4983230072969 + 3 ^ 40 * 3519917 * 2
def baseEnd_3519917 : Nat := 1204939523288006694833135

theorem tailTrace_3519917 : CollatzResearch.WordTrace tailWord_3519917 prefixEnd_3519917 1204939523288006694833135 := by
  unfold tailWord_3519917
  simp only [CollatzResearch.WordTrace]
  refine ⟨128381919988949337808398005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85587946659299558538932003 128381919988949337808398005)
  ·
    refine ⟨12035804998964000419537313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128381919988949337808398005 12035804998964000419537313)
    ·
      refine ⟨9026853749223000314652985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12035804998964000419537313 9026853749223000314652985)
      ·
        refine ⟨6770140311917250235989739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9026853749223000314652985 6770140311917250235989739)
        ·
          refine ⟨10155210467875875353984609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6770140311917250235989739 10155210467875875353984609)
          ·
            refine ⟨7616407850906906515488457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10155210467875875353984609 7616407850906906515488457)
            ·
              refine ⟨5712305888180179886616343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616407850906906515488457 5712305888180179886616343)
              ·
                refine ⟨8568458832270269829924515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712305888180179886616343 8568458832270269829924515)
                ·
                  refine ⟨12852688248405404744886773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8568458832270269829924515 12852688248405404744886773)
                  ·
                    refine ⟨1204939523288006694833135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12852688248405404744886773 1204939523288006694833135)
                    ·
                      rfl

theorem cell22_3519917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_3519917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519917 prefixEnd_3519917 := by exact prefixLift 3519917
  have htrace : WordTrace (prefixWord ++ tailWord_3519917) baseStart_3519917 baseEnd_3519917 := by
    simpa [prefixWord, tailWord_3519917, baseEnd_3519917] using wordTrace_append hprefix tailTrace_3519917
  have hstable : (prefixWord ++ tailWord_3519917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519917).length < 2 ^ (prefixWord ++ tailWord_3519917).sum := by decide
  have hdescent : baseEnd_3519917 < baseStart_3519917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519938 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3519938 : Nat := 118140960795 + 3519938 * 2 ^ 59
def prefixEnd_3519938 : Nat := 4983230072969 + 3 ^ 40 * 3519938 * 2
def baseEnd_3519938 : Nat := 1204946712017169640058071

theorem tailTrace_3519938 : CollatzResearch.WordTrace tailWord_3519938 prefixEnd_3519938 1204946712017169640058071 := by
  unfold tailWord_3519938
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095671480468314598728117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85588457281248838929941645 32095671480468314598728117)
  ·
    refine ⟨3008969201293904493630761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32095671480468314598728117 3008969201293904493630761)
    ·
      refine ⟨2256726900970428370223071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3008969201293904493630761 2256726900970428370223071)
      ·
        refine ⟨3385090351455642555334607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2256726900970428370223071 3385090351455642555334607)
        ·
          refine ⟨5077635527183463833001911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385090351455642555334607 5077635527183463833001911)
          ·
            refine ⟨7616453290775195749502867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077635527183463833001911 7616453290775195749502867)
            ·
              refine ⟨11424679936162793624254301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616453290775195749502867 11424679936162793624254301)
              ·
                refine ⟨4284254976061047609095363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11424679936162793624254301 4284254976061047609095363)
                ·
                  refine ⟨6426382464091571413643045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4284254976061047609095363 6426382464091571413643045)
                  ·
                    refine ⟨1204946712017169640058071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6426382464091571413643045 1204946712017169640058071)
                    ·
                      rfl

theorem cell22_3519938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3519938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519938 prefixEnd_3519938 := by exact prefixLift 3519938
  have htrace : WordTrace (prefixWord ++ tailWord_3519938) baseStart_3519938 baseEnd_3519938 := by
    simpa [prefixWord, tailWord_3519938, baseEnd_3519938] using wordTrace_append hprefix tailTrace_3519938
  have hstable : (prefixWord ++ tailWord_3519938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519938).length < 2 ^ (prefixWord ++ tailWord_3519938).sum := by decide
  have hdescent : baseEnd_3519938 < baseStart_3519938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3519962 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_3519962 : Nat := 118140960795 + 3519962 * 2 ^ 59
def prefixEnd_3519962 : Nat := 4983230072969 + 3 ^ 40 * 3519962 * 2
def baseEnd_3519962 : Nat := 1204954927707641577457997

theorem tailTrace_3519962 : CollatzResearch.WordTrace tailWord_3519962 prefixEnd_3519962 1204954927707641577457997 := by
  unfold tailWord_3519962
  simp only [CollatzResearch.WordTrace]
  refine ⟨32095890318446577623446535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85589040849190873662524093 32095890318446577623446535)
  ·
    refine ⟨48143835477669866435169803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32095890318446577623446535 48143835477669866435169803)
    ·
      refine ⟨72215753216504799652754705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48143835477669866435169803 72215753216504799652754705)
      ·
        refine ⟨54161814912378599739566029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72215753216504799652754705 54161814912378599739566029)
        ·
          refine ⟨20310680592141974902337261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54161814912378599739566029 20310680592141974902337261)
          ·
            refine ⟨7616505222053240588376473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20310680592141974902337261 7616505222053240588376473)
            ·
              refine ⟨5712378916539930441282355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7616505222053240588376473 5712378916539930441282355)
              ·
                refine ⟨8568568374809895661923533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712378916539930441282355 8568568374809895661923533)
                ·
                  refine ⟨3213213140553710873221325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8568568374809895661923533 3213213140553710873221325)
                  ·
                    refine ⟨1204954927707641577457997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213213140553710873221325 1204954927707641577457997)
                    ·
                      rfl

theorem cell22_3519962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_3519962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3519962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3519962 prefixEnd_3519962 := by exact prefixLift 3519962
  have htrace : WordTrace (prefixWord ++ tailWord_3519962) baseStart_3519962 baseEnd_3519962 := by
    simpa [prefixWord, tailWord_3519962, baseEnd_3519962] using wordTrace_append hprefix tailTrace_3519962
  have hstable : (prefixWord ++ tailWord_3519962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3519962).length < 2 ^ (prefixWord ++ tailWord_3519962).sum := by decide
  have hdescent : baseEnd_3519962 < baseStart_3519962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3519962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520013 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_3520013 : Nat := 118140960795 + 3520013 * 2 ^ 59
def prefixEnd_3520013 : Nat := 4983230072969 + 3 ^ 40 * 3520013 * 2
def baseEnd_3520013 : Nat := 1204972386049894444432841

theorem tailTrace_3520013 : CollatzResearch.WordTrace tailWord_3520013 prefixEnd_3520013 1204972386049894444432841 := by
  unfold tailWord_3520013
  simp only [CollatzResearch.WordTrace]
  refine ⟨128385421396601546203892693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85590280931067697469261795 128385421396601546203892693)
  ·
    refine ⟨3009033313982848739153735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 128385421396601546203892693 3009033313982848739153735)
    ·
      refine ⟨4513549970974273108730603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009033313982848739153735 4513549970974273108730603)
      ·
        refine ⟨6770324956461409663095905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513549970974273108730603 6770324956461409663095905)
        ·
          refine ⟨5077743717346057247321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6770324956461409663095905 5077743717346057247321929)
          ·
            refine ⟨3808307788009542935491447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077743717346057247321929 3808307788009542935491447)
            ·
              refine ⟨5712461682014314403237171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808307788009542935491447 5712461682014314403237171)
              ·
                refine ⟨8568692523021471604855757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5712461682014314403237171 8568692523021471604855757)
                ·
                  refine ⟨3213259696133051851820909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8568692523021471604855757 3213259696133051851820909)
                  ·
                    refine ⟨1204972386049894444432841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213259696133051851820909 1204972386049894444432841)
                    ·
                      rfl

theorem cell22_3520013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_3520013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520013 prefixEnd_3520013 := by exact prefixLift 3520013
  have htrace : WordTrace (prefixWord ++ tailWord_3520013) baseStart_3520013 baseEnd_3520013 := by
    simpa [prefixWord, tailWord_3520013, baseEnd_3520013] using wordTrace_append hprefix tailTrace_3520013
  have hstable : (prefixWord ++ tailWord_3520013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520013).length < 2 ^ (prefixWord ++ tailWord_3520013).sum := by decide
  have hdescent : baseEnd_3520013 < baseStart_3520013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520071 : List Nat := [1, 1, 4, 1, 5, 2, 2, 2, 4]
def baseStart_3520071 : Nat := 118140960795 + 3520071 * 2 ^ 59
def prefixEnd_3520071 : Nat := 4983230072969 + 3 ^ 40 * 3520071 * 2
def baseEnd_3520071 : Nat := 401664080211733875494221

theorem tailTrace_3520071 : CollatzResearch.WordTrace tailWord_3520071 prefixEnd_3520071 401664080211733875494221 := by
  unfold tailWord_3520071
  simp only [CollatzResearch.WordTrace]
  refine ⟨128387536830391422109504067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85591691220260948073002711 128387536830391422109504067)
  ·
    refine ⟨192581305245587133164256101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128387536830391422109504067 192581305245587133164256101)
    ·
      refine ⟨36108994733547587468298019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192581305245587133164256101 36108994733547587468298019)
      ·
        refine ⟨54163492100321381202447029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36108994733547587468298019 54163492100321381202447029)
        ·
          refine ⟨5077827384405129487729409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54163492100321381202447029 5077827384405129487729409)
          ·
            refine ⟨3808370538303847115797057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5077827384405129487729409 3808370538303847115797057)
            ·
              refine ⟨2856277903727885336847793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3808370538303847115797057 2856277903727885336847793)
              ·
                refine ⟨2142208427795914002635845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2856277903727885336847793 2142208427795914002635845)
                ·
                  refine ⟨401664080211733875494221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142208427795914002635845 401664080211733875494221)
                  ·
                    rfl

theorem cell22_3520071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 4].length) (baseStart_3520071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520071 prefixEnd_3520071 := by exact prefixLift 3520071
  have htrace : WordTrace (prefixWord ++ tailWord_3520071) baseStart_3520071 baseEnd_3520071 := by
    simpa [prefixWord, tailWord_3520071, baseEnd_3520071] using wordTrace_append hprefix tailTrace_3520071
  have hstable : (prefixWord ++ tailWord_3520071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520071).length < 2 ^ (prefixWord ++ tailWord_3520071).sum := by decide
  have hdescent : baseEnd_3520071 < baseStart_3520071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520082 : List Nat := [3, 2, 2, 1, 2, 4, 1, 7]
def baseStart_3520082 : Nat := 118140960795 + 3520082 * 2 ^ 59
def prefixEnd_3520082 : Nat := 4983230072969 + 3 ^ 40 * 3520082 * 2
def baseEnd_3520082 : Nat := 133888445128889029384181

theorem tailTrace_3520082 : CollatzResearch.WordTrace tailWord_3520082 prefixEnd_3520082 133888445128889029384181 := by
  unfold tailWord_3520082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096984508337892747038625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85591958688901047325436333 32096984508337892747038625)
  ·
    refine ⟨24072738381253419560278969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32096984508337892747038625 24072738381253419560278969)
    ·
      refine ⟨18054553785940064670209227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24072738381253419560278969 18054553785940064670209227)
      ·
        refine ⟨27081830678910097005313841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18054553785940064670209227 27081830678910097005313841)
        ·
          refine ⟨20311373009182572753985381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27081830678910097005313841 20311373009182572753985381)
          ·
            refine ⟨3808382439221732391372259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20311373009182572753985381 3808382439221732391372259)
            ·
              refine ⟨5712573658832598587058389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808382439221732391372259 5712573658832598587058389)
              ·
                refine ⟨133888445128889029384181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5712573658832598587058389 133888445128889029384181)
                ·
                  rfl

theorem cell22_3520082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_3520082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520082 prefixEnd_3520082 := by exact prefixLift 3520082
  have htrace : WordTrace (prefixWord ++ tailWord_3520082) baseStart_3520082 baseEnd_3520082 := by
    simpa [prefixWord, tailWord_3520082, baseEnd_3520082] using wordTrace_append hprefix tailTrace_3520082
  have hstable : (prefixWord ++ tailWord_3520082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520082).length < 2 ^ (prefixWord ++ tailWord_3520082).sum := by decide
  have hdescent : baseEnd_3520082 < baseStart_3520082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520097 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3520097 : Nat := 118140960795 + 3520097 * 2 ^ 59
def prefixEnd_3520097 : Nat := 4983230072969 + 3 ^ 40 * 3520097 * 2
def baseEnd_3520097 : Nat := 1205001140966546225332583

theorem tailTrace_3520097 : CollatzResearch.WordTrace tailWord_3520097 prefixEnd_3520097 1205001140966546225332583 := by
  unfold tailWord_3520097
  simp only [CollatzResearch.WordTrace]
  refine ⟨128388485128297228549950545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85592323418864819033300363 128388485128297228549950545)
  ·
    refine ⟨96291363846222921412462909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128388485128297228549950545 96291363846222921412462909)
    ·
      refine ⟨36109261442333595529673591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96291363846222921412462909 36109261442333595529673591)
      ·
        refine ⟨54163892163500393294510387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36109261442333595529673591 54163892163500393294510387)
        ·
          refine ⟨81245838245250589941765581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54163892163500393294510387 81245838245250589941765581)
          ·
            refine ⟨30467189341968971228162093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81245838245250589941765581 30467189341968971228162093)
            ·
              refine ⟨11425196003238364210560785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30467189341968971228162093 11425196003238364210560785)
              ·
                refine ⟨8568897002428773157920589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11425196003238364210560785 8568897002428773157920589)
                ·
                  refine ⟨3213336375910789934220221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8568897002428773157920589 3213336375910789934220221)
                  ·
                    refine ⟨1205001140966546225332583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213336375910789934220221 1205001140966546225332583)
                    ·
                      rfl

theorem cell22_3520097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3520097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520097 prefixEnd_3520097 := by exact prefixLift 3520097
  have htrace : WordTrace (prefixWord ++ tailWord_3520097) baseStart_3520097 baseEnd_3520097 := by
    simpa [prefixWord, tailWord_3520097, baseEnd_3520097] using wordTrace_append hprefix tailTrace_3520097
  have hstable : (prefixWord ++ tailWord_3520097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520097).length < 2 ^ (prefixWord ++ tailWord_3520097).sum := by decide
  have hdescent : baseEnd_3520097 < baseStart_3520097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520142 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3520142 : Nat := 118140960795 + 3520142 * 2 ^ 59
def prefixEnd_3520142 : Nat := 4983230072969 + 3 ^ 40 * 3520142 * 2
def baseEnd_3520142 : Nat := 1205016545386181107957445

theorem tailTrace_3520142 : CollatzResearch.WordTrace tailWord_3520142 prefixEnd_3520142 1205016545386181107957445 := by
  unfold tailWord_3520142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16048765801641775154417335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85593417608756134156892453 16048765801641775154417335)
  ·
    refine ⟨24073148702462662731626003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16048765801641775154417335 24073148702462662731626003)
    ·
      refine ⟨36109723053693994097439005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24073148702462662731626003 36109723053693994097439005)
      ·
        refine ⟨13541146145135247786539627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36109723053693994097439005 13541146145135247786539627)
        ·
          refine ⟨20311719217702871679809441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541146145135247786539627 20311719217702871679809441)
          ·
            refine ⟨15233789413277153759857081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20311719217702871679809441 15233789413277153759857081)
            ·
              refine ⟨11425342059957865319892811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15233789413277153759857081 11425342059957865319892811)
              ·
                refine ⟨17138013089936797979839217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11425342059957865319892811 17138013089936797979839217)
                ·
                  refine ⟨12853509817452598484879413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17138013089936797979839217 12853509817452598484879413)
                  ·
                    refine ⟨1205016545386181107957445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12853509817452598484879413 1205016545386181107957445)
                    ·
                      rfl

theorem cell22_3520142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3520142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520142 prefixEnd_3520142 := by exact prefixLift 3520142
  have htrace : WordTrace (prefixWord ++ tailWord_3520142) baseStart_3520142 baseEnd_3520142 := by
    simpa [prefixWord, tailWord_3520142, baseEnd_3520142] using wordTrace_append hprefix tailTrace_3520142
  have hstable : (prefixWord ++ tailWord_3520142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520142).length < 2 ^ (prefixWord ++ tailWord_3520142).sum := by decide
  have hdescent : baseEnd_3520142 < baseStart_3520142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520221 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_3520221 : Nat := 118140960795 + 3520221 * 2 ^ 59
def prefixEnd_3520221 : Nat := 4983230072969 + 3 ^ 40 * 3520221 * 2
def baseEnd_3520221 : Nat := 1205043588700651235232203

theorem tailTrace_3520221 : CollatzResearch.WordTrace tailWord_3520221 prefixEnd_3520221 1205043588700651235232203 := by
  unfold tailWord_3520221
  simp only [CollatzResearch.WordTrace]
  refine ⟨128393007779847997727464517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85595338519898665151643011 128393007779847997727464517)
  ·
    refine ⟨24073688958721499573899597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128393007779847997727464517 24073688958721499573899597)
    ·
      refine ⟨9027633359520562340212349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24073688958721499573899597 9027633359520562340212349)
      ·
        refine ⟨3385362509820210877579631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9027633359520562340212349 3385362509820210877579631)
        ·
          refine ⟨5078043764730316316369447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385362509820210877579631 5078043764730316316369447)
          ·
            refine ⟨7617065647095474474554171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078043764730316316369447 7617065647095474474554171)
            ·
              refine ⟨11425598470643211711831257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617065647095474474554171 11425598470643211711831257)
              ·
                refine ⟨8569198852982408783873443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11425598470643211711831257 8569198852982408783873443)
                ·
                  refine ⟨12853798279473613175810165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8569198852982408783873443 12853798279473613175810165)
                  ·
                    refine ⟨1205043588700651235232203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12853798279473613175810165 1205043588700651235232203)
                    ·
                      rfl

theorem cell22_3520221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_3520221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520221 prefixEnd_3520221 := by exact prefixLift 3520221
  have htrace : WordTrace (prefixWord ++ tailWord_3520221) baseStart_3520221 baseEnd_3520221 := by
    simpa [prefixWord, tailWord_3520221, baseEnd_3520221] using wordTrace_append hprefix tailTrace_3520221
  have hstable : (prefixWord ++ tailWord_3520221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520221).length < 2 ^ (prefixWord ++ tailWord_3520221).sum := by decide
  have hdescent : baseEnd_3520221 < baseStart_3520221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520296 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_3520296 : Nat := 118140960795 + 3520296 * 2 ^ 59
def prefixEnd_3520296 : Nat := 4983230072969 + 3 ^ 40 * 3520296 * 2
def baseEnd_3520296 : Nat := 401689754244458679868991

theorem tailTrace_3520296 : CollatzResearch.WordTrace tailWord_3520296 prefixEnd_3520296 401689754244458679868991 := by
  unfold tailWord_3520296
  simp only [CollatzResearch.WordTrace]
  refine ⟨64197871627288142768222371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85597162169717523690963161 64197871627288142768222371)
  ·
    refine ⟨96296807440932214152333557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64197871627288142768222371 96296807440932214152333557)
    ·
      refine ⟨9027825697587395076781271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96296807440932214152333557 9027825697587395076781271)
      ·
        refine ⟨13541738546381092615171907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027825697587395076781271 13541738546381092615171907)
        ·
          refine ⟨20312607819571638922757861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541738546381092615171907 20312607819571638922757861)
          ·
            refine ⟨3808613966169682298017099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20312607819571638922757861 3808613966169682298017099)
            ·
              refine ⟨5712920949254523447025649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808613966169682298017099 5712920949254523447025649)
              ·
                refine ⟨4284690711940892585269237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5712920949254523447025649 4284690711940892585269237)
                ·
                  refine ⟨401689754244458679868991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4284690711940892585269237 401689754244458679868991)
                  ·
                    rfl

theorem cell22_3520296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_3520296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520296 prefixEnd_3520296 := by exact prefixLift 3520296
  have htrace : WordTrace (prefixWord ++ tailWord_3520296) baseStart_3520296 baseEnd_3520296 := by
    simpa [prefixWord, tailWord_3520296, baseEnd_3520296] using wordTrace_append hprefix tailTrace_3520296
  have hstable : (prefixWord ++ tailWord_3520296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520296).length < 2 ^ (prefixWord ++ tailWord_3520296).sum := by decide
  have hdescent : baseEnd_3520296 < baseStart_3520296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520313 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 5]
def baseStart_3520313 : Nat := 118140960795 + 3520313 * 2 ^ 59
def prefixEnd_3520313 : Nat := 4983230072969 + 3 ^ 40 * 3520313 * 2
def baseEnd_3520313 : Nat := 401691694060264553977307

theorem tailTrace_3520313 : CollatzResearch.WordTrace tailWord_3520313 prefixEnd_3520313 401691694060264553977307 := by
  unfold tailWord_3520313
  simp only [CollatzResearch.WordTrace]
  refine ⟨128396363295514697439813593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85597575530343131626542395 128396363295514697439813593)
  ·
    refine ⟨96297272471636023079860195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128396363295514697439813593 96297272471636023079860195)
    ·
      refine ⟨144445908707454034619790293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96297272471636023079860195 144445908707454034619790293)
      ·
        refine ⟨3385450985330953936401335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144445908707454034619790293 3385450985330953936401335)
        ·
          refine ⟨5078176477996430904602003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385450985330953936401335 5078176477996430904602003)
          ·
            refine ⟨7617264716994646356903005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5078176477996430904602003 7617264716994646356903005)
            ·
              refine ⟨2856474268872992383838627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7617264716994646356903005 2856474268872992383838627)
              ·
                refine ⟨4284711403309488575757941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2856474268872992383838627 4284711403309488575757941)
                ·
                  refine ⟨401691694060264553977307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4284711403309488575757941 401691694060264553977307)
                  ·
                    rfl

theorem cell22_3520313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 5].length) (baseStart_3520313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520313 prefixEnd_3520313 := by exact prefixLift 3520313
  have htrace : WordTrace (prefixWord ++ tailWord_3520313) baseStart_3520313 baseEnd_3520313 := by
    simpa [prefixWord, tailWord_3520313, baseEnd_3520313] using wordTrace_append hprefix tailTrace_3520313
  have hstable : (prefixWord ++ tailWord_3520313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520313).length < 2 ^ (prefixWord ++ tailWord_3520313).sum := by decide
  have hdescent : baseEnd_3520313 < baseStart_3520313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520341 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 4]
def baseStart_3520341 : Nat := 118140960795 + 3520341 * 2 ^ 59
def prefixEnd_3520341 : Nat := 4983230072969 + 3 ^ 40 * 3520341 * 2
def baseEnd_3520341 : Nat := 401694889051003640743945

theorem tailTrace_3520341 : CollatzResearch.WordTrace tailWord_3520341 prefixEnd_3520341 401694889051003640743945 := by
  unfold tailWord_3520341
  simp only [CollatzResearch.WordTrace]
  refine ⟨128397384539413258221832877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85598256359608838814555251 128397384539413258221832877)
  ·
    refine ⟨48149019202279971833187329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128397384539413258221832877 48149019202279971833187329)
    ·
      refine ⟨36111764401709978874890497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48149019202279971833187329 36111764401709978874890497)
      ·
        refine ⟨27083823301282484156167873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36111764401709978874890497 27083823301282484156167873)
        ·
          refine ⟨20312867475961863117125905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27083823301282484156167873 20312867475961863117125905)
          ·
            refine ⟨15234650606971397337844429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20312867475961863117125905 15234650606971397337844429)
            ·
              refine ⟨5712993977614274001691661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15234650606971397337844429 5712993977614274001691661)
              ·
                refine ⟨2142372741605352750634373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712993977614274001691661 2142372741605352750634373)
                ·
                  refine ⟨401694889051003640743945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142372741605352750634373 401694889051003640743945)
                  ·
                    rfl

theorem cell22_3520341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_3520341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520341 prefixEnd_3520341 := by exact prefixLift 3520341
  have htrace : WordTrace (prefixWord ++ tailWord_3520341) baseStart_3520341 baseEnd_3520341 := by
    simpa [prefixWord, tailWord_3520341, baseEnd_3520341] using wordTrace_append hprefix tailTrace_3520341
  have hstable : (prefixWord ++ tailWord_3520341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520341).length < 2 ^ (prefixWord ++ tailWord_3520341).sum := by decide
  have hdescent : baseEnd_3520341 < baseStart_3520341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520352 : List Nat := [2, 1, 1, 3, 3, 2, 10]
def baseStart_3520352 : Nat := 118140960795 + 3520352 * 2 ^ 59
def prefixEnd_3520352 : Nat := 4983230072969 + 3 ^ 40 * 3520352 * 2
def baseEnd_3520352 : Nat := 44632904913992983711363

theorem tailTrace_3520352 : CollatzResearch.WordTrace tailWord_3520352 prefixEnd_3520352 44632904913992983711363 := by
  unfold tailWord_3520352
  simp only [CollatzResearch.WordTrace]
  refine ⟨64198892871186703550241655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85598523828248938066988873 64198892871186703550241655)
  ·
    refine ⟨96298339306780055325362483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64198892871186703550241655 96298339306780055325362483)
    ·
      refine ⟨144447508960170082988043725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96298339306780055325362483 144447508960170082988043725)
      ·
        refine ⟨54167815860063781120516397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144447508960170082988043725 54167815860063781120516397)
        ·
          refine ⟨20312930947523917920193649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54167815860063781120516397 20312930947523917920193649)
          ·
            refine ⟨15234698210642938440145237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20312930947523917920193649 15234698210642938440145237)
            ·
              refine ⟨44632904913992983711363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15234698210642938440145237 44632904913992983711363)
              ·
                rfl

theorem cell22_3520352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 10].length) (baseStart_3520352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520352 prefixEnd_3520352 := by exact prefixLift 3520352
  have htrace : WordTrace (prefixWord ++ tailWord_3520352) baseStart_3520352 baseEnd_3520352 := by
    simpa [prefixWord, tailWord_3520352, baseEnd_3520352] using wordTrace_append hprefix tailTrace_3520352
  have hstable : (prefixWord ++ tailWord_3520352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520352).length < 2 ^ (prefixWord ++ tailWord_3520352).sum := by decide
  have hdescent : baseEnd_3520352 < baseStart_3520352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520384 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_3520384 : Nat := 118140960795 + 3520384 * 2 ^ 59
def prefixEnd_3520384 : Nat := 4983230072969 + 3 ^ 40 * 3520384 * 2
def baseEnd_3520384 : Nat := 1205099386931773143406703

theorem tailTrace_3520384 : CollatzResearch.WordTrace tailWord_3520384 prefixEnd_3520384 1205099386931773143406703 := by
  unfold tailWord_3520384
  simp only [CollatzResearch.WordTrace]
  refine ⟨64199476439128738282824103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85599301918838317710432137 64199476439128738282824103)
  ·
    refine ⟨96299214658693107424236155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64199476439128738282824103 96299214658693107424236155)
    ·
      refine ⟨144448821988039661136354233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96299214658693107424236155 144448821988039661136354233)
      ·
        refine ⟨108336616491029745852265675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144448821988039661136354233 108336616491029745852265675)
        ·
          refine ⟨162504924736544618778398513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108336616491029745852265675 162504924736544618778398513)
          ·
            refine ⟨121878693552408464083798885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162504924736544618778398513 121878693552408464083798885)
            ·
              refine ⟨22852255041076587015712291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121878693552408464083798885 22852255041076587015712291)
              ·
                refine ⟨34278382561614880523568437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22852255041076587015712291 34278382561614880523568437)
                ·
                  refine ⟨3213598365151395049084541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34278382561614880523568437 3213598365151395049084541)
                  ·
                    refine ⟨1205099386931773143406703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213598365151395049084541 1205099386931773143406703)
                    ·
                      rfl

theorem cell22_3520384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_3520384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520384 prefixEnd_3520384 := by exact prefixLift 3520384
  have htrace : WordTrace (prefixWord ++ tailWord_3520384) baseStart_3520384 baseEnd_3520384 := by
    simpa [prefixWord, tailWord_3520384, baseEnd_3520384] using wordTrace_append hprefix tailTrace_3520384
  have hstable : (prefixWord ++ tailWord_3520384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520384).length < 2 ^ (prefixWord ++ tailWord_3520384).sum := by decide
  have hdescent : baseEnd_3520384 < baseStart_3520384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 1, 10]
def baseStart_3520427 : Nat := 118140960795 + 3520427 * 2 ^ 59
def prefixEnd_3520427 : Nat := 4983230072969 + 3 ^ 40 * 3520427 * 2
def baseEnd_3520427 : Nat := 1205114106710535364581571

theorem tailTrace_3520427 : CollatzResearch.WordTrace tailWord_3520427 prefixEnd_3520427 1205114106710535364581571 := by
  unfold tailWord_3520427
  simp only [CollatzResearch.WordTrace]
  refine ⟨128400521217101694909463535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85600347478067796606309023 128400521217101694909463535)
  ·
    refine ⟨192600781825652542364195303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128400521217101694909463535 192600781825652542364195303)
    ·
      refine ⟨288901172738478813546292955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192600781825652542364195303 288901172738478813546292955)
      ·
        refine ⟨433351759107718220319439433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288901172738478813546292955 433351759107718220319439433)
        ·
          refine ⟨325013819330788665239579575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433351759107718220319439433 325013819330788665239579575)
          ·
            refine ⟨487520728996182997859369363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325013819330788665239579575 487520728996182997859369363)
            ·
              refine ⟨731281093494274496789054045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487520728996182997859369363 731281093494274496789054045)
              ·
                refine ⟨274230410060352936295895267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731281093494274496789054045 274230410060352936295895267)
                ·
                  refine ⟨411345615090529404443842901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 274230410060352936295895267 411345615090529404443842901)
                  ·
                    refine ⟨1205114106710535364581571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 411345615090529404443842901 1205114106710535364581571)
                    ·
                      rfl

theorem cell22_3520427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_3520427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520427 prefixEnd_3520427 := by exact prefixLift 3520427
  have htrace : WordTrace (prefixWord ++ tailWord_3520427) baseStart_3520427 baseEnd_3520427 := by
    simpa [prefixWord, tailWord_3520427, baseEnd_3520427] using wordTrace_append hprefix tailTrace_3520427
  have hstable : (prefixWord ++ tailWord_3520427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520427).length < 2 ^ (prefixWord ++ tailWord_3520427).sum := by decide
  have hdescent : baseEnd_3520427 < baseStart_3520427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520491 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 2, 3]
def baseStart_3520491 : Nat := 118140960795 + 3520491 * 2 ^ 59
def prefixEnd_3520491 : Nat := 4983230072969 + 3 ^ 40 * 3520491 * 2
def baseEnd_3520491 : Nat := 1205136015218460530981375

theorem tailTrace_3520491 : CollatzResearch.WordTrace tailWord_3520491 prefixEnd_3520491 1205136015218460530981375 := by
  unfold tailWord_3520491
  simp only [CollatzResearch.WordTrace]
  refine ⟨128402855488869833839793327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85601903659246555893195551 128402855488869833839793327)
  ·
    refine ⟨192604283233304750759689991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128402855488869833839793327 192604283233304750759689991)
    ·
      refine ⟨288906424849957126139534987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192604283233304750759689991 288906424849957126139534987)
      ·
        refine ⟨433359637274935689209302481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288906424849957126139534987 433359637274935689209302481)
        ·
          refine ⟨325019727956201766906976861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433359637274935689209302481 325019727956201766906976861)
          ·
            refine ⟨121882397983575662590116323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325019727956201766906976861 121882397983575662590116323)
            ·
              refine ⟨182823596975363493885174485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121882397983575662590116323 182823596975363493885174485)
              ·
                refine ⟨4284928054110081887933777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 182823596975363493885174485 4284928054110081887933777)
                ·
                  refine ⟨3213696040582561415950333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4284928054110081887933777 3213696040582561415950333)
                  ·
                    refine ⟨1205136015218460530981375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213696040582561415950333 1205136015218460530981375)
                    ·
                      rfl

theorem cell22_3520491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 3].length) (baseStart_3520491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520491 prefixEnd_3520491 := by exact prefixLift 3520491
  have htrace : WordTrace (prefixWord ++ tailWord_3520491) baseStart_3520491 baseEnd_3520491 := by
    simpa [prefixWord, tailWord_3520491, baseEnd_3520491] using wordTrace_append hprefix tailTrace_3520491
  have hstable : (prefixWord ++ tailWord_3520491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520491).length < 2 ^ (prefixWord ++ tailWord_3520491).sum := by decide
  have hdescent : baseEnd_3520491 < baseStart_3520491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520510 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3520510 : Nat := 118140960795 + 3520510 * 2 ^ 59
def prefixEnd_3520510 : Nat := 4983230072969 + 3 ^ 40 * 3520510 * 2
def baseEnd_3520510 : Nat := 401714173102250271585439

theorem tailTrace_3520510 : CollatzResearch.WordTrace tailWord_3520510 prefixEnd_3520510 401714173102250271585439 := by
  unfold tailWord_3520510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16050443559475125010591873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85602365650534000056489989 16050443559475125010591873)
  ·
    refine ⟨12037832669606343757943905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16050443559475125010591873 12037832669606343757943905)
    ·
      refine ⟨9028374502204757818457929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12037832669606343757943905 9028374502204757818457929)
      ·
        refine ⟨6771280876653568363843447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9028374502204757818457929 6771280876653568363843447)
        ·
          refine ⟨10156921314980352545765171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771280876653568363843447 10156921314980352545765171)
          ·
            refine ⟨15235381972470528818647757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156921314980352545765171 15235381972470528818647757)
            ·
              refine ⟨5713268239676448306992909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15235381972470528818647757 5713268239676448306992909)
              ·
                refine ⟨2142475589878668115122341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5713268239676448306992909 2142475589878668115122341)
                ·
                  refine ⟨401714173102250271585439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142475589878668115122341 401714173102250271585439)
                  ·
                    rfl

theorem cell22_3520510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3520510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520510 prefixEnd_3520510 := by exact prefixLift 3520510
  have htrace : WordTrace (prefixWord ++ tailWord_3520510) baseStart_3520510 baseEnd_3520510 := by
    simpa [prefixWord, tailWord_3520510, baseEnd_3520510] using wordTrace_append hprefix tailTrace_3520510
  have hstable : (prefixWord ++ tailWord_3520510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520510).length < 2 ^ (prefixWord ++ tailWord_3520510).sum := by decide
  have hdescent : baseEnd_3520510 < baseStart_3520510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520630 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3520630 : Nat := 118140960795 + 3520630 * 2 ^ 59
def prefixEnd_3520630 : Nat := 4983230072969 + 3 ^ 40 * 3520630 * 2
def baseEnd_3520630 : Nat := 1205183597759110501755949

theorem tailTrace_3520630 : CollatzResearch.WordTrace tailWord_3520630 prefixEnd_3520630 1205183597759110501755949 := by
  unfold tailWord_3520630
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025495327210391286193959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85605283490244173719402229 8025495327210391286193959)
  ·
    refine ⟨12038242990815586929290939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025495327210391286193959 12038242990815586929290939)
    ·
      refine ⟨18057364486223380393936409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038242990815586929290939 18057364486223380393936409)
      ·
        refine ⟨13543023364667535295452307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18057364486223380393936409 13543023364667535295452307)
        ·
          refine ⟨20314535047001302943178461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543023364667535295452307 20314535047001302943178461)
          ·
            refine ⟨7617950642625488603691923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20314535047001302943178461 7617950642625488603691923)
            ·
              refine ⟨11426925963938232905537885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617950642625488603691923 11426925963938232905537885)
              ·
                refine ⟨4285097236476837339576707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11426925963938232905537885 4285097236476837339576707)
                ·
                  refine ⟨6427645854715256009365061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285097236476837339576707 6427645854715256009365061)
                  ·
                    refine ⟨1205183597759110501755949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6427645854715256009365061 1205183597759110501755949)
                    ·
                      rfl

theorem cell22_3520630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3520630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520630 prefixEnd_3520630 := by exact prefixLift 3520630
  have htrace : WordTrace (prefixWord ++ tailWord_3520630) baseStart_3520630 baseEnd_3520630 := by
    simpa [prefixWord, tailWord_3520630, baseEnd_3520630] using wordTrace_append hprefix tailTrace_3520630
  have hstable : (prefixWord ++ tailWord_3520630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520630).length < 2 ^ (prefixWord ++ tailWord_3520630).sum := by decide
  have hdescent : baseEnd_3520630 < baseStart_3520630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520643 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 4, 3]
def baseStart_3520643 : Nat := 118140960795 + 3520643 * 2 ^ 59
def prefixEnd_3520643 : Nat := 4983230072969 + 3 ^ 40 * 3520643 * 2
def baseEnd_3520643 : Nat := 1205188047924782801180909

theorem tailTrace_3520643 : CollatzResearch.WordTrace tailWord_3520643 prefixEnd_3520643 1205188047924782801180909 := by
  unfold tailWord_3520643
  simp only [CollatzResearch.WordTrace]
  refine ⟨128408399384319163799326583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85605599589546109199551055 128408399384319163799326583)
  ·
    refine ⟨192612599076478745698989875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128408399384319163799326583 192612599076478745698989875)
    ·
      refine ⟨288918898614718118548484813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192612599076478745698989875 288918898614718118548484813)
      ·
        refine ⟨108344586980519294455681805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 288918898614718118548484813 108344586980519294455681805)
        ·
          refine ⟨40629220117694735420880677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108344586980519294455681805 40629220117694735420880677)
          ·
            refine ⟨7617978772067762891415127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40629220117694735420880677 7617978772067762891415127)
            ·
              refine ⟨11426968158101644337122691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7617978772067762891415127 11426968158101644337122691)
              ·
                refine ⟨17140452237152466505684037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11426968158101644337122691 17140452237152466505684037)
                ·
                  refine ⟨3213834794466087469815757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17140452237152466505684037 3213834794466087469815757)
                  ·
                    refine ⟨1205188047924782801180909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3213834794466087469815757 1205188047924782801180909)
                    ·
                      rfl

theorem cell22_3520643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 3].length) (baseStart_3520643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520643 prefixEnd_3520643 := by exact prefixLift 3520643
  have htrace : WordTrace (prefixWord ++ tailWord_3520643) baseStart_3520643 baseEnd_3520643 := by
    simpa [prefixWord, tailWord_3520643, baseEnd_3520643] using wordTrace_append hprefix tailTrace_3520643
  have hstable : (prefixWord ++ tailWord_3520643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520643).length < 2 ^ (prefixWord ++ tailWord_3520643).sum := by decide
  have hdescent : baseEnd_3520643 < baseStart_3520643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520673 : List Nat := [1, 2, 3, 3, 1, 2, 4, 6]
def baseStart_3520673 : Nat := 118140960795 + 3520673 * 2 ^ 59
def prefixEnd_3520673 : Nat := 4983230072969 + 3 ^ 40 * 3520673 * 2
def baseEnd_3520673 : Nat := 133910924170874746992313

theorem tailTrace_3520673 : CollatzResearch.WordTrace tailWord_3520673 prefixEnd_3520673 133910924170874746992313 := by
  unfold tailWord_3520673
  simp only [CollatzResearch.WordTrace]
  refine ⟨128409493574210478922918673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85606329049473652615279115 128409493574210478922918673)
  ·
    refine ⟨96307120180657859192189005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128409493574210478922918673 96307120180657859192189005)
    ·
      refine ⟨36115170067746697197070877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96307120180657859192189005 36115170067746697197070877)
      ·
        refine ⟨13543188775405011448901579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36115170067746697197070877 13543188775405011448901579)
        ·
          refine ⟨20314783163107517173352369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13543188775405011448901579 20314783163107517173352369)
          ·
            refine ⟨15236087372330637880014277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20314783163107517173352369 15236087372330637880014277)
            ·
              refine ⟨2856766382311994602502677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15236087372330637880014277 2856766382311994602502677)
              ·
                refine ⟨133910924170874746992313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2856766382311994602502677 133910924170874746992313)
                ·
                  rfl

theorem cell22_3520673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 6].length) (baseStart_3520673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520673 prefixEnd_3520673 := by exact prefixLift 3520673
  have htrace : WordTrace (prefixWord ++ tailWord_3520673) baseStart_3520673 baseEnd_3520673 := by
    simpa [prefixWord, tailWord_3520673, baseEnd_3520673] using wordTrace_append hprefix tailTrace_3520673
  have hstable : (prefixWord ++ tailWord_3520673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520673).length < 2 ^ (prefixWord ++ tailWord_3520673).sum := by decide
  have hdescent : baseEnd_3520673 < baseStart_3520673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520679 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 4]
def baseStart_3520679 : Nat := 118140960795 + 3520679 * 2 ^ 59
def prefixEnd_3520679 : Nat := 4983230072969 + 3 ^ 40 * 3520679 * 2
def baseEnd_3520679 : Nat := 401733457153496902426933

theorem tailTrace_3520679 : CollatzResearch.WordTrace tailWord_3520679 prefixEnd_3520679 401733457153496902426933 := by
  unfold tailWord_3520679
  simp only [CollatzResearch.WordTrace]
  refine ⟨128409712412188741947637091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85606474941459161298424727 128409712412188741947637091)
  ·
    refine ⟨192614568618283112921455637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128409712412188741947637091 192614568618283112921455637)
    ·
      refine ⟨9028807903982020918193233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 192614568618283112921455637 9028807903982020918193233)
      ·
        refine ⟨6771605927986515688644925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9028807903982020918193233 6771605927986515688644925)
        ·
          refine ⟨2539352222994943383241847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6771605927986515688644925 2539352222994943383241847)
          ·
            refine ⟨3809028334492415074862771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539352222994943383241847 3809028334492415074862771)
            ·
              refine ⟨5713542501738622612294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809028334492415074862771 5713542501738622612294157)
              ·
                refine ⟨2142578438151983479610309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5713542501738622612294157 2142578438151983479610309)
                ·
                  refine ⟨401733457153496902426933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142578438151983479610309 401733457153496902426933)
                  ·
                    rfl

theorem cell22_3520679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 4].length) (baseStart_3520679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520679 prefixEnd_3520679 := by exact prefixLift 3520679
  have htrace : WordTrace (prefixWord ++ tailWord_3520679) baseStart_3520679 baseEnd_3520679 := by
    simpa [prefixWord, tailWord_3520679, baseEnd_3520679] using wordTrace_append hprefix tailTrace_3520679
  have hstable : (prefixWord ++ tailWord_3520679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520679).length < 2 ^ (prefixWord ++ tailWord_3520679).sum := by decide
  have hdescent : baseEnd_3520679 < baseStart_3520679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520778 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3520778 : Nat := 118140960795 + 3520778 * 2 ^ 59
def prefixEnd_3520778 : Nat := 4983230072969 + 3 ^ 40 * 3520778 * 2
def baseEnd_3520778 : Nat := 1205234261183687449055495

theorem tailTrace_3520778 : CollatzResearch.WordTrace tailWord_3520778 prefixEnd_3520778 1205234261183687449055495 := by
  unfold tailWord_3520778
  simp only [CollatzResearch.WordTrace]
  refine ⟨32103330809707520463872747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85608882159220054570327325 32103330809707520463872747)
  ·
    refine ⟨48154996214561280695809121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32103330809707520463872747 48154996214561280695809121)
    ·
      refine ⟨36116247160920960521856841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48154996214561280695809121 36116247160920960521856841)
      ·
        refine ⟨27087185370690720391392631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36116247160920960521856841 27087185370690720391392631)
        ·
          refine ⟨40630778056036080587088947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27087185370690720391392631 40630778056036080587088947)
          ·
            refine ⟨60946167084054120880633421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40630778056036080587088947 60946167084054120880633421)
            ·
              refine ⟨22854812656520295330237533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60946167084054120880633421 22854812656520295330237533)
              ·
                refine ⟨8570554746195110748839075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22854812656520295330237533 8570554746195110748839075)
                ·
                  refine ⟨12855832119292666123258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8570554746195110748839075 12855832119292666123258613)
                  ·
                    refine ⟨1205234261183687449055495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12855832119292666123258613 1205234261183687449055495)
                    ·
                      rfl

theorem cell22_3520778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3520778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520778 prefixEnd_3520778 := by exact prefixLift 3520778
  have htrace : WordTrace (prefixWord ++ tailWord_3520778) baseStart_3520778 baseEnd_3520778 := by
    simpa [prefixWord, tailWord_3520778, baseEnd_3520778] using wordTrace_append hprefix tailTrace_3520778
  have hstable : (prefixWord ++ tailWord_3520778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520778).length < 2 ^ (prefixWord ++ tailWord_3520778).sum := by decide
  have hdescent : baseEnd_3520778 < baseStart_3520778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520840 : List Nat := [2, 1, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_3520840 : Nat := 118140960795 + 3520840 * 2 ^ 59
def prefixEnd_3520840 : Nat := 4983230072969 + 3 ^ 40 * 3520840 * 2
def baseEnd_3520840 : Nat := 1205255485050739954005305

theorem tailTrace_3520840 : CollatzResearch.WordTrace tailWord_3520840 prefixEnd_3520840 1205255485050739954005305 := by
  unfold tailWord_3520840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64207792282302733222123987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85610389709736977629498649 64207792282302733222123987)
  ·
    refine ⟨96311688423454099833185981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64207792282302733222123987 96311688423454099833185981)
    ·
      refine ⟨36116883158795287437444743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96311688423454099833185981 36116883158795287437444743)
      ·
        refine ⟨54175324738192931156167115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36116883158795287437444743 54175324738192931156167115)
        ·
          refine ⟨81262987107289396734250673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54175324738192931156167115 81262987107289396734250673)
          ·
            refine ⟨60947240330467047550688005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81262987107289396734250673 60947240330467047550688005)
            ·
              refine ⟨11427607561962571415754001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60947240330467047550688005 11427607561962571415754001)
              ·
                refine ⟨8570705671471928561815501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11427607561962571415754001 8570705671471928561815501)
                ·
                  refine ⟨3214014626801973210680813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8570705671471928561815501 3214014626801973210680813)
                  ·
                    refine ⟨1205255485050739954005305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214014626801973210680813 1205255485050739954005305)
                    ·
                      rfl

theorem cell22_3520840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_3520840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520840 prefixEnd_3520840 := by exact prefixLift 3520840
  have htrace : WordTrace (prefixWord ++ tailWord_3520840) baseStart_3520840 baseEnd_3520840 := by
    simpa [prefixWord, tailWord_3520840, baseEnd_3520840] using wordTrace_append hprefix tailTrace_3520840
  have hstable : (prefixWord ++ tailWord_3520840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520840).length < 2 ^ (prefixWord ++ tailWord_3520840).sum := by decide
  have hdescent : baseEnd_3520840 < baseStart_3520840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520874 : List Nat := [3, 1, 3, 3, 1, 3, 1, 1, 3, 3]
def baseStart_3520874 : Nat := 118140960795 + 3520874 * 2 ^ 59
def prefixEnd_3520874 : Nat := 4983230072969 + 3 ^ 40 * 3520874 * 2
def baseEnd_3520874 : Nat := 1205267123945575198655201

theorem tailTrace_3520874 : CollatzResearch.WordTrace tailWord_3520874 prefixEnd_3520874 1205267123945575198655201 := by
  unfold tailWord_3520874
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104206161620572562746419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85611216430988193500657117 32104206161620572562746419)
  ·
    refine ⟨48156309242430858844119629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32104206161620572562746419 48156309242430858844119629)
    ·
      refine ⟨18058615965911572066544861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48156309242430858844119629 18058615965911572066544861)
      ·
        refine ⟨6771980987216839524954323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18058615965911572066544861 6771980987216839524954323)
        ·
          refine ⟨10157971480825259287431485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771980987216839524954323 10157971480825259287431485)
          ·
            refine ⟨3809239305309472232786807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10157971480825259287431485 3809239305309472232786807)
            ·
              refine ⟨5713858957964208349180211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3809239305309472232786807 5713858957964208349180211)
              ·
                refine ⟨8570788436946312523770317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5713858957964208349180211 8570788436946312523770317)
                ·
                  refine ⟨3214045663854867196413869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8570788436946312523770317 3214045663854867196413869)
                  ·
                    refine ⟨1205267123945575198655201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214045663854867196413869 1205267123945575198655201)
                    ·
                      rfl

theorem cell22_3520874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_3520874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520874 prefixEnd_3520874 := by exact prefixLift 3520874
  have htrace : WordTrace (prefixWord ++ tailWord_3520874) baseStart_3520874 baseEnd_3520874 := by
    simpa [prefixWord, tailWord_3520874, baseEnd_3520874] using wordTrace_append hprefix tailTrace_3520874
  have hstable : (prefixWord ++ tailWord_3520874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520874).length < 2 ^ (prefixWord ++ tailWord_3520874).sum := by decide
  have hdescent : baseEnd_3520874 < baseStart_3520874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520883 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 5, 4]
def baseStart_3520883 : Nat := 118140960795 + 3520883 * 2 ^ 59
def prefixEnd_3520883 : Nat := 4983230072969 + 3 ^ 40 * 3520883 * 2
def baseEnd_3520883 : Nat := 1205270204829502175180173

theorem tailTrace_3520883 : CollatzResearch.WordTrace tailWord_3520883 prefixEnd_3520883 1205270204829502175180173 := by
  unfold tailWord_3520883
  simp only [CollatzResearch.WordTrace]
  refine ⟨128417152903449684788063303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85611435268966456525375535 128417152903449684788063303)
  ·
    refine ⟨192625729355174527182094955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128417152903449684788063303 192625729355174527182094955)
    ·
      refine ⟨288938594032761790773142433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192625729355174527182094955 288938594032761790773142433)
      ·
        refine ⟨216703945524571343079856825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288938594032761790773142433 216703945524571343079856825)
        ·
          refine ⟨162527959143428507309892619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216703945524571343079856825 162527959143428507309892619)
          ·
            refine ⟨243791938715142760964838929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162527959143428507309892619 243791938715142760964838929)
            ·
              refine ⟨182843954036357070723629197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243791938715142760964838929 182843954036357070723629197)
              ·
                refine ⟨68566482763633901521360949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182843954036357070723629197 68566482763633901521360949)
                ·
                  refine ⟨6428107759090678267627589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68566482763633901521360949 6428107759090678267627589)
                  ·
                    refine ⟨1205270204829502175180173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6428107759090678267627589 1205270204829502175180173)
                    ·
                      rfl

theorem cell22_3520883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_3520883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520883 prefixEnd_3520883 := by exact prefixLift 3520883
  have htrace : WordTrace (prefixWord ++ tailWord_3520883) baseStart_3520883 baseEnd_3520883 := by
    simpa [prefixWord, tailWord_3520883, baseEnd_3520883] using wordTrace_append hprefix tailTrace_3520883
  have hstable : (prefixWord ++ tailWord_3520883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520883).length < 2 ^ (prefixWord ++ tailWord_3520883).sum := by decide
  have hdescent : baseEnd_3520883 < baseStart_3520883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520900 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3520900 : Nat := 118140960795 + 3520900 * 2 ^ 59
def prefixEnd_3520900 : Nat := 4983230072969 + 3 ^ 40 * 3520900 * 2
def baseEnd_3520900 : Nat := 1205276024276919797505121

theorem tailTrace_3520900 : CollatzResearch.WordTrace tailWord_3520900 prefixEnd_3520900 1205276024276919797505121 := by
  unfold tailWord_3520900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64208886472194048345716077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85611848629592064460954769 64208886472194048345716077)
  ·
    refine ⟨24078332427072768129643529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64208886472194048345716077 24078332427072768129643529)
    ·
      refine ⟨18058749320304576097232647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24078332427072768129643529 18058749320304576097232647)
      ·
        refine ⟨27088123980456864145848971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18058749320304576097232647 27088123980456864145848971)
        ·
          refine ⟨40632185970685296218773457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27088123980456864145848971 40632185970685296218773457)
          ·
            refine ⟨30474139478013972164080093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40632185970685296218773457 30474139478013972164080093)
            ·
              refine ⟨11427802304255239561530035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30474139478013972164080093 11427802304255239561530035)
              ·
                refine ⟨17141703456382859342295053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11427802304255239561530035 17141703456382859342295053)
                ·
                  refine ⟨6428138796143572253360645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17141703456382859342295053 6428138796143572253360645)
                  ·
                    refine ⟨1205276024276919797505121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6428138796143572253360645 1205276024276919797505121)
                    ·
                      rfl

theorem cell22_3520900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3520900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520900 prefixEnd_3520900 := by exact prefixLift 3520900
  have htrace : WordTrace (prefixWord ++ tailWord_3520900) baseStart_3520900 baseEnd_3520900 := by
    simpa [prefixWord, tailWord_3520900, baseEnd_3520900] using wordTrace_append hprefix tailTrace_3520900
  have hstable : (prefixWord ++ tailWord_3520900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520900).length < 2 ^ (prefixWord ++ tailWord_3520900).sum := by decide
  have hdescent : baseEnd_3520900 < baseStart_3520900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520930 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3520930 : Nat := 118140960795 + 3520930 * 2 ^ 59
def prefixEnd_3520930 : Nat := 4983230072969 + 3 ^ 40 * 3520930 * 2
def baseEnd_3520930 : Nat := 1205286293890009719255029

theorem tailTrace_3520930 : CollatzResearch.WordTrace tailWord_3520930 prefixEnd_3520930 1205286293890009719255029 := by
  unfold tailWord_3520930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32104716783569852953756061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85612578089519607876682829 32104716783569852953756061)
  ·
    refine ⟨12039268793838694857658523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32104716783569852953756061 12039268793838694857658523)
    ·
      refine ⟨18058903190758042286487785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039268793838694857658523 18058903190758042286487785)
      ·
        refine ⟨13544177393068531714865839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18058903190758042286487785 13544177393068531714865839)
        ·
          refine ⟨20316266089602797572298759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13544177393068531714865839 20316266089602797572298759)
          ·
            refine ⟨30474399134404196358448139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20316266089602797572298759 30474399134404196358448139)
            ·
              refine ⟨45711598701606294537672209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30474399134404196358448139 45711598701606294537672209)
              ·
                refine ⟨34283699026204720903254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45711598701606294537672209 34283699026204720903254157)
                ·
                  refine ⟨12856387134826770338720309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34283699026204720903254157 12856387134826770338720309)
                  ·
                    refine ⟨1205286293890009719255029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12856387134826770338720309 1205286293890009719255029)
                    ·
                      rfl

theorem cell22_3520930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3520930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520930 prefixEnd_3520930 := by exact prefixLift 3520930
  have htrace : WordTrace (prefixWord ++ tailWord_3520930) baseStart_3520930 baseEnd_3520930 := by
    simpa [prefixWord, tailWord_3520930, baseEnd_3520930] using wordTrace_append hprefix tailTrace_3520930
  have hstable : (prefixWord ++ tailWord_3520930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520930).length < 2 ^ (prefixWord ++ tailWord_3520930).sum := by decide
  have hdescent : baseEnd_3520930 < baseStart_3520930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520975 : List Nat := [1, 1, 2, 1, 1, 4, 1, 1, 7, 3]
def baseStart_3520975 : Nat := 118140960795 + 3520975 * 2 ^ 59
def prefixEnd_3520975 : Nat := 4983230072969 + 3 ^ 40 * 3520975 * 2
def baseEnd_3520975 : Nat := 1205301698309644601879891

theorem tailTrace_3520975 : CollatzResearch.WordTrace tailWord_3520975 prefixEnd_3520975 1205301698309644601879891 := by
  unfold tailWord_3520975
  simp only [CollatzResearch.WordTrace]
  refine ⟨128420508419116384500412379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85613672279410923000274919 128420508419116384500412379)
  ·
    refine ⟨192630762628674576750618569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128420508419116384500412379 192630762628674576750618569)
    ·
      refine ⟨144473071971505932562963927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192630762628674576750618569 144473071971505932562963927)
      ·
        refine ⟨216709607957258898844445891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144473071971505932562963927 216709607957258898844445891)
        ·
          refine ⟨325064411935888348266668837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216709607957258898844445891 325064411935888348266668837)
          ·
            refine ⟨60949577237979065300000407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 325064411935888348266668837 60949577237979065300000407)
            ·
              refine ⟨91424365856968597950000611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60949577237979065300000407 91424365856968597950000611)
              ·
                refine ⟨137136548785452896925000917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91424365856968597950000611 137136548785452896925000917)
                ·
                  refine ⟨3214137862159052271679709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 137136548785452896925000917 3214137862159052271679709)
                  ·
                    refine ⟨1205301698309644601879891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214137862159052271679709 1205301698309644601879891)
                    ·
                      rfl

theorem cell22_3520975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_3520975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520975 prefixEnd_3520975 := by exact prefixLift 3520975
  have htrace : WordTrace (prefixWord ++ tailWord_3520975) baseStart_3520975 baseEnd_3520975 := by
    simpa [prefixWord, tailWord_3520975, baseEnd_3520975] using wordTrace_append hprefix tailTrace_3520975
  have hstable : (prefixWord ++ tailWord_3520975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520975).length < 2 ^ (prefixWord ++ tailWord_3520975).sum := by decide
  have hdescent : baseEnd_3520975 < baseStart_3520975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3520992 : List Nat := [2, 1, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_3520992 : Nat := 118140960795 + 3520992 * 2 ^ 59
def prefixEnd_3520992 : Nat := 4983230072969 + 3 ^ 40 * 3520992 * 2
def baseEnd_3520992 : Nat := 1205307517757062224204839

theorem tailTrace_3520992 : CollatzResearch.WordTrace tailWord_3520992 prefixEnd_3520992 1205307517757062224204839 := by
  unfold tailWord_3520992
  simp only [CollatzResearch.WordTrace]
  refine ⟨64210564230027398201890615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85614085640036530935854153 64210564230027398201890615)
  ·
    refine ⟨96315846345041097302835923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64210564230027398201890615 96315846345041097302835923)
    ·
      refine ⟨144473769517561645954253885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96315846345041097302835923 144473769517561645954253885)
      ·
        refine ⟨54177663569085617232845207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144473769517561645954253885 54177663569085617232845207)
        ·
          refine ⟨81266495353628425849267811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54177663569085617232845207 81266495353628425849267811)
          ·
            refine ⟨121899743030442638773901717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81266495353628425849267811 121899743030442638773901717)
            ·
              refine ⟨5714050454551998692526643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121899743030442638773901717 5714050454551998692526643)
              ·
                refine ⟨8571075681827998038789965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714050454551998692526643 8571075681827998038789965)
                ·
                  refine ⟨3214153380685499264546237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8571075681827998038789965 3214153380685499264546237)
                  ·
                    refine ⟨1205307517757062224204839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214153380685499264546237 1205307517757062224204839)
                    ·
                      rfl

theorem cell22_3520992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_3520992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3520992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3520992 prefixEnd_3520992 := by exact prefixLift 3520992
  have htrace : WordTrace (prefixWord ++ tailWord_3520992) baseStart_3520992 baseEnd_3520992 := by
    simpa [prefixWord, tailWord_3520992, baseEnd_3520992] using wordTrace_append hprefix tailTrace_3520992
  have hstable : (prefixWord ++ tailWord_3520992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3520992).length < 2 ^ (prefixWord ++ tailWord_3520992).sum := by decide
  have hdescent : baseEnd_3520992 < baseStart_3520992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3520992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521056 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_3521056 : Nat := 118140960795 + 3521056 * 2 ^ 59
def prefixEnd_3521056 : Nat := 4983230072969 + 3 ^ 40 * 3521056 * 2
def baseEnd_3521056 : Nat := 401776475421662463534881

theorem tailTrace_3521056 : CollatzResearch.WordTrace tailWord_3521056 prefixEnd_3521056 401776475421662463534881 := by
  unfold tailWord_3521056
  simp only [CollatzResearch.WordTrace]
  refine ⟨64211731365911467667055511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85615641821215290222740681 64211731365911467667055511)
  ·
    refine ⟨96317597048867201500583267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64211731365911467667055511 96317597048867201500583267)
    ·
      refine ⟨144476395573300802250874901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96317597048867201500583267 144476395573300802250874901)
      ·
        refine ⟨6772331042498475105509761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 144476395573300802250874901 6772331042498475105509761)
        ·
          refine ⟨5079248281873856329132321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6772331042498475105509761 5079248281873856329132321)
          ·
            refine ⟨3809436211405392246849241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5079248281873856329132321 3809436211405392246849241)
            ·
              refine ⟨2857077158554044185136931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809436211405392246849241 2857077158554044185136931)
              ·
                refine ⟨4285615737831066277705397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857077158554044185136931 4285615737831066277705397)
                ·
                  refine ⟨401776475421662463534881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4285615737831066277705397 401776475421662463534881)
                  ·
                    rfl

theorem cell22_3521056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_3521056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521056 prefixEnd_3521056 := by exact prefixLift 3521056
  have htrace : WordTrace (prefixWord ++ tailWord_3521056) baseStart_3521056 baseEnd_3521056 := by
    simpa [prefixWord, tailWord_3521056, baseEnd_3521056] using wordTrace_append hprefix tailTrace_3521056
  have hstable : (prefixWord ++ tailWord_3521056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521056).length < 2 ^ (prefixWord ++ tailWord_3521056).sum := by decide
  have hdescent : baseEnd_3521056 < baseStart_3521056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521082 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3521082 : Nat := 118140960795 + 3521082 * 2 ^ 59
def prefixEnd_3521082 : Nat := 4983230072969 + 3 ^ 40 * 3521082 * 2
def baseEnd_3521082 : Nat := 1205338326596331989454563

theorem tailTrace_3521082 : CollatzResearch.WordTrace tailWord_3521082 prefixEnd_3521082 1205338326596331989454563 := by
  unfold tailWord_3521082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32106102757432185443639375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85616274019819161183038333 32106102757432185443639375)
  ·
    refine ⟨48159154136148278165459063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32106102757432185443639375 48159154136148278165459063)
    ·
      refine ⟨72238731204222417248188595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48159154136148278165459063 72238731204222417248188595)
      ·
        refine ⟨108358096806333625872282893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72238731204222417248188595 108358096806333625872282893)
        ·
          refine ⟨40634286302375109702106085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108358096806333625872282893 40634286302375109702106085)
          ·
            refine ⟨7618928681695333069144891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40634286302375109702106085 7618928681695333069144891)
            ·
              refine ⟨11428393022542999603717337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618928681695333069144891 11428393022542999603717337)
              ·
                refine ⟨8571294766907249702788003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428393022542999603717337 8571294766907249702788003)
                ·
                  refine ⟨12856942150360874554182005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8571294766907249702788003 12856942150360874554182005)
                  ·
                    refine ⟨1205338326596331989454563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12856942150360874554182005 1205338326596331989454563)
                    ·
                      rfl

theorem cell22_3521082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3521082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521082 prefixEnd_3521082 := by exact prefixLift 3521082
  have htrace : WordTrace (prefixWord ++ tailWord_3521082) baseStart_3521082 baseEnd_3521082 := by
    simpa [prefixWord, tailWord_3521082, baseEnd_3521082] using wordTrace_append hprefix tailTrace_3521082
  have hstable : (prefixWord ++ tailWord_3521082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521082).length < 2 ^ (prefixWord ++ tailWord_3521082).sum := by decide
  have hdescent : baseEnd_3521082 < baseStart_3521082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521095 : List Nat := [1, 1, 4, 1, 4, 11]
def baseStart_3521095 : Nat := 118140960795 + 3521095 * 2 ^ 59
def prefixEnd_3521095 : Nat := 4983230072969 + 3 ^ 40 * 3521095 * 2
def baseEnd_3521095 : Nat := 14880775021753139368883

theorem tailTrace_3521095 : CollatzResearch.WordTrace tailWord_3521095 prefixEnd_3521095 14880775021753139368883 := by
  unfold tailWord_3521095
  simp only [CollatzResearch.WordTrace]
  refine ⟨128424885178681644994780739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85616590119121096663187159 128424885178681644994780739)
  ·
    refine ⟨192637327768022467492171109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128424885178681644994780739 192637327768022467492171109)
    ·
      refine ⟨36119498956504212654782083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 192637327768022467492171109 36119498956504212654782083)
      ·
        refine ⟨54179248434756318982173125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36119498956504212654782083 54179248434756318982173125)
        ·
          refine ⟨10158609081516809809157461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54179248434756318982173125 10158609081516809809157461)
          ·
            refine ⟨14880775021753139368883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10158609081516809809157461 14880775021753139368883)
            ·
              rfl

theorem cell22_3521095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 11].length) (baseStart_3521095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521095 prefixEnd_3521095 := by exact prefixLift 3521095
  have htrace : WordTrace (prefixWord ++ tailWord_3521095) baseStart_3521095 baseEnd_3521095 := by
    simpa [prefixWord, tailWord_3521095, baseEnd_3521095] using wordTrace_append hprefix tailTrace_3521095
  have hstable : (prefixWord ++ tailWord_3521095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521095).length < 2 ^ (prefixWord ++ tailWord_3521095).sum := by decide
  have hdescent : baseEnd_3521095 < baseStart_3521095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521101 : List Nat := [1, 6, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3521101 : Nat := 118140960795 + 3521101 * 2 ^ 59
def prefixEnd_3521101 : Nat := 4983230072969 + 3 ^ 40 * 3521101 * 2
def baseEnd_3521101 : Nat := 401781610228207424409835

theorem tailTrace_3521101 : CollatzResearch.WordTrace tailWord_3521101 prefixEnd_3521101 401781610228207424409835 := by
  unfold tailWord_3521101
  simp only [CollatzResearch.WordTrace]
  refine ⟨128425104016659908019499157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85616736011106605346332771 128425104016659908019499157)
  ·
    refine ⟨6019926750780933188414023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128425104016659908019499157 6019926750780933188414023)
    ·
      refine ⟨9029890126171399782621035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019926750780933188414023 9029890126171399782621035)
      ·
        refine ⟨13544835189257099673931553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9029890126171399782621035 13544835189257099673931553)
        ·
          refine ⟨10158626391942824755448665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13544835189257099673931553 10158626391942824755448665)
          ·
            refine ⟨7618969793957118566586499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10158626391942824755448665 7618969793957118566586499)
            ·
              refine ⟨11428454690935677849879749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7618969793957118566586499 11428454690935677849879749)
              ·
                refine ⟨2142835254550439596852453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11428454690935677849879749 2142835254550439596852453)
                ·
                  refine ⟨401781610228207424409835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142835254550439596852453 401781610228207424409835)
                  ·
                    rfl

theorem cell22_3521101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3521101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521101 prefixEnd_3521101 := by exact prefixLift 3521101
  have htrace : WordTrace (prefixWord ++ tailWord_3521101) baseStart_3521101 baseEnd_3521101 := by
    simpa [prefixWord, tailWord_3521101, baseEnd_3521101] using wordTrace_append hprefix tailTrace_3521101
  have hstable : (prefixWord ++ tailWord_3521101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521101).length < 2 ^ (prefixWord ++ tailWord_3521101).sum := by decide
  have hdescent : baseEnd_3521101 < baseStart_3521101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521118 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3521118 : Nat := 118140960795 + 3521118 * 2 ^ 59
def prefixEnd_3521118 : Nat := 4983230072969 + 3 ^ 40 * 3521118 * 2
def baseEnd_3521118 : Nat := 401783550044013298518151

theorem tailTrace_3521118 : CollatzResearch.WordTrace tailWord_3521118 prefixEnd_3521118 401783550044013298518151 := by
  unfold tailWord_3521118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053215507199789990358501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85617149371732213281912005 16053215507199789990358501)
  ·
    refine ⟨3009977907599960623192219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16053215507199789990358501 3009977907599960623192219)
    ·
      refine ⟨4514966861399940934788329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009977907599960623192219 4514966861399940934788329)
      ·
        refine ⟨3386225146049955701091247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514966861399940934788329 3386225146049955701091247)
        ·
          refine ⟨5079337719074933551636871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386225146049955701091247 5079337719074933551636871)
          ·
            refine ⟨7619006578612400327455307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079337719074933551636871 7619006578612400327455307)
            ·
              refine ⟨11428509867918600491182961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619006578612400327455307 11428509867918600491182961)
              ·
                refine ⟨8571382400938950368387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11428509867918600491182961 8571382400938950368387221)
                ·
                  refine ⟨401783550044013298518151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8571382400938950368387221 401783550044013298518151)
                  ·
                    rfl

theorem cell22_3521118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3521118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521118 prefixEnd_3521118 := by exact prefixLift 3521118
  have htrace : WordTrace (prefixWord ++ tailWord_3521118) baseStart_3521118 baseEnd_3521118 := by
    simpa [prefixWord, tailWord_3521118, baseEnd_3521118] using wordTrace_append hprefix tailTrace_3521118
  have hstable : (prefixWord ++ tailWord_3521118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521118).length < 2 ^ (prefixWord ++ tailWord_3521118).sum := by decide
  have hdescent : baseEnd_3521118 < baseStart_3521118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521157 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 7]
def baseStart_3521157 : Nat := 118140960795 + 3521157 * 2 ^ 59
def prefixEnd_3521157 : Nat := 4983230072969 + 3 ^ 40 * 3521157 * 2
def baseEnd_3521157 : Nat := 401788000209685597943111

theorem tailTrace_3521157 : CollatzResearch.WordTrace tailWord_3521157 prefixEnd_3521157 401788000209685597943111 := by
  unfold tailWord_3521157
  simp only [CollatzResearch.WordTrace]
  refine ⟨128427146504457029583537725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85618097669638019722358483 128427146504457029583537725)
  ·
    refine ⟨48160179939171386093826647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128427146504457029583537725 48160179939171386093826647)
    ·
      refine ⟨72240269908757079140739971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48160179939171386093826647 72240269908757079140739971)
      ·
        refine ⟨108360404863135618711109957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72240269908757079140739971 108360404863135618711109957)
        ·
          refine ⟨20317575911837928508333117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108360404863135618711109957 20317575911837928508333117)
          ·
            refine ⟨7619090966939223190624919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20317575911837928508333117 7619090966939223190624919)
            ·
              refine ⟨11428636450408834785937379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619090966939223190624919 11428636450408834785937379)
              ·
                refine ⟨17142954675613252178906069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11428636450408834785937379 17142954675613252178906069)
                ·
                  refine ⟨401788000209685597943111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17142954675613252178906069 401788000209685597943111)
                  ·
                    rfl

theorem cell22_3521157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_3521157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521157 prefixEnd_3521157 := by exact prefixLift 3521157
  have htrace : WordTrace (prefixWord ++ tailWord_3521157) baseStart_3521157 baseEnd_3521157 := by
    simpa [prefixWord, tailWord_3521157, baseEnd_3521157] using wordTrace_append hprefix tailTrace_3521157
  have hstable : (prefixWord ++ tailWord_3521157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521157).length < 2 ^ (prefixWord ++ tailWord_3521157).sum := by decide
  have hdescent : baseEnd_3521157 < baseStart_3521157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521247 : List Nat := [1, 1, 2, 3, 2, 3, 2, 8]
def baseStart_3521247 : Nat := 118140960795 + 3521247 * 2 ^ 59
def prefixEnd_3521247 : Nat := 4983230072969 + 3 ^ 40 * 3521247 * 2
def baseEnd_3521247 : Nat := 133932756607591839897673

theorem tailTrace_3521247 : CollatzResearch.WordTrace tailWord_3521247 prefixEnd_3521247 133932756607591839897673 := by
  unfold tailWord_3521247
  simp only [CollatzResearch.WordTrace]
  refine ⟨128430429074130974954313995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85620286049420649969542663 128430429074130974954313995)
  ·
    refine ⟨192645643611196462431470993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128430429074130974954313995 192645643611196462431470993)
    ·
      refine ⟨144484232708397346823603245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192645643611196462431470993 144484232708397346823603245)
      ·
        refine ⟨54181587265649005058851217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144484232708397346823603245 54181587265649005058851217)
        ·
          refine ⟨40636190449236753794138413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54181587265649005058851217 40636190449236753794138413)
          ·
            refine ⟨15238571418463782672801905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40636190449236753794138413 15238571418463782672801905)
            ·
              refine ⟨11428928563847837004601429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15238571418463782672801905 11428928563847837004601429)
              ·
                refine ⟨133932756607591839897673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11428928563847837004601429 133932756607591839897673)
                ·
                  rfl

theorem cell22_3521247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 8].length) (baseStart_3521247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521247 prefixEnd_3521247 := by exact prefixLift 3521247
  have htrace : WordTrace (prefixWord ++ tailWord_3521247) baseStart_3521247 baseEnd_3521247 := by
    simpa [prefixWord, tailWord_3521247, baseEnd_3521247] using wordTrace_append hprefix tailTrace_3521247
  have hstable : (prefixWord ++ tailWord_3521247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521247).length < 2 ^ (prefixWord ++ tailWord_3521247).sum := by decide
  have hdescent : baseEnd_3521247 < baseStart_3521247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521249 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3521249 : Nat := 118140960795 + 3521249 * 2 ^ 59
def prefixEnd_3521249 : Nat := 4983230072969 + 3 ^ 40 * 3521249 * 2
def baseEnd_3521249 : Nat := 1205395494109199220529051

theorem tailTrace_3521249 : CollatzResearch.WordTrace tailWord_3521249 prefixEnd_3521249 1205395494109199220529051 := by
  unfold tailWord_3521249
  simp only [CollatzResearch.WordTrace]
  refine ⟨128430502020123729295886801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85620334680082486197257867 128430502020123729295886801)
  ·
    refine ⟨96322876515092796971915101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128430502020123729295886801 96322876515092796971915101)
    ·
      refine ⟨36121078693159798864468163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96322876515092796971915101 36121078693159798864468163)
      ·
        refine ⟨54181618039739698296702245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36121078693159798864468163 54181618039739698296702245)
        ·
          refine ⟨10159053382451193430631671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54181618039739698296702245 10159053382451193430631671)
          ·
            refine ⟨15238580073676790145947507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159053382451193430631671 15238580073676790145947507)
            ·
              refine ⟨22857870110515185218921261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15238580073676790145947507 22857870110515185218921261)
              ·
                refine ⟨8571701291443194457095473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22857870110515185218921261 8571701291443194457095473)
                ·
                  refine ⟨6428775968582395842821605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8571701291443194457095473 6428775968582395842821605)
                  ·
                    refine ⟨1205395494109199220529051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6428775968582395842821605 1205395494109199220529051)
                    ·
                      rfl

theorem cell22_3521249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3521249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521249 prefixEnd_3521249 := by exact prefixLift 3521249
  have htrace : WordTrace (prefixWord ++ tailWord_3521249) baseStart_3521249 baseEnd_3521249 := by
    simpa [prefixWord, tailWord_3521249, baseEnd_3521249] using wordTrace_append hprefix tailTrace_3521249
  have hstable : (prefixWord ++ tailWord_3521249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521249).length < 2 ^ (prefixWord ++ tailWord_3521249).sum := by decide
  have hdescent : baseEnd_3521249 < baseStart_3521249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521277 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_3521277 : Nat := 118140960795 + 3521277 * 2 ^ 59
def prefixEnd_3521277 : Nat := 4983230072969 + 3 ^ 40 * 3521277 * 2
def baseEnd_3521277 : Nat := 1205405079081416480828965

theorem tailTrace_3521277 : CollatzResearch.WordTrace tailWord_3521277 prefixEnd_3521277 1205405079081416480828965 := by
  unfold tailWord_3521277
  simp only [CollatzResearch.WordTrace]
  refine ⟨128431523264022290077906085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85621015509348193385270723 128431523264022290077906085)
  ·
    refine ⟨24080910612004179389607391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128431523264022290077906085 24080910612004179389607391)
    ·
      refine ⟨36121365918006269084411087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24080910612004179389607391 36121365918006269084411087)
      ·
        refine ⟨54182048877009403626616631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36121365918006269084411087 54182048877009403626616631)
        ·
          refine ⟨81273073315514105439924947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54182048877009403626616631 81273073315514105439924947)
          ·
            refine ⟨121909609973271158159887421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81273073315514105439924947 121909609973271158159887421)
            ·
              refine ⟨45716103739976684309957783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121909609973271158159887421 45716103739976684309957783)
              ·
                refine ⟨68574155609965026464936675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45716103739976684309957783 68574155609965026464936675)
                ·
                  refine ⟨102861233414947539697405013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68574155609965026464936675 102861233414947539697405013)
                  ·
                    refine ⟨1205405079081416480828965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102861233414947539697405013 1205405079081416480828965)
                    ·
                      rfl

theorem cell22_3521277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_3521277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521277 prefixEnd_3521277 := by exact prefixLift 3521277
  have htrace : WordTrace (prefixWord ++ tailWord_3521277) baseStart_3521277 baseEnd_3521277 := by
    simpa [prefixWord, tailWord_3521277, baseEnd_3521277] using wordTrace_append hprefix tailTrace_3521277
  have hstable : (prefixWord ++ tailWord_3521277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521277).length < 2 ^ (prefixWord ++ tailWord_3521277).sum := by decide
  have hdescent : baseEnd_3521277 < baseStart_3521277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521279 : List Nat := [1, 1, 2, 2, 1, 3, 1, 5, 3, 3]
def baseStart_3521279 : Nat := 118140960795 + 3521279 * 2 ^ 59
def prefixEnd_3521279 : Nat := 4983230072969 + 3 ^ 40 * 3521279 * 2
def baseEnd_3521279 : Nat := 1205405763722289142278959

theorem tailTrace_3521279 : CollatzResearch.WordTrace tailWord_3521279 prefixEnd_3521279 1205405763722289142278959 := by
  unfold tailWord_3521279
  simp only [CollatzResearch.WordTrace]
  refine ⟨128431596210015044419478891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85621064140010029612985927 128431596210015044419478891)
  ·
    refine ⟨192647394315022566629218337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128431596210015044419478891 192647394315022566629218337)
    ·
      refine ⟨144485545736266924971913753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192647394315022566629218337 144485545736266924971913753)
      ·
        refine ⟨108364159302200193728935315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144485545736266924971913753 108364159302200193728935315)
        ·
          refine ⟨162546238953300290593402973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108364159302200193728935315 162546238953300290593402973)
          ·
            refine ⟨60954839607487608972526115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162546238953300290593402973 60954839607487608972526115)
            ·
              refine ⟨91432259411231413458789173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60954839607487608972526115 91432259411231413458789173)
              ·
                refine ⟨8571774319802945011761485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91432259411231413458789173 8571774319802945011761485)
                ·
                  refine ⟨3214415369926104379410557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8571774319802945011761485 3214415369926104379410557)
                  ·
                    refine ⟨1205405763722289142278959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214415369926104379410557 1205405763722289142278959)
                    ·
                      rfl

theorem cell22_3521279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_3521279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521279 prefixEnd_3521279 := by exact prefixLift 3521279
  have htrace : WordTrace (prefixWord ++ tailWord_3521279) baseStart_3521279 baseEnd_3521279 := by
    simpa [prefixWord, tailWord_3521279, baseEnd_3521279] using wordTrace_append hprefix tailTrace_3521279
  have hstable : (prefixWord ++ tailWord_3521279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521279).length < 2 ^ (prefixWord ++ tailWord_3521279).sum := by decide
  have hdescent : baseEnd_3521279 < baseStart_3521279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521292 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_3521292 : Nat := 118140960795 + 3521292 * 2 ^ 59
def prefixEnd_3521292 : Nat := 4983230072969 + 3 ^ 40 * 3521292 * 2
def baseEnd_3521292 : Nat := 401803404629320480567973

theorem tailTrace_3521292 : CollatzResearch.WordTrace tailWord_3521292 prefixEnd_3521292 401803404629320480567973 := by
  unfold tailWord_3521292
  simp only [CollatzResearch.WordTrace]
  refine ⟨64216035179483973819851065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85621380239311965093134753 64216035179483973819851065)
  ·
    refine ⟨48162026384612980364888299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64216035179483973819851065 48162026384612980364888299)
    ·
      refine ⟨72243039576919470547332449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48162026384612980364888299 72243039576919470547332449)
      ·
        refine ⟨54182279682689602910499337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72243039576919470547332449 54182279682689602910499337)
        ·
          refine ⟨40636709762017202182874503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54182279682689602910499337 40636709762017202182874503)
          ·
            refine ⟨60955064643025803274311755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40636709762017202182874503 60955064643025803274311755)
            ·
              refine ⟨91432596964538704911467633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60955064643025803274311755 91432596964538704911467633)
              ·
                refine ⟨68574447723404028683600725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91432596964538704911467633 68574447723404028683600725)
                ·
                  refine ⟨401803404629320480567973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68574447723404028683600725 401803404629320480567973)
                  ·
                    rfl

theorem cell22_3521292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_3521292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521292 prefixEnd_3521292 := by exact prefixLift 3521292
  have htrace : WordTrace (prefixWord ++ tailWord_3521292) baseStart_3521292 baseEnd_3521292 := by
    simpa [prefixWord, tailWord_3521292, baseEnd_3521292] using wordTrace_append hprefix tailTrace_3521292
  have hstable : (prefixWord ++ tailWord_3521292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521292).length < 2 ^ (prefixWord ++ tailWord_3521292).sum := by decide
  have hdescent : baseEnd_3521292 < baseStart_3521292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521298 : List Nat := [3, 2, 4, 1, 2, 1, 3, 6]
def baseStart_3521298 : Nat := 118140960795 + 3521298 * 2 ^ 59
def prefixEnd_3521298 : Nat := 4983230072969 + 3 ^ 40 * 3521298 * 2
def baseEnd_3521298 : Nat := 133934696423397714005989

theorem tailTrace_3521298 : CollatzResearch.WordTrace tailWord_3521298 prefixEnd_3521298 133934696423397714005989 := by
  unfold tailWord_3521298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32108072299236552666105137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85621526131297473776280365 32108072299236552666105137)
  ·
    refine ⟨24081054224427414499578853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32108072299236552666105137 24081054224427414499578853)
    ·
      refine ⟨4515197667080140218671035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24081054224427414499578853 4515197667080140218671035)
      ·
        refine ⟨6772796500620210328006553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515197667080140218671035 6772796500620210328006553)
        ·
          refine ⟨5079597375465157746004915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6772796500620210328006553 5079597375465157746004915)
          ·
            refine ⟨7619396063197736619007373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079597375465157746004915 7619396063197736619007373)
            ·
              refine ⟨2857273523699151232127765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7619396063197736619007373 2857273523699151232127765)
              ·
                refine ⟨133934696423397714005989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2857273523699151232127765 133934696423397714005989)
                ·
                  rfl

theorem cell22_3521298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 6].length) (baseStart_3521298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521298 prefixEnd_3521298 := by exact prefixLift 3521298
  have htrace : WordTrace (prefixWord ++ tailWord_3521298) baseStart_3521298 baseEnd_3521298 := by
    simpa [prefixWord, tailWord_3521298, baseEnd_3521298] using wordTrace_append hprefix tailTrace_3521298
  have hstable : (prefixWord ++ tailWord_3521298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521298).length < 2 ^ (prefixWord ++ tailWord_3521298).sum := by decide
  have hdescent : baseEnd_3521298 < baseStart_3521298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521307 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 6, 5]
def baseStart_3521307 : Nat := 118140960795 + 3521307 * 2 ^ 59
def prefixEnd_3521307 : Nat := 4983230072969 + 3 ^ 40 * 3521307 * 2
def baseEnd_3521307 : Nat := 1205415348694506402578873

theorem tailTrace_3521307 : CollatzResearch.WordTrace tailWord_3521307 prefixEnd_3521307 1205415348694506402578873 := by
  unfold tailWord_3521307
  simp only [CollatzResearch.WordTrace]
  refine ⟨128432617453913605201498175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85621744969275736800998783 128432617453913605201498175)
  ·
    refine ⟨192648926180870407802247263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128432617453913605201498175 192648926180870407802247263)
    ·
      refine ⟨288973389271305611703370895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192648926180870407802247263 288973389271305611703370895)
      ·
        refine ⟨433460083906958417555056343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288973389271305611703370895 433460083906958417555056343)
        ·
          refine ⟨650190125860437626332584515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433460083906958417555056343 650190125860437626332584515)
          ·
            refine ⟨975285188790656439498876773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650190125860437626332584515 975285188790656439498876773)
            ·
              refine ⟨182865972898248082406039395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 975285188790656439498876773 182865972898248082406039395)
              ·
                refine ⟨274298959347372123609059093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182865972898248082406039395 274298959347372123609059093)
                ·
                  refine ⟨12857763719408068294174645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 274298959347372123609059093 12857763719408068294174645)
                  ·
                    refine ⟨1205415348694506402578873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12857763719408068294174645 1205415348694506402578873)
                    ·
                      rfl

theorem cell22_3521307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_3521307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521307 prefixEnd_3521307 := by exact prefixLift 3521307
  have htrace : WordTrace (prefixWord ++ tailWord_3521307) baseStart_3521307 baseEnd_3521307 := by
    simpa [prefixWord, tailWord_3521307, baseEnd_3521307] using wordTrace_append hprefix tailTrace_3521307
  have hstable : (prefixWord ++ tailWord_3521307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521307).length < 2 ^ (prefixWord ++ tailWord_3521307).sum := by decide
  have hdescent : baseEnd_3521307 < baseStart_3521307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521313 : List Nat := [1, 2, 3, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3521313 : Nat := 118140960795 + 3521313 * 2 ^ 59
def prefixEnd_3521313 : Nat := 4983230072969 + 3 ^ 40 * 3521313 * 2
def baseEnd_3521313 : Nat := 1205417402617124386928855

theorem tailTrace_3521313 : CollatzResearch.WordTrace tailWord_3521313 prefixEnd_3521313 1205417402617124386928855 := by
  unfold tailWord_3521313
  simp only [CollatzResearch.WordTrace]
  refine ⟨128432836291891868226216593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85621890861261245484144395 128432836291891868226216593)
  ·
    refine ⟨96324627218918901169662445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128432836291891868226216593 96324627218918901169662445)
    ·
      refine ⟨36121735207094587938623417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96324627218918901169662445 36121735207094587938623417)
      ·
        refine ⟨27091301405320940953967563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36121735207094587938623417 27091301405320940953967563)
        ·
          refine ⟨40636952107981411430951345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27091301405320940953967563 40636952107981411430951345)
          ·
            refine ⟨30477714080986058573213509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40636952107981411430951345 30477714080986058573213509)
            ·
              refine ⟨5714571390184885982477533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30477714080986058573213509 5714571390184885982477533)
              ·
                refine ⟨2142964271319332243429075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5714571390184885982477533 2142964271319332243429075)
                ·
                  refine ⟨3214446406978998365143613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2142964271319332243429075 3214446406978998365143613)
                  ·
                    refine ⟨1205417402617124386928855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214446406978998365143613 1205417402617124386928855)
                    ·
                      rfl

theorem cell22_3521313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3521313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521313 prefixEnd_3521313 := by exact prefixLift 3521313
  have htrace : WordTrace (prefixWord ++ tailWord_3521313) baseStart_3521313 baseEnd_3521313 := by
    simpa [prefixWord, tailWord_3521313, baseEnd_3521313] using wordTrace_append hprefix tailTrace_3521313
  have hstable : (prefixWord ++ tailWord_3521313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521313).length < 2 ^ (prefixWord ++ tailWord_3521313).sum := by decide
  have hdescent : baseEnd_3521313 < baseStart_3521313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521326 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3521326 : Nat := 118140960795 + 3521326 * 2 ^ 59
def prefixEnd_3521326 : Nat := 4983230072969 + 3 ^ 40 * 3521326 * 2
def baseEnd_3521326 : Nat := 401807284260932228784605

theorem tailTrace_3521326 : CollatzResearch.WordTrace tailWord_3521326 prefixEnd_3521326 401807284260932228784605 := by
  unfold tailWord_3521326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054163805105596430804979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85622206960563180964293221 16054163805105596430804979)
  ·
    refine ⟨24081245707658394646207469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054163805105596430804979 24081245707658394646207469)
    ·
      refine ⟨9030467140371897992327801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24081245707658394646207469 9030467140371897992327801)
      ·
        refine ⟨6772850355278923494245851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9030467140371897992327801 6772850355278923494245851)
        ·
          refine ⟨10159275532918385241368777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772850355278923494245851 10159275532918385241368777)
          ·
            refine ⟨7619456649688788931026583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10159275532918385241368777 7619456649688788931026583)
            ·
              refine ⟨11429184974533183396539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7619456649688788931026583 11429184974533183396539875)
              ·
                refine ⟨17143777461799775094809813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11429184974533183396539875 17143777461799775094809813)
                ·
                  refine ⟨401807284260932228784605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17143777461799775094809813 401807284260932228784605)
                  ·
                    rfl

theorem cell22_3521326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3521326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521326 prefixEnd_3521326 := by exact prefixLift 3521326
  have htrace : WordTrace (prefixWord ++ tailWord_3521326) baseStart_3521326 baseEnd_3521326 := by
    simpa [prefixWord, tailWord_3521326, baseEnd_3521326] using wordTrace_append hprefix tailTrace_3521326
  have hstable : (prefixWord ++ tailWord_3521326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521326).length < 2 ^ (prefixWord ++ tailWord_3521326).sum := by decide
  have hdescent : baseEnd_3521326 < baseStart_3521326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521356 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_3521356 : Nat := 118140960795 + 3521356 * 2 ^ 59
def prefixEnd_3521356 : Nat := 4983230072969 + 3 ^ 40 * 3521356 * 2
def baseEnd_3521356 : Nat := 1205432122395886608103723

theorem tailTrace_3521356 : CollatzResearch.WordTrace tailWord_3521356 prefixEnd_3521356 1205432122395886608103723 := by
  unfold tailWord_3521356
  simp only [CollatzResearch.WordTrace]
  refine ⟨64217202315368043285015961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85622936420490724380021281 64217202315368043285015961)
  ·
    refine ⟨48162901736526032463761971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64217202315368043285015961 48162901736526032463761971)
    ·
      refine ⟨72244352604789048695642957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48162901736526032463761971 72244352604789048695642957)
      ·
        refine ⟨27091632226795893260866109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72244352604789048695642957 27091632226795893260866109)
        ·
          refine ⟨10159362085048459972824791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27091632226795893260866109 10159362085048459972824791)
          ·
            refine ⟨15239043127572689959237187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159362085048459972824791 15239043127572689959237187)
            ·
              refine ⟨22858564691359034938855781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15239043127572689959237187 22858564691359034938855781)
              ·
                refine ⟨4285980879629819051035459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22858564691359034938855781 4285980879629819051035459)
                ·
                  refine ⟨6428971319444728576553189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4285980879629819051035459 6428971319444728576553189)
                  ·
                    refine ⟨1205432122395886608103723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6428971319444728576553189 1205432122395886608103723)
                    ·
                      rfl

theorem cell22_3521356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_3521356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521356 prefixEnd_3521356 := by exact prefixLift 3521356
  have htrace : WordTrace (prefixWord ++ tailWord_3521356) baseStart_3521356 baseEnd_3521356 := by
    simpa [prefixWord, tailWord_3521356, baseEnd_3521356] using wordTrace_append hprefix tailTrace_3521356
  have hstable : (prefixWord ++ tailWord_3521356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521356).length < 2 ^ (prefixWord ++ tailWord_3521356).sum := by decide
  have hdescent : baseEnd_3521356 < baseStart_3521356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521388 : List Nat := [2, 2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_3521388 : Nat := 118140960795 + 3521388 * 2 ^ 59
def prefixEnd_3521388 : Nat := 4983230072969 + 3 ^ 40 * 3521388 * 2
def baseEnd_3521388 : Nat := 401814358883283063767875

theorem tailTrace_3521388 : CollatzResearch.WordTrace tailWord_3521388 prefixEnd_3521388 401814358883283063767875 := by
  unfold tailWord_3521388
  simp only [CollatzResearch.WordTrace]
  refine ⟨64217785883310078017598409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85623714511080104023464545 64217785883310078017598409)
  ·
    refine ⟨48163339412482558513198807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64217785883310078017598409 48163339412482558513198807)
    ·
      refine ⟨72245009118723837769798211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48163339412482558513198807 72245009118723837769798211)
      ·
        refine ⟨108367513678085756654697317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72245009118723837769798211 108367513678085756654697317)
        ·
          refine ⟨20318908814641079372755747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108367513678085756654697317 20318908814641079372755747)
          ·
            refine ⟨30478363221961619059133621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20318908814641079372755747 30478363221961619059133621)
            ·
              refine ⟨2857346552058901786793777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30478363221961619059133621 2857346552058901786793777)
              ·
                refine ⟨2143009914044176340095333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857346552058901786793777 2143009914044176340095333)
                ·
                  refine ⟨401814358883283063767875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143009914044176340095333 401814358883283063767875)
                  ·
                    rfl

theorem cell22_3521388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_3521388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521388 prefixEnd_3521388 := by exact prefixLift 3521388
  have htrace : WordTrace (prefixWord ++ tailWord_3521388) baseStart_3521388 baseEnd_3521388 := by
    simpa [prefixWord, tailWord_3521388, baseEnd_3521388] using wordTrace_append hprefix tailTrace_3521388
  have hstable : (prefixWord ++ tailWord_3521388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521388).length < 2 ^ (prefixWord ++ tailWord_3521388).sum := by decide
  have hdescent : baseEnd_3521388 < baseStart_3521388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521403 : List Nat := [1, 1, 1, 1, 1, 5, 6, 1, 2, 3]
def baseStart_3521403 : Nat := 118140960795 + 3521403 * 2 ^ 59
def prefixEnd_3521403 : Nat := 4983230072969 + 3 ^ 40 * 3521403 * 2
def baseEnd_3521403 : Nat := 1205448211456394152178579

theorem tailTrace_3521403 : CollatzResearch.WordTrace tailWord_3521403 prefixEnd_3521403 1205448211456394152178579 := by
  unfold tailWord_3521403
  simp only [CollatzResearch.WordTrace]
  refine ⟨128436118861565813596992863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85624079241043875731328575 128436118861565813596992863)
  ·
    refine ⟨192654178292348720395489295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128436118861565813596992863 192654178292348720395489295)
    ·
      refine ⟨288981267438523080593233943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192654178292348720395489295 288981267438523080593233943)
      ·
        refine ⟨433471901157784620889850915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288981267438523080593233943 433471901157784620889850915)
        ·
          refine ⟨650207851736676931334776373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433471901157784620889850915 650207851736676931334776373)
          ·
            refine ⟨60956986100313462312635285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 650207851736676931334776373 60956986100313462312635285)
            ·
              refine ⟨2857358723452193545904779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60956986100313462312635285 2857358723452193545904779)
              ·
                refine ⟨4286038085178290318857169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857358723452193545904779 4286038085178290318857169)
                ·
                  refine ⟨3214528563883717739142877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286038085178290318857169 3214528563883717739142877)
                  ·
                    refine ⟨1205448211456394152178579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214528563883717739142877 1205448211456394152178579)
                    ·
                      rfl

theorem cell22_3521403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 1, 2, 3].length) (baseStart_3521403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521403 prefixEnd_3521403 := by exact prefixLift 3521403
  have htrace : WordTrace (prefixWord ++ tailWord_3521403) baseStart_3521403 baseEnd_3521403 := by
    simpa [prefixWord, tailWord_3521403, baseEnd_3521403] using wordTrace_append hprefix tailTrace_3521403
  have hstable : (prefixWord ++ tailWord_3521403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521403).length < 2 ^ (prefixWord ++ tailWord_3521403).sum := by decide
  have hdescent : baseEnd_3521403 < baseStart_3521403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521418 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 2, 4]
def baseStart_3521418 : Nat := 118140960795 + 3521418 * 2 ^ 59
def prefixEnd_3521418 : Nat := 4983230072969 + 3 ^ 40 * 3521418 * 2
def baseEnd_3521418 : Nat := 1205453346262939113053533

theorem tailTrace_3521418 : CollatzResearch.WordTrace tailWord_3521418 prefixEnd_3521418 1205453346262939113053533 := by
  unfold tailWord_3521418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109166489127867789697227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85624443971007647439192605 32109166489127867789697227)
  ·
    refine ⟨48163749733691801684545841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109166489127867789697227 48163749733691801684545841)
    ·
      refine ⟨36122812300268851263409381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48163749733691801684545841 36122812300268851263409381)
      ·
        refine ⟨6773027306300409611889259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36122812300268851263409381 6773027306300409611889259)
        ·
          refine ⟨10159540959450614417833889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773027306300409611889259 10159540959450614417833889)
          ·
            refine ⟨7619655719587960813375417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10159540959450614417833889 7619655719587960813375417)
            ·
              refine ⟨5714741789690970610031563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7619655719587960813375417 5714741789690970610031563)
              ·
                refine ⟨8572112684536455915047345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714741789690970610031563 8572112684536455915047345)
                ·
                  refine ⟨6429084513402341936285509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8572112684536455915047345 6429084513402341936285509)
                  ·
                    refine ⟨1205453346262939113053533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429084513402341936285509 1205453346262939113053533)
                    ·
                      rfl

theorem cell22_3521418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_3521418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521418 prefixEnd_3521418 := by exact prefixLift 3521418
  have htrace : WordTrace (prefixWord ++ tailWord_3521418) baseStart_3521418 baseEnd_3521418 := by
    simpa [prefixWord, tailWord_3521418, baseEnd_3521418] using wordTrace_append hprefix tailTrace_3521418
  have hstable : (prefixWord ++ tailWord_3521418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521418).length < 2 ^ (prefixWord ++ tailWord_3521418).sum := by decide
  have hdescent : baseEnd_3521418 < baseStart_3521418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521461 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 5]
def baseStart_3521461 : Nat := 118140960795 + 3521461 * 2 ^ 59
def prefixEnd_3521461 : Nat := 4983230072969 + 3 ^ 40 * 3521461 * 2
def baseEnd_3521461 : Nat := 401822688680567111409467

theorem tailTrace_3521461 : CollatzResearch.WordTrace tailWord_3521461 prefixEnd_3521461 401822688680567111409467 := by
  unfold tailWord_3521461
  simp only [CollatzResearch.WordTrace]
  refine ⟨128438234295355689502604237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85625489530237126335069491 128438234295355689502604237)
  ·
    refine ⟨48164337860758383563476589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128438234295355689502604237 48164337860758383563476589)
    ·
      refine ⟨18061626697784393836303721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48164337860758383563476589 18061626697784393836303721)
      ·
        refine ⟨13546220023338295377227791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18061626697784393836303721 13546220023338295377227791)
        ·
          refine ⟨20319330035007443065841687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546220023338295377227791 20319330035007443065841687)
          ·
            refine ⟨30478995052511164598762531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20319330035007443065841687 30478995052511164598762531)
            ·
              refine ⟨45718492578766746898143797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30478995052511164598762531 45718492578766746898143797)
              ·
                refine ⟨4286108679259382521700981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45718492578766746898143797 4286108679259382521700981)
                ·
                  refine ⟨401822688680567111409467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4286108679259382521700981 401822688680567111409467)
                  ·
                    rfl

theorem cell22_3521461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 5].length) (baseStart_3521461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521461 prefixEnd_3521461 := by exact prefixLift 3521461
  have htrace : WordTrace (prefixWord ++ tailWord_3521461) baseStart_3521461 baseEnd_3521461 := by
    simpa [prefixWord, tailWord_3521461, baseEnd_3521461] using wordTrace_append hprefix tailTrace_3521461
  have hstable : (prefixWord ++ tailWord_3521461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521461).length < 2 ^ (prefixWord ++ tailWord_3521461).sum := by decide
  have hdescent : baseEnd_3521461 < baseStart_3521461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521489 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 8]
def baseStart_3521489 : Nat := 118140960795 + 3521489 * 2 ^ 59
def prefixEnd_3521489 : Nat := 4983230072969 + 3 ^ 40 * 3521489 * 2
def baseEnd_3521489 : Nat := 401825883671306198176105

theorem tailTrace_3521489 : CollatzResearch.WordTrace tailWord_3521489 prefixEnd_3521489 401825883671306198176105 := by
  unfold tailWord_3521489
  simp only [CollatzResearch.WordTrace]
  refine ⟨128439255539254250284623521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85626170359502833523082347 128439255539254250284623521)
  ·
    refine ⟨96329441654440687713467641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128439255539254250284623521 96329441654440687713467641)
    ·
      refine ⟨72247081240830515785100731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96329441654440687713467641 72247081240830515785100731)
      ·
        refine ⟨108370621861245773677651097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72247081240830515785100731 108370621861245773677651097)
        ·
          refine ⟨81277966395934330258238323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108370621861245773677651097 81277966395934330258238323)
          ·
            refine ⟨121916949593901495387357485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81277966395934330258238323 121916949593901495387357485)
            ·
              refine ⟨45718856097713060770259057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121916949593901495387357485 45718856097713060770259057)
              ·
                refine ⟨34289142073284795577694293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45718856097713060770259057 34289142073284795577694293)
                ·
                  refine ⟨401825883671306198176105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34289142073284795577694293 401825883671306198176105)
                  ·
                    rfl

theorem cell22_3521489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 8].length) (baseStart_3521489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521489 prefixEnd_3521489 := by exact prefixLift 3521489
  have htrace : WordTrace (prefixWord ++ tailWord_3521489) baseStart_3521489 baseEnd_3521489 := by
    simpa [prefixWord, tailWord_3521489, baseEnd_3521489] using wordTrace_append hprefix tailTrace_3521489
  have hstable : (prefixWord ++ tailWord_3521489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521489).length < 2 ^ (prefixWord ++ tailWord_3521489).sum := by decide
  have hdescent : baseEnd_3521489 < baseStart_3521489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521504 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_3521504 : Nat := 118140960795 + 3521504 * 2 ^ 59
def prefixEnd_3521504 : Nat := 4983230072969 + 3 ^ 40 * 3521504 * 2
def baseEnd_3521504 : Nat := 1205482785820463555403269

theorem tailTrace_3521504 : CollatzResearch.WordTrace tailWord_3521504 prefixEnd_3521504 1205482785820463555403269 := by
  unfold tailWord_3521504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64219901317099953923209783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85626535089466605230946377 64219901317099953923209783)
  ·
    refine ⟨96329851975649930884814675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64219901317099953923209783 96329851975649930884814675)
    ·
      refine ⟨144494777963474896327222013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96329851975649930884814675 144494777963474896327222013)
      ·
        refine ⟨54185541736303086122708255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144494777963474896327222013 54185541736303086122708255)
        ·
          refine ⟨81278312604454629184062383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54185541736303086122708255 81278312604454629184062383)
          ·
            refine ⟨121917468906681943776093575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81278312604454629184062383 121917468906681943776093575)
            ·
              refine ⟨182876203360022915664140363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121917468906681943776093575 182876203360022915664140363)
              ·
                refine ⟨274314305040034373496210545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182876203360022915664140363 274314305040034373496210545)
                ·
                  refine ⟨205735728780025780122157909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 274314305040034373496210545 205735728780025780122157909)
                  ·
                    refine ⟨1205482785820463555403269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205735728780025780122157909 1205482785820463555403269)
                    ·
                      rfl

theorem cell22_3521504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_3521504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521504 prefixEnd_3521504 := by exact prefixLift 3521504
  have htrace : WordTrace (prefixWord ++ tailWord_3521504) baseStart_3521504 baseEnd_3521504 := by
    simpa [prefixWord, tailWord_3521504, baseEnd_3521504] using wordTrace_append hprefix tailTrace_3521504
  have hstable : (prefixWord ++ tailWord_3521504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521504).length < 2 ^ (prefixWord ++ tailWord_3521504).sum := by decide
  have hdescent : baseEnd_3521504 < baseStart_3521504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521572 : List Nat := [2, 3, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3521572 : Nat := 118140960795 + 3521572 * 2 ^ 59
def prefixEnd_3521572 : Nat := 4983230072969 + 3 ^ 40 * 3521572 * 2
def baseEnd_3521572 : Nat := 1205506063610134044703061

theorem tailTrace_3521572 : CollatzResearch.WordTrace tailWord_3521572 prefixEnd_3521572 1205506063610134044703061 := by
  unfold tailWord_3521572
  simp only [CollatzResearch.WordTrace]
  refine ⟨64221141398976777729947485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85628188531969036973263313 64221141398976777729947485)
  ·
    refine ⟨24082928024616291648730307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64221141398976777729947485 24082928024616291648730307)
    ·
      refine ⟨36124392036924437473095461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24082928024616291648730307 36124392036924437473095461)
      ·
        refine ⟨6773323506923332026205399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36124392036924437473095461 6773323506923332026205399)
        ·
          refine ⟨10159985260384998039308099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773323506923332026205399 10159985260384998039308099)
          ·
            refine ⟨15239977890577497058962149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159985260384998039308099 15239977890577497058962149)
            ·
              refine ⟨2857495854483280698555403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15239977890577497058962149 2857495854483280698555403)
              ·
                refine ⟨4286243781724921047833105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857495854483280698555403 4286243781724921047833105)
                ·
                  refine ⟨3214682836293690785874829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286243781724921047833105 3214682836293690785874829)
                  ·
                    refine ⟨1205506063610134044703061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214682836293690785874829 1205506063610134044703061)
                    ·
                      rfl

theorem cell22_3521572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3521572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521572 prefixEnd_3521572 := by exact prefixLift 3521572
  have htrace : WordTrace (prefixWord ++ tailWord_3521572) baseStart_3521572 baseEnd_3521572 := by
    simpa [prefixWord, tailWord_3521572, baseEnd_3521572] using wordTrace_append hprefix tailTrace_3521572
  have hstable : (prefixWord ++ tailWord_3521572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521572).length < 2 ^ (prefixWord ++ tailWord_3521572).sum := by decide
  have hdescent : baseEnd_3521572 < baseStart_3521572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521600 : List Nat := [2, 1, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_3521600 : Nat := 118140960795 + 3521600 * 2 ^ 59
def prefixEnd_3521600 : Nat := 4983230072969 + 3 ^ 40 * 3521600 * 2
def baseEnd_3521600 : Nat := 1205515648582351305002975

theorem tailTrace_3521600 : CollatzResearch.WordTrace tailWord_3521600 prefixEnd_3521600 1205515648582351305002975 := by
  unfold tailWord_3521600
  simp only [CollatzResearch.WordTrace]
  refine ⟨64221652020926058120957127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85628869361234744161276169 64221652020926058120957127)
  ·
    refine ⟨96332478031389087181435691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64221652020926058120957127 96332478031389087181435691)
    ·
      refine ⟨144498717047083630772153537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96332478031389087181435691 144498717047083630772153537)
      ·
        refine ⟨108374037785312723079115153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144498717047083630772153537 108374037785312723079115153)
        ·
          refine ⟨81280528338984542309336365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108374037785312723079115153 81280528338984542309336365)
          ·
            refine ⟨30480198127119203366001137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81280528338984542309336365 30480198127119203366001137)
            ·
              refine ⟨22860148595339402524500853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30480198127119203366001137 22860148595339402524500853)
              ·
                refine ⟨2143138930813068986671955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22860148595339402524500853 2143138930813068986671955)
                ·
                  refine ⟨3214708396219603480007933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143138930813068986671955 3214708396219603480007933)
                  ·
                    refine ⟨1205515648582351305002975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214708396219603480007933 1205515648582351305002975)
                    ·
                      rfl

theorem cell22_3521600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_3521600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521600 prefixEnd_3521600 := by exact prefixLift 3521600
  have htrace : WordTrace (prefixWord ++ tailWord_3521600) baseStart_3521600 baseEnd_3521600 := by
    simpa [prefixWord, tailWord_3521600, baseEnd_3521600] using wordTrace_append hprefix tailTrace_3521600
  have hstable : (prefixWord ++ tailWord_3521600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521600).length < 2 ^ (prefixWord ++ tailWord_3521600).sum := by decide
  have hdescent : baseEnd_3521600 < baseStart_3521600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521617 : List Nat := [1, 2, 2, 1, 3, 1, 6, 2, 1, 3]
def baseStart_3521617 : Nat := 118140960795 + 3521617 * 2 ^ 59
def prefixEnd_3521617 : Nat := 4983230072969 + 3 ^ 40 * 3521617 * 2
def baseEnd_3521617 : Nat := 1205521468029768927327923

theorem tailTrace_3521617 : CollatzResearch.WordTrace tailWord_3521617 prefixEnd_3521617 1205521468029768927327923 := by
  unfold tailWord_3521617
  simp only [CollatzResearch.WordTrace]
  refine ⟨128443924082790528145283105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85629282721860352096855403 128443924082790528145283105)
  ·
    refine ⟨96332943062092896108962329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128443924082790528145283105 96332943062092896108962329)
    ·
      refine ⟨72249707296569672081721747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96332943062092896108962329 72249707296569672081721747)
      ·
        refine ⟨108374560944854508122582621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72249707296569672081721747 108374560944854508122582621)
        ·
          refine ⟨40640460354320440545968483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108374560944854508122582621 40640460354320440545968483)
          ·
            refine ⟨60960690531480660818952725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40640460354320440545968483 60960690531480660818952725)
            ·
              refine ⟨2857532368663155975888409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60960690531480660818952725 2857532368663155975888409)
              ·
                refine ⟨2143149276497366981916307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857532368663155975888409 2143149276497366981916307)
                ·
                  refine ⟨3214723914746050472874461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143149276497366981916307 3214723914746050472874461)
                  ·
                    refine ⟨1205521468029768927327923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214723914746050472874461 1205521468029768927327923)
                    ·
                      rfl

theorem cell22_3521617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_3521617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521617 prefixEnd_3521617 := by exact prefixLift 3521617
  have htrace : WordTrace (prefixWord ++ tailWord_3521617) baseStart_3521617 baseEnd_3521617 := by
    simpa [prefixWord, tailWord_3521617, baseEnd_3521617] using wordTrace_append hprefix tailTrace_3521617
  have hstable : (prefixWord ++ tailWord_3521617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521617).length < 2 ^ (prefixWord ++ tailWord_3521617).sum := by decide
  have hdescent : baseEnd_3521617 < baseStart_3521617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521628 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_3521628 : Nat := 118140960795 + 3521628 * 2 ^ 59
def prefixEnd_3521628 : Nat := 4983230072969 + 3 ^ 40 * 3521628 * 2
def baseEnd_3521628 : Nat := 1205525233554568565302889

theorem tailTrace_3521628 : CollatzResearch.WordTrace tailWord_3521628 prefixEnd_3521628 1205525233554568565302889 := by
  unfold tailWord_3521628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64222162642875338511966769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85629550190500451349289025 64222162642875338511966769)
  ·
    refine ⟨48166621982156503883975077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64222162642875338511966769 48166621982156503883975077)
    ·
      refine ⟨9031241621654344478245327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48166621982156503883975077 9031241621654344478245327)
      ·
        refine ⟨13546862432481516717367991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031241621654344478245327 13546862432481516717367991)
        ·
          refine ⟨20320293648722275076051987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13546862432481516717367991 20320293648722275076051987)
          ·
            refine ⟨30480440473083412614077981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20320293648722275076051987 30480440473083412614077981)
            ·
              refine ⟨11430165177406279730279243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30480440473083412614077981 11430165177406279730279243)
              ·
                refine ⟨17145247766109419595418865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11430165177406279730279243 17145247766109419595418865)
                ·
                  refine ⟨12858935824582064696564149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17145247766109419595418865 12858935824582064696564149)
                  ·
                    refine ⟨1205525233554568565302889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12858935824582064696564149 1205525233554568565302889)
                    ·
                      rfl

theorem cell22_3521628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_3521628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521628 prefixEnd_3521628 := by exact prefixLift 3521628
  have htrace : WordTrace (prefixWord ++ tailWord_3521628) baseStart_3521628 baseEnd_3521628 := by
    simpa [prefixWord, tailWord_3521628, baseEnd_3521628] using wordTrace_append hprefix tailTrace_3521628
  have hstable : (prefixWord ++ tailWord_3521628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521628).length < 2 ^ (prefixWord ++ tailWord_3521628).sum := by decide
  have hdescent : baseEnd_3521628 < baseStart_3521628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521641 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 8]
def baseStart_3521641 : Nat := 118140960795 + 3521641 * 2 ^ 59
def prefixEnd_3521641 : Nat := 4983230072969 + 3 ^ 40 * 3521641 * 2
def baseEnd_3521641 : Nat := 401843227906746954909283

theorem tailTrace_3521641 : CollatzResearch.WordTrace tailWord_3521641 prefixEnd_3521641 401843227906746954909283 := by
  unfold tailWord_3521641
  simp only [CollatzResearch.WordTrace]
  refine ⟨128444799434703580244156777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85629866289802386829437851 128444799434703580244156777)
  ·
    refine ⟨96333599576027685183117583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128444799434703580244156777 96333599576027685183117583)
    ·
      refine ⟨144500399364041527774676375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96333599576027685183117583 144500399364041527774676375)
      ·
        refine ⟨216750599046062291662014563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144500399364041527774676375 216750599046062291662014563)
        ·
          refine ⟨325125898569093437493021845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216750599046062291662014563 325125898569093437493021845)
          ·
            refine ⟨15240276495426254882485399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 325125898569093437493021845 15240276495426254882485399)
            ·
              refine ⟨22860414743139382323728099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240276495426254882485399 22860414743139382323728099)
              ·
                refine ⟨34290622114709073485592149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22860414743139382323728099 34290622114709073485592149)
                ·
                  refine ⟨401843227906746954909283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34290622114709073485592149 401843227906746954909283)
                  ·
                    rfl

theorem cell22_3521641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 8].length) (baseStart_3521641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521641 prefixEnd_3521641 := by exact prefixLift 3521641
  have htrace : WordTrace (prefixWord ++ tailWord_3521641) baseStart_3521641 baseEnd_3521641 := by
    simpa [prefixWord, tailWord_3521641, baseEnd_3521641] using wordTrace_append hprefix tailTrace_3521641
  have hstable : (prefixWord ++ tailWord_3521641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521641).length < 2 ^ (prefixWord ++ tailWord_3521641).sum := by decide
  have hdescent : baseEnd_3521641 < baseStart_3521641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521688 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_3521688 : Nat := 118140960795 + 3521688 * 2 ^ 59
def prefixEnd_3521688 : Nat := 4983230072969 + 3 ^ 40 * 3521688 * 2
def baseEnd_3521688 : Nat := 1205545772780748408802705

theorem tailTrace_3521688 : CollatzResearch.WordTrace tailWord_3521688 prefixEnd_3521688 1205545772780748408802705 := by
  unfold tailWord_3521688
  simp only [CollatzResearch.WordTrace]
  refine ⟨64223256832766653635558859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85631009110355538180745145 64223256832766653635558859)
  ·
    refine ⟨96334885249149980453338289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64223256832766653635558859 96334885249149980453338289)
    ·
      refine ⟨72251163936862485340003717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96334885249149980453338289 72251163936862485340003717)
      ·
        refine ⟨13547093238161716001250697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72251163936862485340003717 13547093238161716001250697)
        ·
          refine ⟨10160319928621287000938023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13547093238161716001250697 10160319928621287000938023)
          ·
            refine ⟨15240479892931930501407035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160319928621287000938023 15240479892931930501407035)
            ·
              refine ⟨22860719839397895752110553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15240479892931930501407035 22860719839397895752110553)
              ·
                refine ⟨17145539879548421814082915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22860719839397895752110553 17145539879548421814082915)
                ·
                  refine ⟨25718309819322632721124373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17145539879548421814082915 25718309819322632721124373)
                  ·
                    refine ⟨1205545772780748408802705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25718309819322632721124373 1205545772780748408802705)
                    ·
                      rfl

theorem cell22_3521688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_3521688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521688 prefixEnd_3521688 := by exact prefixLift 3521688
  have htrace : WordTrace (prefixWord ++ tailWord_3521688) baseStart_3521688 baseEnd_3521688 := by
    simpa [prefixWord, tailWord_3521688, baseEnd_3521688] using wordTrace_append hprefix tailTrace_3521688
  have hstable : (prefixWord ++ tailWord_3521688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521688).length < 2 ^ (prefixWord ++ tailWord_3521688).sum := by decide
  have hdescent : baseEnd_3521688 < baseStart_3521688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521690 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 1, 5]
def baseStart_3521690 : Nat := 118140960795 + 3521690 * 2 ^ 59
def prefixEnd_3521690 : Nat := 4983230072969 + 3 ^ 40 * 3521690 * 2
def baseEnd_3521690 : Nat := 1205546457421621070252699

theorem tailTrace_3521690 : CollatzResearch.WordTrace tailWord_3521690 prefixEnd_3521690 1205546457421621070252699 := by
  unfold tailWord_3521690
  simp only [CollatzResearch.WordTrace]
  refine ⟨32111646652881515403172631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85631057741017374408460349 32111646652881515403172631)
  ·
    refine ⟨48167469979322273104758947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32111646652881515403172631 48167469979322273104758947)
    ·
      refine ⟨72251204968983409657138421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48167469979322273104758947 72251204968983409657138421)
      ·
        refine ⟨6773550465842194655356727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72251204968983409657138421 6773550465842194655356727)
        ·
          refine ⟨10160325698763291983035091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773550465842194655356727 10160325698763291983035091)
          ·
            refine ⟨15240488548144937974552637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160325698763291983035091 15240488548144937974552637)
            ·
              refine ⟨5715183205554351740457239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15240488548144937974552637 5715183205554351740457239)
              ·
                refine ⟨8572774808331527610685859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715183205554351740457239 8572774808331527610685859)
                ·
                  refine ⟨12859162212497291416028789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8572774808331527610685859 12859162212497291416028789)
                  ·
                    refine ⟨1205546457421621070252699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12859162212497291416028789 1205546457421621070252699)
                    ·
                      rfl

theorem cell22_3521690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_3521690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521690 prefixEnd_3521690 := by exact prefixLift 3521690
  have htrace : WordTrace (prefixWord ++ tailWord_3521690) baseStart_3521690 baseEnd_3521690 := by
    simpa [prefixWord, tailWord_3521690, baseEnd_3521690] using wordTrace_append hprefix tailTrace_3521690
  have hstable : (prefixWord ++ tailWord_3521690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521690).length < 2 ^ (prefixWord ++ tailWord_3521690).sum := by decide
  have hdescent : baseEnd_3521690 < baseStart_3521690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521709 : List Nat := [1, 5, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3521709 : Nat := 118140960795 + 3521709 * 2 ^ 59
def prefixEnd_3521709 : Nat := 4983230072969 + 3 ^ 40 * 3521709 * 2
def baseEnd_3521709 : Nat := 401850987169970451342547

theorem tailTrace_3521709 : CollatzResearch.WordTrace tailWord_3521709 prefixEnd_3521709 401850987169970451342547 := by
  unfold tailWord_3521709
  simp only [CollatzResearch.WordTrace]
  refine ⟨128447279598457227857632181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85631519732304818571754787 128447279598457227857632181)
  ·
    refine ⟨12041932462355365111653017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128447279598457227857632181 12041932462355365111653017)
    ·
      refine ⟨9031449346766523833739763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12041932462355365111653017 9031449346766523833739763)
      ·
        refine ⟨13547174020149785750609645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031449346766523833739763 13547174020149785750609645)
        ·
          refine ⟨5080190257556169656478617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13547174020149785750609645 5080190257556169656478617)
          ·
            refine ⟨3810142693167127242358963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5080190257556169656478617 3810142693167127242358963)
            ·
              refine ⟨5715214039750690863538445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810142693167127242358963 5715214039750690863538445)
              ·
                refine ⟨2143205264906509073826917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5715214039750690863538445 2143205264906509073826917)
                ·
                  refine ⟨401850987169970451342547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143205264906509073826917 401850987169970451342547)
                  ·
                    rfl

theorem cell22_3521709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3521709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521709 prefixEnd_3521709 := by exact prefixLift 3521709
  have htrace : WordTrace (prefixWord ++ tailWord_3521709) baseStart_3521709 baseEnd_3521709 := by
    simpa [prefixWord, tailWord_3521709, baseEnd_3521709] using wordTrace_append hprefix tailTrace_3521709
  have hstable : (prefixWord ++ tailWord_3521709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521709).length < 2 ^ (prefixWord ++ tailWord_3521709).sum := by decide
  have hdescent : baseEnd_3521709 < baseStart_3521709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521741 : List Nat := [1, 6, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3521741 : Nat := 118140960795 + 3521741 * 2 ^ 59
def prefixEnd_3521741 : Nat := 4983230072969 + 3 ^ 40 * 3521741 * 2
def baseEnd_3521741 : Nat := 1205563915763873937227543

theorem tailTrace_3521741 : CollatzResearch.WordTrace tailWord_3521741 prefixEnd_3521741 1205563915763873937227543 := by
  unfold tailWord_3521741
  simp only [CollatzResearch.WordTrace]
  refine ⟨128448446734341297322797077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85632297822894198215198051 128448446734341297322797077)
  ·
    refine ⟨6021020940672248312006113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128448446734341297322797077 6021020940672248312006113)
    ·
      refine ⟨4515765705504186234004585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6021020940672248312006113 4515765705504186234004585)
      ·
        refine ⟨3386824279128139675503439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4515765705504186234004585 3386824279128139675503439)
        ·
          refine ⟨5080236418692209513255159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386824279128139675503439 5080236418692209513255159)
          ·
            refine ⟨7620354628038314269882739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080236418692209513255159 7620354628038314269882739)
            ·
              refine ⟨11430531942057471404824109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620354628038314269882739 11430531942057471404824109)
              ·
                refine ⟨4286449478271551776809041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11430531942057471404824109 4286449478271551776809041)
                ·
                  refine ⟨3214837108703663832606781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286449478271551776809041 3214837108703663832606781)
                  ·
                    refine ⟨1205563915763873937227543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214837108703663832606781 1205563915763873937227543)
                    ·
                      rfl

theorem cell22_3521741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3521741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521741 prefixEnd_3521741 := by exact prefixLift 3521741
  have htrace : WordTrace (prefixWord ++ tailWord_3521741) baseStart_3521741 baseEnd_3521741 := by
    simpa [prefixWord, tailWord_3521741, baseEnd_3521741] using wordTrace_append hprefix tailTrace_3521741
  have hstable : (prefixWord ++ tailWord_3521741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521741).length < 2 ^ (prefixWord ++ tailWord_3521741).sum := by decide
  have hdescent : baseEnd_3521741 < baseStart_3521741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521825 : List Nat := [1, 2, 3, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3521825 : Nat := 118140960795 + 3521825 * 2 ^ 59
def prefixEnd_3521825 : Nat := 4983230072969 + 3 ^ 40 * 3521825 * 2
def baseEnd_3521825 : Nat := 1205592670680525718127285

theorem tailTrace_3521825 : CollatzResearch.WordTrace tailWord_3521825 prefixEnd_3521825 1205592670680525718127285 := by
  unfold tailWord_3521825
  simp only [CollatzResearch.WordTrace]
  refine ⟨128451510466036979668854929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85634340310691319779236619 128451510466036979668854929)
  ·
    refine ⟨96338632849527734751641197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128451510466036979668854929 96338632849527734751641197)
    ·
      refine ⟨36126987318572900531865449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96338632849527734751641197 36126987318572900531865449)
      ·
        refine ⟨27095240488929675398899087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36126987318572900531865449 27095240488929675398899087)
        ·
          refine ⟨40642860733394513098348631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27095240488929675398899087 40642860733394513098348631)
          ·
            refine ⟨60964291100091769647522947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40642860733394513098348631 60964291100091769647522947)
            ·
              refine ⟨91446436650137654471284421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60964291100091769647522947 91446436650137654471284421)
              ·
                refine ⟨17146206871900810213365829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91446436650137654471284421 17146206871900810213365829)
                ·
                  refine ⟨3214913788481401915006093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17146206871900810213365829 3214913788481401915006093)
                  ·
                    refine ⟨1205592670680525718127285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214913788481401915006093 1205592670680525718127285)
                    ·
                      rfl

theorem cell22_3521825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3521825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521825 prefixEnd_3521825 := by exact prefixLift 3521825
  have htrace : WordTrace (prefixWord ++ tailWord_3521825) baseStart_3521825 baseEnd_3521825 := by
    simpa [prefixWord, tailWord_3521825, baseEnd_3521825] using wordTrace_append hprefix tailTrace_3521825
  have hstable : (prefixWord ++ tailWord_3521825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521825).length < 2 ^ (prefixWord ++ tailWord_3521825).sum := by decide
  have hdescent : baseEnd_3521825 < baseStart_3521825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521827 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 4]
def baseStart_3521827 : Nat := 118140960795 + 3521827 * 2 ^ 59
def prefixEnd_3521827 : Nat := 4983230072969 + 3 ^ 40 * 3521827 * 2
def baseEnd_3521827 : Nat := 401864451773799459859093

theorem tailTrace_3521827 : CollatzResearch.WordTrace tailWord_3521827 prefixEnd_3521827 401864451773799459859093 := by
  unfold tailWord_3521827
  simp only [CollatzResearch.WordTrace]
  refine ⟨128451583412029734010427735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85634388941353156006951823 128451583412029734010427735)
  ·
    refine ⟨192677375118044601015641603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128451583412029734010427735 192677375118044601015641603)
    ·
      refine ⟨289016062677066901523462405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192677375118044601015641603 289016062677066901523462405)
      ·
        refine ⟨54190511751950044035649201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289016062677066901523462405 54190511751950044035649201)
        ·
          refine ⟨40642883813962533026736901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54190511751950044035649201 40642883813962533026736901)
          ·
            refine ⟨7620540715117974942513169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40642883813962533026736901 7620540715117974942513169)
            ·
              refine ⟨5715405536338481206884877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7620540715117974942513169 5715405536338481206884877)
              ·
                refine ⟨2143277076126930452581829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5715405536338481206884877 2143277076126930452581829)
                ·
                  refine ⟨401864451773799459859093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143277076126930452581829 401864451773799459859093)
                  ·
                    rfl

theorem cell22_3521827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 4].length) (baseStart_3521827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521827 prefixEnd_3521827 := by exact prefixLift 3521827
  have htrace : WordTrace (prefixWord ++ tailWord_3521827) baseStart_3521827 baseEnd_3521827 := by
    simpa [prefixWord, tailWord_3521827, baseEnd_3521827] using wordTrace_append hprefix tailTrace_3521827
  have hstable : (prefixWord ++ tailWord_3521827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521827).length < 2 ^ (prefixWord ++ tailWord_3521827).sum := by decide
  have hdescent : baseEnd_3521827 < baseStart_3521827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521829 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 1, 4]
def baseStart_3521829 : Nat := 118140960795 + 3521829 * 2 ^ 59
def prefixEnd_3521829 : Nat := 4983230072969 + 3 ^ 40 * 3521829 * 2
def baseEnd_3521829 : Nat := 1205594039962271041027273

theorem tailTrace_3521829 : CollatzResearch.WordTrace tailWord_3521829 prefixEnd_3521829 1205594039962271041027273 := by
  unfold tailWord_3521829
  simp only [CollatzResearch.WordTrace]
  refine ⟨128451656358022488352000541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85634437572014992234667027 128451656358022488352000541)
  ·
    refine ⟨48169371134258433132000203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128451656358022488352000541 48169371134258433132000203)
    ·
      refine ⟨72254056701387649698000305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48169371134258433132000203 72254056701387649698000305)
      ·
        refine ⟨54190542526040737273500229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72254056701387649698000305 54190542526040737273500229)
        ·
          refine ⟨10160726723632638238781293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54190542526040737273500229 10160726723632638238781293)
          ·
            refine ⟨3810272521362239339542985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10160726723632638238781293 3810272521362239339542985)
            ·
              refine ⟨2857704391021679504657239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3810272521362239339542985 2857704391021679504657239)
              ·
                refine ⟨4286556586532519256985859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857704391021679504657239 4286556586532519256985859)
                ·
                  refine ⟨6429834879798778885478789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286556586532519256985859 6429834879798778885478789)
                  ·
                    refine ⟨1205594039962271041027273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6429834879798778885478789 1205594039962271041027273)
                    ·
                      rfl

theorem cell22_3521829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_3521829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521829 prefixEnd_3521829 := by exact prefixLift 3521829
  have htrace : WordTrace (prefixWord ++ tailWord_3521829) baseStart_3521829 baseEnd_3521829 := by
    simpa [prefixWord, tailWord_3521829, baseEnd_3521829] using wordTrace_append hprefix tailTrace_3521829
  have hstable : (prefixWord ++ tailWord_3521829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521829).length < 2 ^ (prefixWord ++ tailWord_3521829).sum := by decide
  have hdescent : baseEnd_3521829 < baseStart_3521829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521842 : List Nat := [3, 2, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3521842 : Nat := 118140960795 + 3521842 * 2 ^ 59
def prefixEnd_3521842 : Nat := 4983230072969 + 3 ^ 40 * 3521842 * 2
def baseEnd_3521842 : Nat := 1205598490127943340452233

theorem tailTrace_3521842 : CollatzResearch.WordTrace tailWord_3521842 prefixEnd_3521842 1205598490127943340452233 := by
  unfold tailWord_3521842
  simp only [CollatzResearch.WordTrace]
  refine ⟨32113032626743847893055945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85634753671316927714815853 32113032626743847893055945)
  ·
    refine ⟨24084774470057885919791959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32113032626743847893055945 24084774470057885919791959)
    ·
      refine ⟨36127161705086828879687939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24084774470057885919791959 36127161705086828879687939)
      ·
        refine ⟨54190742557630243319531909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36127161705086828879687939 54190742557630243319531909)
        ·
          refine ⟨10160764229555670622412233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54190742557630243319531909 10160764229555670622412233)
          ·
            refine ⟨7620573172166752966809175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10160764229555670622412233 7620573172166752966809175)
            ·
              refine ⟨11430859758250129450213763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7620573172166752966809175 11430859758250129450213763)
              ·
                refine ⟨17146289637375194175320645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11430859758250129450213763 17146289637375194175320645)
                ·
                  refine ⟨3214929307007848907872621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17146289637375194175320645 3214929307007848907872621)
                  ·
                    refine ⟨1205598490127943340452233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3214929307007848907872621 1205598490127943340452233)
                    ·
                      rfl

theorem cell22_3521842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3521842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521842 prefixEnd_3521842 := by exact prefixLift 3521842
  have htrace : WordTrace (prefixWord ++ tailWord_3521842) baseStart_3521842 baseEnd_3521842 := by
    simpa [prefixWord, tailWord_3521842, baseEnd_3521842] using wordTrace_append hprefix tailTrace_3521842
  have hstable : (prefixWord ++ tailWord_3521842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521842).length < 2 ^ (prefixWord ++ tailWord_3521842).sum := by decide
  have hdescent : baseEnd_3521842 < baseStart_3521842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521900 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_3521900 : Nat := 118140960795 + 3521900 * 2 ^ 59
def prefixEnd_3521900 : Nat := 4983230072969 + 3 ^ 40 * 3521900 * 2
def baseEnd_3521900 : Nat := 401872781571083507500685

theorem tailTrace_3521900 : CollatzResearch.WordTrace tailWord_3521900 prefixEnd_3521900 401872781571083507500685 := by
  unfold tailWord_3521900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64227122970382633738917577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85636163960510178318556769 64227122970382633738917577)
  ·
    refine ⟨48170342227786975304188183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64227122970382633738917577 48170342227786975304188183)
    ·
      refine ⟨72255513341680462956282275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48170342227786975304188183 72255513341680462956282275)
      ·
        refine ⟨108383270012520694434423413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72255513341680462956282275 108383270012520694434423413)
        ·
          refine ⟨10160931563673815103227195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108383270012520694434423413 10160931563673815103227195)
          ·
            refine ⟨15241397345510722654840793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160931563673815103227195 15241397345510722654840793)
            ·
              refine ⟨11431048009133041991130595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15241397345510722654840793 11431048009133041991130595)
              ·
                refine ⟨17146572013699562986695893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431048009133041991130595 17146572013699562986695893)
                ·
                  refine ⟨401872781571083507500685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17146572013699562986695893 401872781571083507500685)
                  ·
                    rfl

theorem cell22_3521900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_3521900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521900 prefixEnd_3521900 := by exact prefixLift 3521900
  have htrace : WordTrace (prefixWord ++ tailWord_3521900) baseStart_3521900 baseEnd_3521900 := by
    simpa [prefixWord, tailWord_3521900, baseEnd_3521900] using wordTrace_append hprefix tailTrace_3521900
  have hstable : (prefixWord ++ tailWord_3521900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521900).length < 2 ^ (prefixWord ++ tailWord_3521900).sum := by decide
  have hdescent : baseEnd_3521900 < baseStart_3521900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3521975 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_3521975 : Nat := 118140960795 + 3521975 * 2 ^ 59
def prefixEnd_3521975 : Nat := 4983230072969 + 3 ^ 40 * 3521975 * 2
def baseEnd_3521975 : Nat := 1205644018745975326876825

theorem tailTrace_3521975 : CollatzResearch.WordTrace tailWord_3521975 prefixEnd_3521975 1205644018745975326876825 := by
  unfold tailWord_3521975
  simp only [CollatzResearch.WordTrace]
  refine ⟨128456981415493555286815379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85637987610329036857876919 128456981415493555286815379)
  ·
    refine ⟨192685472123240332930223069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128456981415493555286815379 192685472123240332930223069)
    ·
      refine ⟨72257052046215124848833651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192685472123240332930223069 72257052046215124848833651)
      ·
        refine ⟨108385578069322687273250477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72257052046215124848833651 108385578069322687273250477)
        ·
          refine ⟨40644591775996007727468929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108385578069322687273250477 40644591775996007727468929)
          ·
            refine ⟨30483443831997005795601697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40644591775996007727468929 30483443831997005795601697)
            ·
              refine ⟨22862582873997754346701273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30483443831997005795601697 22862582873997754346701273)
              ·
                refine ⟨17146937155498315760025955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22862582873997754346701273 17146937155498315760025955)
                ·
                  refine ⟨25720405733247473640038933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17146937155498315760025955 25720405733247473640038933)
                  ·
                    refine ⟨1205644018745975326876825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25720405733247473640038933 1205644018745975326876825)
                    ·
                      rfl

theorem cell22_3521975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_3521975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3521975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3521975 prefixEnd_3521975 := by exact prefixLift 3521975
  have htrace : WordTrace (prefixWord ++ tailWord_3521975) baseStart_3521975 baseEnd_3521975 := by
    simpa [prefixWord, tailWord_3521975, baseEnd_3521975] using wordTrace_append hprefix tailTrace_3521975
  have hstable : (prefixWord ++ tailWord_3521975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3521975).length < 2 ^ (prefixWord ++ tailWord_3521975).sum := by decide
  have hdescent : baseEnd_3521975 < baseStart_3521975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3521975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522020 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3522020 : Nat := 118140960795 + 3522020 * 2 ^ 59
def prefixEnd_3522020 : Nat := 4983230072969 + 3 ^ 40 * 3522020 * 2
def baseEnd_3522020 : Nat := 1205659423165610209501687

theorem tailTrace_3522020 : CollatzResearch.WordTrace tailWord_3522020 prefixEnd_3522020 1205659423165610209501687 := by
  unfold tailWord_3522020
  simp only [CollatzResearch.WordTrace]
  refine ⟨64229311350165263986101757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85639081800220351981469009 64229311350165263986101757)
  ·
    refine ⟨24085991756311973994788159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64229311350165263986101757 24085991756311973994788159)
    ·
      refine ⟨36128987634467960992182239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24085991756311973994788159 36128987634467960992182239)
      ·
        refine ⟨54193481451701941488273359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36128987634467960992182239 54193481451701941488273359)
        ·
          refine ⟨81290222177552912232410039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54193481451701941488273359 81290222177552912232410039)
          ·
            refine ⟨121935333266329368348615059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81290222177552912232410039 121935333266329368348615059)
            ·
              refine ⟨182902999899494052522922589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121935333266329368348615059 182902999899494052522922589)
              ·
                refine ⟨68588624962310269696095971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182902999899494052522922589 68588624962310269696095971)
                ·
                  refine ⟨102882937443465404544143957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68588624962310269696095971 102882937443465404544143957)
                  ·
                    refine ⟨1205659423165610209501687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 102882937443465404544143957 1205659423165610209501687)
                    ·
                      rfl

theorem cell22_3522020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3522020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522020 prefixEnd_3522020 := by exact prefixLift 3522020
  have htrace : WordTrace (prefixWord ++ tailWord_3522020) baseStart_3522020 baseEnd_3522020 := by
    simpa [prefixWord, tailWord_3522020, baseEnd_3522020] using wordTrace_append hprefix tailTrace_3522020
  have hstable : (prefixWord ++ tailWord_3522020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522020).length < 2 ^ (prefixWord ++ tailWord_3522020).sum := by decide
  have hdescent : baseEnd_3522020 < baseStart_3522020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522056 : List Nat := [2, 1, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_3522056 : Nat := 118140960795 + 3522056 * 2 ^ 59
def prefixEnd_3522056 : Nat := 4983230072969 + 3 ^ 40 * 3522056 * 2
def baseEnd_3522056 : Nat := 1205671746701318115601577

theorem tailTrace_3522056 : CollatzResearch.WordTrace tailWord_3522056 prefixEnd_3522056 1205671746701318115601577 := by
  unfold tailWord_3522056
  simp only [CollatzResearch.WordTrace]
  refine ⟨64229967864100053060257011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85639957152133404080342681 64229967864100053060257011)
  ·
    refine ⟨96344951796150079590385517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64229967864100053060257011 96344951796150079590385517)
    ·
      refine ⟨36129356923556279846394569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96344951796150079590385517 36129356923556279846394569)
      ·
        refine ⟨27097017692667209884795927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36129356923556279846394569 27097017692667209884795927)
        ·
          refine ⟨40645526539000814827193891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27097017692667209884795927 40645526539000814827193891)
          ·
            refine ⟨60968289808501222240790837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40645526539000814827193891 60968289808501222240790837)
            ·
              refine ⟨5715777169546989585074141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60968289808501222240790837 5715777169546989585074141)
              ·
                refine ⟨2143416438580121094402803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5715777169546989585074141 2143416438580121094402803)
                ·
                  refine ⟨3215124657870181641604205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2143416438580121094402803 3215124657870181641604205)
                  ·
                    refine ⟨1205671746701318115601577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3215124657870181641604205 1205671746701318115601577)
                    ·
                      rfl

theorem cell22_3522056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_3522056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522056 prefixEnd_3522056 := by exact prefixLift 3522056
  have htrace : WordTrace (prefixWord ++ tailWord_3522056) baseStart_3522056 baseEnd_3522056 := by
    simpa [prefixWord, tailWord_3522056, baseEnd_3522056] using wordTrace_append hprefix tailTrace_3522056
  have hstable : (prefixWord ++ tailWord_3522056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522056).length < 2 ^ (prefixWord ++ tailWord_3522056).sum := by decide
  have hdescent : baseEnd_3522056 < baseStart_3522056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522099 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 1, 4]
def baseStart_3522099 : Nat := 118140960795 + 3522099 * 2 ^ 59
def prefixEnd_3522099 : Nat := 4983230072969 + 3 ^ 40 * 3522099 * 2
def baseEnd_3522099 : Nat := 1205686466480080336776445

theorem tailTrace_3522099 : CollatzResearch.WordTrace tailWord_3522099 prefixEnd_3522099 1205686466480080336776445 := by
  unfold tailWord_3522099
  simp only [CollatzResearch.WordTrace]
  refine ⟨128461504067044324464329351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85641002711362882976219567 128461504067044324464329351)
  ·
    refine ⟨192692256100566486696494027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128461504067044324464329351 192692256100566486696494027)
    ·
      refine ⟨289038384150849730044741041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192692256100566486696494027 289038384150849730044741041)
      ·
        refine ⟨216778788113137297533555781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289038384150849730044741041 216778788113137297533555781)
        ·
          refine ⟨40646022771213243287541709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 216778788113137297533555781 40646022771213243287541709)
          ·
            refine ⟨15242258539204966232828141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40646022771213243287541709 15242258539204966232828141)
            ·
              refine ⟨5715846952201862337310553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15242258539204966232828141 5715846952201862337310553)
              ·
                refine ⟨4286885214151396752982915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715846952201862337310553 4286885214151396752982915)
                ·
                  refine ⟨6430327821227095129474373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4286885214151396752982915 6430327821227095129474373)
                  ·
                    refine ⟨1205686466480080336776445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430327821227095129474373 1205686466480080336776445)
                    ·
                      rfl

theorem cell22_3522099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_3522099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522099 prefixEnd_3522099 := by exact prefixLift 3522099
  have htrace : WordTrace (prefixWord ++ tailWord_3522099) baseStart_3522099 baseEnd_3522099 := by
    simpa [prefixWord, tailWord_3522099, baseEnd_3522099] using wordTrace_append hprefix tailTrace_3522099
  have hstable : (prefixWord ++ tailWord_3522099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522099).length < 2 ^ (prefixWord ++ tailWord_3522099).sum := by decide
  have hdescent : baseEnd_3522099 < baseStart_3522099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522180 : List Nat := [2, 3, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3522180 : Nat := 118140960795 + 3522180 * 2 ^ 59
def prefixEnd_3522180 : Nat := 4983230072969 + 3 ^ 40 * 3522180 * 2
def baseEnd_3522180 : Nat := 1205714194435423125501197

theorem tailTrace_3522180 : CollatzResearch.WordTrace tailWord_3522180 prefixEnd_3522180 1205714194435423125501197 := by
  unfold tailWord_3522180
  simp only [CollatzResearch.WordTrace]
  refine ⟨64232229189875437649013997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85642972253167250198685329 64232229189875437649013997)
  ·
    refine ⟨24087085946203289118380249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64232229189875437649013997 24087085946203289118380249)
    ·
      refine ⟨18065314459652466838785187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24087085946203289118380249 18065314459652466838785187)
      ·
        refine ⟨27097971689478700258177781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18065314459652466838785187 27097971689478700258177781)
        ·
          refine ⟨2540434845888628149204167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27097971689478700258177781 2540434845888628149204167)
          ·
            refine ⟨3810652268832942223806251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540434845888628149204167 3810652268832942223806251)
            ·
              refine ⟨5715978403249413335709377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810652268832942223806251 5715978403249413335709377)
              ·
                refine ⟨4286983802437060001782033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5715978403249413335709377 4286983802437060001782033)
                ·
                  refine ⟨3215237851827795001336525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4286983802437060001782033 3215237851827795001336525)
                  ·
                    refine ⟨1205714194435423125501197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3215237851827795001336525 1205714194435423125501197)
                    ·
                      rfl

theorem cell22_3522180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3522180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522180 prefixEnd_3522180 := by exact prefixLift 3522180
  have htrace : WordTrace (prefixWord ++ tailWord_3522180) baseStart_3522180 baseEnd_3522180 := by
    simpa [prefixWord, tailWord_3522180, baseEnd_3522180] using wordTrace_append hprefix tailTrace_3522180
  have hstable : (prefixWord ++ tailWord_3522180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522180).length < 2 ^ (prefixWord ++ tailWord_3522180).sum := by decide
  have hdescent : baseEnd_3522180 < baseStart_3522180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522187 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 7]
def baseStart_3522187 : Nat := 118140960795 + 3522187 * 2 ^ 59
def prefixEnd_3522187 : Nat := 4983230072969 + 3 ^ 40 * 3522187 * 2
def baseEnd_3522187 : Nat := 401905530226159146858725

theorem tailTrace_3522187 : CollatzResearch.WordTrace tailWord_3522187 prefixEnd_3522187 401905530226159146858725 := by
  unfold tailWord_3522187
  simp only [CollatzResearch.WordTrace]
  refine ⟨128464713690725515493532815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85643142460483676995688543 128464713690725515493532815)
  ·
    refine ⟨192697070536088273240299223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128464713690725515493532815 192697070536088273240299223)
    ·
      refine ⟨289045605804132409860448835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192697070536088273240299223 289045605804132409860448835)
      ·
        refine ⟨433568408706198614790673253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289045605804132409860448835 433568408706198614790673253)
        ·
          refine ⟨81294076632412240273251235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 433568408706198614790673253 81294076632412240273251235)
          ·
            refine ⟨121941114948618360409876853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81294076632412240273251235 121941114948618360409876853)
            ·
              refine ⟨11431979526432971288425955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121941114948618360409876853 11431979526432971288425955)
              ·
                refine ⟨17147969289649456932638933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11431979526432971288425955 17147969289649456932638933)
                ·
                  refine ⟨401905530226159146858725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17147969289649456932638933 401905530226159146858725)
                  ·
                    rfl

theorem cell22_3522187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 7].length) (baseStart_3522187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522187 prefixEnd_3522187 := by exact prefixLift 3522187
  have htrace : WordTrace (prefixWord ++ tailWord_3522187) baseStart_3522187 baseEnd_3522187 := by
    simpa [prefixWord, tailWord_3522187, baseEnd_3522187] using wordTrace_append hprefix tailTrace_3522187
  have hstable : (prefixWord ++ tailWord_3522187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522187).length < 2 ^ (prefixWord ++ tailWord_3522187).sum := by decide
  have hdescent : baseEnd_3522187 < baseStart_3522187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522210 : List Nat := [3, 3, 1, 4, 2, 1, 2, 6]
def baseStart_3522210 : Nat := 118140960795 + 3522210 * 2 ^ 59
def prefixEnd_3522210 : Nat := 4983230072969 + 3 ^ 40 * 3522210 * 2
def baseEnd_3522210 : Nat := 133969384894279227472345

theorem tailTrace_3522210 : CollatzResearch.WordTrace tailWord_3522210 prefixEnd_3522210 133969384894279227472345 := by
  unfold tailWord_3522210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32116388142410547605405021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85643701713094793614413389 32116388142410547605405021)
  ·
    refine ⟨12043645553403955352026883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32116388142410547605405021 12043645553403955352026883)
    ·
      refine ⟨18065468330105933028040325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12043645553403955352026883 18065468330105933028040325)
      ·
        refine ⟨3387275311894862442757561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18065468330105933028040325 3387275311894862442757561)
        ·
          refine ⟨2540456483921146832068171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3387275311894862442757561 2540456483921146832068171)
          ·
            refine ⟨3810684725881720248102257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540456483921146832068171 3810684725881720248102257)
            ·
              refine ⟨2858013544411290186076693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3810684725881720248102257 2858013544411290186076693)
              ·
                refine ⟨133969384894279227472345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2858013544411290186076693 133969384894279227472345)
                ·
                  rfl

theorem cell22_3522210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_3522210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522210 prefixEnd_3522210 := by exact prefixLift 3522210
  have htrace : WordTrace (prefixWord ++ tailWord_3522210) baseStart_3522210 baseEnd_3522210 := by
    simpa [prefixWord, tailWord_3522210, baseEnd_3522210] using wordTrace_append hprefix tailTrace_3522210
  have hstable : (prefixWord ++ tailWord_3522210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522210).length < 2 ^ (prefixWord ++ tailWord_3522210).sum := by decide
  have hdescent : baseEnd_3522210 < baseStart_3522210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522232 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_3522232 : Nat := 118140960795 + 3522232 * 2 ^ 59
def prefixEnd_3522232 : Nat := 4983230072969 + 3 ^ 40 * 3522232 * 2
def baseEnd_3522232 : Nat := 401910665032704107733679

theorem tailTrace_3522232 : CollatzResearch.WordTrace tailWord_3522232 prefixEnd_3522232 401910665032704107733679 := by
  unfold tailWord_3522232
  simp only [CollatzResearch.WordTrace]
  refine ⟨64233177487781244089460475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85644236650374992119280633 64233177487781244089460475)
  ·
    refine ⟨96349766231671866134190713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64233177487781244089460475 96349766231671866134190713)
    ·
      refine ⟨72262324673753899600643035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96349766231671866134190713 72262324673753899600643035)
      ·
        refine ⟨108393487010630849400964553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72262324673753899600643035 108393487010630849400964553)
        ·
          refine ⟨81295115257973137050723415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108393487010630849400964553 81295115257973137050723415)
          ·
            refine ⟨121942672886959705576085123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81295115257973137050723415 121942672886959705576085123)
            ·
              refine ⟨182914009330439558364127685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121942672886959705576085123 182914009330439558364127685)
              ·
                refine ⟨34296376749457417193273941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182914009330439558364127685 34296376749457417193273941)
                ·
                  refine ⟨401910665032704107733679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34296376749457417193273941 401910665032704107733679)
                  ·
                    rfl

theorem cell22_3522232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_3522232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522232 prefixEnd_3522232 := by exact prefixLift 3522232
  have htrace : WordTrace (prefixWord ++ tailWord_3522232) baseStart_3522232 baseEnd_3522232 := by
    simpa [prefixWord, tailWord_3522232, baseEnd_3522232] using wordTrace_append hprefix tailTrace_3522232
  have hstable : (prefixWord ++ tailWord_3522232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522232).length < 2 ^ (prefixWord ++ tailWord_3522232).sum := by decide
  have hdescent : baseEnd_3522232 < baseStart_3522232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522264 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_3522264 : Nat := 118140960795 + 3522264 * 2 ^ 59
def prefixEnd_3522264 : Nat := 4983230072969 + 3 ^ 40 * 3522264 * 2
def baseEnd_3522264 : Nat := 1205742949352074906400939

theorem tailTrace_3522264 : CollatzResearch.WordTrace tailWord_3522264 prefixEnd_3522264 1205742949352074906400939 := by
  unfold tailWord_3522264
  simp only [CollatzResearch.WordTrace]
  refine ⟨64233761055723278822042923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85645014740964371762723897 64233761055723278822042923)
  ·
    refine ⟨96350641583584918233064385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64233761055723278822042923 96350641583584918233064385)
    ·
      refine ⟨72262981187688688674798289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96350641583584918233064385 72262981187688688674798289)
      ·
        refine ⟨54197235890766516506098717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72262981187688688674798289 54197235890766516506098717)
        ·
          refine ⟨20323963459037443689787019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54197235890766516506098717 20323963459037443689787019)
          ·
            refine ⟨30485945188556165534680529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20323963459037443689787019 30485945188556165534680529)
            ·
              refine ⟨22864458891417124151010397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30485945188556165534680529 22864458891417124151010397)
              ·
                refine ⟨8574172084281421556628899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22864458891417124151010397 8574172084281421556628899)
                ·
                  refine ⟨12861258126422132334943349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8574172084281421556628899 12861258126422132334943349)
                  ·
                    refine ⟨1205742949352074906400939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12861258126422132334943349 1205742949352074906400939)
                    ·
                      rfl

theorem cell22_3522264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_3522264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522264 prefixEnd_3522264 := by exact prefixLift 3522264
  have htrace : WordTrace (prefixWord ++ tailWord_3522264) baseStart_3522264 baseEnd_3522264 := by
    simpa [prefixWord, tailWord_3522264, baseEnd_3522264] using wordTrace_append hprefix tailTrace_3522264
  have hstable : (prefixWord ++ tailWord_3522264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522264).length < 2 ^ (prefixWord ++ tailWord_3522264).sum := by decide
  have hdescent : baseEnd_3522264 < baseStart_3522264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522268 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_3522268 : Nat := 118140960795 + 3522268 * 2 ^ 59
def prefixEnd_3522268 : Nat := 4983230072969 + 3 ^ 40 * 3522268 * 2
def baseEnd_3522268 : Nat := 1205744318633820229300927

theorem tailTrace_3522268 : CollatzResearch.WordTrace tailWord_3522268 prefixEnd_3522268 1205744318633820229300927 := by
  unfold tailWord_3522268
  simp only [CollatzResearch.WordTrace]
  refine ⟨64233834001716033163615729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85645112002288044218154305 64233834001716033163615729)
  ·
    refine ⟨48175375501287024872711797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64233834001716033163615729 48175375501287024872711797)
    ·
      refine ⟨4516441453245658581816731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48175375501287024872711797 4516441453245658581816731)
      ·
        refine ⟨6774662179868487872725097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516441453245658581816731 6774662179868487872725097)
        ·
          refine ⟨5080996634901365904543823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6774662179868487872725097 5080996634901365904543823)
          ·
            refine ⟨7621494952352048856815735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5080996634901365904543823 7621494952352048856815735)
            ·
              refine ⟨11432242428528073285223603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621494952352048856815735 11432242428528073285223603)
              ·
                refine ⟨17148363642792109927835405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11432242428528073285223603 17148363642792109927835405)
                ·
                  refine ⟨6430636366047041222938277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17148363642792109927835405 6430636366047041222938277)
                  ·
                    refine ⟨1205744318633820229300927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6430636366047041222938277 1205744318633820229300927)
                    ·
                      rfl

theorem cell22_3522268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_3522268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522268 prefixEnd_3522268 := by exact prefixLift 3522268
  have htrace : WordTrace (prefixWord ++ tailWord_3522268) baseStart_3522268 baseEnd_3522268 := by
    simpa [prefixWord, tailWord_3522268, baseEnd_3522268] using wordTrace_append hprefix tailTrace_3522268
  have hstable : (prefixWord ++ tailWord_3522268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522268).length < 2 ^ (prefixWord ++ tailWord_3522268).sum := by decide
  have hdescent : baseEnd_3522268 < baseStart_3522268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522294 : List Nat := [5, 1, 1, 1, 1, 13]
def baseStart_3522294 : Nat := 118140960795 + 3522294 * 2 ^ 59
def prefixEnd_3522294 : Nat := 4983230072969 + 3 ^ 40 * 3522294 * 2
def baseEnd_3522294 : Nat := 14885842209446479359887

theorem tailTrace_3522294 : CollatzResearch.WordTrace tailWord_3522294 prefixEnd_3522294 14885842209446479359887 := by
  unfold tailWord_3522294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029288518833617047979871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85645744200891915178451957 8029288518833617047979871)
  ·
    refine ⟨12043932778250425571969807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029288518833617047979871 12043932778250425571969807)
    ·
      refine ⟨18065899167375638357954711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12043932778250425571969807 18065899167375638357954711)
      ·
        refine ⟨27098848751063457536932067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18065899167375638357954711 27098848751063457536932067)
        ·
          refine ⟨40648273126595186305398101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27098848751063457536932067 40648273126595186305398101)
          ·
            refine ⟨14885842209446479359887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 40648273126595186305398101 14885842209446479359887)
            ·
              rfl

theorem cell22_3522294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 13].length) (baseStart_3522294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522294 prefixEnd_3522294 := by exact prefixLift 3522294
  have htrace : WordTrace (prefixWord ++ tailWord_3522294) baseStart_3522294 baseEnd_3522294 := by
    simpa [prefixWord, tailWord_3522294, baseEnd_3522294] using wordTrace_append hprefix tailTrace_3522294
  have hstable : (prefixWord ++ tailWord_3522294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522294).length < 2 ^ (prefixWord ++ tailWord_3522294).sum := by decide
  have hdescent : baseEnd_3522294 < baseStart_3522294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522317 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3522317 : Nat := 118140960795 + 3522317 * 2 ^ 59
def prefixEnd_3522317 : Nat := 4983230072969 + 3 ^ 40 * 3522317 * 2
def baseEnd_3522317 : Nat := 401920364111733478275259

theorem tailTrace_3522317 : CollatzResearch.WordTrace tailWord_3522317 prefixEnd_3522317 401920364111733478275259 := by
  unfold tailWord_3522317
  simp only [CollatzResearch.WordTrace]
  refine ⟨128469455180254547695765205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85646303453503031797176803 128469455180254547695765205)
  ·
    refine ⟨3011002855787215961619497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 128469455180254547695765205 3011002855787215961619497)
    ·
      refine ⟨2258252141840411971214623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3011002855787215961619497 2258252141840411971214623)
      ·
        refine ⟨3387378212760617956821935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258252141840411971214623 3387378212760617956821935)
        ·
          refine ⟨5081067319140926935232903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387378212760617956821935 5081067319140926935232903)
          ·
            refine ⟨7621600978711390402849355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081067319140926935232903 7621600978711390402849355)
            ·
              refine ⟨11432401468067085604274033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7621600978711390402849355 11432401468067085604274033)
              ·
                refine ⟨8574301101050314203205525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11432401468067085604274033 8574301101050314203205525)
                ·
                  refine ⟨401920364111733478275259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8574301101050314203205525 401920364111733478275259)
                  ·
                    rfl

theorem cell22_3522317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3522317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522317 prefixEnd_3522317 := by exact prefixLift 3522317
  have htrace : WordTrace (prefixWord ++ tailWord_3522317) baseStart_3522317 baseEnd_3522317 := by
    simpa [prefixWord, tailWord_3522317, baseEnd_3522317] using wordTrace_append hprefix tailTrace_3522317
  have hstable : (prefixWord ++ tailWord_3522317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522317).length < 2 ^ (prefixWord ++ tailWord_3522317).sum := by decide
  have hdescent : baseEnd_3522317 < baseStart_3522317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522568 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_3522568 : Nat := 118140960795 + 3522568 * 2 ^ 59
def prefixEnd_3522568 : Nat := 4983230072969 + 3 ^ 40 * 3522568 * 2
def baseEnd_3522568 : Nat := 1205847014764719446800007

theorem tailTrace_3522568 : CollatzResearch.WordTrace tailWord_3522568 prefixEnd_3522568 1205847014764719446800007 := by
  unfold tailWord_3522568
  simp only [CollatzResearch.WordTrace]
  refine ⟨64239304951172608781576179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85652406601563478375434905 64239304951172608781576179)
  ·
    refine ⟨96358957426758913172364269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64239304951172608781576179 96358957426758913172364269)
    ·
      refine ⟨36134609035034592439636601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96358957426758913172364269 36134609035034592439636601)
      ·
        refine ⟨27100956776275944329727451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36134609035034592439636601 27100956776275944329727451)
        ·
          refine ⟨40651435164413916494591177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27100956776275944329727451 40651435164413916494591177)
          ·
            refine ⟨30488576373310437370943383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40651435164413916494591177 30488576373310437370943383)
            ·
              refine ⟨45732864559965656056415075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30488576373310437370943383 45732864559965656056415075)
              ·
                refine ⟨68599296839948484084622613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45732864559965656056415075 68599296839948484084622613)
                ·
                  refine ⟨3215592039372585191466685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68599296839948484084622613 3215592039372585191466685)
                  ·
                    refine ⟨1205847014764719446800007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3215592039372585191466685 1205847014764719446800007)
                    ·
                      rfl

theorem cell22_3522568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_3522568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522568 prefixEnd_3522568 := by exact prefixLift 3522568
  have htrace : WordTrace (prefixWord ++ tailWord_3522568) baseStart_3522568 baseEnd_3522568 := by
    simpa [prefixWord, tailWord_3522568, baseEnd_3522568] using wordTrace_append hprefix tailTrace_3522568
  have hstable : (prefixWord ++ tailWord_3522568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522568).length < 2 ^ (prefixWord ++ tailWord_3522568).sum := by decide
  have hdescent : baseEnd_3522568 < baseStart_3522568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522602 : List Nat := [3, 1, 4, 1, 2, 2, 1, 3, 2, 3]
def baseStart_3522602 : Nat := 118140960795 + 3522602 * 2 ^ 59
def prefixEnd_3522602 : Nat := 4983230072969 + 3 ^ 40 * 3522602 * 2
def baseEnd_3522602 : Nat := 1205858653659554691449903

theorem tailTrace_3522602 : CollatzResearch.WordTrace tailWord_3522602 prefixEnd_3522602 1205858653659554691449903 := by
  unfold tailWord_3522602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32119962496055510342472515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85653233322814694246593373 32119962496055510342472515)
  ·
    refine ⟨48179943744083265513708773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32119962496055510342472515 48179943744083265513708773)
    ·
      refine ⟨9033739452015612283820395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48179943744083265513708773 9033739452015612283820395)
      ·
        refine ⟨13550609178023418425730593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033739452015612283820395 13550609178023418425730593)
        ·
          refine ⟨10162956883517563819297945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13550609178023418425730593 10162956883517563819297945)
          ·
            refine ⟨7622217662638172864473459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162956883517563819297945 7622217662638172864473459)
            ·
              refine ⟨11433326493957259296710189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622217662638172864473459 11433326493957259296710189)
              ·
                refine ⟨4287497435233972236266321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11433326493957259296710189 4287497435233972236266321)
                ·
                  refine ⟨3215623076425479177199741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4287497435233972236266321 3215623076425479177199741)
                  ·
                    refine ⟨1205858653659554691449903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3215623076425479177199741 1205858653659554691449903)
                    ·
                      rfl

theorem cell22_3522602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_3522602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522602 prefixEnd_3522602 := by exact prefixLift 3522602
  have htrace : WordTrace (prefixWord ++ tailWord_3522602) baseStart_3522602 baseEnd_3522602 := by
    simpa [prefixWord, tailWord_3522602, baseEnd_3522602] using wordTrace_append hprefix tailTrace_3522602
  have hstable : (prefixWord ++ tailWord_3522602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522602).length < 2 ^ (prefixWord ++ tailWord_3522602).sum := by decide
  have hdescent : baseEnd_3522602 < baseStart_3522602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522673 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3522673 : Nat := 118140960795 + 3522673 * 2 ^ 59
def prefixEnd_3522673 : Nat := 4983230072969 + 3 ^ 40 * 3522673 * 2
def baseEnd_3522673 : Nat := 1205882958410534172924685

theorem tailTrace_3522673 : CollatzResearch.WordTrace tailWord_3522673 prefixEnd_3522673 1205882958410534172924685 := by
  unfold tailWord_3522673
  simp only [CollatzResearch.WordTrace]
  refine ⟨128482439566964820495724673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85654959711309880330483115 128482439566964820495724673)
  ·
    refine ⟨96361829675223615371793505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128482439566964820495724673 96361829675223615371793505)
    ·
      refine ⟨72271372256417711528845129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96361829675223615371793505 72271372256417711528845129)
      ·
        refine ⟨54203529192313283646633847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72271372256417711528845129 54203529192313283646633847)
        ·
          refine ⟨81305293788469925469950771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54203529192313283646633847 81305293788469925469950771)
          ·
            refine ⟨121957940682704888204926157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81305293788469925469950771 121957940682704888204926157)
            ·
              refine ⟨45734227756014333076847309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 121957940682704888204926157 45734227756014333076847309)
              ·
                refine ⟨17150335408505374903817741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45734227756014333076847309 17150335408505374903817741)
                ·
                  refine ⟨6431375778189515588931653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17150335408505374903817741 6431375778189515588931653)
                  ·
                    refine ⟨1205882958410534172924685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431375778189515588931653 1205882958410534172924685)
                    ·
                      rfl

theorem cell22_3522673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3522673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522673 prefixEnd_3522673 := by exact prefixLift 3522673
  have htrace : WordTrace (prefixWord ++ tailWord_3522673) baseStart_3522673 baseEnd_3522673 := by
    simpa [prefixWord, tailWord_3522673, baseEnd_3522673] using wordTrace_append hprefix tailTrace_3522673
  have hstable : (prefixWord ++ tailWord_3522673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522673).length < 2 ^ (prefixWord ++ tailWord_3522673).sum := by decide
  have hdescent : baseEnd_3522673 < baseStart_3522673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522720 : List Nat := [2, 1, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_3522720 : Nat := 118140960795 + 3522720 * 2 ^ 59
def prefixEnd_3522720 : Nat := 4983230072969 + 3 ^ 40 * 3522720 * 2
def baseEnd_3522720 : Nat := 1205899047471041716999541

theorem tailTrace_3522720 : CollatzResearch.WordTrace tailWord_3522720 prefixEnd_3522720 1205899047471041716999541 := by
  unfold tailWord_3522720
  simp only [CollatzResearch.WordTrace]
  refine ⟨64242076898897273761342807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85656102531863031681790409 64242076898897273761342807)
  ·
    refine ⟨96363115348345910642014211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64242076898897273761342807 96363115348345910642014211)
    ·
      refine ⟨144544673022518865963021317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96363115348345910642014211 144544673022518865963021317)
      ·
        refine ⟨27102126191722287368066497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144544673022518865963021317 27102126191722287368066497)
        ·
          refine ⟨20326594643791715526049873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27102126191722287368066497 20326594643791715526049873)
          ·
            refine ⟨15244945982843786644537405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20326594643791715526049873 15244945982843786644537405)
            ·
              refine ⟨5716854743566419991701527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15244945982843786644537405 5716854743566419991701527)
              ·
                refine ⟨8575282115349629987552291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5716854743566419991701527 8575282115349629987552291)
                ·
                  refine ⟨12862923173024444981328437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8575282115349629987552291 12862923173024444981328437)
                  ·
                    refine ⟨1205899047471041716999541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12862923173024444981328437 1205899047471041716999541)
                    ·
                      rfl

theorem cell22_3522720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_3522720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522720 prefixEnd_3522720 := by exact prefixLift 3522720
  have htrace : WordTrace (prefixWord ++ tailWord_3522720) baseStart_3522720 baseEnd_3522720 := by
    simpa [prefixWord, tailWord_3522720, baseEnd_3522720] using wordTrace_append hprefix tailTrace_3522720
  have hstable : (prefixWord ++ tailWord_3522720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522720).length < 2 ^ (prefixWord ++ tailWord_3522720).sum := by decide
  have hdescent : baseEnd_3522720 < baseStart_3522720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522763 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_3522763 : Nat := 118140960795 + 3522763 * 2 ^ 59
def prefixEnd_3522763 : Nat := 4983230072969 + 3 ^ 40 * 3522763 * 2
def baseEnd_3522763 : Nat := 1205913767249803938174409

theorem tailTrace_3522763 : CollatzResearch.WordTrace tailWord_3522763 prefixEnd_3522763 1205913767249803938174409 := by
  unfold tailWord_3522763
  simp only [CollatzResearch.WordTrace]
  refine ⟨128485722136638765866500943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85657148091092510577667295 128485722136638765866500943)
  ·
    refine ⟨192728583204958148799751415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128485722136638765866500943 192728583204958148799751415)
    ·
      refine ⟨289092874807437223199627123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192728583204958148799751415 289092874807437223199627123)
      ·
        refine ⟨433639312211155834799440685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289092874807437223199627123 433639312211155834799440685)
        ·
          refine ⟨162614742079183438049790257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433639312211155834799440685 162614742079183438049790257)
          ·
            refine ⟨121961056559387578537342693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162614742079183438049790257 121961056559387578537342693)
            ·
              refine ⟨22867698104885170975751755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 121961056559387578537342693 22867698104885170975751755)
              ·
                refine ⟨34301547157327756463627633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22867698104885170975751755 34301547157327756463627633)
                ·
                  refine ⟨25726160367995817347720725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34301547157327756463627633 25726160367995817347720725)
                  ·
                    refine ⟨1205913767249803938174409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25726160367995817347720725 1205913767249803938174409)
                    ·
                      rfl

theorem cell22_3522763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_3522763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522763 prefixEnd_3522763 := by exact prefixLift 3522763
  have htrace : WordTrace (prefixWord ++ tailWord_3522763) baseStart_3522763 baseEnd_3522763 := by
    simpa [prefixWord, tailWord_3522763, baseEnd_3522763] using wordTrace_append hprefix tailTrace_3522763
  have hstable : (prefixWord ++ tailWord_3522763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522763).length < 2 ^ (prefixWord ++ tailWord_3522763).sum := by decide
  have hdescent : baseEnd_3522763 < baseStart_3522763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522793 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_3522793 : Nat := 118140960795 + 3522793 * 2 ^ 59
def prefixEnd_3522793 : Nat := 4983230072969 + 3 ^ 40 * 3522793 * 2
def baseEnd_3522793 : Nat := 1205924036862893859924317

theorem tailTrace_3522793 : CollatzResearch.WordTrace tailWord_3522793 prefixEnd_3522793 1205924036862893859924317 := by
  unfold tailWord_3522793
  simp only [CollatzResearch.WordTrace]
  refine ⟨128486816326530080990093033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85657877551020053993395355 128486816326530080990093033)
  ·
    refine ⟨96365112244897560742569775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128486816326530080990093033 96365112244897560742569775)
    ·
      refine ⟨144547668367346341113854663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96365112244897560742569775 144547668367346341113854663)
      ·
        refine ⟨216821502551019511670781995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144547668367346341113854663 216821502551019511670781995)
        ·
          refine ⟨325232253826529267506172993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216821502551019511670781995 325232253826529267506172993)
          ·
            refine ⟨243924190369896950629629745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325232253826529267506172993 243924190369896950629629745)
            ·
              refine ⟨182943142777422712972222309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243924190369896950629629745 182943142777422712972222309)
              ·
                refine ⟨34301839270766758682291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182943142777422712972222309 34301839270766758682291683)
                ·
                  refine ⟨51452758906150138023437525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34301839270766758682291683 51452758906150138023437525)
                  ·
                    refine ⟨1205924036862893859924317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51452758906150138023437525 1205924036862893859924317)
                    ·
                      rfl

theorem cell22_3522793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_3522793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522793 prefixEnd_3522793 := by exact prefixLift 3522793
  have htrace : WordTrace (prefixWord ++ tailWord_3522793) baseStart_3522793 baseEnd_3522793 := by
    simpa [prefixWord, tailWord_3522793, baseEnd_3522793] using wordTrace_append hprefix tailTrace_3522793
  have hstable : (prefixWord ++ tailWord_3522793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522793).length < 2 ^ (prefixWord ++ tailWord_3522793).sum := by decide
  have hdescent : baseEnd_3522793 < baseStart_3522793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522812 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_3522812 : Nat := 118140960795 + 3522812 * 2 ^ 59
def prefixEnd_3522812 : Nat := 4983230072969 + 3 ^ 40 * 3522812 * 2
def baseEnd_3522812 : Nat := 401976846983728047899753

theorem tailTrace_3522812 : CollatzResearch.WordTrace tailWord_3522812 prefixEnd_3522812 401976846983728047899753 := by
  unfold tailWord_3522812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64243754656730623617517345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85658339542307498156689793 64243754656730623617517345)
  ·
    refine ⟨48182815992547967713138009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64243754656730623617517345 48182815992547967713138009)
    ·
      refine ⟨36137111994410975784853507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48182815992547967713138009 36137111994410975784853507)
      ·
        refine ⟨54205667991616463677280261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36137111994410975784853507 54205667991616463677280261)
        ·
          refine ⟨10163562748428086939490049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54205667991616463677280261 10163562748428086939490049)
          ·
            refine ⟨7622672061321065204617537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10163562748428086939490049 7622672061321065204617537)
            ·
              refine ⟨5717004045990798903463153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622672061321065204617537 5717004045990798903463153)
              ·
                refine ⟨4287753034493099177597365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717004045990798903463153 4287753034493099177597365)
                ·
                  refine ⟨401976846983728047899753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4287753034493099177597365 401976846983728047899753)
                  ·
                    rfl

theorem cell22_3522812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_3522812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522812 prefixEnd_3522812 := by exact prefixLift 3522812
  have htrace : WordTrace (prefixWord ++ tailWord_3522812) baseStart_3522812 baseEnd_3522812 := by
    simpa [prefixWord, tailWord_3522812, baseEnd_3522812] using wordTrace_append hprefix tailTrace_3522812
  have hstable : (prefixWord ++ tailWord_3522812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522812).length < 2 ^ (prefixWord ++ tailWord_3522812).sum := by decide
  have hdescent : baseEnd_3522812 < baseStart_3522812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522825 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 3, 4]
def baseStart_3522825 : Nat := 118140960795 + 3522825 * 2 ^ 59
def prefixEnd_3522825 : Nat := 4983230072969 + 3 ^ 40 * 3522825 * 2
def baseEnd_3522825 : Nat := 1205934991116856443124219

theorem tailTrace_3522825 : CollatzResearch.WordTrace tailWord_3522825 prefixEnd_3522825 1205934991116856443124219 := by
  unfold tailWord_3522825
  simp only [CollatzResearch.WordTrace]
  refine ⟨128487983462414150455257929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85658655641609433636838619 128487983462414150455257929)
  ·
    refine ⟨96365987596810612841443447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128487983462414150455257929 96365987596810612841443447)
    ·
      refine ⟨144548981395215919262165171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96365987596810612841443447 144548981395215919262165171)
      ·
        refine ⟨216823472092823878893247757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144548981395215919262165171 216823472092823878893247757)
        ·
          refine ⟨81308802034808954584967909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 216823472092823878893247757 81308802034808954584967909)
          ·
            refine ⟨15245400381526678984681483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81308802034808954584967909 15245400381526678984681483)
            ·
              refine ⟨22868100572290018477022225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15245400381526678984681483 22868100572290018477022225)
              ·
                refine ⟨17151075429217513857766669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22868100572290018477022225 17151075429217513857766669)
                ·
                  refine ⟨6431653285956567696662501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17151075429217513857766669 6431653285956567696662501)
                  ·
                    refine ⟨1205934991116856443124219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6431653285956567696662501 1205934991116856443124219)
                    ·
                      rfl

theorem cell22_3522825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_3522825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522825 prefixEnd_3522825 := by exact prefixLift 3522825
  have htrace : WordTrace (prefixWord ++ tailWord_3522825) baseStart_3522825 baseEnd_3522825 := by
    simpa [prefixWord, tailWord_3522825, baseEnd_3522825] using wordTrace_append hprefix tailTrace_3522825
  have hstable : (prefixWord ++ tailWord_3522825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522825).length < 2 ^ (prefixWord ++ tailWord_3522825).sum := by decide
  have hdescent : baseEnd_3522825 < baseStart_3522825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522840 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_3522840 : Nat := 118140960795 + 3522840 * 2 ^ 59
def prefixEnd_3522840 : Nat := 4983230072969 + 3 ^ 40 * 3522840 * 2
def baseEnd_3522840 : Nat := 401980041974467134666391

theorem tailTrace_3522840 : CollatzResearch.WordTrace tailWord_3522840 prefixEnd_3522840 401980041974467134666391 := by
  unfold tailWord_3522840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64244265278679904008526987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85659020371573205344702649 64244265278679904008526987)
  ·
    refine ⟨96366397918019856012790481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64244265278679904008526987 96366397918019856012790481)
    ·
      refine ⟨72274798438514892009592861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96366397918019856012790481 72274798438514892009592861)
      ·
        refine ⟨27103049414443084503597323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72274798438514892009592861 27103049414443084503597323)
        ·
          refine ⟨40654574121664626755395985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27103049414443084503597323 40654574121664626755395985)
          ·
            refine ⟨30490930591248470066546989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40654574121664626755395985 30490930591248470066546989)
            ·
              refine ⟨11434098971718176274955121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30490930591248470066546989 11434098971718176274955121)
              ·
                refine ⟨8575574228788632206216341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11434098971718176274955121 8575574228788632206216341)
                ·
                  refine ⟨401980041974467134666391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8575574228788632206216341 401980041974467134666391)
                  ·
                    rfl

theorem cell22_3522840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_3522840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522840 prefixEnd_3522840 := by exact prefixLift 3522840
  have htrace : WordTrace (prefixWord ++ tailWord_3522840) baseStart_3522840 baseEnd_3522840 := by
    simpa [prefixWord, tailWord_3522840, baseEnd_3522840] using wordTrace_append hprefix tailTrace_3522840
  have hstable : (prefixWord ++ tailWord_3522840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522840).length < 2 ^ (prefixWord ++ tailWord_3522840).sum := by decide
  have hdescent : baseEnd_3522840 < baseStart_3522840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3522908 : List Nat := [2, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_3522908 : Nat := 118140960795 + 3522908 * 2 ^ 59
def prefixEnd_3522908 : Nat := 4983230072969 + 3 ^ 40 * 3522908 * 2
def baseEnd_3522908 : Nat := 401987801237690631099655

theorem tailTrace_3522908 : CollatzResearch.WordTrace tailWord_3522908 prefixEnd_3522908 401987801237690631099655 := by
  unfold tailWord_3522908
  simp only [CollatzResearch.WordTrace]
  refine ⟨64245505360556727815264689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85660673814075637087019585 64245505360556727815264689)
  ·
    refine ⟨48184129020417545861448517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64245505360556727815264689 48184129020417545861448517)
    ·
      refine ⟨9034524191328289849021597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48184129020417545861448517 9034524191328289849021597)
      ·
        refine ⟨3387946571748108693383099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9034524191328289849021597 3387946571748108693383099)
        ·
          refine ⟨5081919857622163040074649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387946571748108693383099 5081919857622163040074649)
          ·
            refine ⟨3811439893216622280055987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5081919857622163040074649 3811439893216622280055987)
            ·
              refine ⟨5717159839824933420083981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811439893216622280055987 5717159839824933420083981)
              ·
                refine ⟨2143934939934350032531493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5717159839824933420083981 2143934939934350032531493)
                ·
                  refine ⟨401987801237690631099655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143934939934350032531493 401987801237690631099655)
                  ·
                    rfl

theorem cell22_3522908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_3522908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3522908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3522908 prefixEnd_3522908 := by exact prefixLift 3522908
  have htrace : WordTrace (prefixWord ++ tailWord_3522908) baseStart_3522908 baseEnd_3522908 := by
    simpa [prefixWord, tailWord_3522908, baseEnd_3522908] using wordTrace_append hprefix tailTrace_3522908
  have hstable : (prefixWord ++ tailWord_3522908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3522908).length < 2 ^ (prefixWord ++ tailWord_3522908).sum := by decide
  have hdescent : baseEnd_3522908 < baseStart_3522908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3522908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523007 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 8, 3]
def baseStart_3523007 : Nat := 118140960795 + 3523007 * 2 ^ 59
def prefixEnd_3523007 : Nat := 4983230072969 + 3 ^ 40 * 3523007 * 2
def baseEnd_3523007 : Nat := 1205997293436268635073661

theorem tailTrace_3523007 : CollatzResearch.WordTrace tailWord_3523007 prefixEnd_3523007 1205997293436268635073661 := by
  unfold tailWord_3523007
  simp only [CollatzResearch.WordTrace]
  refine ⟨128494621547754795538383275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85663081031836530358922183 128494621547754795538383275)
  ·
    refine ⟨192741932321632193307574913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128494621547754795538383275 192741932321632193307574913)
    ·
      refine ⟨144556449241224144980681185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192741932321632193307574913 144556449241224144980681185)
      ·
        refine ⟨108417336930918108735510889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144556449241224144980681185 108417336930918108735510889)
        ·
          refine ⟨81313002698188581551633167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108417336930918108735510889 81313002698188581551633167)
          ·
            refine ⟨121969504047282872327449751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81313002698188581551633167 121969504047282872327449751)
            ·
              refine ⟨182954256070924308491174627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121969504047282872327449751 182954256070924308491174627)
              ·
                refine ⟨274431384106386462736761941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182954256070924308491174627 274431384106386462736761941)
                ·
                  refine ⟨3215992782496716360196429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 274431384106386462736761941 3215992782496716360196429)
                  ·
                    refine ⟨1205997293436268635073661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3215992782496716360196429 1205997293436268635073661)
                    ·
                      rfl

theorem cell22_3523007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_3523007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523007 prefixEnd_3523007 := by exact prefixLift 3523007
  have htrace : WordTrace (prefixWord ++ tailWord_3523007) baseStart_3523007 baseEnd_3523007 := by
    simpa [prefixWord, tailWord_3523007, baseEnd_3523007] using wordTrace_append hprefix tailTrace_3523007
  have hstable : (prefixWord ++ tailWord_3523007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523007).length < 2 ^ (prefixWord ++ tailWord_3523007).sum := by decide
  have hdescent : baseEnd_3523007 < baseStart_3523007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523028 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_3523028 : Nat := 118140960795 + 3523028 * 2 ^ 59
def prefixEnd_3523028 : Nat := 4983230072969 + 3 ^ 40 * 3523028 * 2
def baseEnd_3523028 : Nat := 1206004482165431580298597

theorem tailTrace_3523028 : CollatzResearch.WordTrace tailWord_3523028 prefixEnd_3523028 1206004482165431580298597 := by
  unfold tailWord_3523028
  simp only [CollatzResearch.WordTrace]
  refine ⟨64247693740339358062448869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85663591653785810749931825 64247693740339358062448869)
  ·
    refine ⟨12046442576313629636709163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64247693740339358062448869 12046442576313629636709163)
    ·
      refine ⟨18069663864470444455063745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12046442576313629636709163 18069663864470444455063745)
      ·
        refine ⟨13552247898352833341297809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18069663864470444455063745 13552247898352833341297809)
        ·
          refine ⟨10164185923764625005973357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13552247898352833341297809 10164185923764625005973357)
          ·
            refine ⟨3811569721411734377240009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10164185923764625005973357 3811569721411734377240009)
            ·
              refine ⟨2858677291058800782930007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3811569721411734377240009 2858677291058800782930007)
              ·
                refine ⟨4288015936588201174395011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2858677291058800782930007 4288015936588201174395011)
                ·
                  refine ⟨6432023904882301761592517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288015936588201174395011 6432023904882301761592517)
                  ·
                    refine ⟨1206004482165431580298597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432023904882301761592517 1206004482165431580298597)
                    ·
                      rfl

theorem cell22_3523028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_3523028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523028 prefixEnd_3523028 := by exact prefixLift 3523028
  have htrace : WordTrace (prefixWord ++ tailWord_3523028) baseStart_3523028 baseEnd_3523028 := by
    simpa [prefixWord, tailWord_3523028, baseEnd_3523028] using wordTrace_append hprefix tailTrace_3523028
  have hstable : (prefixWord ++ tailWord_3523028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523028).length < 2 ^ (prefixWord ++ tailWord_3523028).sum := by decide
  have hdescent : baseEnd_3523028 < baseStart_3523028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523037 : List Nat := [1, 4, 3, 1, 1, 1, 11]
def baseStart_3523037 : Nat := 118140960795 + 3523037 * 2 ^ 59
def prefixEnd_3523037 : Nat := 4983230072969 + 3 ^ 40 * 3523037 * 2
def baseEnd_3523037 : Nat := 44666946779605872474947

theorem tailTrace_3523037 : CollatzResearch.WordTrace tailWord_3523037 prefixEnd_3523037 44666946779605872474947 := by
  unfold tailWord_3523037
  simp only [CollatzResearch.WordTrace]
  refine ⟨128495715737646110661975365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85663810491764073774650243 128495715737646110661975365)
  ·
    refine ⟨24092946700808645749120381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128495715737646110661975365 24092946700808645749120381)
    ·
      refine ⟨9034855012803242155920143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24092946700808645749120381 9034855012803242155920143)
      ·
        refine ⟨13552282519204863233880215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9034855012803242155920143 13552282519204863233880215)
        ·
          refine ⟨20328423778807294850820323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13552282519204863233880215 20328423778807294850820323)
          ·
            refine ⟨30492635668210942276230485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328423778807294850820323 30492635668210942276230485)
            ·
              refine ⟨44666946779605872474947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30492635668210942276230485 44666946779605872474947)
              ·
                rfl

theorem cell22_3523037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 11].length) (baseStart_3523037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523037 prefixEnd_3523037 := by exact prefixLift 3523037
  have htrace : WordTrace (prefixWord ++ tailWord_3523037) baseStart_3523037 baseEnd_3523037 := by
    simpa [prefixWord, tailWord_3523037, baseEnd_3523037] using wordTrace_append hprefix tailTrace_3523037
  have hstable : (prefixWord ++ tailWord_3523037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523037).length < 2 ^ (prefixWord ++ tailWord_3523037).sum := by decide
  have hdescent : baseEnd_3523037 < baseStart_3523037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523058 : List Nat := [3, 2, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_3523058 : Nat := 118140960795 + 3523058 * 2 ^ 59
def prefixEnd_3523058 : Nat := 4983230072969 + 3 ^ 40 * 3523058 * 2
def baseEnd_3523058 : Nat := 1206014751778521502048505

theorem tailTrace_3523058 : CollatzResearch.WordTrace tailWord_3523058 prefixEnd_3523058 1206014751778521502048505 := by
  unfold tailWord_3523058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32124120417642507812122457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85664321113713354165659885 32124120417642507812122457)
  ·
    refine ⟨24093090313231880859091843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32124120417642507812122457 24093090313231880859091843)
    ·
      refine ⟨36139635469847821288637765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24093090313231880859091843 36139635469847821288637765)
      ·
        refine ⟨6776181650596466491619581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36139635469847821288637765 6776181650596466491619581)
        ·
          refine ⟨2541068118973674934357343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6776181650596466491619581 2541068118973674934357343)
          ·
            refine ⟨3811602178460512401536015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541068118973674934357343 3811602178460512401536015)
            ·
              refine ⟨5717403267690768602304023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811602178460512401536015 5717403267690768602304023)
              ·
                refine ⟨8576104901536152903456035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5717403267690768602304023 8576104901536152903456035)
                ·
                  refine ⟨12864157352304229355184053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576104901536152903456035 12864157352304229355184053)
                  ·
                    refine ⟨1206014751778521502048505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12864157352304229355184053 1206014751778521502048505)
                    ·
                      rfl

theorem cell22_3523058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_3523058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523058 prefixEnd_3523058 := by exact prefixLift 3523058
  have htrace : WordTrace (prefixWord ++ tailWord_3523058) baseStart_3523058 baseEnd_3523058 := by
    simpa [prefixWord, tailWord_3523058, baseEnd_3523058] using wordTrace_append hprefix tailTrace_3523058
  have hstable : (prefixWord ++ tailWord_3523058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523058).length < 2 ^ (prefixWord ++ tailWord_3523058).sum := by decide
  have hdescent : baseEnd_3523058 < baseStart_3523058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523069 : List Nat := [1, 4, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_3523069 : Nat := 118140960795 + 3523069 * 2 ^ 59
def prefixEnd_3523069 : Nat := 4983230072969 + 3 ^ 40 * 3523069 * 2
def baseEnd_3523069 : Nat := 1206018517303321140023471

theorem tailTrace_3523069 : CollatzResearch.WordTrace tailWord_3523069 prefixEnd_3523069 1206018517303321140023471 := by
  unfold tailWord_3523069
  simp only [CollatzResearch.WordTrace]
  refine ⟨128496882873530180127140261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85664588582353453418093507 128496882873530180127140261)
  ·
    refine ⟨24093165538786908773838799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128496882873530180127140261 24093165538786908773838799)
    ·
      refine ⟨36139748308180363160758199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24093165538786908773838799 36139748308180363160758199)
      ·
        refine ⟨54209622462270544741137299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36139748308180363160758199 54209622462270544741137299)
        ·
          refine ⟨81314433693405817111705949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54209622462270544741137299 81314433693405817111705949)
          ·
            refine ⟨30492912635027181416889731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81314433693405817111705949 30492912635027181416889731)
            ·
              refine ⟨45739368952540772125334597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30492912635027181416889731 45739368952540772125334597)
              ·
                refine ⟨8576131678601394773500237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45739368952540772125334597 8576131678601394773500237)
                ·
                  refine ⟨3216049379475523040062589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8576131678601394773500237 3216049379475523040062589)
                  ·
                    refine ⟨1206018517303321140023471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216049379475523040062589 1206018517303321140023471)
                    ·
                      rfl

theorem cell22_3523069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_3523069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523069 prefixEnd_3523069 := by exact prefixLift 3523069
  have htrace : WordTrace (prefixWord ++ tailWord_3523069) baseStart_3523069 baseEnd_3523069 := by
    simpa [prefixWord, tailWord_3523069, baseEnd_3523069] using wordTrace_append hprefix tailTrace_3523069
  have hstable : (prefixWord ++ tailWord_3523069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523069).length < 2 ^ (prefixWord ++ tailWord_3523069).sum := by decide
  have hdescent : baseEnd_3523069 < baseStart_3523069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523082 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_3523082 : Nat := 118140960795 + 3523082 * 2 ^ 59
def prefixEnd_3523082 : Nat := 4983230072969 + 3 ^ 40 * 3523082 * 2
def baseEnd_3523082 : Nat := 402007655822997813149477

theorem tailTrace_3523082 : CollatzResearch.WordTrace tailWord_3523082 prefixEnd_3523082 402007655822997813149477 := by
  unfold tailWord_3523082
  simp only [CollatzResearch.WordTrace]
  refine ⟨32124339255620770836840875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85664904681655388898242333 32124339255620770836840875)
  ·
    refine ⟨48186508883431156255261313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32124339255620770836840875 48186508883431156255261313)
    ·
      refine ⟨36139881662573367191445985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48186508883431156255261313 36139881662573367191445985)
      ·
        refine ⟨27104911246930025393584489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36139881662573367191445985 27104911246930025393584489)
        ·
          refine ⟨20328683435197519045188367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27104911246930025393584489 20328683435197519045188367)
          ·
            refine ⟨30493025152796278567782551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328683435197519045188367 30493025152796278567782551)
            ·
              refine ⟨45739537729194417851673827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30493025152796278567782551 45739537729194417851673827)
              ·
                refine ⟨68609306593791626777510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45739537729194417851673827 68609306593791626777510741)
                ·
                  refine ⟨402007655822997813149477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68609306593791626777510741 402007655822997813149477)
                  ·
                    rfl

theorem cell22_3523082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_3523082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523082 prefixEnd_3523082 := by exact prefixLift 3523082
  have htrace : WordTrace (prefixWord ++ tailWord_3523082) baseStart_3523082 baseEnd_3523082 := by
    simpa [prefixWord, tailWord_3523082, baseEnd_3523082] using wordTrace_append hprefix tailTrace_3523082
  have hstable : (prefixWord ++ tailWord_3523082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523082).length < 2 ^ (prefixWord ++ tailWord_3523082).sum := by decide
  have hdescent : baseEnd_3523082 < baseStart_3523082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523127 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 8]
def baseStart_3523127 : Nat := 118140960795 + 3523127 * 2 ^ 59
def prefixEnd_3523127 : Nat := 4983230072969 + 3 ^ 40 * 3523127 * 2
def baseEnd_3523127 : Nat := 402012790629542774024431

theorem tailTrace_3523127 : CollatzResearch.WordTrace tailWord_3523127 prefixEnd_3523127 402012790629542774024431 := by
  unfold tailWord_3523127
  simp only [CollatzResearch.WordTrace]
  refine ⟨128498998307320056032751635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85665998871546704021834423 128498998307320056032751635)
  ·
    refine ⟨192748497460980084049127453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128498998307320056032751635 192748497460980084049127453)
    ·
      refine ⟨72280686547867531518422795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192748497460980084049127453 72280686547867531518422795)
      ·
        refine ⟨108421029821801297277634193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72280686547867531518422795 108421029821801297277634193)
        ·
          refine ⟨81315772366350972958225645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108421029821801297277634193 81315772366350972958225645)
          ·
            refine ⟨30493414637381614859334617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81315772366350972958225645 30493414637381614859334617)
            ·
              refine ⟨22870060978036211144500963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30493414637381614859334617 22870060978036211144500963)
              ·
                refine ⟨34305091467054316716751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22870060978036211144500963 34305091467054316716751445)
                ·
                  refine ⟨402012790629542774024431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34305091467054316716751445 402012790629542774024431)
                  ·
                    rfl

theorem cell22_3523127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 8].length) (baseStart_3523127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523127 prefixEnd_3523127 := by exact prefixLift 3523127
  have htrace : WordTrace (prefixWord ++ tailWord_3523127) baseStart_3523127 baseEnd_3523127 := by
    simpa [prefixWord, tailWord_3523127, baseEnd_3523127] using wordTrace_append hprefix tailTrace_3523127
  have hstable : (prefixWord ++ tailWord_3523127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523127).length < 2 ^ (prefixWord ++ tailWord_3523127).sum := by decide
  have hdescent : baseEnd_3523127 < baseStart_3523127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523129 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 3, 4]
def baseStart_3523129 : Nat := 118140960795 + 3523129 * 2 ^ 59
def prefixEnd_3523129 : Nat := 4983230072969 + 3 ^ 40 * 3523129 * 2
def baseEnd_3523129 : Nat := 1206039056529500983523287

theorem tailTrace_3523129 : CollatzResearch.WordTrace tailWord_3523129 prefixEnd_3523129 1206039056529500983523287 := by
  unfold tailWord_3523129
  simp only [CollatzResearch.WordTrace]
  refine ⟨128499071253312810374324441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85666047502208540249549627 128499071253312810374324441)
  ·
    refine ⟨96374303439984607780743331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128499071253312810374324441 96374303439984607780743331)
    ·
      refine ⟨144561455159976911671114997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96374303439984607780743331 144561455159976911671114997)
      ·
        refine ⟨13552636421247835469167031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144561455159976911671114997 13552636421247835469167031)
        ·
          refine ⟨20328954631871753203750547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13552636421247835469167031 20328954631871753203750547)
          ·
            refine ⟨30493431947807629805625821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20328954631871753203750547 30493431947807629805625821)
            ·
              refine ⟨11435036980427861177109683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30493431947807629805625821 11435036980427861177109683)
              ·
                refine ⟨17152555470641791765664525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435036980427861177109683 17152555470641791765664525)
                ·
                  refine ⟨6432208301490671912124197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17152555470641791765664525 6432208301490671912124197)
                  ·
                    refine ⟨1206039056529500983523287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432208301490671912124197 1206039056529500983523287)
                    ·
                      rfl

theorem cell22_3523129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_3523129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523129 prefixEnd_3523129 := by exact prefixLift 3523129
  have htrace : WordTrace (prefixWord ++ tailWord_3523129) baseStart_3523129 baseEnd_3523129 := by
    simpa [prefixWord, tailWord_3523129, baseEnd_3523129] using wordTrace_append hprefix tailTrace_3523129
  have hstable : (prefixWord ++ tailWord_3523129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523129).length < 2 ^ (prefixWord ++ tailWord_3523129).sum := by decide
  have hdescent : baseEnd_3523129 < baseStart_3523129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 1, 9]
def baseStart_3523187 : Nat := 118140960795 + 3523187 * 2 ^ 59
def prefixEnd_3523187 : Nat := 4983230072969 + 3 ^ 40 * 3523187 * 2
def baseEnd_3523187 : Nat := 1206058911114808165573109

theorem tailTrace_3523187 : CollatzResearch.WordTrace tailWord_3523187 prefixEnd_3523187 1206058911114808165573109 := by
  unfold tailWord_3523187
  simp only [CollatzResearch.WordTrace]
  refine ⟨128501186687102686279935815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85667457791401790853290543 128501186687102686279935815)
  ·
    refine ⟨192751780030654029419903723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128501186687102686279935815 192751780030654029419903723)
    ·
      refine ⟨289127670045981044129855585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192751780030654029419903723 289127670045981044129855585)
      ·
        refine ⟨216845752534485783097391689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289127670045981044129855585 216845752534485783097391689)
        ·
          refine ⟨162634314400864337323043767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216845752534485783097391689 162634314400864337323043767)
          ·
            refine ⟨243951471601296505984565651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162634314400864337323043767 243951471601296505984565651)
            ·
              refine ⟨365927207401944758976848477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243951471601296505984565651 365927207401944758976848477)
              ·
                refine ⟨137222702775729284616318179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 365927207401944758976848477 137222702775729284616318179)
                ·
                  refine ⟨205834054163593926924477269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 137222702775729284616318179 205834054163593926924477269)
                  ·
                    refine ⟨1206058911114808165573109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 205834054163593926924477269 1206058911114808165573109)
                    ·
                      rfl

theorem cell22_3523187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_3523187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523187 prefixEnd_3523187 := by exact prefixLift 3523187
  have htrace : WordTrace (prefixWord ++ tailWord_3523187) baseStart_3523187 baseEnd_3523187 := by
    simpa [prefixWord, tailWord_3523187, baseEnd_3523187] using wordTrace_append hprefix tailTrace_3523187
  have hstable : (prefixWord ++ tailWord_3523187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523187).length < 2 ^ (prefixWord ++ tailWord_3523187).sum := by decide
  have hdescent : baseEnd_3523187 < baseStart_3523187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523210 : List Nat := [3, 1, 2, 3, 3, 2, 1, 2, 2, 3]
def baseStart_3523210 : Nat := 118140960795 + 3523210 * 2 ^ 59
def prefixEnd_3523210 : Nat := 4983230072969 + 3 ^ 40 * 3523210 * 2
def baseEnd_3523210 : Nat := 1206066784484843772248039

theorem tailTrace_3523210 : CollatzResearch.WordTrace tailWord_3523210 prefixEnd_3523210 1206066784484843772248039 := by
  unfold tailWord_3523210
  simp only [CollatzResearch.WordTrace]
  refine ⟨32125506391504840302005771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85668017044012907472015389 32125506391504840302005771)
  ·
    refine ⟨48188259587257260453008657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32125506391504840302005771 48188259587257260453008657)
    ·
      refine ⟨36141194690442945339756493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48188259587257260453008657 36141194690442945339756493)
      ·
        refine ⟨13552948008916104502408685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36141194690442945339756493 13552948008916104502408685)
        ·
          refine ⟨5082355503343539188403257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13552948008916104502408685 5082355503343539188403257)
          ·
            refine ⟨3811766627507654391302443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082355503343539188403257 3811766627507654391302443)
            ·
              refine ⟨5717649941261481586953665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811766627507654391302443 5717649941261481586953665)
              ·
                refine ⟨4288237455946111190215249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5717649941261481586953665 4288237455946111190215249)
                ·
                  refine ⟨3216178091959583392661437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4288237455946111190215249 3216178091959583392661437)
                  ·
                    refine ⟨1206066784484843772248039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216178091959583392661437 1206066784484843772248039)
                    ·
                      rfl

theorem cell22_3523210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_3523210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523210 prefixEnd_3523210 := by exact prefixLift 3523210
  have htrace : WordTrace (prefixWord ++ tailWord_3523210) baseStart_3523210 baseEnd_3523210 := by
    simpa [prefixWord, tailWord_3523210, baseEnd_3523210] using wordTrace_append hprefix tailTrace_3523210
  have hstable : (prefixWord ++ tailWord_3523210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523210).length < 2 ^ (prefixWord ++ tailWord_3523210).sum := by decide
  have hdescent : baseEnd_3523210 < baseStart_3523210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523311 : List Nat := [1, 1, 2, 1, 5, 3, 1, 2, 1, 5]
def baseStart_3523311 : Nat := 118140960795 + 3523311 * 2 ^ 59
def prefixEnd_3523311 : Nat := 4983230072969 + 3 ^ 40 * 3523311 * 2
def baseEnd_3523311 : Nat := 1206101358848913175472729

theorem tailTrace_3523311 : CollatzResearch.WordTrace tailWord_3523311 prefixEnd_3523311 1206101358848913175472729 := by
  unfold tailWord_3523311
  simp only [CollatzResearch.WordTrace]
  refine ⟨128505709338653455457449787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85670472892435636971633191 128505709338653455457449787)
  ·
    refine ⟨192758564007980183186174681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128505709338653455457449787 192758564007980183186174681)
    ·
      refine ⟨144568923005985137389631011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192758564007980183186174681 144568923005985137389631011)
      ·
        refine ⟨216853384508977706084446517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144568923005985137389631011 216853384508977706084446517)
        ·
          refine ⟨20330004797716659945416861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 216853384508977706084446517 20330004797716659945416861)
          ·
            refine ⟨7623751799143747479531323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20330004797716659945416861 7623751799143747479531323)
            ·
              refine ⟨11435627698715621219296985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623751799143747479531323 11435627698715621219296985)
              ·
                refine ⟨8576720774036715914472739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11435627698715621219296985 8576720774036715914472739)
                ·
                  refine ⟨12865081161055073871709109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8576720774036715914472739 12865081161055073871709109)
                  ·
                    refine ⟨1206101358848913175472729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12865081161055073871709109 1206101358848913175472729)
                    ·
                      rfl

theorem cell22_3523311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_3523311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523311 prefixEnd_3523311 := by exact prefixLift 3523311
  have htrace : WordTrace (prefixWord ++ tailWord_3523311) baseStart_3523311 baseEnd_3523311 := by
    simpa [prefixWord, tailWord_3523311, baseEnd_3523311] using wordTrace_append hprefix tailTrace_3523311
  have hstable : (prefixWord ++ tailWord_3523311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523311).length < 2 ^ (prefixWord ++ tailWord_3523311).sum := by decide
  have hdescent : baseEnd_3523311 < baseStart_3523311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523324 : List Nat := [2, 2, 2, 1, 3, 12]
def baseStart_3523324 : Nat := 118140960795 + 3523324 * 2 ^ 59
def prefixEnd_3523324 : Nat := 4983230072969 + 3 ^ 40 * 3523324 * 2
def baseEnd_3523324 : Nat := 14890195173019573764169

theorem tailTrace_3523324 : CollatzResearch.WordTrace tailWord_3523324 prefixEnd_3523324 14890195173019573764169 := by
  unfold tailWord_3523324
  simp only [CollatzResearch.WordTrace]
  refine ⟨64253091743803179338836513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85670788991737572451782017 64253091743803179338836513)
  ·
    refine ⟨48189818807852384504127385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64253091743803179338836513 48189818807852384504127385)
    ·
      refine ⟨36142364105889288378095539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48189818807852384504127385 36142364105889288378095539)
      ·
        refine ⟨54213546158833932567143309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36142364105889288378095539 54213546158833932567143309)
        ·
          refine ⟨20330079809562724712678741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54213546158833932567143309 20330079809562724712678741)
          ·
            refine ⟨14890195173019573764169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 20330079809562724712678741 14890195173019573764169)
            ·
              rfl

theorem cell22_3523324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 12].length) (baseStart_3523324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523324 prefixEnd_3523324 := by exact prefixLift 3523324
  have htrace : WordTrace (prefixWord ++ tailWord_3523324) baseStart_3523324 baseEnd_3523324 := by
    simpa [prefixWord, tailWord_3523324, baseEnd_3523324] using wordTrace_append hprefix tailTrace_3523324
  have hstable : (prefixWord ++ tailWord_3523324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523324).length < 2 ^ (prefixWord ++ tailWord_3523324).sum := by decide
  have hdescent : baseEnd_3523324 < baseStart_3523324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523330 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3523330 : Nat := 118140960795 + 3523330 * 2 ^ 59
def prefixEnd_3523330 : Nat := 4983230072969 + 3 ^ 40 * 3523330 * 2
def baseEnd_3523330 : Nat := 402035954312401153082557

theorem tailTrace_3523330 : CollatzResearch.WordTrace tailWord_3523330 prefixEnd_3523330 402035954312401153082557 := by
  unfold tailWord_3523330
  simp only [CollatzResearch.WordTrace]
  refine ⟨32126600581396155425597861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85670934883723081134927629 32126600581396155425597861)
  ·
    refine ⟨6023737609011779142299599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32126600581396155425597861 6023737609011779142299599)
    ·
      refine ⟨9035606413517668713449399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6023737609011779142299599 9035606413517668713449399)
      ·
        refine ⟨13553409620276503070174099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9035606413517668713449399 13553409620276503070174099)
        ·
          refine ⟨20330114430414754605261149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13553409620276503070174099 20330114430414754605261149)
          ·
            refine ⟨7623792911405532976972931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20330114430414754605261149 7623792911405532976972931)
            ·
              refine ⟨11435689367108299465459397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623792911405532976972931 11435689367108299465459397)
              ·
                refine ⟨2144191756332806149773637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11435689367108299465459397 2144191756332806149773637)
                ·
                  refine ⟨402035954312401153082557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144191756332806149773637 402035954312401153082557)
                  ·
                    rfl

theorem cell22_3523330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3523330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523330 prefixEnd_3523330 := by exact prefixLift 3523330
  have htrace : WordTrace (prefixWord ++ tailWord_3523330) baseStart_3523330 baseEnd_3523330 := by
    simpa [prefixWord, tailWord_3523330, baseEnd_3523330] using wordTrace_append hprefix tailTrace_3523330
  have hstable : (prefixWord ++ tailWord_3523330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523330).length < 2 ^ (prefixWord ++ tailWord_3523330).sum := by decide
  have hdescent : baseEnd_3523330 < baseStart_3523330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523339 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 2, 7]
def baseStart_3523339 : Nat := 118140960795 + 3523339 * 2 ^ 59
def prefixEnd_3523339 : Nat := 4983230072969 + 3 ^ 40 * 3523339 * 2
def baseEnd_3523339 : Nat := 1206110943821130435772643

theorem tailTrace_3523339 : CollatzResearch.WordTrace tailWord_3523339 prefixEnd_3523339 1206110943821130435772643 := by
  unfold tailWord_3523339
  simp only [CollatzResearch.WordTrace]
  refine ⟨128506730582552016239469071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85671153721701344159646047 128506730582552016239469071)
  ·
    refine ⟨192760095873828024359203607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128506730582552016239469071 192760095873828024359203607)
    ·
      refine ⟨289140143810742036538805411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192760095873828024359203607 289140143810742036538805411)
      ·
        refine ⟨433710215716113054808208117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289140143810742036538805411 433710215716113054808208117)
        ·
          refine ⟨40660332723385598888269511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 433710215716113054808208117 40660332723385598888269511)
          ·
            refine ⟨60990499085078398332404267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40660332723385598888269511 60990499085078398332404267)
            ·
              refine ⟨91485748627617597498606401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60990499085078398332404267 91485748627617597498606401)
              ·
                refine ⟨68614311470713198123954801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91485748627617597498606401 68614311470713198123954801)
                ·
                  refine ⟨51460733603034898592966101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68614311470713198123954801 51460733603034898592966101)
                  ·
                    refine ⟨1206110943821130435772643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51460733603034898592966101 1206110943821130435772643)
                    ·
                      rfl

theorem cell22_3523339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 7].length) (baseStart_3523339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523339 prefixEnd_3523339 := by exact prefixLift 3523339
  have htrace : WordTrace (prefixWord ++ tailWord_3523339) baseStart_3523339 baseEnd_3523339 := by
    simpa [prefixWord, tailWord_3523339, baseEnd_3523339] using wordTrace_append hprefix tailTrace_3523339
  have hstable : (prefixWord ++ tailWord_3523339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523339).length < 2 ^ (prefixWord ++ tailWord_3523339).sum := by decide
  have hdescent : baseEnd_3523339 < baseStart_3523339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523369 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 9]
def baseStart_3523369 : Nat := 118140960795 + 3523369 * 2 ^ 59
def prefixEnd_3523369 : Nat := 4983230072969 + 3 ^ 40 * 3523369 * 2
def baseEnd_3523369 : Nat := 402040404478073452507517

theorem tailTrace_3523369 : CollatzResearch.WordTrace tailWord_3523369 prefixEnd_3523369 402040404478073452507517 := by
  unfold tailWord_3523369
  simp only [CollatzResearch.WordTrace]
  refine ⟨128507824772443331363061161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85671883181628887575374107 128507824772443331363061161)
  ·
    refine ⟨96380868579332498522295871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128507824772443331363061161 96380868579332498522295871)
    ·
      refine ⟨144571302868998747783443807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96380868579332498522295871 144571302868998747783443807)
      ·
        refine ⟨216856954303498121675165711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144571302868998747783443807 216856954303498121675165711)
        ·
          refine ⟨325285431455247182512748567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216856954303498121675165711 325285431455247182512748567)
          ·
            refine ⟨487928147182870773769122851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325285431455247182512748567 487928147182870773769122851)
            ·
              refine ⟨731892220774306160653684277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487928147182870773769122851 731892220774306160653684277)
              ·
                refine ⟨68614895697591202561282901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 731892220774306160653684277 68614895697591202561282901)
                ·
                  refine ⟨402040404478073452507517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68614895697591202561282901 402040404478073452507517)
                  ·
                    rfl

theorem cell22_3523369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 9].length) (baseStart_3523369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523369 prefixEnd_3523369 := by exact prefixLift 3523369
  have htrace : WordTrace (prefixWord ++ tailWord_3523369) baseStart_3523369 baseEnd_3523369 := by
    simpa [prefixWord, tailWord_3523369, baseEnd_3523369] using wordTrace_append hprefix tailTrace_3523369
  have hstable : (prefixWord ++ tailWord_3523369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523369).length < 2 ^ (prefixWord ++ tailWord_3523369).sum := by decide
  have hdescent : baseEnd_3523369 < baseStart_3523369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523401 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 2, 5]
def baseStart_3523401 : Nat := 118140960795 + 3523401 * 2 ^ 59
def prefixEnd_3523401 : Nat := 4983230072969 + 3 ^ 40 * 3523401 * 2
def baseEnd_3523401 : Nat := 1206132167688182940722453

theorem tailTrace_3523401 : CollatzResearch.WordTrace tailWord_3523401 prefixEnd_3523401 1206132167688182940722453 := by
  unfold tailWord_3523401
  simp only [CollatzResearch.WordTrace]
  refine ⟨128508991908327400828226057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85672661272218267218817371 128508991908327400828226057)
  ·
    refine ⟨96381743931245550621169543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128508991908327400828226057 96381743931245550621169543)
    ·
      refine ⟨144572615896868325931754315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96381743931245550621169543 144572615896868325931754315)
      ·
        refine ⟨216858923845302488897631473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144572615896868325931754315 216858923845302488897631473)
        ·
          refine ⟨162644192883976866673223605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216858923845302488897631473 162644192883976866673223605)
          ·
            refine ⟨15247893082872831250614713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 162644192883976866673223605 15247893082872831250614713)
            ·
              refine ⟨11435919812154623437961035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15247893082872831250614713 11435919812154623437961035)
              ·
                refine ⟨17153879718231935156941553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11435919812154623437961035 17153879718231935156941553)
                ·
                  refine ⟨12865409788673951367706165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17153879718231935156941553 12865409788673951367706165)
                  ·
                    refine ⟨1206132167688182940722453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12865409788673951367706165 1206132167688182940722453)
                    ·
                      rfl

theorem cell22_3523401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_3523401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523401 prefixEnd_3523401 := by exact prefixLift 3523401
  have htrace : WordTrace (prefixWord ++ tailWord_3523401) baseStart_3523401 baseEnd_3523401 := by
    simpa [prefixWord, tailWord_3523401, baseEnd_3523401] using wordTrace_append hprefix tailTrace_3523401
  have hstable : (prefixWord ++ tailWord_3523401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523401).length < 2 ^ (prefixWord ++ tailWord_3523401).sum := by decide
  have hdescent : baseEnd_3523401 < baseStart_3523401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523416 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_3523416 : Nat := 118140960795 + 3523416 * 2 ^ 59
def prefixEnd_3523416 : Nat := 4983230072969 + 3 ^ 40 * 3523416 * 2
def baseEnd_3523416 : Nat := 1206137302494727901597407

theorem tailTrace_3523416 : CollatzResearch.WordTrace tailWord_3523416 prefixEnd_3523416 1206137302494727901597407 := by
  unfold tailWord_3523416
  simp only [CollatzResearch.WordTrace]
  refine ⟨64254769501636529195011051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85673026002182038926681401 64254769501636529195011051)
  ·
    refine ⟨96382154252454793792516577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64254769501636529195011051 96382154252454793792516577)
    ·
      refine ⟨72286615689341095344387433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96382154252454793792516577 72286615689341095344387433)
      ·
        refine ⟨54214961767005821508290575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72286615689341095344387433 54214961767005821508290575)
        ·
          refine ⟨81322442650508732262435863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54214961767005821508290575 81322442650508732262435863)
          ·
            refine ⟨121983663975763098393653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81322442650508732262435863 121983663975763098393653795)
            ·
              refine ⟨182975495963644647590480693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121983663975763098393653795 182975495963644647590480693)
              ·
                refine ⟨17153952746591685711607565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 182975495963644647590480693 17153952746591685711607565)
                ·
                  refine ⟨6432732279971882141852837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17153952746591685711607565 6432732279971882141852837)
                  ·
                    refine ⟨1206137302494727901597407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6432732279971882141852837 1206137302494727901597407)
                    ·
                      rfl

theorem cell22_3523416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_3523416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523416 prefixEnd_3523416 := by exact prefixLift 3523416
  have htrace : WordTrace (prefixWord ++ tailWord_3523416) baseStart_3523416 baseEnd_3523416 := by
    simpa [prefixWord, tailWord_3523416, baseEnd_3523416] using wordTrace_append hprefix tailTrace_3523416
  have hstable : (prefixWord ++ tailWord_3523416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523416).length < 2 ^ (prefixWord ++ tailWord_3523416).sum := by decide
  have hdescent : baseEnd_3523416 < baseStart_3523416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523454 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_3523454 : Nat := 118140960795 + 3523454 * 2 ^ 59
def prefixEnd_3523454 : Nat := 4983230072969 + 3 ^ 40 * 3523454 * 2
def baseEnd_3523454 : Nat := 402050103557102823049097

theorem tailTrace_3523454 : CollatzResearch.WordTrace tailWord_3523454 prefixEnd_3523454 402050103557102823049097 := by
  unfold tailWord_3523454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16063865622141923859988177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85673949984756927253270277 16063865622141923859988177)
  ·
    refine ⟨12047899216606442894991133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16063865622141923859988177 12047899216606442894991133)
    ·
      refine ⟨4517962206227416085621675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12047899216606442894991133 4517962206227416085621675)
      ·
        refine ⟨6776943309341124128432513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517962206227416085621675 6776943309341124128432513)
        ·
          refine ⟨5082707482005843096324385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776943309341124128432513 5082707482005843096324385)
          ·
            refine ⟨3812030611504382322243289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082707482005843096324385 3812030611504382322243289)
            ·
              refine ⟨2859022958628286741682467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3812030611504382322243289 2859022958628286741682467)
              ·
                refine ⟨4288534437942430112523701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859022958628286741682467 4288534437942430112523701)
                ·
                  refine ⟨402050103557102823049097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4288534437942430112523701 402050103557102823049097)
                  ·
                    rfl

theorem cell22_3523454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_3523454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523454 prefixEnd_3523454 := by exact prefixLift 3523454
  have htrace : WordTrace (prefixWord ++ tailWord_3523454) baseStart_3523454 baseEnd_3523454 := by
    simpa [prefixWord, tailWord_3523454, baseEnd_3523454] using wordTrace_append hprefix tailTrace_3523454
  have hstable : (prefixWord ++ tailWord_3523454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523454).length < 2 ^ (prefixWord ++ tailWord_3523454).sum := by decide
  have hdescent : baseEnd_3523454 < baseStart_3523454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523536 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_3523536 : Nat := 118140960795 + 3523536 * 2 ^ 59
def prefixEnd_3523536 : Nat := 4983230072969 + 3 ^ 40 * 3523536 * 2
def baseEnd_3523536 : Nat := 1206178380947087588597039

theorem tailTrace_3523536 : CollatzResearch.WordTrace tailWord_3523536 prefixEnd_3523536 1206178380947087588597039 := by
  unfold tailWord_3523536
  simp only [CollatzResearch.WordTrace]
  refine ⟨64256957881419159442195231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85675943841892212589593641 64256957881419159442195231)
  ·
    refine ⟨96385436822128739163292847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64256957881419159442195231 96385436822128739163292847)
    ·
      refine ⟨144578155233193108744939271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96385436822128739163292847 144578155233193108744939271)
      ·
        refine ⟨216867232849789663117408907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144578155233193108744939271 216867232849789663117408907)
        ·
          refine ⟨325300849274684494676113361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216867232849789663117408907 325300849274684494676113361)
          ·
            refine ⟨243975636956013371007085021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325300849274684494676113361 243975636956013371007085021)
            ·
              refine ⟨91490863858505014127656883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243975636956013371007085021 91490863858505014127656883)
              ·
                refine ⟨137236295787757521191485325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91490863858505014127656883 137236295787757521191485325)
                ·
                  refine ⟨51463610920409070446806997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137236295787757521191485325 51463610920409070446806997)
                  ·
                    refine ⟨1206178380947087588597039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 51463610920409070446806997 1206178380947087588597039)
                    ·
                      rfl

theorem cell22_3523536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_3523536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523536 prefixEnd_3523536 := by exact prefixLift 3523536
  have htrace : WordTrace (prefixWord ++ tailWord_3523536) baseStart_3523536 baseEnd_3523536 := by
    simpa [prefixWord, tailWord_3523536, baseEnd_3523536] using wordTrace_append hprefix tailTrace_3523536
  have hstable : (prefixWord ++ tailWord_3523536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523536).length < 2 ^ (prefixWord ++ tailWord_3523536).sum := by decide
  have hdescent : baseEnd_3523536 < baseStart_3523536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523585 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3523585 : Nat := 118140960795 + 3523585 * 2 ^ 59
def prefixEnd_3523585 : Nat := 4983230072969 + 3 ^ 40 * 3523585 * 2
def baseEnd_3523585 : Nat := 1206195154648467794121889

theorem tailTrace_3523585 : CollatzResearch.WordTrace tailWord_3523585 prefixEnd_3523585 1206195154648467794121889 := by
  unfold tailWord_3523585
  simp only [CollatzResearch.WordTrace]
  refine ⟨128515702939660800252924209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85677135293107200168616139 128515702939660800252924209)
  ·
    refine ⟨96386777204745600189693157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128515702939660800252924209 96386777204745600189693157)
    ·
      refine ⟨18072520725889800035567467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96386777204745600189693157 18072520725889800035567467)
      ·
        refine ⟨27108781088834700053351201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18072520725889800035567467 27108781088834700053351201)
        ·
          refine ⟨20331585816626025040013401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27108781088834700053351201 20331585816626025040013401)
          ·
            refine ⟨15248689362469518780010051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20331585816626025040013401 15248689362469518780010051)
            ·
              refine ⟨22873034043704278170015077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15248689362469518780010051 22873034043704278170015077)
              ·
                refine ⟨4288693883194552156877827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22873034043704278170015077 4288693883194552156877827)
                ·
                  refine ⟨6433040824791828235316741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288693883194552156877827 6433040824791828235316741)
                  ·
                    refine ⟨1206195154648467794121889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433040824791828235316741 1206195154648467794121889)
                    ·
                      rfl

theorem cell22_3523585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3523585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523585 prefixEnd_3523585 := by exact prefixLift 3523585
  have htrace : WordTrace (prefixWord ++ tailWord_3523585) baseStart_3523585 baseEnd_3523585 := by
    simpa [prefixWord, tailWord_3523585, baseEnd_3523585] using wordTrace_append hprefix tailTrace_3523585
  have hstable : (prefixWord ++ tailWord_3523585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523585).length < 2 ^ (prefixWord ++ tailWord_3523585).sum := by decide
  have hdescent : baseEnd_3523585 < baseStart_3523585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523615 : List Nat := [1, 1, 2, 4, 1, 3, 2, 1, 4, 3]
def baseStart_3523615 : Nat := 118140960795 + 3523615 * 2 ^ 59
def prefixEnd_3523615 : Nat := 4983230072969 + 3 ^ 40 * 3523615 * 2
def baseEnd_3523615 : Nat := 1206205424261557715871797

theorem tailTrace_3523615 : CollatzResearch.WordTrace tailWord_3523615 prefixEnd_3523615 1206205424261557715871797 := by
  unfold tailWord_3523615
  simp only [CollatzResearch.WordTrace]
  refine ⟨128516797129552115376516299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85677864753034743584344199 128516797129552115376516299)
  ·
    refine ⟨192775195694328173064774449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128516797129552115376516299 192775195694328173064774449)
    ·
      refine ⟨144581396770746129798580837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 192775195694328173064774449 144581396770746129798580837)
      ·
        refine ⟨27109011894514899337233907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144581396770746129798580837 27109011894514899337233907)
        ·
          refine ⟨40663517841772349005850861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27109011894514899337233907 40663517841772349005850861)
          ·
            refine ⟨15248819190664630877194073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40663517841772349005850861 15248819190664630877194073)
            ·
              refine ⟨11436614392998473157895555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15248819190664630877194073 11436614392998473157895555)
              ·
                refine ⟨17154921589497709736843333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11436614392998473157895555 17154921589497709736843333)
                ·
                  refine ⟨3216547798030820575658125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17154921589497709736843333 3216547798030820575658125)
                  ·
                    refine ⟨1206205424261557715871797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216547798030820575658125 1206205424261557715871797)
                    ·
                      rfl

theorem cell22_3523615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_3523615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523615 prefixEnd_3523615 := by exact prefixLift 3523615
  have htrace : WordTrace (prefixWord ++ tailWord_3523615) baseStart_3523615 baseEnd_3523615 := by
    simpa [prefixWord, tailWord_3523615, baseEnd_3523615] using wordTrace_append hprefix tailTrace_3523615
  have hstable : (prefixWord ++ tailWord_3523615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523615).length < 2 ^ (prefixWord ++ tailWord_3523615).sum := by decide
  have hdescent : baseEnd_3523615 < baseStart_3523615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523628 : List Nat := [2, 2, 1, 1, 1, 2, 6, 7]
def baseStart_3523628 : Nat := 118140960795 + 3523628 * 2 ^ 59
def prefixEnd_3523628 : Nat := 4983230072969 + 3 ^ 40 * 3523628 * 2
def baseEnd_3523628 : Nat := 134023319380803335032973

theorem tailTrace_3523628 : CollatzResearch.WordTrace tailWord_3523628 prefixEnd_3523628 134023319380803335032973 := by
  unfold tailWord_3523628
  simp only [CollatzResearch.WordTrace]
  refine ⟨64258635639252509298369769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85678180852336679064493025 64258635639252509298369769)
  ·
    refine ⟨48193976729439381973777327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64258635639252509298369769 48193976729439381973777327)
    ·
      refine ⟨72290965094159072960665991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48193976729439381973777327 72290965094159072960665991)
      ·
        refine ⟨108436447641238609440998987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72290965094159072960665991 108436447641238609440998987)
        ·
          refine ⟨162654671461857914161498481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108436447641238609440998987 162654671461857914161498481)
          ·
            refine ⟨121991003596393435621123861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162654671461857914161498481 121991003596393435621123861)
            ·
              refine ⟨5718328293580942294740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 121991003596393435621123861 5718328293580942294740181)
              ·
                refine ⟨134023319380803335032973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5718328293580942294740181 134023319380803335032973)
                ·
                  rfl

theorem cell22_3523628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_3523628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523628 prefixEnd_3523628 := by exact prefixLift 3523628
  have htrace : WordTrace (prefixWord ++ tailWord_3523628) baseStart_3523628 baseEnd_3523628 := by
    simpa [prefixWord, tailWord_3523628, baseEnd_3523628] using wordTrace_append hprefix tailTrace_3523628
  have hstable : (prefixWord ++ tailWord_3523628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523628).length < 2 ^ (prefixWord ++ tailWord_3523628).sum := by decide
  have hdescent : baseEnd_3523628 < baseStart_3523628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523630 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3523630 : Nat := 118140960795 + 3523630 * 2 ^ 59
def prefixEnd_3523630 : Nat := 4983230072969 + 3 ^ 40 * 3523630 * 2
def baseEnd_3523630 : Nat := 1206210559068102676746751

theorem tailTrace_3523630 : CollatzResearch.WordTrace tailWord_3523630 prefixEnd_3523630 1206210559068102676746751 := by
  unfold tailWord_3523630
  simp only [CollatzResearch.WordTrace]
  refine ⟨16064668028062221617289043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85678229482998515292208229 16064668028062221617289043)
  ·
    refine ⟨24097002042093332425933565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16064668028062221617289043 24097002042093332425933565)
    ·
      refine ⟨9036375765784999659725087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24097002042093332425933565 9036375765784999659725087)
      ·
        refine ⟨13554563648677499489587631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9036375765784999659725087 13554563648677499489587631)
        ·
          refine ⟨20331845473016249234381447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13554563648677499489587631 20331845473016249234381447)
          ·
            refine ⟨30497768209524373851572171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20331845473016249234381447 30497768209524373851572171)
            ·
              refine ⟨45746652314286560777358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30497768209524373851572171 45746652314286560777358257)
              ·
                refine ⟨34309989235714920583018693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45746652314286560777358257 34309989235714920583018693)
                ·
                  refine ⟨6433122981696547609316005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34309989235714920583018693 6433122981696547609316005)
                  ·
                    refine ⟨1206210559068102676746751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433122981696547609316005 1206210559068102676746751)
                    ·
                      rfl

theorem cell22_3523630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3523630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523630 prefixEnd_3523630 := by exact prefixLift 3523630
  have htrace : WordTrace (prefixWord ++ tailWord_3523630) baseStart_3523630 baseEnd_3523630 := by
    simpa [prefixWord, tailWord_3523630, baseEnd_3523630] using wordTrace_append hprefix tailTrace_3523630
  have hstable : (prefixWord ++ tailWord_3523630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523630).length < 2 ^ (prefixWord ++ tailWord_3523630).sum := by decide
  have hdescent : baseEnd_3523630 < baseStart_3523630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523735 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 6]
def baseStart_3523735 : Nat := 118140960795 + 3523735 * 2 ^ 59
def prefixEnd_3523735 : Nat := 4983230072969 + 3 ^ 40 * 3523735 * 2
def baseEnd_3523735 : Nat := 402082167571305800957143

theorem tailTrace_3523735 : CollatzResearch.WordTrace tailWord_3523735 prefixEnd_3523735 402082167571305800957143 := by
  unfold tailWord_3523735
  simp only [CollatzResearch.WordTrace]
  refine ⟨128521173889117375870884659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85680782592744917247256439 128521173889117375870884659)
  ·
    refine ⟨192781760833676063806326989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128521173889117375870884659 192781760833676063806326989)
    ·
      refine ⟨72293160312628523927372621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 192781760833676063806326989 72293160312628523927372621)
      ·
        refine ⟨27109935117235696472764733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72293160312628523927372621 27109935117235696472764733)
        ·
          refine ⟨10166225668963386177286775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27109935117235696472764733 10166225668963386177286775)
          ·
            refine ⟨15249338503445079265930163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166225668963386177286775 15249338503445079265930163)
            ·
              refine ⟨22874007755167618898895245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249338503445079265930163 22874007755167618898895245)
              ·
                refine ⟨8577752908187857087085717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22874007755167618898895245 8577752908187857087085717)
                ·
                  refine ⟨402082167571305800957143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8577752908187857087085717 402082167571305800957143)
                  ·
                    rfl

theorem cell22_3523735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 6].length) (baseStart_3523735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523735 prefixEnd_3523735 := by exact prefixLift 3523735
  have htrace : WordTrace (prefixWord ++ tailWord_3523735) baseStart_3523735 baseEnd_3523735 := by
    simpa [prefixWord, tailWord_3523735, baseEnd_3523735] using wordTrace_append hprefix tailTrace_3523735
  have hstable : (prefixWord ++ tailWord_3523735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523735).length < 2 ^ (prefixWord ++ tailWord_3523735).sum := by decide
  have hdescent : baseEnd_3523735 < baseStart_3523735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523754 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3523754 : Nat := 118140960795 + 3523754 * 2 ^ 59
def prefixEnd_3523754 : Nat := 4983230072969 + 3 ^ 40 * 3523754 * 2
def baseEnd_3523754 : Nat := 1206253006802207686646371

theorem tailTrace_3523754 : CollatzResearch.WordTrace tailWord_3523754 prefixEnd_3523754 1206253006802207686646371 := by
  unfold tailWord_3523754
  simp only [CollatzResearch.WordTrace]
  refine ⟨32130466719012135528956579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85681244584032361410550877 32130466719012135528956579)
  ·
    refine ⟨48195700078518203293434869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32130466719012135528956579 48195700078518203293434869)
    ·
      refine ⟨4518346882361081558759519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48195700078518203293434869 4518346882361081558759519)
      ·
        refine ⟨6777520323541622338139279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518346882361081558759519 6777520323541622338139279)
        ·
          refine ⟨10166280485312433507208919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777520323541622338139279 10166280485312433507208919)
          ·
            refine ⟨15249420727968650260813379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10166280485312433507208919 15249420727968650260813379)
            ·
              refine ⟨22874131091952975391220069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15249420727968650260813379 22874131091952975391220069)
              ·
                refine ⟨4288899579741182885853763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22874131091952975391220069 4288899579741182885853763)
                ·
                  refine ⟨6433349369611774328780645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4288899579741182885853763 6433349369611774328780645)
                  ·
                    refine ⟨1206253006802207686646371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433349369611774328780645 1206253006802207686646371)
                    ·
                      rfl

theorem cell22_3523754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3523754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523754 prefixEnd_3523754 := by exact prefixLift 3523754
  have htrace : WordTrace (prefixWord ++ tailWord_3523754) baseStart_3523754 baseEnd_3523754 := by
    simpa [prefixWord, tailWord_3523754, baseEnd_3523754] using wordTrace_append hprefix tailTrace_3523754
  have hstable : (prefixWord ++ tailWord_3523754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523754).length < 2 ^ (prefixWord ++ tailWord_3523754).sum := by decide
  have hdescent : baseEnd_3523754 < baseStart_3523754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523769 : List Nat := [1, 2, 1, 4, 1, 5, 1, 3, 4]
def baseStart_3523769 : Nat := 118140960795 + 3523769 * 2 ^ 59
def prefixEnd_3523769 : Nat := 4983230072969 + 3 ^ 40 * 3523769 * 2
def baseEnd_3523769 : Nat := 402086047202917549173775

theorem tailTrace_3523769 : CollatzResearch.WordTrace tailWord_3523769 prefixEnd_3523769 402086047202917549173775 := by
  unfold tailWord_3523769
  simp only [CollatzResearch.WordTrace]
  refine ⟨128522413970994199677622361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85681609313996133118414907 128522413970994199677622361)
  ·
    refine ⟨96391810478245649758216771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128522413970994199677622361 96391810478245649758216771)
    ·
      refine ⟨144587715717368474637325157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96391810478245649758216771 144587715717368474637325157)
      ·
        refine ⟨27110196697006588994498467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144587715717368474637325157 27110196697006588994498467)
        ·
          refine ⟨40665295045509883491747701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27110196697006588994498467 40665295045509883491747701)
          ·
            refine ⟨3812371410516551577351347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40665295045509883491747701 3812371410516551577351347)
            ·
              refine ⟨5718557115774827366027021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812371410516551577351347 5718557115774827366027021)
              ·
                refine ⟨2144458918415560262260133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5718557115774827366027021 2144458918415560262260133)
                ·
                  refine ⟨402086047202917549173775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144458918415560262260133 402086047202917549173775)
                  ·
                    rfl

theorem cell22_3523769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 4].length) (baseStart_3523769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523769 prefixEnd_3523769 := by exact prefixLift 3523769
  have htrace : WordTrace (prefixWord ++ tailWord_3523769) baseStart_3523769 baseEnd_3523769 := by
    simpa [prefixWord, tailWord_3523769, baseEnd_3523769] using wordTrace_append hprefix tailTrace_3523769
  have hstable : (prefixWord ++ tailWord_3523769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523769).length < 2 ^ (prefixWord ++ tailWord_3523769).sum := by decide
  have hdescent : baseEnd_3523769 < baseStart_3523769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523797 : List Nat := [1, 3, 2, 4, 1, 2, 2, 7]
def baseStart_3523797 : Nat := 118140960795 + 3523797 * 2 ^ 59
def prefixEnd_3523797 : Nat := 4983230072969 + 3 ^ 40 * 3523797 * 2
def baseEnd_3523797 : Nat := 134029747397885545313471

theorem tailTrace_3523797 : CollatzResearch.WordTrace tailWord_3523797 prefixEnd_3523797 134029747397885545313471 := by
  unfold tailWord_3523797
  simp only [CollatzResearch.WordTrace]
  refine ⟨128523435214892760459641645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85682290143261840306427763 128523435214892760459641645)
  ·
    refine ⟨48196288205584785172365617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128523435214892760459641645 48196288205584785172365617)
    ·
      refine ⟨36147216154188588879274213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48196288205584785172365617 36147216154188588879274213)
      ·
        refine ⟨6777603028910360414863915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36147216154188588879274213 6777603028910360414863915)
        ·
          refine ⟨10166404543365540622295873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777603028910360414863915 10166404543365540622295873)
          ·
            refine ⟨7624803407524155466721905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10166404543365540622295873 7624803407524155466721905)
            ·
              refine ⟨5718602555643116600041429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7624803407524155466721905 5718602555643116600041429)
              ·
                refine ⟨134029747397885545313471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5718602555643116600041429 134029747397885545313471)
                ·
                  rfl

theorem cell22_3523797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 7].length) (baseStart_3523797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523797 prefixEnd_3523797 := by exact prefixLift 3523797
  have htrace : WordTrace (prefixWord ++ tailWord_3523797) baseStart_3523797 baseEnd_3523797 := by
    simpa [prefixWord, tailWord_3523797, baseEnd_3523797] using wordTrace_append hprefix tailTrace_3523797
  have hstable : (prefixWord ++ tailWord_3523797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523797).length < 2 ^ (prefixWord ++ tailWord_3523797).sum := by decide
  have hdescent : baseEnd_3523797 < baseStart_3523797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523812 : List Nat := [2, 3, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3523812 : Nat := 118140960795 + 3523812 * 2 ^ 59
def prefixEnd_3523812 : Nat := 4983230072969 + 3 ^ 40 * 3523812 * 2
def baseEnd_3523812 : Nat := 1206272861387514868696193

theorem tailTrace_3523812 : CollatzResearch.WordTrace tailWord_3523812 prefixEnd_3523812 1206272861387514868696193 := by
  unfold tailWord_3523812
  simp only [CollatzResearch.WordTrace]
  refine ⟨64261991154919209010718845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85682654873225612014291793 64261991154919209010718845)
  ·
    refine ⟨24098246683094703379019567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64261991154919209010718845 24098246683094703379019567)
    ·
      refine ⟨36147370024642055068529351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24098246683094703379019567 36147370024642055068529351)
      ·
        refine ⟨54221055036963082602794027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36147370024642055068529351 54221055036963082602794027)
        ·
          refine ⟨81331582555444623904191041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54221055036963082602794027 81331582555444623904191041)
          ·
            refine ⟨60998686916583467928143281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81331582555444623904191041 60998686916583467928143281)
            ·
              refine ⟨45749015187437600946107461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60998686916583467928143281 45749015187437600946107461)
              ·
                refine ⟨8577940347644550177395149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45749015187437600946107461 8577940347644550177395149)
                ·
                  refine ⟨3216727630366706316523181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8577940347644550177395149 3216727630366706316523181)
                  ·
                    refine ⟨1206272861387514868696193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3216727630366706316523181 1206272861387514868696193)
                    ·
                      rfl

theorem cell22_3523812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3523812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523812 prefixEnd_3523812 := by exact prefixLift 3523812
  have htrace : WordTrace (prefixWord ++ tailWord_3523812) baseStart_3523812 baseEnd_3523812 := by
    simpa [prefixWord, tailWord_3523812, baseEnd_3523812] using wordTrace_append hprefix tailTrace_3523812
  have hstable : (prefixWord ++ tailWord_3523812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523812).length < 2 ^ (prefixWord ++ tailWord_3523812).sum := by decide
  have hdescent : baseEnd_3523812 < baseStart_3523812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523840 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_3523840 : Nat := 118140960795 + 3523840 * 2 ^ 59
def prefixEnd_3523840 : Nat := 4983230072969 + 3 ^ 40 * 3523840 * 2
def baseEnd_3523840 : Nat := 1206282446359732128996107

theorem tailTrace_3523840 : CollatzResearch.WordTrace tailWord_3523840 prefixEnd_3523840 1206282446359732128996107 := by
  unfold tailWord_3523840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64262501776868489401728487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85683335702491319202304649 64262501776868489401728487)
  ·
    refine ⟨96393752665302734102592731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64262501776868489401728487 96393752665302734102592731)
    ·
      refine ⟨144590628997954101153889097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96393752665302734102592731 144590628997954101153889097)
      ·
        refine ⟨108442971748465575865416823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144590628997954101153889097 108442971748465575865416823)
        ·
          refine ⟨162664457622698363798125235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108442971748465575865416823 162664457622698363798125235)
          ·
            refine ⟨243996686434047545697187853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162664457622698363798125235 243996686434047545697187853)
            ·
              refine ⟨91498757412767829636445445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 243996686434047545697187853 91498757412767829636445445)
              ·
                refine ⟨17156017014893968056833521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91498757412767829636445445 17156017014893968056833521)
                ·
                  refine ⟨12867012761170476042625141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17156017014893968056833521 12867012761170476042625141)
                  ·
                    refine ⟨1206282446359732128996107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12867012761170476042625141 1206282446359732128996107)
                    ·
                      rfl

theorem cell22_3523840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_3523840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523840 prefixEnd_3523840 := by exact prefixLift 3523840
  have htrace : WordTrace (prefixWord ++ tailWord_3523840) baseStart_3523840 baseEnd_3523840 := by
    simpa [prefixWord, tailWord_3523840, baseEnd_3523840] using wordTrace_append hprefix tailTrace_3523840
  have hstable : (prefixWord ++ tailWord_3523840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523840).length < 2 ^ (prefixWord ++ tailWord_3523840).sum := by decide
  have hdescent : baseEnd_3523840 < baseStart_3523840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523889 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3523889 : Nat := 118140960795 + 3523889 * 2 ^ 59
def prefixEnd_3523889 : Nat := 4983230072969 + 3 ^ 40 * 3523889 * 2
def baseEnd_3523889 : Nat := 1206299220061112334520957

theorem tailTrace_3523889 : CollatzResearch.WordTrace tailWord_3523889 prefixEnd_3523889 1206299220061112334520957 := by
  unfold tailWord_3523889
  simp only [CollatzResearch.WordTrace]
  refine ⟨128526790730559460171990721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85684527153706306781327147 128526790730559460171990721)
  ·
    refine ⟨96395093047919595128993041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128526790730559460171990721 96395093047919595128993041)
    ·
      refine ⟨72296319785939696346744781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96395093047919595128993041 72296319785939696346744781)
      ·
        refine ⟨27111119919727386130029293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72296319785939696346744781 27111119919727386130029293)
        ·
          refine ⟨10166669969897769798760985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27111119919727386130029293 10166669969897769798760985)
          ·
            refine ⟨7625002477423327349070739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10166669969897769798760985 7625002477423327349070739)
            ·
              refine ⟨11437503716134991023606109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7625002477423327349070739 11437503716134991023606109)
              ·
                refine ⟨4289063893550621633852291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11437503716134991023606109 4289063893550621633852291)
                ·
                  refine ⟨6433595840325932450778437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4289063893550621633852291 6433595840325932450778437)
                  ·
                    refine ⟨1206299220061112334520957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6433595840325932450778437 1206299220061112334520957)
                    ·
                      rfl

theorem cell22_3523889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3523889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523889 prefixEnd_3523889 := by exact prefixLift 3523889
  have htrace : WordTrace (prefixWord ++ tailWord_3523889) baseStart_3523889 baseEnd_3523889 := by
    simpa [prefixWord, tailWord_3523889, baseEnd_3523889] using wordTrace_append hprefix tailTrace_3523889
  have hstable : (prefixWord ++ tailWord_3523889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523889).length < 2 ^ (prefixWord ++ tailWord_3523889).sum := by decide
  have hdescent : baseEnd_3523889 < baseStart_3523889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3523910 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3523910 : Nat := 118140960795 + 3523910 * 2 ^ 59
def prefixEnd_3523910 : Nat := 4983230072969 + 3 ^ 40 * 3523910 * 2
def baseEnd_3523910 : Nat := 402102136263425093248631

theorem tailTrace_3523910 : CollatzResearch.WordTrace tailWord_3523910 prefixEnd_3523910 402102136263425093248631 := by
  unfold tailWord_3523910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016486145733855648703287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85685037775655587172336789 4016486145733855648703287)
  ·
    refine ⟨6024729218600783473054931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4016486145733855648703287 6024729218600783473054931)
    ·
      refine ⟨9037093827901175209582397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6024729218600783473054931 9037093827901175209582397)
      ·
        refine ⟨3388910185462940703593399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9037093827901175209582397 3388910185462940703593399)
        ·
          refine ⟨5083365278194411055390099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388910185462940703593399 5083365278194411055390099)
          ·
            refine ⟨7625047917291616583085149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5083365278194411055390099 7625047917291616583085149)
            ·
              refine ⟨2859392968984356218656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7625047917291616583085149 2859392968984356218656931)
              ·
                refine ⟨4289089453476534327985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2859392968984356218656931 4289089453476534327985397)
                ·
                  refine ⟨402102136263425093248631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4289089453476534327985397 402102136263425093248631)
                  ·
                    rfl

theorem cell22_3523910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3523910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3523910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3523910 prefixEnd_3523910 := by exact prefixLift 3523910
  have htrace : WordTrace (prefixWord ++ tailWord_3523910) baseStart_3523910 baseEnd_3523910 := by
    simpa [prefixWord, tailWord_3523910, baseEnd_3523910] using wordTrace_append hprefix tailTrace_3523910
  have hstable : (prefixWord ++ tailWord_3523910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3523910).length < 2 ^ (prefixWord ++ tailWord_3523910).sum := by decide
  have hdescent : baseEnd_3523910 < baseStart_3523910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3523910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
