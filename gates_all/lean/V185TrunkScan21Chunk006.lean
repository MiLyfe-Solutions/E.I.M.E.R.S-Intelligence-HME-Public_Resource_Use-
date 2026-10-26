import V185TrunkScan21Chunk005

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_72796 : List Nat := [2, 2, 4, 1, 1, 1, 5, 5]
def baseStart_72796 : Nat := 118140960795 + 72796 * 2 ^ 59
def prefixEnd_72796 : Nat := 4983230072969 + 3 ^ 40 * 72796 * 2
def baseEnd_72796 : Nat := 5537679662933691705959

theorem tailTrace_72796 : CollatzResearch.WordTrace tailWord_72796 prefixEnd_72796 5537679662933691705959 := by
  unfold tailWord_72796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327544122139999706051121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1770058829519999608068161 1327544122139999706051121)
  ·
    refine ⟨995658091604999779538341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1327544122139999706051121 995658091604999779538341)
    ·
      refine ⟨186685892175937458663439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 995658091604999779538341 186685892175937458663439)
      ·
        refine ⟨280028838263906187995159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186685892175937458663439 280028838263906187995159)
        ·
          refine ⟨420043257395859281992739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280028838263906187995159 420043257395859281992739)
          ·
            refine ⟨630064886093788922989109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420043257395859281992739 630064886093788922989109)
            ·
              refine ⟨59068583071292711530229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 630064886093788922989109 59068583071292711530229)
              ·
                refine ⟨5537679662933691705959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59068583071292711530229 5537679662933691705959)
                ·
                  rfl

theorem cell21_72796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_72796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72796 prefixEnd_72796 := by exact prefixLift 72796
  have htrace : WordTrace (prefixWord ++ tailWord_72796) baseStart_72796 baseEnd_72796 := by
    simpa [prefixWord, tailWord_72796, baseEnd_72796] using wordTrace_append hprefix tailTrace_72796
  have hstable : (prefixWord ++ tailWord_72796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72796).length < 2 ^ (prefixWord ++ tailWord_72796).sum := by decide
  have hdescent : baseEnd_72796 < baseStart_72796 := by decide
  rcases family_descends (prefixWord ++ tailWord_72796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72855 : List Nat := [1, 1, 3, 3, 3, 2, 1, 7]
def baseStart_72855 : Nat := 118140960795 + 72855 * 2 ^ 59
def prefixEnd_72855 : Nat := 4983230072969 + 3 ^ 40 * 72855 * 2
def baseEnd_72855 : Nat := 5542167864210027878141

theorem tailTrace_72855 : CollatzResearch.WordTrace tailWord_72855 prefixEnd_72855 5542167864210027878141 := by
  unfold tailWord_72855
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657240151066252488500019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1771493434044168325666679 2657240151066252488500019)
  ·
    refine ⟨3985860226599378732750029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2657240151066252488500019 3985860226599378732750029)
    ·
      refine ⟨1494697584974767024781261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3985860226599378732750029 1494697584974767024781261)
      ·
        refine ⟨560511594365537634292973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1494697584974767024781261 560511594365537634292973)
        ·
          refine ⟨210191847887076612859865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 560511594365537634292973 210191847887076612859865)
          ·
            refine ⟨157643885915307459644899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210191847887076612859865 157643885915307459644899)
            ·
              refine ⟨236465828872961189467349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157643885915307459644899 236465828872961189467349)
              ·
                refine ⟨5542167864210027878141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 236465828872961189467349 5542167864210027878141)
                ·
                  rfl

theorem cell21_72855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 7].length) (baseStart_72855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72855 prefixEnd_72855 := by exact prefixLift 72855
  have htrace : WordTrace (prefixWord ++ tailWord_72855) baseStart_72855 baseEnd_72855 := by
    simpa [prefixWord, tailWord_72855, baseEnd_72855] using wordTrace_append hprefix tailTrace_72855
  have hstable : (prefixWord ++ tailWord_72855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72855).length < 2 ^ (prefixWord ++ tailWord_72855).sum := by decide
  have hdescent : baseEnd_72855 < baseStart_72855 := by decide
  rcases family_descends (prefixWord ++ tailWord_72855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_72945 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 5]
def baseStart_72945 : Nat := 118140960795 + 72945 * 2 ^ 59
def prefixEnd_72945 : Nat := 4983230072969 + 3 ^ 40 * 72945 * 2
def baseEnd_72945 : Nat := 16647042818809927134239

theorem tailTrace_72945 : CollatzResearch.WordTrace tailWord_72945 prefixEnd_72945 16647042818809927134239 := by
  unfold tailWord_72945
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660522720740197859276289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1773681813826798572850859 2660522720740197859276289)
  ·
    refine ⟨1995392040555148394457217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660522720740197859276289 1995392040555148394457217)
    ·
      refine ⟨1496544030416361295842913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1995392040555148394457217 1496544030416361295842913)
      ·
        refine ⟨1122408022812270971882185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496544030416361295842913 1122408022812270971882185)
        ·
          refine ⟨841806017109203228911639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1122408022812270971882185 841806017109203228911639)
          ·
            refine ⟨1262709025663804843367459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 841806017109203228911639 1262709025663804843367459)
            ·
              refine ⟨1894063538495707265051189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1262709025663804843367459 1894063538495707265051189)
              ·
                refine ⟨177568456733972556098549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1894063538495707265051189 177568456733972556098549)
                ·
                  refine ⟨16647042818809927134239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 177568456733972556098549 16647042818809927134239)
                  ·
                    rfl

theorem cell21_72945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_72945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_72945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_72945 prefixEnd_72945 := by exact prefixLift 72945
  have htrace : WordTrace (prefixWord ++ tailWord_72945) baseStart_72945 baseEnd_72945 := by
    simpa [prefixWord, tailWord_72945, baseEnd_72945] using wordTrace_append hprefix tailTrace_72945
  have hstable : (prefixWord ++ tailWord_72945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_72945).length < 2 ^ (prefixWord ++ tailWord_72945).sum := by decide
  have hdescent : baseEnd_72945 < baseStart_72945 := by decide
  rcases family_descends (prefixWord ++ tailWord_72945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73010 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_73010 : Nat := 118140960795 + 73010 * 2 ^ 59
def prefixEnd_73010 : Nat := 4983230072969 + 3 ^ 40 * 73010 * 2
def baseEnd_73010 : Nat := 16661876704384258550773

theorem tailTrace_73010 : CollatzResearch.WordTrace tailWord_73010 prefixEnd_73010 16661876704384258550773 := by
  unfold tailWord_73010
  simp only [CollatzResearch.WordTrace]
  refine ⟨665723366376178490098121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1775262310336475973594989 665723366376178490098121)
  ·
    refine ⟨499292524782133867573591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665723366376178490098121 499292524782133867573591)
    ·
      refine ⟨748938787173200801360387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499292524782133867573591 748938787173200801360387)
      ·
        refine ⟨1123408180759801202040581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 748938787173200801360387 1123408180759801202040581)
        ·
          refine ⟨210639033892462725382609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1123408180759801202040581 210639033892462725382609)
          ·
            refine ⟨157979275419347044036957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210639033892462725382609 157979275419347044036957)
            ·
              refine ⟨59242228282255141513859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157979275419347044036957 59242228282255141513859)
              ·
                refine ⟨88863342423382712270789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59242228282255141513859 88863342423382712270789)
                ·
                  refine ⟨16661876704384258550773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88863342423382712270789 16661876704384258550773)
                  ·
                    rfl

theorem cell21_73010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_73010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73010 prefixEnd_73010 := by exact prefixLift 73010
  have htrace : WordTrace (prefixWord ++ tailWord_73010) baseStart_73010 baseEnd_73010 := by
    simpa [prefixWord, tailWord_73010, baseEnd_73010] using wordTrace_append hprefix tailTrace_73010
  have hstable : (prefixWord ++ tailWord_73010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73010).length < 2 ^ (prefixWord ++ tailWord_73010).sum := by decide
  have hdescent : baseEnd_73010 < baseStart_73010 := by decide
  rcases family_descends (prefixWord ++ tailWord_73010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73069 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 4]
def baseStart_73069 : Nat := 118140960795 + 73069 * 2 ^ 59
def prefixEnd_73069 : Nat := 4983230072969 + 3 ^ 40 * 73069 * 2
def baseEnd_73069 : Nat := 16675341308213267067319

theorem tailTrace_73069 : CollatzResearch.WordTrace tailWord_73069 prefixEnd_73069 16675341308213267067319 := by
  unfold tailWord_73069
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665045372290967036790261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1776696914860644691193507 2665045372290967036790261)
  ·
    refine ⟨249848003652278159699087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2665045372290967036790261 249848003652278159699087)
    ·
      refine ⟨374772005478417239548631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 249848003652278159699087 374772005478417239548631)
      ·
        refine ⟨562158008217625859322947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 374772005478417239548631 562158008217625859322947)
        ·
          refine ⟨843237012326438788984421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 562158008217625859322947 843237012326438788984421)
          ·
            refine ⟨158106939811207272934579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 843237012326438788984421 158106939811207272934579)
            ·
              refine ⟨237160409716810909401869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158106939811207272934579 237160409716810909401869)
              ·
                refine ⟨88935153643804091025701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237160409716810909401869 88935153643804091025701)
                ·
                  refine ⟨16675341308213267067319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88935153643804091025701 16675341308213267067319)
                  ·
                    rfl

theorem cell21_73069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_73069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73069 prefixEnd_73069 := by exact prefixLift 73069
  have htrace : WordTrace (prefixWord ++ tailWord_73069) baseStart_73069 baseEnd_73069 := by
    simpa [prefixWord, tailWord_73069, baseEnd_73069] using wordTrace_append hprefix tailTrace_73069
  have hstable : (prefixWord ++ tailWord_73069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73069).length < 2 ^ (prefixWord ++ tailWord_73069).sum := by decide
  have hdescent : baseEnd_73069 < baseStart_73069 := by decide
  rcases family_descends (prefixWord ++ tailWord_73069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73106 : List Nat := [3, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_73106 : Nat := 118140960795 + 73106 * 2 ^ 59
def prefixEnd_73106 : Nat := 4983230072969 + 3 ^ 40 * 73106 * 2
def baseEnd_73106 : Nat := 16683785212309424950577

theorem tailTrace_73106 : CollatzResearch.WordTrace tailWord_73106 prefixEnd_73106 16683785212309424950577 := by
  unfold tailWord_73106
  simp only [CollatzResearch.WordTrace]
  refine ⟨666598718289230588971793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1777596582104614903924781 666598718289230588971793)
  ·
    refine ⟨499949038716922941728845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 666598718289230588971793 499949038716922941728845)
    ·
      refine ⟨187480889518846103148317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 499949038716922941728845 187480889518846103148317)
      ·
        refine ⟨70305333569567288680619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187480889518846103148317 70305333569567288680619)
        ·
          refine ⟨105458000354350933020929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70305333569567288680619 105458000354350933020929)
          ·
            refine ⟨79093500265763199765697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105458000354350933020929 79093500265763199765697)
            ·
              refine ⟨59320125199322399824273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79093500265763199765697 59320125199322399824273)
              ·
                refine ⟨44490093899491799868205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59320125199322399824273 44490093899491799868205)
                ·
                  refine ⟨16683785212309424950577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44490093899491799868205 16683785212309424950577)
                  ·
                    rfl

theorem cell21_73106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_73106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73106 prefixEnd_73106 := by exact prefixLift 73106
  have htrace : WordTrace (prefixWord ++ tailWord_73106) baseStart_73106 baseEnd_73106 := by
    simpa [prefixWord, tailWord_73106, baseEnd_73106] using wordTrace_append hprefix tailTrace_73106
  have hstable : (prefixWord ++ tailWord_73106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73106).length < 2 ^ (prefixWord ++ tailWord_73106).sum := by decide
  have hdescent : baseEnd_73106 < baseStart_73106 := by decide
  rcases family_descends (prefixWord ++ tailWord_73106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73148 : List Nat := [2, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_73148 : Nat := 118140960795 + 73148 * 2 ^ 59
def prefixEnd_73148 : Nat := 4983230072969 + 3 ^ 40 * 73148 * 2
def baseEnd_73148 : Nat := 16693370184526685250491

theorem tailTrace_73148 : CollatzResearch.WordTrace tailWord_73148 prefixEnd_73148 16693370184526685250491 := by
  unfold tailWord_73148
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333963369502381764458049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1778617826003175685944065 1333963369502381764458049)
  ·
    refine ⟨1000472527126786323343537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1333963369502381764458049 1000472527126786323343537)
    ·
      refine ⟨750354395345089742507653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1000472527126786323343537 750354395345089742507653)
      ·
        refine ⟨140691449127204326720185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 750354395345089742507653 140691449127204326720185)
        ·
          refine ⟨105518586845403245040139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140691449127204326720185 105518586845403245040139)
          ·
            refine ⟨158277880268104867560209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105518586845403245040139 158277880268104867560209)
            ·
              refine ⟨118708410201078650670157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158277880268104867560209 118708410201078650670157)
              ·
                refine ⟨44515653825404494001309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118708410201078650670157 44515653825404494001309)
                ·
                  refine ⟨16693370184526685250491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44515653825404494001309 16693370184526685250491)
                  ·
                    rfl

theorem cell21_73148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_73148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73148 prefixEnd_73148 := by exact prefixLift 73148
  have htrace : WordTrace (prefixWord ++ tailWord_73148) baseStart_73148 baseEnd_73148 := by
    simpa [prefixWord, tailWord_73148, baseEnd_73148] using wordTrace_append hprefix tailTrace_73148
  have hstable : (prefixWord ++ tailWord_73148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73148).length < 2 ^ (prefixWord ++ tailWord_73148).sum := by decide
  have hdescent : baseEnd_73148 < baseStart_73148 := by decide
  rcases family_descends (prefixWord ++ tailWord_73148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73154 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_73154 : Nat := 118140960795 + 73154 * 2 ^ 59
def prefixEnd_73154 : Nat := 4983230072969 + 3 ^ 40 * 73154 * 2
def baseEnd_73154 : Nat := 16694739466272008150479

theorem tailTrace_73154 : CollatzResearch.WordTrace tailWord_73154 prefixEnd_73154 16694739466272008150479 := by
  unfold tailWord_73154
  simp only [CollatzResearch.WordTrace]
  refine ⟨667036394245756638408629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1778763717988684369089677 667036394245756638408629)
  ·
    refine ⟨62534661960539684850809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 667036394245756638408629 62534661960539684850809)
    ·
      refine ⟨46900996470404763638107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62534661960539684850809 46900996470404763638107)
      ·
        refine ⟨70351494705607145457161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46900996470404763638107 70351494705607145457161)
        ·
          refine ⟨52763621029205359092871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70351494705607145457161 52763621029205359092871)
          ·
            refine ⟨79145431543808038639307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52763621029205359092871 79145431543808038639307)
            ·
              refine ⟨118718147315712057958961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79145431543808038639307 118718147315712057958961)
              ·
                refine ⟨89038610486784043469221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118718147315712057958961 89038610486784043469221)
                ·
                  refine ⟨16694739466272008150479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89038610486784043469221 16694739466272008150479)
                  ·
                    rfl

theorem cell21_73154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_73154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73154 prefixEnd_73154 := by exact prefixLift 73154
  have htrace : WordTrace (prefixWord ++ tailWord_73154) baseStart_73154 baseEnd_73154 := by
    simpa [prefixWord, tailWord_73154, baseEnd_73154] using wordTrace_append hprefix tailTrace_73154
  have hstable : (prefixWord ++ tailWord_73154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73154).length < 2 ^ (prefixWord ++ tailWord_73154).sum := by decide
  have hdescent : baseEnd_73154 < baseStart_73154 := by decide
  rcases family_descends (prefixWord ++ tailWord_73154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73266 : List Nat := [3, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_73266 : Nat := 118140960795 + 73266 * 2 ^ 59
def prefixEnd_73266 : Nat := 4983230072969 + 3 ^ 40 * 73266 * 2
def baseEnd_73266 : Nat := 16720299392184702283583

theorem tailTrace_73266 : CollatzResearch.WordTrace tailWord_73266 prefixEnd_73266 16720299392184702283583 := by
  unfold tailWord_73266
  simp only [CollatzResearch.WordTrace]
  refine ⟨668057638144317420427913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1781487035051513121141101 668057638144317420427913)
  ·
    refine ⟨501043228608238065320935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 668057638144317420427913 501043228608238065320935)
    ·
      refine ⟨751564842912357097981403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 501043228608238065320935 751564842912357097981403)
      ·
        refine ⟨1127347264368535646972105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 751564842912357097981403 1127347264368535646972105)
        ·
          refine ⟨845510448276401735229079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1127347264368535646972105 845510448276401735229079)
          ·
            refine ⟨1268265672414602602843619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 845510448276401735229079 1268265672414602602843619)
            ·
              refine ⟨1902398508621903904265429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1268265672414602602843619 1902398508621903904265429)
              ·
                refine ⟨44587465045825872756221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1902398508621903904265429 44587465045825872756221)
                ·
                  refine ⟨16720299392184702283583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44587465045825872756221 16720299392184702283583)
                  ·
                    rfl

theorem cell21_73266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_73266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73266 prefixEnd_73266 := by exact prefixLift 73266
  have htrace : WordTrace (prefixWord ++ tailWord_73266) baseStart_73266 baseEnd_73266 := by
    simpa [prefixWord, tailWord_73266, baseEnd_73266] using wordTrace_append hprefix tailTrace_73266
  have hstable : (prefixWord ++ tailWord_73266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73266).length < 2 ^ (prefixWord ++ tailWord_73266).sum := by decide
  have hdescent : baseEnd_73266 < baseStart_73266 := by decide
  rcases family_descends (prefixWord ++ tailWord_73266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73286 : List Nat := [6, 1, 1, 1, 4, 1, 1, 6]
def baseStart_73286 : Nat := 118140960795 + 73286 * 2 ^ 59
def prefixEnd_73286 : Nat := 4983230072969 + 3 ^ 40 * 73286 * 2
def baseEnd_73286 : Nat := 5574954554889703983403

theorem tailTrace_73286 : CollatzResearch.WordTrace tailWord_73286 prefixEnd_73286 5574954554889703983403 := by
  unfold tailWord_73286
  simp only [CollatzResearch.WordTrace]
  refine ⟨83530000390775409294991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1781973341669875398293141 83530000390775409294991)
  ·
    refine ⟨125295000586163113942487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83530000390775409294991 125295000586163113942487)
    ·
      refine ⟨187942500879244670913731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125295000586163113942487 187942500879244670913731)
      ·
        refine ⟨281913751318867006370597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187942500879244670913731 281913751318867006370597)
        ·
          refine ⟨52858828372287563694487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281913751318867006370597 52858828372287563694487)
          ·
            refine ⟨79288242558431345541731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52858828372287563694487 79288242558431345541731)
            ·
              refine ⟨118932363837647018312597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79288242558431345541731 118932363837647018312597)
              ·
                refine ⟨5574954554889703983403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118932363837647018312597 5574954554889703983403)
                ·
                  rfl

theorem cell21_73286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_73286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73286 prefixEnd_73286 := by exact prefixLift 73286
  have htrace : WordTrace (prefixWord ++ tailWord_73286) baseStart_73286 baseEnd_73286 := by
    simpa [prefixWord, tailWord_73286, baseEnd_73286] using wordTrace_append hprefix tailTrace_73286
  have hstable : (prefixWord ++ tailWord_73286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73286).length < 2 ^ (prefixWord ++ tailWord_73286).sum := by decide
  have hdescent : baseEnd_73286 < baseStart_73286 := by decide
  rcases family_descends (prefixWord ++ tailWord_73286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73339 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 6]
def baseStart_73339 : Nat := 118140960795 + 73339 * 2 ^ 59
def prefixEnd_73339 : Nat := 4983230072969 + 3 ^ 40 * 73339 * 2
def baseEnd_73339 : Nat := 16736958986752797566767

theorem tailTrace_73339 : CollatzResearch.WordTrace tailWord_73339 prefixEnd_73339 16736958986752797566767 := by
  unfold tailWord_73339
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674893081312803149119071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1783262054208535432746047 2674893081312803149119071)
  ·
    refine ⟨4012339621969204723678607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2674893081312803149119071 4012339621969204723678607)
    ·
      refine ⟨6018509432953807085517911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4012339621969204723678607 6018509432953807085517911)
      ·
        refine ⟨9027764149430710628276867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6018509432953807085517911 9027764149430710628276867)
        ·
          refine ⟨13541646224146065942415301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9027764149430710628276867 13541646224146065942415301)
          ·
            refine ⟨2539058667027387364202869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13541646224146065942415301 2539058667027387364202869)
            ·
              refine ⟨238036750033817565394019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2539058667027387364202869 238036750033817565394019)
              ·
                refine ⟨357055125050726348091029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238036750033817565394019 357055125050726348091029)
                ·
                  refine ⟨16736958986752797566767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357055125050726348091029 16736958986752797566767)
                  ·
                    rfl

theorem cell21_73339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 6].length) (baseStart_73339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73339 prefixEnd_73339 := by exact prefixLift 73339
  have htrace : WordTrace (prefixWord ++ tailWord_73339) baseStart_73339 baseEnd_73339 := by
    simpa [prefixWord, tailWord_73339, baseEnd_73339] using wordTrace_append hprefix tailTrace_73339
  have hstable : (prefixWord ++ tailWord_73339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73339).length < 2 ^ (prefixWord ++ tailWord_73339).sum := by decide
  have hdescent : baseEnd_73339 < baseStart_73339 := by decide
  rcases family_descends (prefixWord ++ tailWord_73339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73401 : List Nat := [1, 2, 1, 4, 1, 1, 5, 1, 5]
def baseStart_73401 : Nat := 118140960795 + 73401 * 2 ^ 59
def prefixEnd_73401 : Nat := 4983230072969 + 3 ^ 40 * 73401 * 2
def baseEnd_73401 : Nat := 16751108231454467533307

theorem tailTrace_73401 : CollatzResearch.WordTrace tailWord_73401 prefixEnd_73401 16751108231454467533307 := by
  unfold tailWord_73401
  simp only [CollatzResearch.WordTrace]
  refine ⟨2677154407088187737876057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1784769604725458491917371 2677154407088187737876057)
  ·
    refine ⟨2007865805316140803407043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2677154407088187737876057 2007865805316140803407043)
    ·
      refine ⟨3011798707974211205110565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2007865805316140803407043 3011798707974211205110565)
      ·
        refine ⟨564712257745164600958231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3011798707974211205110565 564712257745164600958231)
        ·
          refine ⟨847068386617746901437347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 564712257745164600958231 847068386617746901437347)
          ·
            refine ⟨1270602579926620352156021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 847068386617746901437347 1270602579926620352156021)
            ·
              refine ⟨119118991868120658014627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1270602579926620352156021 119118991868120658014627)
              ·
                refine ⟨178678487802180987021941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119118991868120658014627 178678487802180987021941)
                ·
                  refine ⟨16751108231454467533307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 178678487802180987021941 16751108231454467533307)
                  ·
                    rfl

theorem cell21_73401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_73401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73401 prefixEnd_73401 := by exact prefixLift 73401
  have htrace : WordTrace (prefixWord ++ tailWord_73401) baseStart_73401 baseEnd_73401 := by
    simpa [prefixWord, tailWord_73401, baseEnd_73401] using wordTrace_append hprefix tailTrace_73401
  have hstable : (prefixWord ++ tailWord_73401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73401).length < 2 ^ (prefixWord ++ tailWord_73401).sum := by decide
  have hdescent : baseEnd_73401 < baseStart_73401 := by decide
  rcases family_descends (prefixWord ++ tailWord_73401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73508 : List Nat := [2, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_73508 : Nat := 118140960795 + 73508 * 2 ^ 59
def prefixEnd_73508 : Nat := 4983230072969 + 3 ^ 40 * 73508 * 2
def baseEnd_73508 : Nat := 16775527089246059249755

theorem tailTrace_73508 : CollatzResearch.WordTrace tailWord_73508 prefixEnd_73508 16775527089246059249755 := by
  unfold tailWord_73508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340528508850272506010589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1787371345133696674680785 1340528508850272506010589)
  ·
    refine ⟨502698190818852189753971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1340528508850272506010589 502698190818852189753971)
    ·
      refine ⟨754047286228278284630957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502698190818852189753971 754047286228278284630957)
      ·
        refine ⟨282767732335604356736609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 754047286228278284630957 282767732335604356736609)
        ·
          refine ⟨212075799251703267552457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282767732335604356736609 212075799251703267552457)
          ·
            refine ⟨159056849438777450664343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212075799251703267552457 159056849438777450664343)
            ·
              refine ⟨238585274158166175996515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159056849438777450664343 238585274158166175996515)
              ·
                refine ⟨357877911237249263994773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238585274158166175996515 357877911237249263994773)
                ·
                  refine ⟨16775527089246059249755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 357877911237249263994773 16775527089246059249755)
                  ·
                    rfl

theorem cell21_73508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_73508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73508 prefixEnd_73508 := by exact prefixLift 73508
  have htrace : WordTrace (prefixWord ++ tailWord_73508) baseStart_73508 baseEnd_73508 := by
    simpa [prefixWord, tailWord_73508, baseEnd_73508] using wordTrace_append hprefix tailTrace_73508
  have hstable : (prefixWord ++ tailWord_73508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73508).length < 2 ^ (prefixWord ++ tailWord_73508).sum := by decide
  have hdescent : baseEnd_73508 < baseStart_73508 := by decide
  rcases family_descends (prefixWord ++ tailWord_73508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73539 : List Nat := [1, 1, 1, 3, 1, 7, 2, 5]
def baseStart_73539 : Nat := 118140960795 + 73539 * 2 ^ 59
def prefixEnd_73539 : Nat := 4983230072969 + 3 ^ 40 * 73539 * 2
def baseEnd_73539 : Nat := 5594200570532298077675

theorem tailTrace_73539 : CollatzResearch.WordTrace tailWord_73539 prefixEnd_73539 5594200570532298077675 := by
  unfold tailWord_73539
  simp only [CollatzResearch.WordTrace]
  refine ⟨2682187680588237306399671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1788125120392158204266447 2682187680588237306399671)
  ·
    refine ⟨4023281520882355959599507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2682187680588237306399671 4023281520882355959599507)
    ·
      refine ⟨6034922281323533939399261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4023281520882355959599507 6034922281323533939399261)
      ·
        refine ⟨2263095855496325227274723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6034922281323533939399261 2263095855496325227274723)
        ·
          refine ⟨3394643783244487840912085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2263095855496325227274723 3394643783244487840912085)
          ·
            refine ⟨79561963669792683771377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3394643783244487840912085 79561963669792683771377)
            ·
              refine ⟨59671472752344512828533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79561963669792683771377 59671472752344512828533)
              ·
                refine ⟨5594200570532298077675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59671472752344512828533 5594200570532298077675)
                ·
                  rfl

theorem cell21_73539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 5].length) (baseStart_73539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73539 prefixEnd_73539 := by exact prefixLift 73539
  have htrace : WordTrace (prefixWord ++ tailWord_73539) baseStart_73539 baseEnd_73539 := by
    simpa [prefixWord, tailWord_73539, baseEnd_73539] using wordTrace_append hprefix tailTrace_73539
  have hstable : (prefixWord ++ tailWord_73539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73539).length < 2 ^ (prefixWord ++ tailWord_73539).sum := by decide
  have hdescent : baseEnd_73539 < baseStart_73539 := by decide
  rcases family_descends (prefixWord ++ tailWord_73539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73567 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 6]
def baseStart_73567 : Nat := 118140960795 + 73567 * 2 ^ 59
def prefixEnd_73567 : Nat := 4983230072969 + 3 ^ 40 * 73567 * 2
def baseEnd_73567 : Nat := 16788991693075067766301

theorem tailTrace_73567 : CollatzResearch.WordTrace tailWord_73567 prefixEnd_73567 16788991693075067766301 := by
  unfold tailWord_73567
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683208924486798088418955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1788805949657865392279303 2683208924486798088418955)
  ·
    refine ⟨4024813386730197132628433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2683208924486798088418955 4024813386730197132628433)
    ·
      refine ⟨3018610040047647849471325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4024813386730197132628433 3018610040047647849471325)
      ·
        refine ⟨1131978765017867943551747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3018610040047647849471325 1131978765017867943551747)
        ·
          refine ⟨1697968147526801915327621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1131978765017867943551747 1697968147526801915327621)
          ·
            refine ⟨318369027661275359123929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1697968147526801915327621 318369027661275359123929)
            ·
              refine ⟨238776770745956519342947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318369027661275359123929 238776770745956519342947)
              ·
                refine ⟨358165156118934779014421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238776770745956519342947 358165156118934779014421)
                ·
                  refine ⟨16788991693075067766301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 358165156118934779014421 16788991693075067766301)
                  ·
                    rfl

theorem cell21_73567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 6].length) (baseStart_73567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73567 prefixEnd_73567 := by exact prefixLift 73567
  have htrace : WordTrace (prefixWord ++ tailWord_73567) baseStart_73567 baseEnd_73567 := by
    simpa [prefixWord, tailWord_73567, baseEnd_73567] using wordTrace_append hprefix tailTrace_73567
  have hstable : (prefixWord ++ tailWord_73567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73567).length < 2 ^ (prefixWord ++ tailWord_73567).sum := by decide
  have hdescent : baseEnd_73567 < baseStart_73567 := by decide
  rcases family_descends (prefixWord ++ tailWord_73567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73570 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_73570 : Nat := 118140960795 + 73570 * 2 ^ 59
def prefixEnd_73570 : Nat := 4983230072969 + 3 ^ 40 * 73570 * 2
def baseEnd_73570 : Nat := 16789676333947729216295

theorem tailTrace_73570 : CollatzResearch.WordTrace tailWord_73570 prefixEnd_73570 16789676333947729216295 := by
  unfold tailWord_73570
  simp only [CollatzResearch.WordTrace]
  refine ⟨670829585868982400194541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1788878895650619733852109 670829585868982400194541)
  ·
    refine ⟨251561094700868400072953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 670829585868982400194541 251561094700868400072953)
    ·
      refine ⟨188670821025651300054715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251561094700868400072953 188670821025651300054715)
      ·
        refine ⟨283006231538476950082073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188670821025651300054715 283006231538476950082073)
        ·
          refine ⟨212254673653857712561555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283006231538476950082073 212254673653857712561555)
          ·
            refine ⟨318382010480786568842333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212254673653857712561555 318382010480786568842333)
            ·
              refine ⟨119393253930294963315875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318382010480786568842333 119393253930294963315875)
              ·
                refine ⟨179089880895442444973813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119393253930294963315875 179089880895442444973813)
                ·
                  refine ⟨16789676333947729216295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179089880895442444973813 16789676333947729216295)
                  ·
                    rfl

theorem cell21_73570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_73570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73570 prefixEnd_73570 := by exact prefixLift 73570
  have htrace : WordTrace (prefixWord ++ tailWord_73570) baseStart_73570 baseEnd_73570 := by
    simpa [prefixWord, tailWord_73570, baseEnd_73570] using wordTrace_append hprefix tailTrace_73570
  have hstable : (prefixWord ++ tailWord_73570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73570).length < 2 ^ (prefixWord ++ tailWord_73570).sum := by decide
  have hdescent : baseEnd_73570 < baseStart_73570 := by decide
  rcases family_descends (prefixWord ++ tailWord_73570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73733 : List Nat := [1, 3, 1, 1, 2, 4, 9]
def baseStart_73733 : Nat := 118140960795 + 73733 * 2 ^ 59
def prefixEnd_73733 : Nat := 4983230072969 + 3 ^ 40 * 73733 * 2
def baseEnd_73733 : Nat := 1869652794966185333255

theorem tailTrace_73733 : CollatzResearch.WordTrace tailWord_73733 prefixEnd_73733 1869652794966185333255 := by
  unfold tailWord_73733
  simp only [CollatzResearch.WordTrace]
  refine ⟨2689263441885408438961853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1792842294590272292641235 2689263441885408438961853)
  ·
    refine ⟨1008473790707028164610695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2689263441885408438961853 1008473790707028164610695)
    ·
      refine ⟨1512710686060542246916043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008473790707028164610695 1512710686060542246916043)
      ·
        refine ⟨2269066029090813370374065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512710686060542246916043 2269066029090813370374065)
        ·
          refine ⟨1701799521818110027780549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2269066029090813370374065 1701799521818110027780549)
          ·
            refine ⟨319087410340895630208853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1701799521818110027780549 319087410340895630208853)
            ·
              refine ⟨1869652794966185333255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 319087410340895630208853 1869652794966185333255)
              ·
                rfl

theorem cell21_73733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 9].length) (baseStart_73733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73733 prefixEnd_73733 := by exact prefixLift 73733
  have htrace : WordTrace (prefixWord ++ tailWord_73733) baseStart_73733 baseEnd_73733 := by
    simpa [prefixWord, tailWord_73733, baseEnd_73733] using wordTrace_append hprefix tailTrace_73733
  have hstable : (prefixWord ++ tailWord_73733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73733).length < 2 ^ (prefixWord ++ tailWord_73733).sum := by decide
  have hdescent : baseEnd_73733 < baseStart_73733 := by decide
  rcases family_descends (prefixWord ++ tailWord_73733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73798 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_73798 : Nat := 118140960795 + 73798 * 2 ^ 59
def prefixEnd_73798 : Nat := 4983230072969 + 3 ^ 40 * 73798 * 2
def baseEnd_73798 : Nat := 16841709040269999415829

theorem tailTrace_73798 : CollatzResearch.WordTrace tailWord_73798 prefixEnd_73798 16841709040269999415829 := by
  unfold tailWord_73798
  simp only [CollatzResearch.WordTrace]
  refine ⟨84113568332810141877439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1794422791099949693385365 84113568332810141877439)
  ·
    refine ⟨126170352499215212816159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84113568332810141877439 126170352499215212816159)
    ·
      refine ⟨189255528748822819224239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126170352499215212816159 189255528748822819224239)
      ·
        refine ⟨283883293123234228836359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189255528748822819224239 283883293123234228836359)
        ·
          refine ⟨425824939684851343254539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283883293123234228836359 425824939684851343254539)
          ·
            refine ⟨638737409527277014881809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425824939684851343254539 638737409527277014881809)
            ·
              refine ⟨479053057145457761161357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638737409527277014881809 479053057145457761161357)
              ·
                refine ⟨179644896429546660435509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 479053057145457761161357 179644896429546660435509)
                ·
                  refine ⟨16841709040269999415829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179644896429546660435509 16841709040269999415829)
                  ·
                    rfl

theorem cell21_73798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_73798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73798 prefixEnd_73798 := by exact prefixLift 73798
  have htrace : WordTrace (prefixWord ++ tailWord_73798) baseStart_73798 baseEnd_73798 := by
    simpa [prefixWord, tailWord_73798, baseEnd_73798] using wordTrace_append hprefix tailTrace_73798
  have hstable : (prefixWord ++ tailWord_73798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73798).length < 2 ^ (prefixWord ++ tailWord_73798).sum := by decide
  have hdescent : baseEnd_73798 < baseStart_73798 := by decide
  rcases family_descends (prefixWord ++ tailWord_73798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73922 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_73922 : Nat := 118140960795 + 73922 * 2 ^ 59
def prefixEnd_73922 : Nat := 4983230072969 + 3 ^ 40 * 73922 * 2
def baseEnd_73922 : Nat := 16870007529673339348909

theorem tailTrace_73922 : CollatzResearch.WordTrace tailWord_73922 prefixEnd_73922 16870007529673339348909 := by
  unfold tailWord_73922
  simp only [CollatzResearch.WordTrace]
  refine ⟨674039209550173429398005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1797437892133795811728013 674039209550173429398005)
  ·
    refine ⟨63191175895328759006063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 674039209550173429398005 63191175895328759006063)
    ·
      refine ⟨94786763842993138509095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63191175895328759006063 94786763842993138509095)
      ·
        refine ⟨142180145764489707763643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94786763842993138509095 142180145764489707763643)
        ·
          refine ⟨213270218646734561645465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142180145764489707763643 213270218646734561645465)
          ·
            refine ⟨159952663985050921234099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213270218646734561645465 159952663985050921234099)
            ·
              refine ⟨239928995977576381851149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159952663985050921234099 239928995977576381851149)
              ·
                refine ⟨89973373491591143194181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239928995977576381851149 89973373491591143194181)
                ·
                  refine ⟨16870007529673339348909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89973373491591143194181 16870007529673339348909)
                  ·
                    rfl

theorem cell21_73922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_73922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73922 prefixEnd_73922 := by exact prefixLift 73922
  have htrace : WordTrace (prefixWord ++ tailWord_73922) baseStart_73922 baseEnd_73922 := by
    simpa [prefixWord, tailWord_73922, baseEnd_73922] using wordTrace_append hprefix tailTrace_73922
  have hstable : (prefixWord ++ tailWord_73922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73922).length < 2 ^ (prefixWord ++ tailWord_73922).sum := by decide
  have hdescent : baseEnd_73922 < baseStart_73922 := by decide
  rcases family_descends (prefixWord ++ tailWord_73922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73967 : List Nat := [1, 1, 2, 1, 6, 3, 2, 2, 3]
def baseStart_73967 : Nat := 118140960795 + 73967 * 2 ^ 59
def prefixEnd_73967 : Nat := 4983230072969 + 3 ^ 40 * 73967 * 2
def baseEnd_73967 : Nat := 16880277142763261098817

theorem tailTrace_73967 : CollatzResearch.WordTrace tailWord_73967 prefixEnd_73967 16880277142763261098817 := by
  unfold tailWord_73967
  simp only [CollatzResearch.WordTrace]
  refine ⟨2697798123037666402980155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1798532082025110935320103 2697798123037666402980155)
  ·
    refine ⟨4046697184556499604470233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2697798123037666402980155 4046697184556499604470233)
    ·
      refine ⟨3035022888417374703352675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4046697184556499604470233 3035022888417374703352675)
      ·
        refine ⟨4552534332626062055029013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3035022888417374703352675 4552534332626062055029013)
        ·
          refine ⟨213400046841846658829485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4552534332626062055029013 213400046841846658829485)
          ·
            refine ⟨80025017565692497061057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213400046841846658829485 80025017565692497061057)
            ·
              refine ⟨60018763174269372795793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80025017565692497061057 60018763174269372795793)
              ·
                refine ⟨45014072380702029596845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60018763174269372795793 45014072380702029596845)
                ·
                  refine ⟨16880277142763261098817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45014072380702029596845 16880277142763261098817)
                  ·
                    rfl

theorem cell21_73967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 2, 3].length) (baseStart_73967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73967 prefixEnd_73967 := by exact prefixLift 73967
  have htrace : WordTrace (prefixWord ++ tailWord_73967) baseStart_73967 baseEnd_73967 := by
    simpa [prefixWord, tailWord_73967, baseEnd_73967] using wordTrace_append hprefix tailTrace_73967
  have hstable : (prefixWord ++ tailWord_73967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73967).length < 2 ^ (prefixWord ++ tailWord_73967).sum := by decide
  have hdescent : baseEnd_73967 < baseStart_73967 := by decide
  rcases family_descends (prefixWord ++ tailWord_73967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73978 : List Nat := [3, 1, 1, 1, 1, 7, 1, 6]
def baseStart_73978 : Nat := 118140960795 + 73978 * 2 ^ 59
def prefixEnd_73978 : Nat := 4983230072969 + 3 ^ 40 * 73978 * 2
def baseEnd_73978 : Nat := 5627595830876562138487

theorem tailTrace_73978 : CollatzResearch.WordTrace tailWord_73978 prefixEnd_73978 5627595830876562138487 := by
  unfold tailWord_73978
  simp only [CollatzResearch.WordTrace]
  refine ⟨674549831499453820407647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1798799550665210187753725 674549831499453820407647)
  ·
    refine ⟨1011824747249180730611471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674549831499453820407647 1011824747249180730611471)
    ·
      refine ⟨1517737120873771095917207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1011824747249180730611471 1517737120873771095917207)
      ·
        refine ⟨2276605681310656643875811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517737120873771095917207 2276605681310656643875811)
        ·
          refine ⟨3414908521965984965813717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2276605681310656643875811 3414908521965984965813717)
          ·
            refine ⟨80036918483577772636259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3414908521965984965813717 80036918483577772636259)
            ·
              refine ⟨120055377725366658954389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80036918483577772636259 120055377725366658954389)
              ·
                refine ⟨5627595830876562138487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120055377725366658954389 5627595830876562138487)
                ·
                  rfl

theorem cell21_73978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_73978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73978 prefixEnd_73978 := by exact prefixLift 73978
  have htrace : WordTrace (prefixWord ++ tailWord_73978) baseStart_73978 baseEnd_73978 := by
    simpa [prefixWord, tailWord_73978, baseEnd_73978] using wordTrace_append hprefix tailTrace_73978
  have hstable : (prefixWord ++ tailWord_73978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73978).length < 2 ^ (prefixWord ++ tailWord_73978).sum := by decide
  have hdescent : baseEnd_73978 < baseStart_73978 := by decide
  rcases family_descends (prefixWord ++ tailWord_73978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_73992 : List Nat := [2, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_73992 : Nat := 118140960795 + 73992 * 2 ^ 59
def prefixEnd_73992 : Nat := 4983230072969 + 3 ^ 40 * 73992 * 2
def baseEnd_73992 : Nat := 16885982483368773182099

theorem tailTrace_73992 : CollatzResearch.WordTrace tailWord_73992 prefixEnd_73992 16885982483368773182099 := by
  unfold tailWord_73992
  simp only [CollatzResearch.WordTrace]
  refine ⟨1349354973973547836320115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1799139965298063781760153 1349354973973547836320115)
  ·
    refine ⟨2024032460960321754480173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1349354973973547836320115 2024032460960321754480173)
    ·
      refine ⟨759012172860120657930065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2024032460960321754480173 759012172860120657930065)
      ·
        refine ⟨569259129645090493447549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 759012172860120657930065 569259129645090493447549)
        ·
          refine ⟨213472173616908935042831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 569259129645090493447549 213472173616908935042831)
          ·
            refine ⟨320208260425363402564247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213472173616908935042831 320208260425363402564247)
            ·
              refine ⟨480312390638045103846371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320208260425363402564247 480312390638045103846371)
              ·
                refine ⟨720468585957067655769557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 480312390638045103846371 720468585957067655769557)
                ·
                  refine ⟨16885982483368773182099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 720468585957067655769557 16885982483368773182099)
                  ·
                    rfl

theorem cell21_73992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_73992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_73992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_73992 prefixEnd_73992 := by exact prefixLift 73992
  have htrace : WordTrace (prefixWord ++ tailWord_73992) baseStart_73992 baseEnd_73992 := by
    simpa [prefixWord, tailWord_73992, baseEnd_73992] using wordTrace_append hprefix tailTrace_73992
  have hstable : (prefixWord ++ tailWord_73992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_73992).length < 2 ^ (prefixWord ++ tailWord_73992).sum := by decide
  have hdescent : baseEnd_73992 < baseStart_73992 := by decide
  rcases family_descends (prefixWord ++ tailWord_73992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74026 : List Nat := [3, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_74026 : Nat := 118140960795 + 74026 * 2 ^ 59
def prefixEnd_74026 : Nat := 4983230072969 + 3 ^ 40 * 74026 * 2
def baseEnd_74026 : Nat := 16893741746592269615363

theorem tailTrace_74026 : CollatzResearch.WordTrace tailWord_74026 prefixEnd_74026 16893741746592269615363 := by
  unfold tailWord_74026
  simp only [CollatzResearch.WordTrace]
  refine ⟨674987507455979869844483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1799966686549279652918621 674987507455979869844483)
  ·
    refine ⟨1012481261183969804766725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 674987507455979869844483 1012481261183969804766725)
    ·
      refine ⟨189840236471994338393761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1012481261183969804766725 189840236471994338393761)
      ·
        refine ⟨142380177353995753795321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189840236471994338393761 142380177353995753795321)
        ·
          refine ⟨106785133015496815346491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142380177353995753795321 106785133015496815346491)
          ·
            refine ⟨160177699523245223019737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106785133015496815346491 160177699523245223019737)
            ·
              refine ⟨120133274642433917264803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160177699523245223019737 120133274642433917264803)
              ·
                refine ⟨180199911963650875897205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120133274642433917264803 180199911963650875897205)
                ·
                  refine ⟨16893741746592269615363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180199911963650875897205 16893741746592269615363)
                  ·
                    rfl

theorem cell21_74026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_74026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74026 prefixEnd_74026 := by exact prefixLift 74026
  have htrace : WordTrace (prefixWord ++ tailWord_74026) baseStart_74026 baseEnd_74026 := by
    simpa [prefixWord, tailWord_74026, baseEnd_74026] using wordTrace_append hprefix tailTrace_74026
  have hstable : (prefixWord ++ tailWord_74026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74026).length < 2 ^ (prefixWord ++ tailWord_74026).sum := by decide
  have hdescent : baseEnd_74026 < baseStart_74026 := by decide
  rcases family_descends (prefixWord ++ tailWord_74026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74037 : List Nat := [1, 3, 3, 1, 2, 1, 2, 8]
def baseStart_74037 : Nat := 118140960795 + 74037 * 2 ^ 59
def prefixEnd_74037 : Nat := 4983230072969 + 3 ^ 40 * 74037 * 2
def baseEnd_74037 : Nat := 5632084032152898310669

theorem tailTrace_74037 : CollatzResearch.WordTrace tailWord_74037 prefixEnd_74037 5632084032152898310669 := by
  unfold tailWord_74037
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700351232784068358028365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1800234155189378905352243 2700351232784068358028365)
  ·
    refine ⟨1012631712294025634260637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2700351232784068358028365 1012631712294025634260637)
    ·
      refine ⟨379736892110259612847739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1012631712294025634260637 379736892110259612847739)
      ·
        refine ⟨569605338165389419271609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 379736892110259612847739 569605338165389419271609)
        ·
          refine ⟨427204003624042064453707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 569605338165389419271609 427204003624042064453707)
          ·
            refine ⟨640806005436063096680561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427204003624042064453707 640806005436063096680561)
            ·
              refine ⟨480604504077047322510421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 640806005436063096680561 480604504077047322510421)
              ·
                refine ⟨5632084032152898310669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 480604504077047322510421 5632084032152898310669)
                ·
                  rfl

theorem cell21_74037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 8].length) (baseStart_74037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74037 prefixEnd_74037 := by exact prefixLift 74037
  have htrace : WordTrace (prefixWord ++ tailWord_74037) baseStart_74037 baseEnd_74037 := by
    simpa [prefixWord, tailWord_74037, baseEnd_74037] using wordTrace_append hprefix tailTrace_74037
  have hstable : (prefixWord ++ tailWord_74037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74037).length < 2 ^ (prefixWord ++ tailWord_74037).sum := by decide
  have hdescent : baseEnd_74037 < baseStart_74037 := by decide
  rcases family_descends (prefixWord ++ tailWord_74037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74085 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 5]
def baseStart_74085 : Nat := 118140960795 + 74085 * 2 ^ 59
def prefixEnd_74085 : Nat := 4983230072969 + 3 ^ 40 * 74085 * 2
def baseEnd_74085 : Nat := 16907206350421278131909

theorem tailTrace_74085 : CollatzResearch.WordTrace tailWord_74085 prefixEnd_74085 16907206350421278131909 := by
  unfold tailWord_74085
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702101936610172555775709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1801401291073448370517139 2702101936610172555775709)
  ·
    refine ⟨1013288226228814708415891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2702101936610172555775709 1013288226228814708415891)
    ·
      refine ⟨1519932339343222062623837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013288226228814708415891 1519932339343222062623837)
      ·
        refine ⟨569974627253708273483939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1519932339343222062623837 569974627253708273483939)
        ·
          refine ⟨854961940880562410225909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 569974627253708273483939 854961940880562410225909)
          ·
            refine ⟨80152681957552725958679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 854961940880562410225909 80152681957552725958679)
            ·
              refine ⟨120229022936329088938019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80152681957552725958679 120229022936329088938019)
              ·
                refine ⟨180343534404493633407029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120229022936329088938019 180343534404493633407029)
                ·
                  refine ⟨16907206350421278131909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180343534404493633407029 16907206350421278131909)
                  ·
                    rfl

theorem cell21_74085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_74085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74085 prefixEnd_74085 := by exact prefixLift 74085
  have htrace : WordTrace (prefixWord ++ tailWord_74085) baseStart_74085 baseEnd_74085 := by
    simpa [prefixWord, tailWord_74085, baseEnd_74085] using wordTrace_append hprefix tailTrace_74085
  have hstable : (prefixWord ++ tailWord_74085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74085).length < 2 ^ (prefixWord ++ tailWord_74085).sum := by decide
  have hdescent : baseEnd_74085 < baseStart_74085 := by decide
  rcases family_descends (prefixWord ++ tailWord_74085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74268 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_74268 : Nat := 118140960795 + 74268 * 2 ^ 59
def prefixEnd_74268 : Nat := 4983230072969 + 3 ^ 40 * 74268 * 2
def baseEnd_74268 : Nat := 16948969443653626581535

theorem tailTrace_74268 : CollatzResearch.WordTrace tailWord_74268 prefixEnd_74268 16948969443653626581535 := by
  unfold tailWord_74268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1354388247473597404843729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1805850996631463206458305 1354388247473597404843729)
  ·
    refine ⟨1015791185605198053632797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1354388247473597404843729 1015791185605198053632797)
    ·
      refine ⟨380921694601949270112299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1015791185605198053632797 380921694601949270112299)
      ·
        refine ⟨571382541902923905168449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380921694601949270112299 571382541902923905168449)
        ·
          refine ⟨428536906427192928876337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 571382541902923905168449 428536906427192928876337)
          ·
            refine ⟨321402679820394696657253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 428536906427192928876337 321402679820394696657253)
            ·
              refine ⟨60263002466324005623235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 321402679820394696657253 60263002466324005623235)
              ·
                refine ⟨90394503699486008434853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60263002466324005623235 90394503699486008434853)
                ·
                  refine ⟨16948969443653626581535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90394503699486008434853 16948969443653626581535)
                  ·
                    rfl

theorem cell21_74268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_74268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74268 prefixEnd_74268 := by exact prefixLift 74268
  have htrace : WordTrace (prefixWord ++ tailWord_74268) baseStart_74268 baseEnd_74268 := by
    simpa [prefixWord, tailWord_74268, baseEnd_74268] using wordTrace_append hprefix tailTrace_74268
  have hstable : (prefixWord ++ tailWord_74268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74268).length < 2 ^ (prefixWord ++ tailWord_74268).sum := by decide
  have hdescent : baseEnd_74268 < baseStart_74268 := by decide
  rcases family_descends (prefixWord ++ tailWord_74268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74358 : List Nat := [5, 1, 1, 2, 3, 1, 8]
def baseStart_74358 : Nat := 118140960795 + 74358 * 2 ^ 59
def prefixEnd_74358 : Nat := 4983230072969 + 3 ^ 40 * 74358 * 2
def baseEnd_74358 : Nat := 1885500963314830009039

theorem tailTrace_74358 : CollatzResearch.WordTrace tailWord_74358 prefixEnd_74358 1885500963314830009039 := by
  unfold tailWord_74358
  simp only [CollatzResearch.WordTrace]
  refine ⟨169503691538821261278983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1808039376414093453642485 169503691538821261278983)
  ·
    refine ⟨254255537308231891918475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169503691538821261278983 254255537308231891918475)
    ·
      refine ⟨381383305962347837877713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 254255537308231891918475 381383305962347837877713)
      ·
        refine ⟨286037479471760878408285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 381383305962347837877713 286037479471760878408285)
        ·
          refine ⟨107264054801910329403107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 286037479471760878408285 107264054801910329403107)
          ·
            refine ⟨160896082202865494104661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107264054801910329403107 160896082202865494104661)
            ·
              refine ⟨1885500963314830009039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 160896082202865494104661 1885500963314830009039)
              ·
                rfl

theorem cell21_74358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 8].length) (baseStart_74358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74358 prefixEnd_74358 := by exact prefixLift 74358
  have htrace : WordTrace (prefixWord ++ tailWord_74358) baseStart_74358 baseEnd_74358 := by
    simpa [prefixWord, tailWord_74358, baseEnd_74358] using wordTrace_append hprefix tailTrace_74358
  have hstable : (prefixWord ++ tailWord_74358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74358).length < 2 ^ (prefixWord ++ tailWord_74358).sum := by decide
  have hdescent : baseEnd_74358 < baseStart_74358 := by decide
  rcases family_descends (prefixWord ++ tailWord_74358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74372 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_74372 : Nat := 118140960795 + 74372 * 2 ^ 59
def prefixEnd_74372 : Nat := 4983230072969 + 3 ^ 40 * 74372 * 2
def baseEnd_74372 : Nat := 16972703660572556847989

theorem tailTrace_74372 : CollatzResearch.WordTrace tailWord_74372 prefixEnd_74372 16972703660572556847989 := by
  unfold tailWord_74372
  simp only [CollatzResearch.WordTrace]
  refine ⟨1356284843285210285736685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1808379791046947047648913 1356284843285210285736685)
  ·
    refine ⟨508606816231953857151257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1356284843285210285736685 508606816231953857151257)
    ·
      refine ⟨381455112173965392863443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 508606816231953857151257 381455112173965392863443)
      ·
        refine ⟨572182668260948089295165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 381455112173965392863443 572182668260948089295165)
        ·
          refine ⟨214568500597855533485687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572182668260948089295165 214568500597855533485687)
          ·
            refine ⟨321852750896783300228531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214568500597855533485687 321852750896783300228531)
            ·
              refine ⟨482779126345174950342797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321852750896783300228531 482779126345174950342797)
              ·
                refine ⟨181042172379440606378549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 482779126345174950342797 181042172379440606378549)
                ·
                  refine ⟨16972703660572556847989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181042172379440606378549 16972703660572556847989)
                  ·
                    rfl

theorem cell21_74372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_74372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74372 prefixEnd_74372 := by exact prefixLift 74372
  have htrace : WordTrace (prefixWord ++ tailWord_74372) baseStart_74372 baseEnd_74372 := by
    simpa [prefixWord, tailWord_74372, baseEnd_74372] using wordTrace_append hprefix tailTrace_74372
  have hstable : (prefixWord ++ tailWord_74372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74372).length < 2 ^ (prefixWord ++ tailWord_74372).sum := by decide
  have hdescent : baseEnd_74372 < baseStart_74372 := by decide
  rcases family_descends (prefixWord ++ tailWord_74372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74479 : List Nat := [1, 1, 2, 1, 5, 3, 2, 2, 4]
def baseStart_74479 : Nat := 118140960795 + 74479 * 2 ^ 59
def prefixEnd_74479 : Nat := 4983230072969 + 3 ^ 40 * 74479 * 2
def baseEnd_74479 : Nat := 16997122518364148564437

theorem tailTrace_74479 : CollatzResearch.WordTrace tailWord_74479 prefixEnd_74479 16997122518364148564437 := by
  unfold tailWord_74479
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716472297182777845618491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1810981531455185230412327 2716472297182777845618491)
  ·
    refine ⟨4074708445774166768427737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2716472297182777845618491 4074708445774166768427737)
    ·
      refine ⟨3056031334330625076320803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4074708445774166768427737 3056031334330625076320803)
      ·
        refine ⟨4584047001495937614481205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056031334330625076320803 4584047001495937614481205)
        ·
          refine ⟨429754406390244151357613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4584047001495937614481205 429754406390244151357613)
          ·
            refine ⟨161157902396341556759105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 429754406390244151357613 161157902396341556759105)
            ·
              refine ⟨120868426797256167569329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161157902396341556759105 120868426797256167569329)
              ·
                refine ⟨90651320097942125676997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120868426797256167569329 90651320097942125676997)
                ·
                  refine ⟨16997122518364148564437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90651320097942125676997 16997122518364148564437)
                  ·
                    rfl

theorem cell21_74479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 4].length) (baseStart_74479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74479 prefixEnd_74479 := by exact prefixLift 74479
  have htrace : WordTrace (prefixWord ++ tailWord_74479) baseStart_74479 baseEnd_74479 := by
    simpa [prefixWord, tailWord_74479, baseEnd_74479] using wordTrace_append hprefix tailTrace_74479
  have hstable : (prefixWord ++ tailWord_74479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74479).length < 2 ^ (prefixWord ++ tailWord_74479).sum := by decide
  have hdescent : baseEnd_74479 < baseStart_74479 := by decide
  rcases family_descends (prefixWord ++ tailWord_74479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74482 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_74482 : Nat := 118140960795 + 74482 * 2 ^ 59
def prefixEnd_74482 : Nat := 4983230072969 + 3 ^ 40 * 74482 * 2
def baseEnd_74482 : Nat := 16997807159236810014431

theorem tailTrace_74482 : CollatzResearch.WordTrace tailWord_74482 prefixEnd_74482 16997807159236810014431 := by
  unfold tailWord_74482
  simp only [CollatzResearch.WordTrace]
  refine ⟨679145429042977339494425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1811054477447939571985133 679145429042977339494425)
  ·
    refine ⟨509359071782233004620819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 679145429042977339494425 509359071782233004620819)
    ·
      refine ⟨764038607673349506931229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 509359071782233004620819 764038607673349506931229)
      ·
        refine ⟨286514477877506065099211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 764038607673349506931229 286514477877506065099211)
        ·
          refine ⟨429771716816259097648817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286514477877506065099211 429771716816259097648817)
          ·
            refine ⟨322328787612194323236613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429771716816259097648817 322328787612194323236613)
            ·
              refine ⟨60436647677286435606865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322328787612194323236613 60436647677286435606865)
              ·
                refine ⟨45327485757964826705149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60436647677286435606865 45327485757964826705149)
                ·
                  refine ⟨16997807159236810014431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45327485757964826705149 16997807159236810014431)
                  ·
                    rfl

theorem cell21_74482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_74482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74482 prefixEnd_74482 := by exact prefixLift 74482
  have htrace : WordTrace (prefixWord ++ tailWord_74482) baseStart_74482 baseEnd_74482 := by
    simpa [prefixWord, tailWord_74482, baseEnd_74482] using wordTrace_append hprefix tailTrace_74482
  have hstable : (prefixWord ++ tailWord_74482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74482).length < 2 ^ (prefixWord ++ tailWord_74482).sum := by decide
  have hdescent : baseEnd_74482 < baseStart_74482 := by decide
  rcases family_descends (prefixWord ++ tailWord_74482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74485 : List Nat := [1, 3, 6, 1, 2, 1, 1, 6]
def baseStart_74485 : Nat := 118140960795 + 74485 * 2 ^ 59
def prefixEnd_74485 : Nat := 4983230072969 + 3 ^ 40 * 74485 * 2
def baseEnd_74485 : Nat := 5666163933369823821475

theorem tailTrace_74485 : CollatzResearch.WordTrace tailWord_74485 prefixEnd_74485 5666163933369823821475 := by
  unfold tailWord_74485
  simp only [CollatzResearch.WordTrace]
  refine ⟨2716691135161040870336909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1811127423440693913557939 2716691135161040870336909)
  ·
    refine ⟨1018759175685390326376341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2716691135161040870336909 1018759175685390326376341)
    ·
      refine ⟨47754336360252671548891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1018759175685390326376341 47754336360252671548891)
      ·
        refine ⟨71631504540379007323337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47754336360252671548891 71631504540379007323337)
        ·
          refine ⟨53723628405284255492503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71631504540379007323337 53723628405284255492503)
          ·
            refine ⟨80585442607926383238755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53723628405284255492503 80585442607926383238755)
            ·
              refine ⟨120878163911889574858133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80585442607926383238755 120878163911889574858133)
              ·
                refine ⟨5666163933369823821475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120878163911889574858133 5666163933369823821475)
                ·
                  rfl

theorem cell21_74485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 6].length) (baseStart_74485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74485 prefixEnd_74485 := by exact prefixLift 74485
  have htrace : WordTrace (prefixWord ++ tailWord_74485) baseStart_74485 baseEnd_74485 := by
    simpa [prefixWord, tailWord_74485, baseEnd_74485] using wordTrace_append hprefix tailTrace_74485
  have hstable : (prefixWord ++ tailWord_74485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74485).length < 2 ^ (prefixWord ++ tailWord_74485).sum := by decide
  have hdescent : baseEnd_74485 < baseStart_74485 := by decide
  rcases family_descends (prefixWord ++ tailWord_74485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74552 : List Nat := [2, 1, 2, 1, 3, 2, 2, 8]
def baseStart_74552 : Nat := 118140960795 + 74552 * 2 ^ 59
def prefixEnd_74552 : Nat := 4983230072969 + 3 ^ 40 * 74552 * 2
def baseEnd_74552 : Nat := 5671260704310747949207

theorem tailTrace_74552 : CollatzResearch.WordTrace tailWord_74552 prefixEnd_74552 5671260704310747949207 := by
  unfold tailWord_74552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1359567412959155656512955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1812756550612207542017273 1359567412959155656512955)
  ·
    refine ⟨2039351119438733484769433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1359567412959155656512955 2039351119438733484769433)
    ·
      refine ⟨1529513339579050113577075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039351119438733484769433 1529513339579050113577075)
      ·
        refine ⟨2294270009368575170365613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529513339579050113577075 2294270009368575170365613)
        ·
          refine ⟨860351253513215688887105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2294270009368575170365613 860351253513215688887105)
          ·
            refine ⟨645263440134911766665329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 860351253513215688887105 645263440134911766665329)
            ·
              refine ⟨483947580101183824998997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 645263440134911766665329 483947580101183824998997)
              ·
                refine ⟨5671260704310747949207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 483947580101183824998997 5671260704310747949207)
                ·
                  rfl

theorem cell21_74552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_74552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74552 prefixEnd_74552 := by exact prefixLift 74552
  have htrace : WordTrace (prefixWord ++ tailWord_74552) baseStart_74552 baseEnd_74552 := by
    simpa [prefixWord, tailWord_74552, baseEnd_74552] using wordTrace_append hprefix tailTrace_74552
  have hstable : (prefixWord ++ tailWord_74552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74552).length < 2 ^ (prefixWord ++ tailWord_74552).sum := by decide
  have hdescent : baseEnd_74552 < baseStart_74552 := by decide
  rcases family_descends (prefixWord ++ tailWord_74552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74569 : List Nat := [1, 2, 1, 1, 2, 5, 4, 5]
def baseStart_74569 : Nat := 118140960795 + 74569 * 2 ^ 59
def prefixEnd_74569 : Nat := 4983230072969 + 3 ^ 40 * 74569 * 2
def baseEnd_74569 : Nat := 5672553914847997354751

theorem tailTrace_74569 : CollatzResearch.WordTrace tailWord_74569 prefixEnd_74569 5672553914847997354751 := by
  unfold tailWord_74569
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719754866856723216394761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1813169911237815477596507 2719754866856723216394761)
  ·
    refine ⟨2039816150142542412296071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2719754866856723216394761 2039816150142542412296071)
    ·
      refine ⟨3059724225213813618444107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2039816150142542412296071 3059724225213813618444107)
      ·
        refine ⟨4589586337820720427666161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059724225213813618444107 4589586337820720427666161)
        ·
          refine ⟨3442189753365540320749621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589586337820720427666161 3442189753365540320749621)
          ·
            refine ⟨322705289378019405070277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3442189753365540320749621 322705289378019405070277)
            ·
              refine ⟨60507241758378638450677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 322705289378019405070277 60507241758378638450677)
              ·
                refine ⟨5672553914847997354751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60507241758378638450677 5672553914847997354751)
                ·
                  rfl

theorem cell21_74569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 5].length) (baseStart_74569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74569 prefixEnd_74569 := by exact prefixLift 74569
  have htrace : WordTrace (prefixWord ++ tailWord_74569) baseStart_74569 baseEnd_74569 := by
    simpa [prefixWord, tailWord_74569, baseEnd_74569] using wordTrace_append hprefix tailTrace_74569
  have hstable : (prefixWord ++ tailWord_74569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74569).length < 2 ^ (prefixWord ++ tailWord_74569).sum := by decide
  have hdescent : baseEnd_74569 < baseStart_74569 := by decide
  rcases family_descends (prefixWord ++ tailWord_74569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74600 : List Nat := [2, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_74600 : Nat := 118140960795 + 74600 * 2 ^ 59
def prefixEnd_74600 : Nat := 4983230072969 + 3 ^ 40 * 74600 * 2
def baseEnd_74600 : Nat := 17024736366894827047523

theorem tailTrace_74600 : CollatzResearch.WordTrace tailWord_74600 prefixEnd_74600 17024736366894827047523 := by
  unfold tailWord_74600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360442764872207755386627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1813923686496277007182169 1360442764872207755386627)
  ·
    refine ⟨2040664147308311633079941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1360442764872207755386627 2040664147308311633079941)
    ·
      refine ⟨382624527620308431202489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2040664147308311633079941 382624527620308431202489)
      ·
        refine ⟨286968395715231323401867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 382624527620308431202489 286968395715231323401867)
        ·
          refine ⟨430452593572846985102801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 286968395715231323401867 430452593572846985102801)
          ·
            refine ⟨322839445179635238827101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430452593572846985102801 322839445179635238827101)
            ·
              refine ⟨121064791942363214560163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 322839445179635238827101 121064791942363214560163)
              ·
                refine ⟨181597187913544821840245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 121064791942363214560163 181597187913544821840245)
                ·
                  refine ⟨17024736366894827047523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181597187913544821840245 17024736366894827047523)
                  ·
                    rfl

theorem cell21_74600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_74600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74600 prefixEnd_74600 := by exact prefixLift 74600
  have htrace : WordTrace (prefixWord ++ tailWord_74600) baseStart_74600 baseEnd_74600 := by
    simpa [prefixWord, tailWord_74600, baseEnd_74600] using wordTrace_append hprefix tailTrace_74600
  have hstable : (prefixWord ++ tailWord_74600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74600).length < 2 ^ (prefixWord ++ tailWord_74600).sum := by decide
  have hdescent : baseEnd_74600 < baseStart_74600 := by decide
  rcases family_descends (prefixWord ++ tailWord_74600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74606 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_74606 : Nat := 118140960795 + 74606 * 2 ^ 59
def prefixEnd_74606 : Nat := 4983230072969 + 3 ^ 40 * 74606 * 2
def baseEnd_74606 : Nat := 17026105648640149947511

theorem tailTrace_74606 : CollatzResearch.WordTrace tailWord_74606 prefixEnd_74606 17026105648640149947511 := by
  unfold tailWord_74606
  simp only [CollatzResearch.WordTrace]
  refine ⟨340138045965334816936459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1814069578481785690327781 340138045965334816936459)
  ·
    refine ⟨510207068948002225404689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340138045965334816936459 510207068948002225404689)
    ·
      refine ⟨382655301711001669053517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 510207068948002225404689 382655301711001669053517)
      ·
        refine ⟨143495738141625625895069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 382655301711001669053517 143495738141625625895069)
        ·
          refine ⟨53810901803109609710651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 143495738141625625895069 53810901803109609710651)
          ·
            refine ⟨80716352704664414565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53810901803109609710651 80716352704664414565977)
            ·
              refine ⟨60537264528498310924483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80716352704664414565977 60537264528498310924483)
              ·
                refine ⟨90805896792747466386725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60537264528498310924483 90805896792747466386725)
                ·
                  refine ⟨17026105648640149947511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90805896792747466386725 17026105648640149947511)
                  ·
                    rfl

theorem cell21_74606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_74606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74606 prefixEnd_74606 := by exact prefixLift 74606
  have htrace : WordTrace (prefixWord ++ tailWord_74606) baseStart_74606 baseEnd_74606 := by
    simpa [prefixWord, tailWord_74606, baseEnd_74606] using wordTrace_append hprefix tailTrace_74606
  have hstable : (prefixWord ++ tailWord_74606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74606).length < 2 ^ (prefixWord ++ tailWord_74606).sum := by decide
  have hdescent : baseEnd_74606 < baseStart_74606 := by decide
  rcases family_descends (prefixWord ++ tailWord_74606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74710 : List Nat := [5, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_74710 : Nat := 118140960795 + 74710 * 2 ^ 59
def prefixEnd_74710 : Nat := 4983230072969 + 3 ^ 40 * 74710 * 2
def baseEnd_74710 : Nat := 17049839865559080213965

theorem tailTrace_74710 : CollatzResearch.WordTrace tailWord_74710 prefixEnd_74710 17049839865559080213965 := by
  unfold tailWord_74710
  simp only [CollatzResearch.WordTrace]
  refine ⟨170306097459119018579849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1816598372897269531518389 170306097459119018579849)
  ·
    refine ⟨127729573094339263934887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 170306097459119018579849 127729573094339263934887)
    ·
      refine ⟨191594359641508895902331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 127729573094339263934887 191594359641508895902331)
      ·
        refine ⟨287391539462263343853497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 191594359641508895902331 287391539462263343853497)
        ·
          refine ⟨215543654596697507890123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287391539462263343853497 215543654596697507890123)
          ·
            refine ⟨323315481895046261835185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215543654596697507890123 323315481895046261835185)
            ·
              refine ⟨242486611421284696376389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323315481895046261835185 242486611421284696376389)
              ·
                refine ⟨45466239641490880570573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 242486611421284696376389 45466239641490880570573)
                ·
                  refine ⟨17049839865559080213965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45466239641490880570573 17049839865559080213965)
                  ·
                    rfl

theorem cell21_74710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_74710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74710 prefixEnd_74710 := by exact prefixLift 74710
  have htrace : WordTrace (prefixWord ++ tailWord_74710) baseStart_74710 baseEnd_74710 := by
    simpa [prefixWord, tailWord_74710, baseEnd_74710] using wordTrace_append hprefix tailTrace_74710
  have hstable : (prefixWord ++ tailWord_74710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74710).length < 2 ^ (prefixWord ++ tailWord_74710).sum := by decide
  have hdescent : baseEnd_74710 < baseStart_74710 := by decide
  rcases family_descends (prefixWord ++ tailWord_74710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74735 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 5]
def baseStart_74735 : Nat := 118140960795 + 74735 * 2 ^ 59
def prefixEnd_74735 : Nat := 4983230072969 + 3 ^ 40 * 74735 * 2
def baseEnd_74735 : Nat := 17055545206164592297247

theorem tailTrace_74735 : CollatzResearch.WordTrace tailWord_74735 prefixEnd_74735 17055545206164592297247 := by
  unfold tailWord_74735
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725809384255333566937659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1817206256170222377958439 2725809384255333566937659)
  ·
    refine ⟨4088714076383000350406489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725809384255333566937659 4088714076383000350406489)
    ·
      refine ⟨3066535557287250262804867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4088714076383000350406489 3066535557287250262804867)
      ·
        refine ⟨4599803335930875394207301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3066535557287250262804867 4599803335930875394207301)
        ·
          refine ⟨862463125487039136413869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4599803335930875394207301 862463125487039136413869)
          ·
            refine ⟨323423672057639676155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 862463125487039136413869 323423672057639676155201)
            ·
              refine ⟨242567754043229757116401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323423672057639676155201 242567754043229757116401)
              ·
                refine ⟨181925815532422317837301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242567754043229757116401 181925815532422317837301)
                ·
                  refine ⟨17055545206164592297247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 181925815532422317837301 17055545206164592297247)
                  ·
                    rfl

theorem cell21_74735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 5].length) (baseStart_74735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74735 prefixEnd_74735 := by exact prefixLift 74735
  have htrace : WordTrace (prefixWord ++ tailWord_74735) baseStart_74735 baseEnd_74735 := by
    simpa [prefixWord, tailWord_74735, baseEnd_74735] using wordTrace_append hprefix tailTrace_74735
  have hstable : (prefixWord ++ tailWord_74735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74735).length < 2 ^ (prefixWord ++ tailWord_74735).sum := by decide
  have hdescent : baseEnd_74735 < baseStart_74735 := by decide
  rcases family_descends (prefixWord ++ tailWord_74735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74738 : List Nat := [3, 2, 1, 5, 1, 1, 1, 7]
def baseStart_74738 : Nat := 118140960795 + 74738 * 2 ^ 59
def prefixEnd_74738 : Nat := 4983230072969 + 3 ^ 40 * 74738 * 2
def baseEnd_74738 : Nat := 5685409949012417915747

theorem tailTrace_74738 : CollatzResearch.WordTrace tailWord_74738 prefixEnd_74738 5685409949012417915747 := by
  unfold tailWord_74738
  simp only [CollatzResearch.WordTrace]
  refine ⟨681479700811116269824217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1817279202162976719531245 681479700811116269824217)
  ·
    refine ⟨511109775608337202368163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 681479700811116269824217 511109775608337202368163)
    ·
      refine ⟨766664663412505803552245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511109775608337202368163 766664663412505803552245)
      ·
        refine ⟨71874812194922419083023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 766664663412505803552245 71874812194922419083023)
        ·
          refine ⟨107812218292383628624535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71874812194922419083023 107812218292383628624535)
          ·
            refine ⟨161718327438575442936803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107812218292383628624535 161718327438575442936803)
            ·
              refine ⟨242577491157863164405205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161718327438575442936803 242577491157863164405205)
              ·
                refine ⟨5685409949012417915747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 242577491157863164405205 5685409949012417915747)
                ·
                  rfl

theorem cell21_74738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_74738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74738 prefixEnd_74738 := by exact prefixLift 74738
  have htrace : WordTrace (prefixWord ++ tailWord_74738) baseStart_74738 baseEnd_74738 := by
    simpa [prefixWord, tailWord_74738, baseEnd_74738] using wordTrace_append hprefix tailTrace_74738
  have hstable : (prefixWord ++ tailWord_74738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74738).length < 2 ^ (prefixWord ++ tailWord_74738).sum := by decide
  have hdescent : baseEnd_74738 < baseStart_74738 := by decide
  rcases family_descends (prefixWord ++ tailWord_74738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74766 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_74766 : Nat := 118140960795 + 74766 * 2 ^ 59
def prefixEnd_74766 : Nat := 4983230072969 + 3 ^ 40 * 74766 * 2
def baseEnd_74766 : Nat := 17062619828515427280517

theorem tailTrace_74766 : CollatzResearch.WordTrace tailWord_74766 prefixEnd_74766 17062619828515427280517 := by
  unfold tailWord_74766
  simp only [CollatzResearch.WordTrace]
  refine ⟨340867505892878232664519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1817960031428683907544101 340867505892878232664519)
  ·
    refine ⟨511301258839317348996779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 340867505892878232664519 511301258839317348996779)
    ·
      refine ⟨766951888258976023495169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 511301258839317348996779 766951888258976023495169)
      ·
        refine ⟨575213916194232017621377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 766951888258976023495169 575213916194232017621377)
        ·
          refine ⟨431410437145674013216033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 575213916194232017621377 431410437145674013216033)
          ·
            refine ⟨323557827859255509912025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431410437145674013216033 323557827859255509912025)
            ·
              refine ⟨242668370894441632434019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 323557827859255509912025 242668370894441632434019)
              ·
                refine ⟨364002556341662448651029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242668370894441632434019 364002556341662448651029)
                ·
                  refine ⟨17062619828515427280517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 364002556341662448651029 17062619828515427280517)
                  ·
                    rfl

theorem cell21_74766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_74766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74766 prefixEnd_74766 := by exact prefixLift 74766
  have htrace : WordTrace (prefixWord ++ tailWord_74766) baseStart_74766 baseEnd_74766 := by
    simpa [prefixWord, tailWord_74766, baseEnd_74766] using wordTrace_append hprefix tailTrace_74766
  have hstable : (prefixWord ++ tailWord_74766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74766).length < 2 ^ (prefixWord ++ tailWord_74766).sum := by decide
  have hdescent : baseEnd_74766 < baseStart_74766 := by decide
  rcases family_descends (prefixWord ++ tailWord_74766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74783 : List Nat := [1, 1, 2, 4, 1, 3, 4, 1, 4]
def baseStart_74783 : Nat := 118140960795 + 74783 * 2 ^ 59
def prefixEnd_74783 : Nat := 4983230072969 + 3 ^ 40 * 74783 * 2
def baseEnd_74783 : Nat := 17066499460127175497149

theorem tailTrace_74783 : CollatzResearch.WordTrace tailWord_74783 prefixEnd_74783 17066499460127175497149 := by
  unfold tailWord_74783
  simp only [CollatzResearch.WordTrace]
  refine ⟨2727560088081437764685003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1818373392054291843123335 2727560088081437764685003)
  ·
    refine ⟨4091340132122156647027505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2727560088081437764685003 4091340132122156647027505)
    ·
      refine ⟨3068505099091617485270629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4091340132122156647027505 3068505099091617485270629)
      ·
        refine ⟨575344706079678278488243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3068505099091617485270629 575344706079678278488243)
        ·
          refine ⟨863017059119517417732365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575344706079678278488243 863017059119517417732365)
          ·
            refine ⟨323631397169819031649637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 863017059119517417732365 323631397169819031649637)
            ·
              refine ⟨60680886969341068434307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 323631397169819031649637 60680886969341068434307)
              ·
                refine ⟨91021330454011602651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60680886969341068434307 91021330454011602651461)
                ·
                  refine ⟨17066499460127175497149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91021330454011602651461 17066499460127175497149)
                  ·
                    rfl

theorem cell21_74783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 1, 4].length) (baseStart_74783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74783 prefixEnd_74783 := by exact prefixLift 74783
  have htrace : WordTrace (prefixWord ++ tailWord_74783) baseStart_74783 baseEnd_74783 := by
    simpa [prefixWord, tailWord_74783, baseEnd_74783] using wordTrace_append hprefix tailTrace_74783
  have hstable : (prefixWord ++ tailWord_74783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74783).length < 2 ^ (prefixWord ++ tailWord_74783).sum := by decide
  have hdescent : baseEnd_74783 < baseStart_74783 := by decide
  rcases family_descends (prefixWord ++ tailWord_74783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74845 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 5]
def baseStart_74845 : Nat := 118140960795 + 74845 * 2 ^ 59
def prefixEnd_74845 : Nat := 4983230072969 + 3 ^ 40 * 74845 * 2
def baseEnd_74845 : Nat := 17080648704828845463689

theorem tailTrace_74845 : CollatzResearch.WordTrace tailWord_74845 prefixEnd_74845 17080648704828845463689 := by
  unfold tailWord_74845
  simp only [CollatzResearch.WordTrace]
  refine ⟨2729821413856822353441989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1819880942571214902294659 2729821413856822353441989)
  ·
    refine ⟨511841515098154191270373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2729821413856822353441989 511841515098154191270373)
    ·
      refine ⟨95970284080903910863195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 511841515098154191270373 95970284080903910863195)
      ·
        refine ⟨143955426121355866294793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95970284080903910863195 143955426121355866294793)
        ·
          refine ⟨107966569591016899721095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 143955426121355866294793 107966569591016899721095)
          ·
            refine ⟨161949854386525349581643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107966569591016899721095 161949854386525349581643)
            ·
              refine ⟨242924781579788024372465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161949854386525349581643 242924781579788024372465)
              ·
                refine ⟨182193586184841018279349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 242924781579788024372465 182193586184841018279349)
                ·
                  refine ⟨17080648704828845463689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 182193586184841018279349 17080648704828845463689)
                  ·
                    rfl

theorem cell21_74845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_74845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74845 prefixEnd_74845 := by exact prefixLift 74845
  have htrace : WordTrace (prefixWord ++ tailWord_74845) baseStart_74845 baseEnd_74845 := by
    simpa [prefixWord, tailWord_74845, baseEnd_74845] using wordTrace_append hprefix tailTrace_74845
  have hstable : (prefixWord ++ tailWord_74845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74845).length < 2 ^ (prefixWord ++ tailWord_74845).sum := by decide
  have hdescent : baseEnd_74845 < baseStart_74845 := by decide
  rcases family_descends (prefixWord ++ tailWord_74845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_74991 : List Nat := [1, 1, 2, 1, 16]
def baseStart_74991 : Nat := 118140960795 + 74991 * 2 ^ 59
def prefixEnd_74991 : Nat := 4983230072969 + 3 ^ 40 * 74991 * 2
def baseEnd_74991 : Nat := 211283554246481926297

theorem tailTrace_74991 : CollatzResearch.WordTrace tailWord_74991 prefixEnd_74991 211283554246481926297 := by
  unfold tailWord_74991
  simp only [CollatzResearch.WordTrace]
  refine ⟨2735146471327889288256827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1823430980885259525504551 2735146471327889288256827)
  ·
    refine ⟨4102719706991833932385241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2735146471327889288256827 4102719706991833932385241)
    ·
      refine ⟨3077039780243875449288931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4102719706991833932385241 3077039780243875449288931)
      ·
        refine ⟨4615559670365813173933397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077039780243875449288931 4615559670365813173933397)
        ·
          refine ⟨211283554246481926297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 4615559670365813173933397 211283554246481926297)
          ·
            rfl

theorem cell21_74991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 16].length) (baseStart_74991 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_74991 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_74991 prefixEnd_74991 := by exact prefixLift 74991
  have htrace : WordTrace (prefixWord ++ tailWord_74991) baseStart_74991 baseEnd_74991 := by
    simpa [prefixWord, tailWord_74991, baseEnd_74991] using wordTrace_append hprefix tailTrace_74991
  have hstable : (prefixWord ++ tailWord_74991).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_74991).length < 2 ^ (prefixWord ++ tailWord_74991).sum := by decide
  have hdescent : baseEnd_74991 < baseStart_74991 := by decide
  rcases family_descends (prefixWord ++ tailWord_74991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75084 : List Nat := [2, 2, 1, 3, 2, 3, 1, 7]
def baseStart_75084 : Nat := 118140960795 + 75084 * 2 ^ 59
def prefixEnd_75084 : Nat := 4983230072969 + 3 ^ 40 * 75084 * 2
def baseEnd_75084 : Nat := 5711730587005846993289

theorem tailTrace_75084 : CollatzResearch.WordTrace tailWord_75084 prefixEnd_75084 5711730587005846993289 := by
  unfold tailWord_75084
  simp only [CollatzResearch.WordTrace]
  refine ⟨1369269229995483085696153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1825692306660644114261537 1369269229995483085696153)
  ·
    refine ⟨1026951922496612314272115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1369269229995483085696153 1026951922496612314272115)
    ·
      refine ⟨1540427883744918471408173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1026951922496612314272115 1540427883744918471408173)
      ·
        refine ⟨577660456404344426778065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1540427883744918471408173 577660456404344426778065)
        ·
          refine ⟨433245342303258320083549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 577660456404344426778065 433245342303258320083549)
          ·
            refine ⟨162467003363721870031331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 433245342303258320083549 162467003363721870031331)
            ·
              refine ⟨243700505045582805046997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162467003363721870031331 243700505045582805046997)
              ·
                refine ⟨5711730587005846993289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 243700505045582805046997 5711730587005846993289)
                ·
                  rfl

theorem cell21_75084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_75084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75084 prefixEnd_75084 := by exact prefixLift 75084
  have htrace : WordTrace (prefixWord ++ tailWord_75084) baseStart_75084 baseEnd_75084 := by
    simpa [prefixWord, tailWord_75084, baseEnd_75084] using wordTrace_append hprefix tailTrace_75084
  have hstable : (prefixWord ++ tailWord_75084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75084).length < 2 ^ (prefixWord ++ tailWord_75084).sum := by decide
  have hdescent : baseEnd_75084 < baseStart_75084 := by decide
  rcases family_descends (prefixWord ++ tailWord_75084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75098 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_75098 : Nat := 118140960795 + 75098 * 2 ^ 59
def prefixEnd_75098 : Nat := 4983230072969 + 3 ^ 40 * 75098 * 2
def baseEnd_75098 : Nat := 17138386751756627746505

theorem tailTrace_75098 : CollatzResearch.WordTrace tailWord_75098 prefixEnd_75098 17138386751756627746505 := by
  unfold tailWord_75098
  simp only [CollatzResearch.WordTrace]
  refine ⟨684762270485061640600487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1826032721293497708267965 684762270485061640600487)
  ·
    refine ⟨1027143405727592460900731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 684762270485061640600487 1027143405727592460900731)
    ·
      refine ⟨1540715108591388691351097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1027143405727592460900731 1540715108591388691351097)
      ·
        refine ⟨1155536331443541518513323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1540715108591388691351097 1155536331443541518513323)
        ·
          refine ⟨1733304497165312277769985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155536331443541518513323 1733304497165312277769985)
          ·
            refine ⟨1299978372873984208327489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733304497165312277769985 1299978372873984208327489)
            ·
              refine ⟨974983779655488156245617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299978372873984208327489 974983779655488156245617)
              ·
                refine ⟨731237834741616117184213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974983779655488156245617 731237834741616117184213)
                ·
                  refine ⟨17138386751756627746505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 731237834741616117184213 17138386751756627746505)
                  ·
                    rfl

theorem cell21_75098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_75098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75098 prefixEnd_75098 := by exact prefixLift 75098
  have htrace : WordTrace (prefixWord ++ tailWord_75098) baseStart_75098 baseEnd_75098 := by
    simpa [prefixWord, tailWord_75098, baseEnd_75098] using wordTrace_append hprefix tailTrace_75098
  have hstable : (prefixWord ++ tailWord_75098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75098).length < 2 ^ (prefixWord ++ tailWord_75098).sum := by decide
  have hdescent : baseEnd_75098 < baseStart_75098 := by decide
  rcases family_descends (prefixWord ++ tailWord_75098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75118 : List Nat := [4, 1, 2, 4, 1, 1, 2, 6]
def baseStart_75118 : Nat := 118140960795 + 75118 * 2 ^ 59
def prefixEnd_75118 : Nat := 4983230072969 + 3 ^ 40 * 75118 * 2
def baseEnd_75118 : Nat := 5714317008080345804377

theorem tailTrace_75118 : CollatzResearch.WordTrace tailWord_75118 prefixEnd_75118 5714317008080345804377 := by
  unfold tailWord_75118
  simp only [CollatzResearch.WordTrace]
  refine ⟨342472317733473747266251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1826519027911859985420005 342472317733473747266251)
  ·
    refine ⟨513708476600210620899377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 342472317733473747266251 513708476600210620899377)
    ·
      refine ⟨385281357450157965674533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 513708476600210620899377 385281357450157965674533)
      ·
        refine ⟨72240254521904618563975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 385281357450157965674533 72240254521904618563975)
        ·
          refine ⟨108360381782856927845963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72240254521904618563975 108360381782856927845963)
          ·
            refine ⟨162540572674285391768945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108360381782856927845963 162540572674285391768945)
            ·
              refine ⟨121905429505714043826709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162540572674285391768945 121905429505714043826709)
              ·
                refine ⟨5714317008080345804377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 121905429505714043826709 5714317008080345804377)
                ·
                  rfl

theorem cell21_75118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_75118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75118 prefixEnd_75118 := by exact prefixLift 75118
  have htrace : WordTrace (prefixWord ++ tailWord_75118) baseStart_75118 baseEnd_75118 := by
    simpa [prefixWord, tailWord_75118, baseEnd_75118] using wordTrace_append hprefix tailTrace_75118
  have hstable : (prefixWord ++ tailWord_75118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75118).length < 2 ^ (prefixWord ++ tailWord_75118).sum := by decide
  have hdescent : baseEnd_75118 < baseStart_75118 := by decide
  rcases family_descends (prefixWord ++ tailWord_75118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75160 : List Nat := [2, 1, 2, 5, 2, 9]
def baseStart_75160 : Nat := 118140960795 + 75160 * 2 ^ 59
def prefixEnd_75160 : Nat := 4983230072969 + 3 ^ 40 * 75160 * 2
def baseEnd_75160 : Nat := 635279110979936952335

theorem tailTrace_75160 : CollatzResearch.WordTrace tailWord_75160 prefixEnd_75160 635279110979936952335 := by
  unfold tailWord_75160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1370655203857815575579467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1827540271810420767439289 1370655203857815575579467)
  ·
    refine ⟨2055982805786723363369201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1370655203857815575579467 2055982805786723363369201)
    ·
      refine ⟨1541987104340042522526901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2055982805786723363369201 1541987104340042522526901)
      ·
        refine ⟨144561291031878986486897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1541987104340042522526901 144561291031878986486897)
        ·
          refine ⟨108420968273909239865173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144561291031878986486897 108420968273909239865173)
          ·
            refine ⟨635279110979936952335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 108420968273909239865173 635279110979936952335)
            ·
              rfl

theorem cell21_75160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 9].length) (baseStart_75160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75160 prefixEnd_75160 := by exact prefixLift 75160
  have htrace : WordTrace (prefixWord ++ tailWord_75160) baseStart_75160 baseEnd_75160 := by
    simpa [prefixWord, tailWord_75160, baseEnd_75160] using wordTrace_append hprefix tailTrace_75160
  have hstable : (prefixWord ++ tailWord_75160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75160).length < 2 ^ (prefixWord ++ tailWord_75160).sum := by decide
  have hdescent : baseEnd_75160 < baseStart_75160 := by decide
  rcases family_descends (prefixWord ++ tailWord_75160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75166 : List Nat := [4, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_75166 : Nat := 118140960795 + 75166 * 2 ^ 59
def prefixEnd_75166 : Nat := 4983230072969 + 3 ^ 40 * 75166 * 2
def baseEnd_75166 : Nat := 17153905278203620613033

theorem tailTrace_75166 : CollatzResearch.WordTrace tailWord_75166 prefixEnd_75166 17153905278203620613033 := by
  unfold tailWord_75166
  simp only [CollatzResearch.WordTrace]
  refine ⟨342691155711736771984669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1827686163795929450584901 342691155711736771984669)
  ·
    refine ⟨128509183391901289494251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 342691155711736771984669 128509183391901289494251)
    ·
      refine ⟨192763775087851934241377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128509183391901289494251 192763775087851934241377)
      ·
        refine ⟨144572831315888950681033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 192763775087851934241377 144572831315888950681033)
        ·
          refine ⟨108429623486916713010775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 144572831315888950681033 108429623486916713010775)
          ·
            refine ⟨162644435230375069516163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108429623486916713010775 162644435230375069516163)
            ·
              refine ⟨243966652845562604274245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162644435230375069516163 243966652845562604274245)
              ·
                refine ⟨45743747408542988301421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 243966652845562604274245 45743747408542988301421)
                ·
                  refine ⟨17153905278203620613033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45743747408542988301421 17153905278203620613033)
                  ·
                    rfl

theorem cell21_75166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_75166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75166 prefixEnd_75166 := by exact prefixLift 75166
  have htrace : WordTrace (prefixWord ++ tailWord_75166) baseStart_75166 baseEnd_75166 := by
    simpa [prefixWord, tailWord_75166, baseEnd_75166] using wordTrace_append hprefix tailTrace_75166
  have hstable : (prefixWord ++ tailWord_75166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75166).length < 2 ^ (prefixWord ++ tailWord_75166).sum := by decide
  have hdescent : baseEnd_75166 < baseStart_75166 := by decide
  rcases family_descends (prefixWord ++ tailWord_75166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75208 : List Nat := [2, 1, 3, 1, 3, 1, 4, 3, 3]
def baseStart_75208 : Nat := 118140960795 + 75208 * 2 ^ 59
def prefixEnd_75208 : Nat := 4983230072969 + 3 ^ 40 * 75208 * 2
def baseEnd_75208 : Nat := 17163490250420880912947

theorem tailTrace_75208 : CollatzResearch.WordTrace tailWord_75208 prefixEnd_75208 17163490250420880912947 := by
  unfold tailWord_75208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1371530555770867674453139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1828707407694490232604185 1371530555770867674453139)
  ·
    refine ⟨2057295833656301511679709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1371530555770867674453139 2057295833656301511679709)
    ·
      refine ⟨771485937621113066879891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2057295833656301511679709 771485937621113066879891)
      ·
        refine ⟨1157228906431669600319837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771485937621113066879891 1157228906431669600319837)
        ·
          refine ⟨433960839911876100119939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1157228906431669600319837 433960839911876100119939)
          ·
            refine ⟨650941259867814150179909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 433960839911876100119939 650941259867814150179909)
            ·
              refine ⟨122051486225215153158733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 650941259867814150179909 122051486225215153158733)
              ·
                refine ⟨45769307334455682434525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122051486225215153158733 45769307334455682434525)
                ·
                  refine ⟨17163490250420880912947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45769307334455682434525 17163490250420880912947)
                  ·
                    rfl

theorem cell21_75208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 3, 3].length) (baseStart_75208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75208 prefixEnd_75208 := by exact prefixLift 75208
  have htrace : WordTrace (prefixWord ++ tailWord_75208) baseStart_75208 baseEnd_75208 := by
    simpa [prefixWord, tailWord_75208, baseEnd_75208] using wordTrace_append hprefix tailTrace_75208
  have hstable : (prefixWord ++ tailWord_75208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75208).length < 2 ^ (prefixWord ++ tailWord_75208).sum := by decide
  have hdescent : baseEnd_75208 < baseStart_75208 := by decide
  rcases family_descends (prefixWord ++ tailWord_75208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75239 : List Nat := [1, 1, 5, 2, 1, 3, 3, 1, 4]
def baseStart_75239 : Nat := 118140960795 + 75239 * 2 ^ 59
def prefixEnd_75239 : Nat := 4983230072969 + 3 ^ 40 * 75239 * 2
def baseEnd_75239 : Nat := 17170564872771715896217

theorem tailTrace_75239 : CollatzResearch.WordTrace tailWord_75239 prefixEnd_75239 17170564872771715896217 := by
  unfold tailWord_75239
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744191774429427643284771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1829461182952951762189847 2744191774429427643284771)
  ·
    refine ⟨4116287661644141464927157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2744191774429427643284771 4116287661644141464927157)
    ·
      refine ⟨385901968279138262336921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4116287661644141464927157 385901968279138262336921)
      ·
        refine ⟨289426476209353696752691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 385901968279138262336921 289426476209353696752691)
        ·
          refine ⟨434139714314030545129037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289426476209353696752691 434139714314030545129037)
          ·
            refine ⟨162802392867761454423389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434139714314030545129037 162802392867761454423389)
            ·
              refine ⟨61050897325410545408771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 162802392867761454423389 61050897325410545408771)
              ·
                refine ⟨91576345988115818113157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61050897325410545408771 91576345988115818113157)
                ·
                  refine ⟨17170564872771715896217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91576345988115818113157 17170564872771715896217)
                  ·
                    rfl

theorem cell21_75239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 1, 4].length) (baseStart_75239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75239 prefixEnd_75239 := by exact prefixLift 75239
  have htrace : WordTrace (prefixWord ++ tailWord_75239) baseStart_75239 baseEnd_75239 := by
    simpa [prefixWord, tailWord_75239, baseEnd_75239] using wordTrace_append hprefix tailTrace_75239
  have hstable : (prefixWord ++ tailWord_75239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75239).length < 2 ^ (prefixWord ++ tailWord_75239).sum := by decide
  have hdescent : baseEnd_75239 < baseStart_75239 := by decide
  rcases family_descends (prefixWord ++ tailWord_75239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75253 : List Nat := [1, 3, 5, 1, 1, 2, 1, 7]
def baseStart_75253 : Nat := 118140960795 + 75253 * 2 ^ 59
def prefixEnd_75253 : Nat := 4983230072969 + 3 ^ 40 * 75253 * 2
def baseEnd_75253 : Nat := 5724586621170267554285

theorem tailTrace_75253 : CollatzResearch.WordTrace tailWord_75253 prefixEnd_75253 5724586621170267554285 := by
  unfold tailWord_75253
  simp only [CollatzResearch.WordTrace]
  refine ⟨2744702396378708034294413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1829801597585805356196275 2744702396378708034294413)
  ·
    refine ⟨1029263398642015512860405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2744702396378708034294413 1029263398642015512860405)
    ·
      refine ⟨96493443622688954330663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1029263398642015512860405 96493443622688954330663)
      ·
        refine ⟨144740165434033431495995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96493443622688954330663 144740165434033431495995)
        ·
          refine ⟨217110248151050147243993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144740165434033431495995 217110248151050147243993)
          ·
            refine ⟨162832686113287610432995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217110248151050147243993 162832686113287610432995)
            ·
              refine ⟨244249029169931415649493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162832686113287610432995 244249029169931415649493)
              ·
                refine ⟨5724586621170267554285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 244249029169931415649493 5724586621170267554285)
                ·
                  rfl

theorem cell21_75253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 7].length) (baseStart_75253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75253 prefixEnd_75253 := by exact prefixLift 75253
  have htrace : WordTrace (prefixWord ++ tailWord_75253) baseStart_75253 baseEnd_75253 := by
    simpa [prefixWord, tailWord_75253, baseEnd_75253] using wordTrace_append hprefix tailTrace_75253
  have hstable : (prefixWord ++ tailWord_75253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75253).length < 2 ^ (prefixWord ++ tailWord_75253).sum := by decide
  have hdescent : baseEnd_75253 < baseStart_75253 := by decide
  rcases family_descends (prefixWord ++ tailWord_75253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75267 : List Nat := [1, 1, 1, 3, 2, 1, 2, 7, 3]
def baseStart_75267 : Nat := 118140960795 + 75267 * 2 ^ 59
def prefixEnd_75267 : Nat := 4983230072969 + 3 ^ 40 * 75267 * 2
def baseEnd_75267 : Nat := 17176954854249889429493

theorem tailTrace_75267 : CollatzResearch.WordTrace tailWord_75267 prefixEnd_75267 17176954854249889429493 := by
  unfold tailWord_75267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745213018327988425304055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830142012218658950202703 2745213018327988425304055)
  ·
    refine ⟨4117819527491982637956083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2745213018327988425304055 4117819527491982637956083)
    ·
      refine ⟨6176729291237973956934125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4117819527491982637956083 6176729291237973956934125)
      ·
        refine ⟨2316273484214240233850297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6176729291237973956934125 2316273484214240233850297)
        ·
          refine ⟨1737205113160680175387723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2316273484214240233850297 1737205113160680175387723)
          ·
            refine ⟨2605807669741020263081585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737205113160680175387723 2605807669741020263081585)
            ·
              refine ⟨1954355752305765197311189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2605807669741020263081585 1954355752305765197311189)
              ·
                refine ⟨45805212944666371811981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1954355752305765197311189 45805212944666371811981)
                ·
                  refine ⟨17176954854249889429493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45805212944666371811981 17176954854249889429493)
                  ·
                    rfl

theorem cell21_75267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 3].length) (baseStart_75267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75267 prefixEnd_75267 := by exact prefixLift 75267
  have htrace : WordTrace (prefixWord ++ tailWord_75267) baseStart_75267 baseEnd_75267 := by
    simpa [prefixWord, tailWord_75267, baseEnd_75267] using wordTrace_append hprefix tailTrace_75267
  have hstable : (prefixWord ++ tailWord_75267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75267).length < 2 ^ (prefixWord ++ tailWord_75267).sum := by decide
  have hdescent : baseEnd_75267 < baseStart_75267 := by decide
  rcases family_descends (prefixWord ++ tailWord_75267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75281 : List Nat := [1, 2, 2, 1, 1, 2, 4, 4, 4]
def baseStart_75281 : Nat := 118140960795 + 75281 * 2 ^ 59
def prefixEnd_75281 : Nat := 4983230072969 + 3 ^ 40 * 75281 * 2
def baseEnd_75281 : Nat := 17180149844988976196131

theorem tailTrace_75281 : CollatzResearch.WordTrace tailWord_75281 prefixEnd_75281 17180149844988976196131 := by
  unfold tailWord_75281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745723640277268816313697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830482426851512544209131 2745723640277268816313697)
  ·
    refine ⟨2059292730207951612235273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745723640277268816313697 2059292730207951612235273)
    ·
      refine ⟨1544469547655963709176455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2059292730207951612235273 1544469547655963709176455)
      ·
        refine ⟨2316704321483945563764683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544469547655963709176455 2316704321483945563764683)
        ·
          refine ⟨3475056482225918345647025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316704321483945563764683 3475056482225918345647025)
          ·
            refine ⟨2606292361669438759235269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3475056482225918345647025 2606292361669438759235269)
            ·
              refine ⟨488679817813019767356613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2606292361669438759235269 488679817813019767356613)
              ·
                refine ⟨91627465839941206379365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 488679817813019767356613 91627465839941206379365)
                ·
                  refine ⟨17180149844988976196131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 91627465839941206379365 17180149844988976196131)
                  ·
                    rfl

theorem cell21_75281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_75281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75281 prefixEnd_75281 := by exact prefixLift 75281
  have htrace : WordTrace (prefixWord ++ tailWord_75281) baseStart_75281 baseEnd_75281 := by
    simpa [prefixWord, tailWord_75281, baseEnd_75281] using wordTrace_append hprefix tailTrace_75281
  have hstable : (prefixWord ++ tailWord_75281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75281).length < 2 ^ (prefixWord ++ tailWord_75281).sum := by decide
  have hdescent : baseEnd_75281 < baseStart_75281 := by decide
  rcases family_descends (prefixWord ++ tailWord_75281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75295 : List Nat := [1, 1, 2, 4, 1, 1, 3, 8]
def baseStart_75295 : Nat := 118140960795 + 75295 * 2 ^ 59
def prefixEnd_75295 : Nat := 4983230072969 + 3 ^ 40 * 75295 * 2
def baseEnd_75295 : Nat := 5727781611909354320923

theorem tailTrace_75295 : CollatzResearch.WordTrace tailWord_75295 prefixEnd_75295 5727781611909354320923 := by
  unfold tailWord_75295
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746234262226549207323339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1830822841484366138215559 2746234262226549207323339)
  ·
    refine ⟨4119351393339823810985009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746234262226549207323339 4119351393339823810985009)
    ·
      refine ⟨3089513545004867858238757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4119351393339823810985009 3089513545004867858238757)
      ·
        refine ⟨579283789688412723419767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3089513545004867858238757 579283789688412723419767)
        ·
          refine ⟨868925684532619085129651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 579283789688412723419767 868925684532619085129651)
          ·
            refine ⟨1303388526798928627694477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868925684532619085129651 1303388526798928627694477)
            ·
              refine ⟨488770697549598235385429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1303388526798928627694477 488770697549598235385429)
              ·
                refine ⟨5727781611909354320923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 488770697549598235385429 5727781611909354320923)
                ·
                  rfl

theorem cell21_75295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 8].length) (baseStart_75295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75295 prefixEnd_75295 := by exact prefixLift 75295
  have htrace : WordTrace (prefixWord ++ tailWord_75295) baseStart_75295 baseEnd_75295 := by
    simpa [prefixWord, tailWord_75295, baseEnd_75295] using wordTrace_append hprefix tailTrace_75295
  have hstable : (prefixWord ++ tailWord_75295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75295).length < 2 ^ (prefixWord ++ tailWord_75295).sum := by decide
  have hdescent : baseEnd_75295 < baseStart_75295 := by decide
  rcases family_descends (prefixWord ++ tailWord_75295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75422 : List Nat := [4, 3, 1, 1, 1, 4, 2, 5]
def baseStart_75422 : Nat := 118140960795 + 75422 * 2 ^ 59
def prefixEnd_75422 : Nat := 4983230072969 + 3 ^ 40 * 75422 * 2
def baseEnd_75422 : Nat := 5737442655334688115281

theorem tailTrace_75422 : CollatzResearch.WordTrace tailWord_75422 prefixEnd_75422 5737442655334688115281 := by
  unfold tailWord_75422
  simp only [CollatzResearch.WordTrace]
  refine ⟨343858291595806237149565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1833910888510966598131013 343858291595806237149565)
  ·
    refine ⟨128946859348427338931087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 343858291595806237149565 128946859348427338931087)
    ·
      refine ⟨193420289022641008396631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 128946859348427338931087 193420289022641008396631)
      ·
        refine ⟨290130433533961512594947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193420289022641008396631 290130433533961512594947)
        ·
          refine ⟨435195650300942268892421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290130433533961512594947 435195650300942268892421)
          ·
            refine ⟨81599184431426675417329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 435195650300942268892421 81599184431426675417329)
            ·
              refine ⟨61199388323570006562997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 81599184431426675417329 61199388323570006562997)
              ·
                refine ⟨5737442655334688115281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61199388323570006562997 5737442655334688115281)
                ·
                  rfl

theorem cell21_75422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_75422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75422 prefixEnd_75422 := by exact prefixLift 75422
  have htrace : WordTrace (prefixWord ++ tailWord_75422) baseStart_75422 baseEnd_75422 := by
    simpa [prefixWord, tailWord_75422, baseEnd_75422] using wordTrace_append hprefix tailTrace_75422
  have hstable : (prefixWord ++ tailWord_75422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75422).length < 2 ^ (prefixWord ++ tailWord_75422).sum := by decide
  have hdescent : baseEnd_75422 < baseStart_75422 := by decide
  rcases family_descends (prefixWord ++ tailWord_75422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75447 : List Nat := [1, 1, 3, 1, 5, 1, 9]
def baseStart_75447 : Nat := 118140960795 + 75447 * 2 ^ 59
def prefixEnd_75447 : Nat := 4983230072969 + 3 ^ 40 * 75447 * 2
def baseEnd_75447 : Nat := 1913114811845508492125

theorem tailTrace_75447 : CollatzResearch.WordTrace tailWord_75447 prefixEnd_75447 1913114811845508492125 := by
  unfold tailWord_75447
  simp only [CollatzResearch.WordTrace]
  refine ⟨2751778157675879166856595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1834518771783919444571063 2751778157675879166856595)
  ·
    refine ⟨4127667236513818750284893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2751778157675879166856595 4127667236513818750284893)
    ·
      refine ⟨1547875213692682031356835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4127667236513818750284893 1547875213692682031356835)
      ·
        refine ⟨2321812820539023047035253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547875213692682031356835 2321812820539023047035253)
        ·
          refine ⟨217669951925533410659555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2321812820539023047035253 217669951925533410659555)
          ·
            refine ⟨326504927888300115989333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217669951925533410659555 326504927888300115989333)
            ·
              refine ⟨1913114811845508492125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 326504927888300115989333 1913114811845508492125)
              ·
                rfl

theorem cell21_75447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 9].length) (baseStart_75447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75447 prefixEnd_75447 := by exact prefixLift 75447
  have htrace : WordTrace (prefixWord ++ tailWord_75447) baseStart_75447 baseEnd_75447 := by
    simpa [prefixWord, tailWord_75447, baseEnd_75447] using wordTrace_append hprefix tailTrace_75447
  have hstable : (prefixWord ++ tailWord_75447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75447).length < 2 ^ (prefixWord ++ tailWord_75447).sum := by decide
  have hdescent : baseEnd_75447 < baseStart_75447 := by decide
  rcases family_descends (prefixWord ++ tailWord_75447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75523 : List Nat := [1, 1, 1, 3, 2, 2, 5, 6]
def baseStart_75523 : Nat := 118140960795 + 75523 * 2 ^ 59
def prefixEnd_75523 : Nat := 4983230072969 + 3 ^ 40 * 75523 * 2
def baseEnd_75523 : Nat := 5745125847350111054101

theorem tailTrace_75523 : CollatzResearch.WordTrace tailWord_75523 prefixEnd_75523 5745125847350111054101 := by
  unfold tailWord_75523
  simp only [CollatzResearch.WordTrace]
  refine ⟨2754550105400544146623223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1836366736933696097748815 2754550105400544146623223)
  ·
    refine ⟨4131825158100816219934835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2754550105400544146623223 4131825158100816219934835)
    ·
      refine ⟨6197737737151224329902253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4131825158100816219934835 6197737737151224329902253)
      ·
        refine ⟨2324151651431709123713345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197737737151224329902253 2324151651431709123713345)
        ·
          refine ⟨1743113738573781842785009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324151651431709123713345 1743113738573781842785009)
          ·
            refine ⟨1307335303930336382088757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743113738573781842785009 1307335303930336382088757)
            ·
              refine ⟨122562684743469035820821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1307335303930336382088757 122562684743469035820821)
              ·
                refine ⟨5745125847350111054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 122562684743469035820821 5745125847350111054101)
                ·
                  rfl

theorem cell21_75523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 6].length) (baseStart_75523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75523 prefixEnd_75523 := by exact prefixLift 75523
  have htrace : WordTrace (prefixWord ++ tailWord_75523) baseStart_75523 baseEnd_75523 := by
    simpa [prefixWord, tailWord_75523, baseEnd_75523] using wordTrace_append hprefix tailTrace_75523
  have hstable : (prefixWord ++ tailWord_75523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75523).length < 2 ^ (prefixWord ++ tailWord_75523).sum := by decide
  have hdescent : baseEnd_75523 < baseStart_75523 := by decide
  rcases family_descends (prefixWord ++ tailWord_75523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75554 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_75554 : Nat := 118140960795 + 75554 * 2 ^ 59
def prefixEnd_75554 : Nat := 4983230072969 + 3 ^ 40 * 75554 * 2
def baseEnd_75554 : Nat := 17242452164401168145573

theorem tailTrace_75554 : CollatzResearch.WordTrace tailWord_75554 prefixEnd_75554 17242452164401168145573 := by
  unfold tailWord_75554
  simp only [CollatzResearch.WordTrace]
  refine ⟨688920192072059110250429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1837120512192157627334477 688920192072059110250429)
  ·
    refine ⟨258345072027022166343911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 688920192072059110250429 258345072027022166343911)
    ·
      refine ⟨387517608040533249515867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 258345072027022166343911 387517608040533249515867)
      ·
        refine ⟨581276412060799874273801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 387517608040533249515867 581276412060799874273801)
        ·
          refine ⟨435957309045599905705351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 581276412060799874273801 435957309045599905705351)
          ·
            refine ⟨653935963568399858558027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 435957309045599905705351 653935963568399858558027)
            ·
              refine ⟨980903945352599787837041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 653935963568399858558027 980903945352599787837041)
              ·
                refine ⟨735677959014449840877781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 980903945352599787837041 735677959014449840877781)
                ·
                  refine ⟨17242452164401168145573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 735677959014449840877781 17242452164401168145573)
                  ·
                    rfl

theorem cell21_75554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_75554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75554 prefixEnd_75554 := by exact prefixLift 75554
  have htrace : WordTrace (prefixWord ++ tailWord_75554) baseStart_75554 baseEnd_75554 := by
    simpa [prefixWord, tailWord_75554, baseEnd_75554] using wordTrace_append hprefix tailTrace_75554
  have hstable : (prefixWord ++ tailWord_75554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75554).length < 2 ^ (prefixWord ++ tailWord_75554).sum := by decide
  have hdescent : baseEnd_75554 < baseStart_75554 := by decide
  rcases family_descends (prefixWord ++ tailWord_75554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75571 : List Nat := [1, 1, 1, 2, 7, 1, 2, 1, 5]
def baseStart_75571 : Nat := 118140960795 + 75571 * 2 ^ 59
def prefixEnd_75571 : Nat := 4983230072969 + 3 ^ 40 * 75571 * 2
def baseEnd_75571 : Nat := 17246331796012916362205

theorem tailTrace_75571 : CollatzResearch.WordTrace tailWord_75571 prefixEnd_75571 17246331796012916362205 := by
  unfold tailWord_75571
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756300809226648344370567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1837533872817765562913711 2756300809226648344370567)
  ·
    refine ⟨4134451213839972516555851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756300809226648344370567 4134451213839972516555851)
    ·
      refine ⟨6201676820759958774833777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134451213839972516555851 6201676820759958774833777)
      ·
        refine ⟨4651257615569969081125333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6201676820759958774833777 4651257615569969081125333)
        ·
          refine ⟨109013850364921150338875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4651257615569969081125333 109013850364921150338875)
          ·
            refine ⟨163520775547381725508313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109013850364921150338875 163520775547381725508313)
            ·
              refine ⟨122640581660536294131235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163520775547381725508313 122640581660536294131235)
              ·
                refine ⟨183960872490804441196853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122640581660536294131235 183960872490804441196853)
                ·
                  refine ⟨17246331796012916362205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 183960872490804441196853 17246331796012916362205)
                  ·
                    rfl

theorem cell21_75571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 5].length) (baseStart_75571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75571 prefixEnd_75571 := by exact prefixLift 75571
  have htrace : WordTrace (prefixWord ++ tailWord_75571) baseStart_75571 baseEnd_75571 := by
    simpa [prefixWord, tailWord_75571, baseEnd_75571] using wordTrace_append hprefix tailTrace_75571
  have hstable : (prefixWord ++ tailWord_75571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75571).length < 2 ^ (prefixWord ++ tailWord_75571).sum := by decide
  have hdescent : baseEnd_75571 < baseStart_75571 := by decide
  rcases family_descends (prefixWord ++ tailWord_75571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75723 : List Nat := [1, 1, 1, 1, 3, 4, 4, 3, 3]
def baseStart_75723 : Nat := 118140960795 + 75723 * 2 ^ 59
def prefixEnd_75723 : Nat := 4983230072969 + 3 ^ 40 * 75723 * 2
def baseEnd_75723 : Nat := 17281020266894429828561

theorem tailTrace_75723 : CollatzResearch.WordTrace tailWord_75723 prefixEnd_75723 17281020266894429828561 := by
  unfold tailWord_75723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761844704675978303903823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1841229803117318869269215 2761844704675978303903823)
  ·
    refine ⟨4142767057013967455855735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761844704675978303903823 4142767057013967455855735)
    ·
      refine ⟨6214150585520951183783603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4142767057013967455855735 6214150585520951183783603)
      ·
        refine ⟨9321225878281426775675405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6214150585520951183783603 9321225878281426775675405)
        ·
          refine ⟨3495459704355535040878277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9321225878281426775675405 3495459704355535040878277)
          ·
            refine ⟨655398694566662820164677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3495459704355535040878277 655398694566662820164677)
            ·
              refine ⟨122887255231249278780877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 655398694566662820164677 122887255231249278780877)
              ·
                refine ⟨46082720711718479542829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 122887255231249278780877 46082720711718479542829)
                ·
                  refine ⟨17281020266894429828561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46082720711718479542829 17281020266894429828561)
                  ·
                    rfl

theorem cell21_75723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 3].length) (baseStart_75723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75723 prefixEnd_75723 := by exact prefixLift 75723
  have htrace : WordTrace (prefixWord ++ tailWord_75723) baseStart_75723 baseEnd_75723 := by
    simpa [prefixWord, tailWord_75723, baseEnd_75723] using wordTrace_append hprefix tailTrace_75723
  have hstable : (prefixWord ++ tailWord_75723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75723).length < 2 ^ (prefixWord ++ tailWord_75723).sum := by decide
  have hdescent : baseEnd_75723 < baseStart_75723 := by decide
  rcases family_descends (prefixWord ++ tailWord_75723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75737 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 6]
def baseStart_75737 : Nat := 118140960795 + 75737 * 2 ^ 59
def prefixEnd_75737 : Nat := 4983230072969 + 3 ^ 40 * 75737 * 2
def baseEnd_75737 : Nat := 17284215257633516595199

theorem tailTrace_75737 : CollatzResearch.WordTrace tailWord_75737 prefixEnd_75737 17284215257633516595199 := by
  unfold tailWord_75737
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762355326625258694913465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1841570217750172463275643 2762355326625258694913465)
  ·
    refine ⟨2071766494968944021185099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2762355326625258694913465 2071766494968944021185099)
    ·
      refine ⟨3107649742453416031777649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2071766494968944021185099 3107649742453416031777649)
      ·
        refine ⟨2330737306840062023833237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3107649742453416031777649 2330737306840062023833237)
        ·
          refine ⟨109253311258127907367183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2330737306840062023833237 109253311258127907367183)
          ·
            refine ⟨163879966887191861050775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109253311258127907367183 163879966887191861050775)
            ·
              refine ⟨245819950330787791576163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163879966887191861050775 245819950330787791576163)
              ·
                refine ⟨368729925496181687364245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 245819950330787791576163 368729925496181687364245)
                ·
                  refine ⟨17284215257633516595199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 368729925496181687364245 17284215257633516595199)
                  ·
                    rfl

theorem cell21_75737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_75737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75737 prefixEnd_75737 := by exact prefixLift 75737
  have htrace : WordTrace (prefixWord ++ tailWord_75737) baseStart_75737 baseEnd_75737 := by
    simpa [prefixWord, tailWord_75737, baseEnd_75737] using wordTrace_append hprefix tailTrace_75737
  have hstable : (prefixWord ++ tailWord_75737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75737).length < 2 ^ (prefixWord ++ tailWord_75737).sum := by decide
  have hdescent : baseEnd_75737 < baseStart_75737 := by decide
  rcases family_descends (prefixWord ++ tailWord_75737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75754 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_75754 : Nat := 118140960795 + 75754 * 2 ^ 59
def prefixEnd_75754 : Nat := 4983230072969 + 3 ^ 40 * 75754 * 2
def baseEnd_75754 : Nat := 17288094889245264811831

theorem tailTrace_75754 : CollatzResearch.WordTrace tailWord_75754 prefixEnd_75754 17288094889245264811831 := by
  unfold tailWord_75754
  simp only [CollatzResearch.WordTrace]
  refine ⟨690743841890917649570579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1841983578375780398854877 690743841890917649570579)
  ·
    refine ⟨1036115762836376474355869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 690743841890917649570579 1036115762836376474355869)
    ·
      refine ⟨388543411063641177883451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1036115762836376474355869 388543411063641177883451)
      ·
        refine ⟨582815116595461766825177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 388543411063641177883451 582815116595461766825177)
        ·
          refine ⟨437111337446596325118883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 582815116595461766825177 437111337446596325118883)
          ·
            refine ⟨655667006169894487678325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437111337446596325118883 655667006169894487678325)
            ·
              refine ⟨61468781828427608219843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 655667006169894487678325 61468781828427608219843)
              ·
                refine ⟨92203172742641412329765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61468781828427608219843 92203172742641412329765)
                ·
                  refine ⟨17288094889245264811831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92203172742641412329765 17288094889245264811831)
                  ·
                    rfl

theorem cell21_75754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_75754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75754 prefixEnd_75754 := by exact prefixLift 75754
  have htrace : WordTrace (prefixWord ++ tailWord_75754) baseStart_75754 baseEnd_75754 := by
    simpa [prefixWord, tailWord_75754, baseEnd_75754] using wordTrace_append hprefix tailTrace_75754
  have hstable : (prefixWord ++ tailWord_75754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75754).length < 2 ^ (prefixWord ++ tailWord_75754).sum := by decide
  have hdescent : baseEnd_75754 < baseStart_75754 := by decide
  rcases family_descends (prefixWord ++ tailWord_75754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75813 : List Nat := [1, 3, 1, 2, 2, 4, 1, 3, 4]
def baseStart_75813 : Nat := 118140960795 + 75813 * 2 ^ 59
def prefixEnd_75813 : Nat := 4983230072969 + 3 ^ 40 * 75813 * 2
def baseEnd_75813 : Nat := 17301559493074273328377

theorem tailTrace_75813 : CollatzResearch.WordTrace tailWord_75813 prefixEnd_75813 17301559493074273328377 := by
  unfold tailWord_75813
  simp only [CollatzResearch.WordTrace]
  refine ⟨2765127274349923674680093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1843418182899949116453395 2765127274349923674680093)
  ·
    refine ⟨1036922727881221378005035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2765127274349923674680093 1036922727881221378005035)
    ·
      refine ⟨1555384091821832067007553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036922727881221378005035 1555384091821832067007553)
      ·
        refine ⟨1166538068866374050255665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1555384091821832067007553 1166538068866374050255665)
        ·
          refine ⟨874903551649780537691749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1166538068866374050255665 874903551649780537691749)
          ·
            refine ⟨164044415934333850817203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 874903551649780537691749 164044415934333850817203)
            ·
              refine ⟨246066623901500776225805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164044415934333850817203 246066623901500776225805)
              ·
                refine ⟨92274983963062791084677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246066623901500776225805 92274983963062791084677)
                ·
                  refine ⟨17301559493074273328377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92274983963062791084677 17301559493074273328377)
                  ·
                    rfl

theorem cell21_75813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_75813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75813 prefixEnd_75813 := by exact prefixLift 75813
  have htrace : WordTrace (prefixWord ++ tailWord_75813) baseStart_75813 baseEnd_75813 := by
    simpa [prefixWord, tailWord_75813, baseEnd_75813] using wordTrace_append hprefix tailTrace_75813
  have hstable : (prefixWord ++ tailWord_75813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75813).length < 2 ^ (prefixWord ++ tailWord_75813).sum := by decide
  have hdescent : baseEnd_75813 < baseStart_75813 := by decide
  rcases family_descends (prefixWord ++ tailWord_75813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75962 : List Nat := [3, 1, 1, 1, 2, 2, 11]
def baseStart_75962 : Nat := 118140960795 + 75962 * 2 ^ 59
def prefixEnd_75962 : Nat := 4983230072969 + 3 ^ 40 * 75962 * 2
def baseEnd_75962 : Nat := 1926173702564791704971

theorem tailTrace_75962 : CollatzResearch.WordTrace tailWord_75962 prefixEnd_75962 1926173702564791704971 := by
  unfold tailWord_75962
  simp only [CollatzResearch.WordTrace]
  refine ⟨692640437702530530463535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1847041167206748081236093 692640437702530530463535)
  ·
    refine ⟨1038960656553795795695303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 692640437702530530463535 1038960656553795795695303)
    ·
      refine ⟨1558440984830693693542955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1038960656553795795695303 1558440984830693693542955)
      ·
        refine ⟨2337661477246040540314433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1558440984830693693542955 2337661477246040540314433)
        ·
          refine ⟨1753246107934530405235825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2337661477246040540314433 1753246107934530405235825)
          ·
            refine ⟨1314934580950897803926869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753246107934530405235825 1314934580950897803926869)
            ·
              refine ⟨1926173702564791704971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1314934580950897803926869 1926173702564791704971)
              ·
                rfl

theorem cell21_75962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 11].length) (baseStart_75962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75962 prefixEnd_75962 := by exact prefixLift 75962
  have htrace : WordTrace (prefixWord ++ tailWord_75962) baseStart_75962 baseEnd_75962 := by
    simpa [prefixWord, tailWord_75962, baseEnd_75962] using wordTrace_append hprefix tailTrace_75962
  have hstable : (prefixWord ++ tailWord_75962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75962).length < 2 ^ (prefixWord ++ tailWord_75962).sum := by decide
  have hdescent : baseEnd_75962 < baseStart_75962 := by decide
  rcases family_descends (prefixWord ++ tailWord_75962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75968 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 3]
def baseStart_75968 : Nat := 118140960795 + 75968 * 2 ^ 59
def prefixEnd_75968 : Nat := 4983230072969 + 3 ^ 40 * 75968 * 2
def baseEnd_75968 : Nat := 17336932604828448244727

theorem tailTrace_75968 : CollatzResearch.WordTrace tailWord_75968 prefixEnd_75968 17336932604828448244727 := by
  unfold tailWord_75968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385390294394192573286279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1847187059192256764381705 1385390294394192573286279)
  ·
    refine ⟨2078085441591288859929419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1385390294394192573286279 2078085441591288859929419)
    ·
      refine ⟨3117128162386933289894129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078085441591288859929419 3117128162386933289894129)
      ·
        refine ⟨2337846121790199967420597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3117128162386933289894129 2337846121790199967420597)
        ·
          refine ⟨219173073917831246945681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2337846121790199967420597 219173073917831246945681)
          ·
            refine ⟨164379805438373435209261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219173073917831246945681 164379805438373435209261)
            ·
              refine ⟨61642427039390038203473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164379805438373435209261 61642427039390038203473)
              ·
                refine ⟨46231820279542528652605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61642427039390038203473 46231820279542528652605)
                ·
                  refine ⟨17336932604828448244727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46231820279542528652605 17336932604828448244727)
                  ·
                    rfl

theorem cell21_75968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 3].length) (baseStart_75968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75968 prefixEnd_75968 := by exact prefixLift 75968
  have htrace : WordTrace (prefixWord ++ tailWord_75968) baseStart_75968 baseEnd_75968 := by
    simpa [prefixWord, tailWord_75968, baseEnd_75968] using wordTrace_append hprefix tailTrace_75968
  have hstable : (prefixWord ++ tailWord_75968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75968).length < 2 ^ (prefixWord ++ tailWord_75968).sum := by decide
  have hdescent : baseEnd_75968 < baseStart_75968 := by decide
  rcases family_descends (prefixWord ++ tailWord_75968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75982 : List Nat := [4, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_75982 : Nat := 118140960795 + 75982 * 2 ^ 59
def prefixEnd_75982 : Nat := 4983230072969 + 3 ^ 40 * 75982 * 2
def baseEnd_75982 : Nat := 17340127595567535011365

theorem tailTrace_75982 : CollatzResearch.WordTrace tailWord_75982 prefixEnd_75982 17340127595567535011365 := by
  unfold tailWord_75982
  simp only [CollatzResearch.WordTrace]
  refine ⟨346411401342208192197775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1847527473825110358388133 346411401342208192197775)
  ·
    refine ⟨519617102013312288296663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 346411401342208192197775 519617102013312288296663)
    ·
      refine ⟨779425653019968432444995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519617102013312288296663 779425653019968432444995)
      ·
        refine ⟨1169138479529952648667493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779425653019968432444995 1169138479529952648667493)
        ·
          refine ⟨219213464911866121625155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1169138479529952648667493 219213464911866121625155)
          ·
            refine ⟨328820197367799182437733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219213464911866121625155 328820197367799182437733)
            ·
              refine ⟨61653787006462346707075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 328820197367799182437733 61653787006462346707075)
              ·
                refine ⟨92480680509693520060613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61653787006462346707075 92480680509693520060613)
                ·
                  refine ⟨17340127595567535011365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92480680509693520060613 17340127595567535011365)
                  ·
                    rfl

theorem cell21_75982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_75982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75982 prefixEnd_75982 := by exact prefixLift 75982
  have htrace : WordTrace (prefixWord ++ tailWord_75982) baseStart_75982 baseEnd_75982 := by
    simpa [prefixWord, tailWord_75982, baseEnd_75982] using wordTrace_append hprefix tailTrace_75982
  have hstable : (prefixWord ++ tailWord_75982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75982).length < 2 ^ (prefixWord ++ tailWord_75982).sum := by decide
  have hdescent : baseEnd_75982 < baseStart_75982 := by decide
  rcases family_descends (prefixWord ++ tailWord_75982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_75993 : List Nat := [1, 2, 1, 2, 3, 1, 2, 4, 5]
def baseStart_75993 : Nat := 118140960795 + 75993 * 2 ^ 59
def prefixEnd_75993 : Nat := 4983230072969 + 3 ^ 40 * 75993 * 2
def baseEnd_75993 : Nat := 17342637945433960328009

theorem tailTrace_75993 : CollatzResearch.WordTrace tailWord_75993 prefixEnd_75993 17342637945433960328009 := by
  unfold tailWord_75993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2771692413697814416232633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1847794942465209610821755 2771692413697814416232633)
  ·
    refine ⟨2078769310273360812174475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2771692413697814416232633 2078769310273360812174475)
    ·
      refine ⟨3118153965410041218261713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2078769310273360812174475 3118153965410041218261713)
      ·
        refine ⟨2338615474057530913696285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3118153965410041218261713 2338615474057530913696285)
        ·
          refine ⟨876980802771574092636107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2338615474057530913696285 876980802771574092636107)
          ·
            refine ⟨1315471204157361138954161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876980802771574092636107 1315471204157361138954161)
            ·
              refine ⟨986603403118020854215621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1315471204157361138954161 986603403118020854215621)
              ·
                refine ⟨184988138084628910165429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 986603403118020854215621 184988138084628910165429)
                ·
                  refine ⟨17342637945433960328009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184988138084628910165429 17342637945433960328009)
                  ·
                    rfl

theorem cell21_75993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_75993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_75993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_75993 prefixEnd_75993 := by exact prefixLift 75993
  have htrace : WordTrace (prefixWord ++ tailWord_75993) baseStart_75993 baseEnd_75993 := by
    simpa [prefixWord, tailWord_75993, baseEnd_75993] using wordTrace_append hprefix tailTrace_75993
  have hstable : (prefixWord ++ tailWord_75993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_75993).length < 2 ^ (prefixWord ++ tailWord_75993).sum := by decide
  have hdescent : baseEnd_75993 < baseStart_75993 := by decide
  rcases family_descends (prefixWord ++ tailWord_75993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76182 : List Nat := [5, 3, 1, 2, 2, 8]
def baseStart_76182 : Nat := 118140960795 + 76182 * 2 ^ 59
def prefixEnd_76182 : Nat := 4983230072969 + 3 ^ 40 * 76182 * 2
def baseEnd_76182 : Nat := 643917419274504876949

theorem tailTrace_76182 : CollatzResearch.WordTrace tailWord_76182 prefixEnd_76182 643917419274504876949 := by
  unfold tailWord_76182
  simp only [CollatzResearch.WordTrace]
  refine ⟨173661613125818730928925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1852390540008733129908533 173661613125818730928925)
  ·
    refine ⟨65123104922182024098347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 173661613125818730928925 65123104922182024098347)
    ·
      refine ⟨97684657383273036147521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65123104922182024098347 97684657383273036147521)
      ·
        refine ⟨73263493037454777110641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97684657383273036147521 73263493037454777110641)
        ·
          refine ⟨54947619778091082832981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73263493037454777110641 54947619778091082832981)
          ·
            refine ⟨643917419274504876949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 54947619778091082832981 643917419274504876949)
            ·
              rfl

theorem cell21_76182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 8].length) (baseStart_76182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76182 prefixEnd_76182 := by exact prefixLift 76182
  have htrace : WordTrace (prefixWord ++ tailWord_76182) baseStart_76182 baseEnd_76182 := by
    simpa [prefixWord, tailWord_76182, baseEnd_76182] using wordTrace_append hprefix tailTrace_76182
  have hstable : (prefixWord ++ tailWord_76182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76182).length < 2 ^ (prefixWord ++ tailWord_76182).sum := by decide
  have hdescent : baseEnd_76182 < baseStart_76182 := by decide
  rcases family_descends (prefixWord ++ tailWord_76182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76221 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 7]
def baseStart_76221 : Nat := 118140960795 + 76221 * 2 ^ 59
def prefixEnd_76221 : Nat := 4983230072969 + 3 ^ 40 * 76221 * 2
def baseEnd_76221 : Nat := 17394670651756230527543

theorem tailTrace_76221 : CollatzResearch.WordTrace tailWord_76221 prefixEnd_76221 17394670651756230527543 := by
  unfold tailWord_76221
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780008256871809355532517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1853338837914539570355011 2780008256871809355532517)
  ·
    refine ⟨521251548163464254162347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2780008256871809355532517 521251548163464254162347)
    ·
      refine ⟨781877322245196381243521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521251548163464254162347 781877322245196381243521)
      ·
        refine ⟨586407991683897285932641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781877322245196381243521 586407991683897285932641)
        ·
          refine ⟨439805993762922964449481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586407991683897285932641 439805993762922964449481)
          ·
            refine ⟨329854495322192223337111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439805993762922964449481 329854495322192223337111)
            ·
              refine ⟨494781742983288335005667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329854495322192223337111 494781742983288335005667)
              ·
                refine ⟨742172614474932502508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494781742983288335005667 742172614474932502508501)
                ·
                  refine ⟨17394670651756230527543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 742172614474932502508501 17394670651756230527543)
                  ·
                    rfl

theorem cell21_76221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_76221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76221 prefixEnd_76221 := by exact prefixLift 76221
  have htrace : WordTrace (prefixWord ++ tailWord_76221) baseStart_76221 baseEnd_76221 := by
    simpa [prefixWord, tailWord_76221, baseEnd_76221] using wordTrace_append hprefix tailTrace_76221
  have hstable : (prefixWord ++ tailWord_76221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76221).length < 2 ^ (prefixWord ++ tailWord_76221).sum := by decide
  have hdescent : baseEnd_76221 < baseStart_76221 := by decide
  rcases family_descends (prefixWord ++ tailWord_76221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76235 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 6]
def baseStart_76235 : Nat := 118140960795 + 76235 * 2 ^ 59
def prefixEnd_76235 : Nat := 4983230072969 + 3 ^ 40 * 76235 * 2
def baseEnd_76235 : Nat := 17397865642495317294181

theorem tailTrace_76235 : CollatzResearch.WordTrace tailWord_76235 prefixEnd_76235 17397865642495317294181 := by
  unfold tailWord_76235
  simp only [CollatzResearch.WordTrace]
  refine ⟨2780518878821089746542159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1853679252547393164361439 2780518878821089746542159)
  ·
    refine ⟨4170778318231634619813239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2780518878821089746542159 4170778318231634619813239)
    ·
      refine ⟨6256167477347451929719859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170778318231634619813239 6256167477347451929719859)
      ·
        refine ⟨9384251216021177894579789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256167477347451929719859 9384251216021177894579789)
        ·
          refine ⟨3519094206007941710467421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9384251216021177894579789 3519094206007941710467421)
          ·
            refine ⟨1319660327252978141425283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3519094206007941710467421 1319660327252978141425283)
            ·
              refine ⟨1979490490879467212137925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319660327252978141425283 1979490490879467212137925)
              ·
                refine ⟨371154467039900102275861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1979490490879467212137925 371154467039900102275861)
                ·
                  refine ⟨17397865642495317294181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 371154467039900102275861 17397865642495317294181)
                  ·
                    rfl

theorem cell21_76235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 6].length) (baseStart_76235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76235 prefixEnd_76235 := by exact prefixLift 76235
  have htrace : WordTrace (prefixWord ++ tailWord_76235) baseStart_76235 baseEnd_76235 := by
    simpa [prefixWord, tailWord_76235, baseEnd_76235] using wordTrace_append hprefix tailTrace_76235
  have hstable : (prefixWord ++ tailWord_76235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76235).length < 2 ^ (prefixWord ++ tailWord_76235).sum := by decide
  have hdescent : baseEnd_76235 < baseStart_76235 := by decide
  rcases family_descends (prefixWord ++ tailWord_76235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76314 : List Nat := [3, 1, 1, 3, 1, 1, 2, 6, 3]
def baseStart_76314 : Nat := 118140960795 + 76314 * 2 ^ 59
def prefixEnd_76314 : Nat := 4983230072969 + 3 ^ 40 * 76314 * 2
def baseEnd_76314 : Nat := 17415894518808735477353

theorem tailTrace_76314 : CollatzResearch.WordTrace tailWord_76314 prefixEnd_76314 17415894518808735477353 := by
  unfold tailWord_76314
  simp only [CollatzResearch.WordTrace]
  refine ⟨695850061383721559666999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1855600163689924159111997 695850061383721559666999)
  ·
    refine ⟨1043775092075582339500499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 695850061383721559666999 1043775092075582339500499)
    ·
      refine ⟨1565662638113373509250749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1043775092075582339500499 1565662638113373509250749)
      ·
        refine ⟨587123489292515065969031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1565662638113373509250749 587123489292515065969031)
        ·
          refine ⟨880685233938772598953547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587123489292515065969031 880685233938772598953547)
          ·
            refine ⟨1321027850908158898430321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880685233938772598953547 1321027850908158898430321)
            ·
              refine ⟨990770888181119173822741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1321027850908158898430321 990770888181119173822741)
              ·
                refine ⟨46442385383489961272941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 990770888181119173822741 46442385383489961272941)
                ·
                  refine ⟨17415894518808735477353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46442385383489961272941 17415894518808735477353)
                  ·
                    rfl

theorem cell21_76314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 3].length) (baseStart_76314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76314 prefixEnd_76314 := by exact prefixLift 76314
  have htrace : WordTrace (prefixWord ++ tailWord_76314) baseStart_76314 baseEnd_76314 := by
    simpa [prefixWord, tailWord_76314, baseEnd_76314] using wordTrace_append hprefix tailTrace_76314
  have hstable : (prefixWord ++ tailWord_76314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76314).length < 2 ^ (prefixWord ++ tailWord_76314).sum := by decide
  have hdescent : baseEnd_76314 < baseStart_76314 := by decide
  rcases family_descends (prefixWord ++ tailWord_76314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76365 : List Nat := [1, 6, 1, 1, 2, 3, 2, 2, 3]
def baseStart_76365 : Nat := 118140960795 + 76365 * 2 ^ 59
def prefixEnd_76365 : Nat := 4983230072969 + 3 ^ 40 * 76365 * 2
def baseEnd_76365 : Nat := 17427533413643980127249

theorem tailTrace_76365 : CollatzResearch.WordTrace tailWord_76365 prefixEnd_76365 17427533413643980127249 := by
  unfold tailWord_76365
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785260368350121948774549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1856840245566747965849699 2785260368350121948774549)
  ·
    refine ⟨130559079766411966348807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2785260368350121948774549 130559079766411966348807)
    ·
      refine ⟨195838619649617949523211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130559079766411966348807 195838619649617949523211)
      ·
        refine ⟨293757929474426924284817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195838619649617949523211 293757929474426924284817)
        ·
          refine ⟨220318447105820193213613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293757929474426924284817 220318447105820193213613)
          ·
            refine ⟨82619417664682572455105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220318447105820193213613 82619417664682572455105)
            ·
              refine ⟨61964563248511929341329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82619417664682572455105 61964563248511929341329)
              ·
                refine ⟨46473422436383947005997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61964563248511929341329 46473422436383947005997)
                ·
                  refine ⟨17427533413643980127249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46473422436383947005997 17427533413643980127249)
                  ·
                    rfl

theorem cell21_76365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_76365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76365 prefixEnd_76365 := by exact prefixLift 76365
  have htrace : WordTrace (prefixWord ++ tailWord_76365) baseStart_76365 baseEnd_76365 := by
    simpa [prefixWord, tailWord_76365, baseEnd_76365] using wordTrace_append hprefix tailTrace_76365
  have hstable : (prefixWord ++ tailWord_76365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76365).length < 2 ^ (prefixWord ++ tailWord_76365).sum := by decide
  have hdescent : baseEnd_76365 < baseStart_76365 := by decide
  rcases family_descends (prefixWord ++ tailWord_76365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76421 : List Nat := [1, 3, 1, 1, 4, 4, 1, 2, 4]
def baseStart_76421 : Nat := 118140960795 + 76421 * 2 ^ 59
def prefixEnd_76421 : Nat := 4983230072969 + 3 ^ 40 * 76421 * 2
def baseEnd_76421 : Nat := 17440313376600327193801

theorem tailTrace_76421 : CollatzResearch.WordTrace tailWord_76421 prefixEnd_76421 17440313376600327193801 := by
  unfold tailWord_76421
  simp only [CollatzResearch.WordTrace]
  refine ⟨2787302856147243512813117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1858201904098162341875411 2787302856147243512813117)
  ·
    refine ⟨1045238571055216317304919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2787302856147243512813117 1045238571055216317304919)
    ·
      refine ⟨1567857856582824475957379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1045238571055216317304919 1567857856582824475957379)
      ·
        refine ⟨2351786784874236713936069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567857856582824475957379 2351786784874236713936069)
        ·
          refine ⟨440960022163919383863013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2351786784874236713936069 440960022163919383863013)
          ·
            refine ⟨82680004155734884474315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 440960022163919383863013 82680004155734884474315)
            ·
              refine ⟨124020006233602326711473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82680004155734884474315 124020006233602326711473)
              ·
                refine ⟨93015004675201745033605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124020006233602326711473 93015004675201745033605)
                ·
                  refine ⟨17440313376600327193801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93015004675201745033605 17440313376600327193801)
                  ·
                    rfl

theorem cell21_76421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_76421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76421 prefixEnd_76421 := by exact prefixLift 76421
  have htrace : WordTrace (prefixWord ++ tailWord_76421) baseStart_76421 baseEnd_76421 := by
    simpa [prefixWord, tailWord_76421, baseEnd_76421] using wordTrace_append hprefix tailTrace_76421
  have hstable : (prefixWord ++ tailWord_76421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76421).length < 2 ^ (prefixWord ++ tailWord_76421).sum := by decide
  have hdescent : baseEnd_76421 < baseStart_76421 := by decide
  rcases family_descends (prefixWord ++ tailWord_76421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76458 : List Nat := [3, 1, 5, 2, 2, 1, 1, 3, 3]
def baseStart_76458 : Nat := 118140960795 + 76458 * 2 ^ 59
def prefixEnd_76458 : Nat := 4983230072969 + 3 ^ 40 * 76458 * 2
def baseEnd_76458 : Nat := 17448757280696485077059

theorem tailTrace_76458 : CollatzResearch.WordTrace tailWord_76458 prefixEnd_76458 17448757280696485077059 := by
  unfold tailWord_76458
  simp only [CollatzResearch.WordTrace]
  refine ⟨697163089253299707977507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1859101571342132554606685 697163089253299707977507)
  ·
    refine ⟨1045744633879949561966261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697163089253299707977507 1045744633879949561966261)
    ·
      refine ⟨98038559426245271434337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1045744633879949561966261 98038559426245271434337)
      ·
        refine ⟨73528919569683953575753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98038559426245271434337 73528919569683953575753)
        ·
          refine ⟨55146689677262965181815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73528919569683953575753 55146689677262965181815)
          ·
            refine ⟨82720034515894447772723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55146689677262965181815 82720034515894447772723)
            ·
              refine ⟨124080051773841671659085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82720034515894447772723 124080051773841671659085)
              ·
                refine ⟨46530019415190626872157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124080051773841671659085 46530019415190626872157)
                ·
                  refine ⟨17448757280696485077059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46530019415190626872157 17448757280696485077059)
                  ·
                    rfl

theorem cell21_76458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_76458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76458 prefixEnd_76458 := by exact prefixLift 76458
  have htrace : WordTrace (prefixWord ++ tailWord_76458) baseStart_76458 baseEnd_76458 := by
    simpa [prefixWord, tailWord_76458, baseEnd_76458] using wordTrace_append hprefix tailTrace_76458
  have hstable : (prefixWord ++ tailWord_76458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76458).length < 2 ^ (prefixWord ++ tailWord_76458).sum := by decide
  have hdescent : baseEnd_76458 < baseStart_76458 := by decide
  rcases family_descends (prefixWord ++ tailWord_76458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76463 : List Nat := [1, 1, 2, 1, 2, 5, 1, 2, 6]
def baseStart_76463 : Nat := 118140960795 + 76463 * 2 ^ 59
def prefixEnd_76463 : Nat := 4983230072969 + 3 ^ 40 * 76463 * 2
def baseEnd_76463 : Nat := 17449898348817587493715

theorem tailTrace_76463 : CollatzResearch.WordTrace tailWord_76463 prefixEnd_76463 17449898348817587493715 := by
  unfold tailWord_76463
  simp only [CollatzResearch.WordTrace]
  refine ⟨2788834721995084685842043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1859223147996723123894695 2788834721995084685842043)
  ·
    refine ⟨4183252082992627028763065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2788834721995084685842043 4183252082992627028763065)
    ·
      refine ⟨3137439062244470271572299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183252082992627028763065 3137439062244470271572299)
      ·
        refine ⟨4706158593366705407358449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137439062244470271572299 4706158593366705407358449)
        ·
          refine ⟨3529618945025029055518837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706158593366705407358449 3529618945025029055518837)
          ·
            refine ⟨330901776096096473954891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3529618945025029055518837 330901776096096473954891)
            ·
              refine ⟨496352664144144710932337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330901776096096473954891 496352664144144710932337)
              ·
                refine ⟨372264498108108533199253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496352664144144710932337 372264498108108533199253)
                ·
                  refine ⟨17449898348817587493715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 372264498108108533199253 17449898348817587493715)
                  ·
                    rfl

theorem cell21_76463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 2, 6].length) (baseStart_76463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76463 prefixEnd_76463 := by exact prefixLift 76463
  have htrace : WordTrace (prefixWord ++ tailWord_76463) baseStart_76463 baseEnd_76463 := by
    simpa [prefixWord, tailWord_76463, baseEnd_76463] using wordTrace_append hprefix tailTrace_76463
  have hstable : (prefixWord ++ tailWord_76463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76463).length < 2 ^ (prefixWord ++ tailWord_76463).sum := by decide
  have hdescent : baseEnd_76463 < baseStart_76463 := by decide
  rcases family_descends (prefixWord ++ tailWord_76463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76494 : List Nat := [4, 1, 1, 1, 3, 2, 1, 8]
def baseStart_76494 : Nat := 118140960795 + 76494 * 2 ^ 59
def prefixEnd_76494 : Nat := 4983230072969 + 3 ^ 40 * 76494 * 2
def baseEnd_76494 : Nat := 5818990990389474158995

theorem tailTrace_76494 : CollatzResearch.WordTrace tailWord_76494 prefixEnd_76494 5818990990389474158995 := by
  unfold tailWord_76494
  simp only [CollatzResearch.WordTrace]
  refine ⟨348745673110347122527567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1859976923255184653480357 348745673110347122527567)
  ·
    refine ⟨523118509665520683791351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 348745673110347122527567 523118509665520683791351)
    ·
      refine ⟨784677764498281025687027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523118509665520683791351 784677764498281025687027)
      ·
        refine ⟨1177016646747421538530541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784677764498281025687027 1177016646747421538530541)
        ·
          refine ⟨441381242530283076948953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1177016646747421538530541 441381242530283076948953)
          ·
            refine ⟨331035931897712307711715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441381242530283076948953 331035931897712307711715)
            ·
              refine ⟨496553897846568461567573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331035931897712307711715 496553897846568461567573)
              ·
                refine ⟨5818990990389474158995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 496553897846568461567573 5818990990389474158995)
                ·
                  rfl

theorem cell21_76494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_76494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76494 prefixEnd_76494 := by exact prefixLift 76494
  have htrace : WordTrace (prefixWord ++ tailWord_76494) baseStart_76494 baseEnd_76494 := by
    simpa [prefixWord, tailWord_76494, baseEnd_76494] using wordTrace_append hprefix tailTrace_76494
  have hstable : (prefixWord ++ tailWord_76494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76494).length < 2 ^ (prefixWord ++ tailWord_76494).sum := by decide
  have hdescent : baseEnd_76494 < baseStart_76494 := by decide
  rcases family_descends (prefixWord ++ tailWord_76494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76590 : List Nat := [4, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_76590 : Nat := 118140960795 + 76590 * 2 ^ 59
def prefixEnd_76590 : Nat := 4983230072969 + 3 ^ 40 * 76590 * 2
def baseEnd_76590 : Nat := 17478881479093588876789

theorem tailTrace_76590 : CollatzResearch.WordTrace tailWord_76590 prefixEnd_76590 17478881479093588876789 := by
  unfold tailWord_76590
  simp only [CollatzResearch.WordTrace]
  refine ⟨349183349066873171964403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1862311195023323583810149 349183349066873171964403)
  ·
    refine ⟨523775023600309757946605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349183349066873171964403 523775023600309757946605)
    ·
      refine ⟨196415633850116159229977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 523775023600309757946605 196415633850116159229977)
      ·
        refine ⟨147311725387587119422483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196415633850116159229977 147311725387587119422483)
        ·
          refine ⟨220967588081380679133725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147311725387587119422483 220967588081380679133725)
          ·
            refine ⟨82862845530517754675147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220967588081380679133725 82862845530517754675147)
            ·
              refine ⟨124294268295776632012721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82862845530517754675147 124294268295776632012721)
              ·
                refine ⟨93220701221832474009541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124294268295776632012721 93220701221832474009541)
                ·
                  refine ⟨17478881479093588876789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93220701221832474009541 17478881479093588876789)
                  ·
                    rfl

theorem cell21_76590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_76590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76590 prefixEnd_76590 := by exact prefixLift 76590
  have htrace : WordTrace (prefixWord ++ tailWord_76590) baseStart_76590 baseEnd_76590 := by
    simpa [prefixWord, tailWord_76590, baseEnd_76590] using wordTrace_append hprefix tailTrace_76590
  have hstable : (prefixWord ++ tailWord_76590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76590).length < 2 ^ (prefixWord ++ tailWord_76590).sum := by decide
  have hdescent : baseEnd_76590 < baseStart_76590 := by decide
  rcases family_descends (prefixWord ++ tailWord_76590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76621 : List Nat := [1, 6, 1, 2, 2, 2, 2, 5]
def baseStart_76621 : Nat := 118140960795 + 76621 * 2 ^ 59
def prefixEnd_76621 : Nat := 4983230072969 + 3 ^ 40 * 76621 * 2
def baseEnd_76621 : Nat := 5828652033814807953353

theorem tailTrace_76621 : CollatzResearch.WordTrace tailWord_76621 prefixEnd_76621 5828652033814807953353 := by
  unfold tailWord_76621
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794597455422677670093717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1863064970281785113395811 2794597455422677670093717)
  ·
    refine ⟨130996755722938015785643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2794597455422677670093717 130996755722938015785643)
    ·
      refine ⟨196495133584407023678465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130996755722938015785643 196495133584407023678465)
      ·
        refine ⟨147371350188305267758849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196495133584407023678465 147371350188305267758849)
        ·
          refine ⟨110528512641228950819137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147371350188305267758849 110528512641228950819137)
          ·
            refine ⟨82896384480921713114353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110528512641228950819137 82896384480921713114353)
            ·
              refine ⟨62172288360691284835765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82896384480921713114353 62172288360691284835765)
              ·
                refine ⟨5828652033814807953353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62172288360691284835765 5828652033814807953353)
                ·
                  rfl

theorem cell21_76621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 5].length) (baseStart_76621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76621 prefixEnd_76621 := by exact prefixLift 76621
  have htrace : WordTrace (prefixWord ++ tailWord_76621) baseStart_76621 baseEnd_76621 := by
    simpa [prefixWord, tailWord_76621, baseEnd_76621] using wordTrace_append hprefix tailTrace_76621
  have hstable : (prefixWord ++ tailWord_76621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76621).length < 2 ^ (prefixWord ++ tailWord_76621).sum := by decide
  have hdescent : baseEnd_76621 < baseStart_76621 := by decide
  rcases family_descends (prefixWord ++ tailWord_76621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76708 : List Nat := [2, 3, 1, 2, 1, 2, 4, 2, 4]
def baseStart_76708 : Nat := 118140960795 + 76708 * 2 ^ 59
def prefixEnd_76708 : Nat := 4983230072969 + 3 ^ 40 * 76708 * 2
def baseEnd_76708 : Nat := 17505810686751605909881

theorem tailTrace_76708 : CollatzResearch.WordTrace tailWord_76708 prefixEnd_76708 17505810686751605909881 := by
  unfold tailWord_76708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1398885303053745764255389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1865180404071661019007185 1398885303053745764255389)
  ·
    refine ⟨524581988645154661595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1398885303053745764255389 524581988645154661595771)
    ·
      refine ⟨786872982967731992393657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 524581988645154661595771 786872982967731992393657)
      ·
        refine ⟨590154737225798994295243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 786872982967731992393657 590154737225798994295243)
        ·
          refine ⟨885232105838698491442865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590154737225798994295243 885232105838698491442865)
          ·
            refine ⟨663924079379023868582149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 885232105838698491442865 663924079379023868582149)
            ·
              refine ⟨124485764883566975359153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 663924079379023868582149 124485764883566975359153)
              ·
                refine ⟨93364323662675231519365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124485764883566975359153 93364323662675231519365)
                ·
                  refine ⟨17505810686751605909881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93364323662675231519365 17505810686751605909881)
                  ·
                    rfl

theorem cell21_76708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_76708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76708 prefixEnd_76708 := by exact prefixLift 76708
  have htrace : WordTrace (prefixWord ++ tailWord_76708) baseStart_76708 baseEnd_76708 := by
    simpa [prefixWord, tailWord_76708, baseEnd_76708] using wordTrace_append hprefix tailTrace_76708
  have hstable : (prefixWord ++ tailWord_76708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76708).length < 2 ^ (prefixWord ++ tailWord_76708).sum := by decide
  have hdescent : baseEnd_76708 < baseStart_76708 := by decide
  rcases family_descends (prefixWord ++ tailWord_76708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76711 : List Nat := [1, 1, 6, 1, 3, 1, 1, 4, 3]
def baseStart_76711 : Nat := 118140960795 + 76711 * 2 ^ 59
def prefixEnd_76711 : Nat := 4983230072969 + 3 ^ 40 * 76711 * 2
def baseEnd_76711 : Nat := 17506495327624267359875

theorem tailTrace_76711 : CollatzResearch.WordTrace tailWord_76711 prefixEnd_76711 17506495327624267359875 := by
  unfold tailWord_76711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797880025096623040869987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1865253350064415360579991 2797880025096623040869987)
  ·
    refine ⟨4196820037644934561304981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2797880025096623040869987 4196820037644934561304981)
    ·
      refine ⟨196725939264606307561171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4196820037644934561304981 196725939264606307561171)
      ·
        refine ⟨295088908896909461341757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196725939264606307561171 295088908896909461341757)
        ·
          refine ⟨110658340836341048003159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295088908896909461341757 110658340836341048003159)
          ·
            refine ⟨165987511254511572004739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110658340836341048003159 165987511254511572004739)
            ·
              refine ⟨248981266881767358007109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165987511254511572004739 248981266881767358007109)
              ·
                refine ⟨46683987540331379626333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248981266881767358007109 46683987540331379626333)
                ·
                  refine ⟨17506495327624267359875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46683987540331379626333 17506495327624267359875)
                  ·
                    rfl

theorem cell21_76711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 4, 3].length) (baseStart_76711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76711 prefixEnd_76711 := by exact prefixLift 76711
  have htrace : WordTrace (prefixWord ++ tailWord_76711) baseStart_76711 baseEnd_76711 := by
    simpa [prefixWord, tailWord_76711, baseEnd_76711] using wordTrace_append hprefix tailTrace_76711
  have hstable : (prefixWord ++ tailWord_76711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76711).length < 2 ^ (prefixWord ++ tailWord_76711).sum := by decide
  have hdescent : baseEnd_76711 < baseStart_76711 := by decide
  rcases family_descends (prefixWord ++ tailWord_76711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76736 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_76736 : Nat := 118140960795 + 76736 * 2 ^ 59
def prefixEnd_76736 : Nat := 4983230072969 + 3 ^ 40 * 76736 * 2
def baseEnd_76736 : Nat := 17512200668229779443157

theorem tailTrace_76736 : CollatzResearch.WordTrace tailWord_76736 prefixEnd_76736 17512200668229779443157 := by
  unfold tailWord_76736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399395925003026155265031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1865861233337368207020041 1399395925003026155265031)
  ·
    refine ⟨2099093887504539232897547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399395925003026155265031 2099093887504539232897547)
    ·
      refine ⟨3148640831256808849346321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2099093887504539232897547 3148640831256808849346321)
      ·
        refine ⟨2361480623442606637009741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3148640831256808849346321 2361480623442606637009741)
        ·
          refine ⟨885555233790977488878653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2361480623442606637009741 885555233790977488878653)
          ·
            refine ⟨332083212671616558329495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 885555233790977488878653 332083212671616558329495)
            ·
              refine ⟨498124819007424837494243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332083212671616558329495 498124819007424837494243)
              ·
                refine ⟨747187228511137256241365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498124819007424837494243 747187228511137256241365)
                ·
                  refine ⟨17512200668229779443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 747187228511137256241365 17512200668229779443157)
                  ·
                    rfl

theorem cell21_76736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_76736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76736 prefixEnd_76736 := by exact prefixLift 76736
  have htrace : WordTrace (prefixWord ++ tailWord_76736) baseStart_76736 baseEnd_76736 := by
    simpa [prefixWord, tailWord_76736, baseEnd_76736] using wordTrace_append hprefix tailTrace_76736
  have hstable : (prefixWord ++ tailWord_76736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76736).length < 2 ^ (prefixWord ++ tailWord_76736).sum := by decide
  have hdescent : baseEnd_76736 < baseStart_76736 := by decide
  rcases family_descends (prefixWord ++ tailWord_76736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76770 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 5]
def baseStart_76770 : Nat := 118140960795 + 76770 * 2 ^ 59
def prefixEnd_76770 : Nat := 4983230072969 + 3 ^ 40 * 76770 * 2
def baseEnd_76770 : Nat := 17519959931453275876421

theorem tailTrace_76770 : CollatzResearch.WordTrace tailWord_76770 prefixEnd_76770 17519959931453275876421 := by
  unfold tailWord_76770
  simp only [CollatzResearch.WordTrace]
  refine ⟨700007982970719029316941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1866687954588584078178509 700007982970719029316941)
  ·
    refine ⟨262502993614019635993853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 700007982970719029316941 262502993614019635993853)
    ·
      refine ⟨98438622605257363497695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 262502993614019635993853 98438622605257363497695)
      ·
        refine ⟨147657933907886045246543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98438622605257363497695 147657933907886045246543)
        ·
          refine ⟨221486900861829067869815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147657933907886045246543 221486900861829067869815)
          ·
            refine ⟨332230351292743601804723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221486900861829067869815 332230351292743601804723)
            ·
              refine ⟨498345526939115402707085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332230351292743601804723 498345526939115402707085)
              ·
                refine ⟨186879572602168276015157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498345526939115402707085 186879572602168276015157)
                ·
                  refine ⟨17519959931453275876421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186879572602168276015157 17519959931453275876421)
                  ·
                    rfl

theorem cell21_76770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_76770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76770 prefixEnd_76770 := by exact prefixLift 76770
  have htrace : WordTrace (prefixWord ++ tailWord_76770) baseStart_76770 baseEnd_76770 := by
    simpa [prefixWord, tailWord_76770, baseEnd_76770] using wordTrace_append hprefix tailTrace_76770
  have hstable : (prefixWord ++ tailWord_76770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76770).length < 2 ^ (prefixWord ++ tailWord_76770).sum := by decide
  have hdescent : baseEnd_76770 < baseStart_76770 := by decide
  rcases family_descends (prefixWord ++ tailWord_76770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76843 : List Nat := [1, 1, 1, 1, 2, 1, 7, 3, 4]
def baseStart_76843 : Nat := 118140960795 + 76843 * 2 ^ 59
def prefixEnd_76843 : Nat := 4983230072969 + 3 ^ 40 * 76843 * 2
def baseEnd_76843 : Nat := 17536619526021371159605

theorem tailTrace_76843 : CollatzResearch.WordTrace tailWord_76843 prefixEnd_76843 17536619526021371159605 := by
  unfold tailWord_76843
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802694460618409584675183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1868462973745606389783455 2802694460618409584675183)
  ·
    refine ⟨4204041690927614377012775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802694460618409584675183 4204041690927614377012775)
    ·
      refine ⟨6306062536391421565519163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4204041690927614377012775 6306062536391421565519163)
      ·
        refine ⟨9459093804587132348278745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6306062536391421565519163 9459093804587132348278745)
        ·
          refine ⟨7094320353440349261209059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9459093804587132348278745 7094320353440349261209059)
          ·
            refine ⟨10641480530160523891813589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7094320353440349261209059 10641480530160523891813589)
            ·
              refine ⟨249409699925637278714381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10641480530160523891813589 249409699925637278714381)
              ·
                refine ⟨93528637472113979517893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249409699925637278714381 93528637472113979517893)
                ·
                  refine ⟨17536619526021371159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93528637472113979517893 17536619526021371159605)
                  ·
                    rfl

theorem cell21_76843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 4].length) (baseStart_76843 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76843 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76843 prefixEnd_76843 := by exact prefixLift 76843
  have htrace : WordTrace (prefixWord ++ tailWord_76843) baseStart_76843 baseEnd_76843 := by
    simpa [prefixWord, tailWord_76843, baseEnd_76843] using wordTrace_append hprefix tailTrace_76843
  have hstable : (prefixWord ++ tailWord_76843).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76843).length < 2 ^ (prefixWord ++ tailWord_76843).sum := by decide
  have hdescent : baseEnd_76843 < baseStart_76843 := by decide
  rcases family_descends (prefixWord ++ tailWord_76843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76877 : List Nat := [1, 6, 1, 1, 1, 3, 2, 2, 4]
def baseStart_76877 : Nat := 118140960795 + 76877 * 2 ^ 59
def prefixEnd_76877 : Nat := 4983230072969 + 3 ^ 40 * 76877 * 2
def baseEnd_76877 : Nat := 17544378789244867592869

theorem tailTrace_76877 : CollatzResearch.WordTrace tailWord_76877 prefixEnd_76877 17544378789244867592869 := by
  unfold tailWord_76877
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803934542495233391412885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1869289694996822260941923 2803934542495233391412885)
  ·
    refine ⟨131434431679464065222479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2803934542495233391412885 131434431679464065222479)
    ·
      refine ⟨197151647519196097833719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 131434431679464065222479 197151647519196097833719)
      ·
        refine ⟨295727471278794146750579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197151647519196097833719 295727471278794146750579)
        ·
          refine ⟨443591206918191220125869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295727471278794146750579 443591206918191220125869)
          ·
            refine ⟨166346702594321707547201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443591206918191220125869 166346702594321707547201)
            ·
              refine ⟨124760026945741280660401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166346702594321707547201 124760026945741280660401)
              ·
                refine ⟨93570020209305960495301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124760026945741280660401 93570020209305960495301)
                ·
                  refine ⟨17544378789244867592869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93570020209305960495301 17544378789244867592869)
                  ·
                    rfl

theorem cell21_76877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_76877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76877 prefixEnd_76877 := by exact prefixLift 76877
  have htrace : WordTrace (prefixWord ++ tailWord_76877) baseStart_76877 baseEnd_76877 := by
    simpa [prefixWord, tailWord_76877, baseEnd_76877] using wordTrace_append hprefix tailTrace_76877
  have hstable : (prefixWord ++ tailWord_76877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76877).length < 2 ^ (prefixWord ++ tailWord_76877).sum := by decide
  have hdescent : baseEnd_76877 < baseStart_76877 := by decide
  rcases family_descends (prefixWord ++ tailWord_76877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76888 : List Nat := [2, 1, 2, 2, 1, 3, 2, 3, 5]
def baseStart_76888 : Nat := 118140960795 + 76888 * 2 ^ 59
def prefixEnd_76888 : Nat := 4983230072969 + 3 ^ 40 * 76888 * 2
def baseEnd_76888 : Nat := 17546889139111292909513

theorem tailTrace_76888 : CollatzResearch.WordTrace tailWord_76888 prefixEnd_76888 17546889139111292909513 := by
  unfold tailWord_76888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402167872727691135031659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1869557163636921513375545 1402167872727691135031659)
  ·
    refine ⟨2103251809091536702547489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402167872727691135031659 2103251809091536702547489)
    ·
      refine ⟨1577438856818652526910617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2103251809091536702547489 1577438856818652526910617)
      ·
        refine ⟨1183079142613989395182963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577438856818652526910617 1183079142613989395182963)
        ·
          refine ⟨1774618713920984092774445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183079142613989395182963 1774618713920984092774445)
          ·
            refine ⟨665482017720369034790417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1774618713920984092774445 665482017720369034790417)
            ·
              refine ⟨499111513290276776092813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665482017720369034790417 499111513290276776092813)
              ·
                refine ⟨187166817483853791034805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499111513290276776092813 187166817483853791034805)
                ·
                  refine ⟨17546889139111292909513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187166817483853791034805 17546889139111292909513)
                  ·
                    rfl

theorem cell21_76888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_76888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76888 prefixEnd_76888 := by exact prefixLift 76888
  have htrace : WordTrace (prefixWord ++ tailWord_76888) baseStart_76888 baseEnd_76888 := by
    simpa [prefixWord, tailWord_76888, baseEnd_76888] using wordTrace_append hprefix tailTrace_76888
  have hstable : (prefixWord ++ tailWord_76888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76888).length < 2 ^ (prefixWord ++ tailWord_76888).sum := by decide
  have hdescent : baseEnd_76888 < baseStart_76888 := by decide
  rcases family_descends (prefixWord ++ tailWord_76888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76894 : List Nat := [4, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_76894 : Nat := 118140960795 + 76894 * 2 ^ 59
def prefixEnd_76894 : Nat := 4983230072969 + 3 ^ 40 * 76894 * 2
def baseEnd_76894 : Nat := 17548258420856615809501

theorem tailTrace_76894 : CollatzResearch.WordTrace tailWord_76894 prefixEnd_76894 17548258420856615809501 := by
  unfold tailWord_76894
  simp only [CollatzResearch.WordTrace]
  refine ⟨350569322929205661847717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1869703055622430196521157 350569322929205661847717)
  ·
    refine ⟨65731748049226061596447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 350569322929205661847717 65731748049226061596447)
    ·
      refine ⟨98597622073839092394671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65731748049226061596447 98597622073839092394671)
      ·
        refine ⟨147896433110758638592007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98597622073839092394671 147896433110758638592007)
        ·
          refine ⟨221844649666137957888011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147896433110758638592007 221844649666137957888011)
          ·
            refine ⟨332766974499206936832017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221844649666137957888011 332766974499206936832017)
            ·
              refine ⟨249575230874405202624013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332766974499206936832017 249575230874405202624013)
              ·
                refine ⟨93590711577901950984005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249575230874405202624013 93590711577901950984005)
                ·
                  refine ⟨17548258420856615809501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93590711577901950984005 17548258420856615809501)
                  ·
                    rfl

theorem cell21_76894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_76894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76894 prefixEnd_76894 := by exact prefixLift 76894
  have htrace : WordTrace (prefixWord ++ tailWord_76894) baseStart_76894 baseEnd_76894 := by
    simpa [prefixWord, tailWord_76894, baseEnd_76894] using wordTrace_append hprefix tailTrace_76894
  have hstable : (prefixWord ++ tailWord_76894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76894).length < 2 ^ (prefixWord ++ tailWord_76894).sum := by decide
  have hdescent : baseEnd_76894 < baseStart_76894 := by decide
  rcases family_descends (prefixWord ++ tailWord_76894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76936 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 6]
def baseStart_76936 : Nat := 118140960795 + 76936 * 2 ^ 59
def prefixEnd_76936 : Nat := 4983230072969 + 3 ^ 40 * 76936 * 2
def baseEnd_76936 : Nat := 17557843393073876109415

theorem tailTrace_76936 : CollatzResearch.WordTrace tailWord_76936 prefixEnd_76936 17557843393073876109415 := by
  unfold tailWord_76936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403043224640743233905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1870724299520990978540441 1403043224640743233905331)
  ·
    refine ⟨2104564836961114850857997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403043224640743233905331 2104564836961114850857997)
    ·
      refine ⟨789211813860418069071749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2104564836961114850857997 789211813860418069071749)
      ·
        refine ⟨147977215098828387950953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 789211813860418069071749 147977215098828387950953)
        ·
          refine ⟨110982911324121290963215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147977215098828387950953 110982911324121290963215)
          ·
            refine ⟨166474366986181936444823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110982911324121290963215 166474366986181936444823)
            ·
              refine ⟨249711550479272904667235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166474366986181936444823 249711550479272904667235)
              ·
                refine ⟨374567325718909357000853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249711550479272904667235 374567325718909357000853)
                ·
                  refine ⟨17557843393073876109415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 374567325718909357000853 17557843393073876109415)
                  ·
                    rfl

theorem cell21_76936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_76936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76936 prefixEnd_76936 := by exact prefixLift 76936
  have htrace : WordTrace (prefixWord ++ tailWord_76936) baseStart_76936 baseEnd_76936 := by
    simpa [prefixWord, tailWord_76936, baseEnd_76936] using wordTrace_append hprefix tailTrace_76936
  have hstable : (prefixWord ++ tailWord_76936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76936).length < 2 ^ (prefixWord ++ tailWord_76936).sum := by decide
  have hdescent : baseEnd_76936 < baseStart_76936 := by decide
  rcases family_descends (prefixWord ++ tailWord_76936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_76967 : List Nat := [1, 1, 6, 2, 1, 1, 4, 5]
def baseStart_76967 : Nat := 118140960795 + 76967 * 2 ^ 59
def prefixEnd_76967 : Nat := 4983230072969 + 3 ^ 40 * 76967 * 2
def baseEnd_76967 : Nat := 5854972671808237030895

theorem tailTrace_76967 : CollatzResearch.WordTrace tailWord_76967 prefixEnd_76967 5854972671808237030895 := by
  unfold tailWord_76967
  simp only [CollatzResearch.WordTrace]
  refine ⟨2807217112169178762189155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1871478074779452508126103 2807217112169178762189155)
  ·
    refine ⟨4210825668253768143283733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2807217112169178762189155 4210825668253768143283733)
    ·
      refine ⟨197382453199395381716425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4210825668253768143283733 197382453199395381716425)
      ·
        refine ⟨148036839899546536287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197382453199395381716425 148036839899546536287319)
        ·
          refine ⟨222055259849319804430979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148036839899546536287319 222055259849319804430979)
          ·
            refine ⟨333082889773979706646469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222055259849319804430979 333082889773979706646469)
            ·
              refine ⟨62453041832621194996213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 333082889773979706646469 62453041832621194996213)
              ·
                refine ⟨5854972671808237030895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62453041832621194996213 5854972671808237030895)
                ·
                  rfl

theorem cell21_76967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 5].length) (baseStart_76967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_76967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_76967 prefixEnd_76967 := by exact prefixLift 76967
  have htrace : WordTrace (prefixWord ++ tailWord_76967) baseStart_76967 baseEnd_76967 := by
    simpa [prefixWord, tailWord_76967, baseEnd_76967] using wordTrace_append hprefix tailTrace_76967
  have hstable : (prefixWord ++ tailWord_76967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_76967).length < 2 ^ (prefixWord ++ tailWord_76967).sum := by decide
  have hdescent : baseEnd_76967 < baseStart_76967 := by decide
  rcases family_descends (prefixWord ++ tailWord_76967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77116 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_77116 : Nat := 118140960795 + 77116 * 2 ^ 59
def prefixEnd_77116 : Nat := 4983230072969 + 3 ^ 40 * 77116 * 2
def baseEnd_77116 : Nat := 17598921845433563109047

theorem tailTrace_77116 : CollatzResearch.WordTrace tailWord_77116 prefixEnd_77116 17598921845433563109047 := by
  unfold tailWord_77116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406325794314688604681601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1875101059086251472908801 1406325794314688604681601)
  ·
    refine ⟨1054744345736016453511201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1406325794314688604681601 1054744345736016453511201)
    ·
      refine ⟨791058259302012340133401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1054744345736016453511201 791058259302012340133401)
      ·
        refine ⟨593293694476509255100051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 791058259302012340133401 593293694476509255100051)
        ·
          refine ⟨889940541714763882650077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593293694476509255100051 889940541714763882650077)
          ·
            refine ⟨333727703143036455993779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 889940541714763882650077 333727703143036455993779)
            ·
              refine ⟨500591554714554683990669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333727703143036455993779 500591554714554683990669)
              ·
                refine ⟨187721833017958006496501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500591554714554683990669 187721833017958006496501)
                ·
                  refine ⟨17598921845433563109047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187721833017958006496501 17598921845433563109047)
                  ·
                    rfl

theorem cell21_77116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_77116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77116 prefixEnd_77116 := by exact prefixLift 77116
  have htrace : WordTrace (prefixWord ++ tailWord_77116) baseStart_77116 baseEnd_77116 := by
    simpa [prefixWord, tailWord_77116, baseEnd_77116] using wordTrace_append hprefix tailTrace_77116
  have hstable : (prefixWord ++ tailWord_77116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77116).length < 2 ^ (prefixWord ++ tailWord_77116).sum := by decide
  have hdescent : baseEnd_77116 < baseStart_77116 := by decide
  rcases family_descends (prefixWord ++ tailWord_77116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77142 : List Nat := [5, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_77142 : Nat := 118140960795 + 77142 * 2 ^ 59
def prefixEnd_77142 : Nat := 4983230072969 + 3 ^ 40 * 77142 * 2
def baseEnd_77142 : Nat := 17604855399663295675661

theorem tailTrace_77142 : CollatzResearch.WordTrace tailWord_77142 prefixEnd_77142 17604855399663295675661 := by
  unfold tailWord_77142
  simp only [CollatzResearch.WordTrace]
  refine ⟨175849992908448978113105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1875733257690122433206453 175849992908448978113105)
  ·
    refine ⟨131887494681336733584829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 175849992908448978113105 131887494681336733584829)
    ·
      refine ⟨49457810505501275094311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 131887494681336733584829 49457810505501275094311)
      ·
        refine ⟨74186715758251912641467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49457810505501275094311 74186715758251912641467)
        ·
          refine ⟨111280073637377868962201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74186715758251912641467 111280073637377868962201)
          ·
            refine ⟨83460055228033401721651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111280073637377868962201 83460055228033401721651)
            ·
              refine ⟨125190082842050102582477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83460055228033401721651 125190082842050102582477)
              ·
                refine ⟨46946281065768788468429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125190082842050102582477 46946281065768788468429)
                ·
                  refine ⟨17604855399663295675661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46946281065768788468429 17604855399663295675661)
                  ·
                    rfl

theorem cell21_77142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_77142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77142 prefixEnd_77142 := by exact prefixLift 77142
  have htrace : WordTrace (prefixWord ++ tailWord_77142) baseStart_77142 baseEnd_77142 := by
    simpa [prefixWord, tailWord_77142, baseEnd_77142] using wordTrace_append hprefix tailTrace_77142
  have hstable : (prefixWord ++ tailWord_77142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77142).length < 2 ^ (prefixWord ++ tailWord_77142).sum := by decide
  have hdescent : baseEnd_77142 < baseStart_77142 := by decide
  rcases family_descends (prefixWord ++ tailWord_77142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77251 : List Nat := [1, 1, 1, 3, 1, 1, 5, 1, 7]
def baseStart_77251 : Nat := 118140960795 + 77251 * 2 ^ 59
def prefixEnd_77251 : Nat := 4983230072969 + 3 ^ 40 * 77251 * 2
def baseEnd_77251 : Nat := 17629730684703328358771

theorem tailTrace_77251 : CollatzResearch.WordTrace tailWord_77251 prefixEnd_77251 17629730684703328358771 := by
  unfold tailWord_77251
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817575443140295265527607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1878383628760196843685071 2817575443140295265527607)
  ·
    refine ⟨4226363164710442898291411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817575443140295265527607 4226363164710442898291411)
    ·
      refine ⟨6339544747065664347437117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226363164710442898291411 6339544747065664347437117)
      ·
        refine ⟨2377329280149624130288919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6339544747065664347437117 2377329280149624130288919)
        ·
          refine ⟨3565993920224436195433379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2377329280149624130288919 3565993920224436195433379)
          ·
            refine ⟨5348990880336654293150069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565993920224436195433379 5348990880336654293150069)
            ·
              refine ⟨501467895031561339982819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5348990880336654293150069 501467895031561339982819)
              ·
                refine ⟨752201842547342009974229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501467895031561339982819 752201842547342009974229)
                ·
                  refine ⟨17629730684703328358771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 752201842547342009974229 17629730684703328358771)
                  ·
                    rfl

theorem cell21_77251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 7].length) (baseStart_77251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77251 prefixEnd_77251 := by exact prefixLift 77251
  have htrace : WordTrace (prefixWord ++ tailWord_77251) baseStart_77251 baseEnd_77251 := by
    simpa [prefixWord, tailWord_77251, baseEnd_77251] using wordTrace_append hprefix tailTrace_77251
  have hstable : (prefixWord ++ tailWord_77251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77251).length < 2 ^ (prefixWord ++ tailWord_77251).sum := by decide
  have hdescent : baseEnd_77251 < baseStart_77251 := by decide
  rcases family_descends (prefixWord ++ tailWord_77251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77285 : List Nat := [1, 3, 1, 5, 1, 2, 2, 1, 5]
def baseStart_77285 : Nat := 118140960795 + 77285 * 2 ^ 59
def prefixEnd_77285 : Nat := 4983230072969 + 3 ^ 40 * 77285 * 2
def baseEnd_77285 : Nat := 17637489947926824792035

theorem tailTrace_77285 : CollatzResearch.WordTrace tailWord_77285 prefixEnd_77285 17637489947926824792035 := by
  unfold tailWord_77285
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818815525017119072265309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1879210350011412714843539 2818815525017119072265309)
  ·
    refine ⟨1057055821881419652099491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2818815525017119072265309 1057055821881419652099491)
    ·
      refine ⟨1585583732822129478149237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057055821881419652099491 1585583732822129478149237)
      ·
        refine ⟨148648474952074638576491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1585583732822129478149237 148648474952074638576491)
        ·
          refine ⟨222972712428111957864737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148648474952074638576491 222972712428111957864737)
          ·
            refine ⟨167229534321083968398553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222972712428111957864737 167229534321083968398553)
            ·
              refine ⟨125422150740812976298915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167229534321083968398553 125422150740812976298915)
              ·
                refine ⟨188133226111219464448373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125422150740812976298915 188133226111219464448373)
                ·
                  refine ⟨17637489947926824792035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 188133226111219464448373 17637489947926824792035)
                  ·
                    rfl

theorem cell21_77285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_77285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77285 prefixEnd_77285 := by exact prefixLift 77285
  have htrace : WordTrace (prefixWord ++ tailWord_77285) baseStart_77285 baseEnd_77285 := by
    simpa [prefixWord, tailWord_77285, baseEnd_77285] using wordTrace_append hprefix tailTrace_77285
  have hstable : (prefixWord ++ tailWord_77285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77285).length < 2 ^ (prefixWord ++ tailWord_77285).sum := by decide
  have hdescent : baseEnd_77285 < baseStart_77285 := by decide
  rcases family_descends (prefixWord ++ tailWord_77285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77389 : List Nat := [1, 6, 1, 1, 12]
def baseStart_77389 : Nat := 118140960795 + 77389 * 2 ^ 59
def prefixEnd_77389 : Nat := 4983230072969 + 3 ^ 40 * 77389 * 2
def baseEnd_77389 : Nat := 218039804504268580969

theorem tailTrace_77389 : CollatzResearch.WordTrace tailWord_77389 prefixEnd_77389 218039804504268580969 := by
  unfold tailWord_77389
  simp only [CollatzResearch.WordTrace]
  refine ⟨2822608716640344834051221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1881739144426896556034147 2822608716640344834051221)
  ·
    refine ⟨132309783592516164096151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2822608716640344834051221 132309783592516164096151)
    ·
      refine ⟨198464675388774246144227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132309783592516164096151 198464675388774246144227)
      ·
        refine ⟨297697013083161369216341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198464675388774246144227 297697013083161369216341)
        ·
          refine ⟨218039804504268580969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 297697013083161369216341 218039804504268580969)
          ·
            rfl

theorem cell21_77389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 12].length) (baseStart_77389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77389 prefixEnd_77389 := by exact prefixLift 77389
  have htrace : WordTrace (prefixWord ++ tailWord_77389) baseStart_77389 baseEnd_77389 := by
    simpa [prefixWord, tailWord_77389, baseEnd_77389] using wordTrace_append hprefix tailTrace_77389
  have hstable : (prefixWord ++ tailWord_77389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77389).length < 2 ^ (prefixWord ++ tailWord_77389).sum := by decide
  have hdescent : baseEnd_77389 < baseStart_77389 := by decide
  rcases family_descends (prefixWord ++ tailWord_77389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77437 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 3]
def baseStart_77437 : Nat := 118140960795 + 77437 * 2 ^ 59
def prefixEnd_77437 : Nat := 4983230072969 + 3 ^ 40 * 77437 * 2
def baseEnd_77437 : Nat := 17672178418808338258391

theorem tailTrace_77437 : CollatzResearch.WordTrace tailWord_77437 prefixEnd_77437 17672178418808338258391 := by
  unfold tailWord_77437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824359420466449031798565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1882906280310966021199043 2824359420466449031798565)
  ·
    refine ⟨529567391337459193462231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2824359420466449031798565 529567391337459193462231)
    ·
      refine ⟨794351087006188790193347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 529567391337459193462231 794351087006188790193347)
      ·
        refine ⟨1191526630509283185290021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794351087006188790193347 1191526630509283185290021)
        ·
          refine ⟨223411243220490597241879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1191526630509283185290021 223411243220490597241879)
          ·
            refine ⟨335116864830735895862819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223411243220490597241879 335116864830735895862819)
            ·
              refine ⟨502675297246103843794229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335116864830735895862819 502675297246103843794229)
              ·
                refine ⟨47125809116822235355709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 502675297246103843794229 47125809116822235355709)
                ·
                  refine ⟨17672178418808338258391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47125809116822235355709 17672178418808338258391)
                  ·
                    rfl

theorem cell21_77437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_77437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77437 prefixEnd_77437 := by exact prefixLift 77437
  have htrace : WordTrace (prefixWord ++ tailWord_77437) baseStart_77437 baseEnd_77437 := by
    simpa [prefixWord, tailWord_77437, baseEnd_77437] using wordTrace_append hprefix tailTrace_77437
  have hstable : (prefixWord ++ tailWord_77437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77437).length < 2 ^ (prefixWord ++ tailWord_77437).sum := by decide
  have hdescent : baseEnd_77437 < baseStart_77437 := by decide
  rcases family_descends (prefixWord ++ tailWord_77437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77575 : List Nat := [1, 1, 4, 4, 3, 1, 1, 6]
def baseStart_77575 : Nat := 118140960795 + 77575 * 2 ^ 59
def prefixEnd_77575 : Nat := 4983230072969 + 3 ^ 40 * 77575 * 2
def baseEnd_77575 : Nat := 5901223966316921652703

theorem tailTrace_77575 : CollatzResearch.WordTrace tailWord_77575 prefixEnd_77575 5901223966316921652703 := by
  unfold tailWord_77575
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829392693966498600322179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1886261795977665733548119 2829392693966498600322179)
  ·
    refine ⟨4244089040949747900483269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829392693966498600322179 4244089040949747900483269)
    ·
      refine ⟨795766695178077731340613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4244089040949747900483269 795766695178077731340613)
      ·
        refine ⟨149206255345889574626365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 795766695178077731340613 149206255345889574626365)
        ·
          refine ⟨55952345754708590484887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149206255345889574626365 55952345754708590484887)
          ·
            refine ⟨83928518632062885727331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55952345754708590484887 83928518632062885727331)
            ·
              refine ⟨125892777948094328590997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83928518632062885727331 125892777948094328590997)
              ·
                refine ⟨5901223966316921652703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125892777948094328590997 5901223966316921652703)
                ·
                  rfl

theorem cell21_77575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 6].length) (baseStart_77575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77575 prefixEnd_77575 := by exact prefixLift 77575
  have htrace : WordTrace (prefixWord ++ tailWord_77575) baseStart_77575 baseEnd_77575 := by
    simpa [prefixWord, tailWord_77575, baseEnd_77575] using wordTrace_append hprefix tailTrace_77575
  have hstable : (prefixWord ++ tailWord_77575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77575).length < 2 ^ (prefixWord ++ tailWord_77575).sum := by decide
  have hdescent : baseEnd_77575 < baseStart_77575 := by decide
  rcases family_descends (prefixWord ++ tailWord_77575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77620 : List Nat := [2, 5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_77620 : Nat := 118140960795 + 77620 * 2 ^ 59
def prefixEnd_77620 : Nat := 4983230072969 + 3 ^ 40 * 77620 * 2
def baseEnd_77620 : Nat := 17713941512040686708017

theorem tailTrace_77620 : CollatzResearch.WordTrace tailWord_77620 prefixEnd_77620 17713941512040686708017 := by
  unfold tailWord_77620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1415516989401735642855157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1887355985868980857140209 1415516989401735642855157)
  ·
    refine ⟨132704717756412716517671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1415516989401735642855157 132704717756412716517671)
    ·
      refine ⟨199057076634619074776507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132704717756412716517671 199057076634619074776507)
      ·
        refine ⟨298585614951928612164761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199057076634619074776507 298585614951928612164761)
        ·
          refine ⟨223939211213946459123571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298585614951928612164761 223939211213946459123571)
          ·
            refine ⟨335908816820919688685357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223939211213946459123571 335908816820919688685357)
            ·
              refine ⟨125965806307844883257009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335908816820919688685357 125965806307844883257009)
              ·
                refine ⟨94474354730883662442757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125965806307844883257009 94474354730883662442757)
                ·
                  refine ⟨17713941512040686708017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94474354730883662442757 17713941512040686708017)
                  ·
                    rfl

theorem cell21_77620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_77620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77620 prefixEnd_77620 := by exact prefixLift 77620
  have htrace : WordTrace (prefixWord ++ tailWord_77620) baseStart_77620 baseEnd_77620 := by
    simpa [prefixWord, tailWord_77620, baseEnd_77620] using wordTrace_append hprefix tailTrace_77620
  have hstable : (prefixWord ++ tailWord_77620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77620).length < 2 ^ (prefixWord ++ tailWord_77620).sum := by decide
  have hdescent : baseEnd_77620 < baseStart_77620 := by decide
  rcases family_descends (prefixWord ++ tailWord_77620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77676 : List Nat := [2, 2, 1, 1, 4, 2, 9]
def baseStart_77676 : Nat := 118140960795 + 77676 * 2 ^ 59
def prefixEnd_77676 : Nat := 4983230072969 + 3 ^ 40 * 77676 * 2
def baseEnd_77676 : Nat := 1969635719444114863841

theorem tailTrace_77676 : CollatzResearch.WordTrace tailWord_77676 prefixEnd_77676 1969635719444114863841 := by
  unfold tailWord_77676
  simp only [CollatzResearch.WordTrace]
  refine ⟨1416538233300296424874441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1888717644400395233165921 1416538233300296424874441)
  ·
    refine ⟨1062403674975222318655831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1416538233300296424874441 1062403674975222318655831)
    ·
      refine ⟨1593605512462833477983747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062403674975222318655831 1593605512462833477983747)
      ·
        refine ⟨2390408268694250216975621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593605512462833477983747 2390408268694250216975621)
        ·
          refine ⟨448201550380171915682929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2390408268694250216975621 448201550380171915682929)
          ·
            refine ⟨336151162785128936762197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448201550380171915682929 336151162785128936762197)
            ·
              refine ⟨1969635719444114863841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 336151162785128936762197 1969635719444114863841)
              ·
                rfl

theorem cell21_77676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 9].length) (baseStart_77676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77676 prefixEnd_77676 := by exact prefixLift 77676
  have htrace : WordTrace (prefixWord ++ tailWord_77676) baseStart_77676 baseEnd_77676 := by
    simpa [prefixWord, tailWord_77676, baseEnd_77676] using wordTrace_append hprefix tailTrace_77676
  have hstable : (prefixWord ++ tailWord_77676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77676).length < 2 ^ (prefixWord ++ tailWord_77676).sum := by decide
  have hdescent : baseEnd_77676 < baseStart_77676 := by decide
  rcases family_descends (prefixWord ++ tailWord_77676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77721 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 8]
def baseStart_77721 : Nat := 118140960795 + 77721 * 2 ^ 59
def prefixEnd_77721 : Nat := 4983230072969 + 3 ^ 40 * 77721 * 2
def baseEnd_77721 : Nat := 17736991088086955524477

theorem tailTrace_77721 : CollatzResearch.WordTrace tailWord_77721 prefixEnd_77721 17736991088086955524477 := by
  unfold tailWord_77721
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834717751437565535137017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1889811834291710356758011 2834717751437565535137017)
  ·
    refine ⟨2126038313578174151352763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2834717751437565535137017 2126038313578174151352763)
    ·
      refine ⟨3189057470367261227029145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126038313578174151352763 3189057470367261227029145)
      ·
        refine ⟨2391793102775445920271859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189057470367261227029145 2391793102775445920271859)
        ·
          refine ⟨3587689654163168880407789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391793102775445920271859 3587689654163168880407789)
          ·
            refine ⟨1345383620311188330152921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3587689654163168880407789 1345383620311188330152921)
            ·
              refine ⟨1009037715233391247614691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345383620311188330152921 1009037715233391247614691)
              ·
                refine ⟨1513556572850086871422037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009037715233391247614691 1513556572850086871422037)
                ·
                  refine ⟨17736991088086955524477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1513556572850086871422037 17736991088086955524477)
                  ·
                    rfl

theorem cell21_77721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_77721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77721 prefixEnd_77721 := by exact prefixLift 77721
  have htrace : WordTrace (prefixWord ++ tailWord_77721) baseStart_77721 baseEnd_77721 := by
    simpa [prefixWord, tailWord_77721, baseEnd_77721] using wordTrace_append hprefix tailTrace_77721
  have hstable : (prefixWord ++ tailWord_77721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77721).length < 2 ^ (prefixWord ++ tailWord_77721).sum := by decide
  have hdescent : baseEnd_77721 < baseStart_77721 := by decide
  rcases family_descends (prefixWord ++ tailWord_77721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77789 : List Nat := [1, 4, 3, 1, 4, 1, 1, 2, 4]
def baseStart_77789 : Nat := 118140960795 + 77789 * 2 ^ 59
def prefixEnd_77789 : Nat := 4983230072969 + 3 ^ 40 * 77789 * 2
def baseEnd_77789 : Nat := 17752509614533948391005

theorem tailTrace_77789 : CollatzResearch.WordTrace tailWord_77789 prefixEnd_77789 17752509614533948391005 := by
  unfold tailWord_77789
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837197915191213148612421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1891465276794142099074947 2837197915191213148612421)
  ·
    refine ⟨531974609098352465364829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2837197915191213148612421 531974609098352465364829)
    ·
      refine ⟨199490478411882174511811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 531974609098352465364829 199490478411882174511811)
      ·
        refine ⟨299235717617823261767717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199490478411882174511811 299235717617823261767717)
        ·
          refine ⟨56106697053341861581447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299235717617823261767717 56106697053341861581447)
          ·
            refine ⟨84160045580012792372171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56106697053341861581447 84160045580012792372171)
            ·
              refine ⟨126240068370019188558257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84160045580012792372171 126240068370019188558257)
              ·
                refine ⟨94680051277514391418693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126240068370019188558257 94680051277514391418693)
                ·
                  refine ⟨17752509614533948391005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94680051277514391418693 17752509614533948391005)
                  ·
                    rfl

theorem cell21_77789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_77789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77789 prefixEnd_77789 := by exact prefixLift 77789
  have htrace : WordTrace (prefixWord ++ tailWord_77789) baseStart_77789 baseEnd_77789 := by
    simpa [prefixWord, tailWord_77789, baseEnd_77789] using wordTrace_append hprefix tailTrace_77789
  have hstable : (prefixWord ++ tailWord_77789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77789).length < 2 ^ (prefixWord ++ tailWord_77789).sum := by decide
  have hdescent : baseEnd_77789 < baseStart_77789 := by decide
  rcases family_descends (prefixWord ++ tailWord_77789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77834 : List Nat := [3, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_77834 : Nat := 118140960795 + 77834 * 2 ^ 59
def prefixEnd_77834 : Nat := 4983230072969 + 3 ^ 40 * 77834 * 2
def baseEnd_77834 : Nat := 17762779227623870140913

theorem tailTrace_77834 : CollatzResearch.WordTrace tailWord_77834 prefixEnd_77834 17762779227623870140913 := by
  unfold tailWord_77834
  simp only [CollatzResearch.WordTrace]
  refine ⟨709709800007046458500139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1892559466685457222667037 709709800007046458500139)
  ·
    refine ⟨1064564700010569687750209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709709800007046458500139 1064564700010569687750209)
    ·
      refine ⟨798423525007927265812657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1064564700010569687750209 798423525007927265812657)
      ·
        refine ⟨598817643755945449359493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 798423525007927265812657 598817643755945449359493)
        ·
          refine ⟨112278308204239771754905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 598817643755945449359493 112278308204239771754905)
          ·
            refine ⟨84208731153179828816179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112278308204239771754905 84208731153179828816179)
            ·
              refine ⟨126313096729769743224269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84208731153179828816179 126313096729769743224269)
              ·
                refine ⟨47367411273663653709101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126313096729769743224269 47367411273663653709101)
                ·
                  refine ⟨17762779227623870140913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47367411273663653709101 17762779227623870140913)
                  ·
                    rfl

theorem cell21_77834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_77834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77834 prefixEnd_77834 := by exact prefixLift 77834
  have htrace : WordTrace (prefixWord ++ tailWord_77834) baseStart_77834 baseEnd_77834 := by
    simpa [prefixWord, tailWord_77834, baseEnd_77834] using wordTrace_append hprefix tailTrace_77834
  have hstable : (prefixWord ++ tailWord_77834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77834).length < 2 ^ (prefixWord ++ tailWord_77834).sum := by decide
  have hdescent : baseEnd_77834 < baseStart_77834 := by decide
  rcases family_descends (prefixWord ++ tailWord_77834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77845 : List Nat := [1, 3, 2, 1, 5, 2, 7]
def baseStart_77845 : Nat := 118140960795 + 77845 * 2 ^ 59
def prefixEnd_77845 : Nat := 4983230072969 + 3 ^ 40 * 77845 * 2
def baseEnd_77845 : Nat := 1973921064165588384173

theorem tailTrace_77845 : CollatzResearch.WordTrace tailWord_77845 prefixEnd_77845 1973921064165588384173 := by
  unfold tailWord_77845
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839240402988334712650989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1892826935325556475100659 2839240402988334712650989)
  ·
    refine ⟨1064715151120625517244121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2839240402988334712650989 1064715151120625517244121)
    ·
      refine ⟨798536363340469137933091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1064715151120625517244121 798536363340469137933091)
      ·
        refine ⟨1197804545010703706899637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798536363340469137933091 1197804545010703706899637)
        ·
          refine ⟨112294176094753472521841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1197804545010703706899637 112294176094753472521841)
          ·
            refine ⟨84220632071065104391381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112294176094753472521841 84220632071065104391381)
            ·
              refine ⟨1973921064165588384173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84220632071065104391381 1973921064165588384173)
              ·
                rfl

theorem cell21_77845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 7].length) (baseStart_77845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77845 prefixEnd_77845 := by exact prefixLift 77845
  have htrace : WordTrace (prefixWord ++ tailWord_77845) baseStart_77845 baseEnd_77845 := by
    simpa [prefixWord, tailWord_77845, baseEnd_77845] using wordTrace_append hprefix tailTrace_77845
  have hstable : (prefixWord ++ tailWord_77845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77845).length < 2 ^ (prefixWord ++ tailWord_77845).sum := by decide
  have hdescent : baseEnd_77845 < baseStart_77845 := by decide
  rcases family_descends (prefixWord ++ tailWord_77845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77935 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 5]
def baseStart_77935 : Nat := 118140960795 + 77935 * 2 ^ 59
def prefixEnd_77935 : Nat := 4983230072969 + 3 ^ 40 * 77935 * 2
def baseEnd_77935 : Nat := 17785828803670138957373

theorem tailTrace_77935 : CollatzResearch.WordTrace tailWord_77935 prefixEnd_77935 17785828803670138957373 := by
  unfold tailWord_77935
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842522972662280083427259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1895015315108186722284839 2842522972662280083427259)
  ·
    refine ⟨4263784458993420125140889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842522972662280083427259 4263784458993420125140889)
    ·
      refine ⟨3197838344245065093855667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4263784458993420125140889 3197838344245065093855667)
      ·
        refine ⟨4796757516367597640783501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197838344245065093855667 4796757516367597640783501)
        ·
          refine ⟨1798784068637849115293813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4796757516367597640783501 1798784068637849115293813)
          ·
            refine ⟨168636006434798354558795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1798784068637849115293813 168636006434798354558795)
            ·
              refine ⟨252954009652197531838193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168636006434798354558795 252954009652197531838193)
              ·
                refine ⟨189715507239148148878645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252954009652197531838193 189715507239148148878645)
                ·
                  refine ⟨17785828803670138957373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189715507239148148878645 17785828803670138957373)
                  ·
                    rfl

theorem cell21_77935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_77935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77935 prefixEnd_77935 := by exact prefixLift 77935
  have htrace : WordTrace (prefixWord ++ tailWord_77935) baseStart_77935 baseEnd_77935 := by
    simpa [prefixWord, tailWord_77935, baseEnd_77935] using wordTrace_append hprefix tailTrace_77935
  have hstable : (prefixWord ++ tailWord_77935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77935).length < 2 ^ (prefixWord ++ tailWord_77935).sum := by decide
  have hdescent : baseEnd_77935 < baseStart_77935 := by decide
  rcases family_descends (prefixWord ++ tailWord_77935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77980 : List Nat := [2, 2, 3, 2, 1, 1, 2, 8]
def baseStart_77980 : Nat := 118140960795 + 77980 * 2 ^ 59
def prefixEnd_77980 : Nat := 4983230072969 + 3 ^ 40 * 77980 * 2
def baseEnd_77980 : Nat := 5932032805586686902427

theorem tailTrace_77980 : CollatzResearch.WordTrace tailWord_77980 prefixEnd_77980 5932032805586686902427 := by
  unfold tailWord_77980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422082128749626384407697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1896109504999501845876929 1422082128749626384407697)
  ·
    refine ⟨1066561596562219788305773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1422082128749626384407697 1066561596562219788305773)
    ·
      refine ⟨399960598710832420614665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1066561596562219788305773 399960598710832420614665)
      ·
        refine ⟨299970449033124315460999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399960598710832420614665 299970449033124315460999)
        ·
          refine ⟨449955673549686473191499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299970449033124315460999 449955673549686473191499)
          ·
            refine ⟨674933510324529709787249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449955673549686473191499 674933510324529709787249)
            ·
              refine ⟨506200132743397282340437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674933510324529709787249 506200132743397282340437)
              ·
                refine ⟨5932032805586686902427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 506200132743397282340437 5932032805586686902427)
                ·
                  rfl

theorem cell21_77980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_77980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77980 prefixEnd_77980 := by exact prefixLift 77980
  have htrace : WordTrace (prefixWord ++ tailWord_77980) baseStart_77980 baseEnd_77980 := by
    simpa [prefixWord, tailWord_77980, baseEnd_77980] using wordTrace_append hprefix tailTrace_77980
  have hstable : (prefixWord ++ tailWord_77980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77980).length < 2 ^ (prefixWord ++ tailWord_77980).sum := by decide
  have hdescent : baseEnd_77980 < baseStart_77980 := by decide
  rcases family_descends (prefixWord ++ tailWord_77980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_77997 : List Nat := [1, 5, 2, 1, 2, 2, 1, 7]
def baseStart_77997 : Nat := 118140960795 + 77997 * 2 ^ 59
def prefixEnd_77997 : Nat := 4983230072969 + 3 ^ 40 * 77997 * 2
def baseEnd_77997 : Nat := 5933326016123936307971

theorem tailTrace_77997 : CollatzResearch.WordTrace tailWord_77997 prefixEnd_77997 5933326016123936307971 := by
  unfold tailWord_77997
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844784298437664672184245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1896522865625109781456163 2844784298437664672184245)
  ·
    refine ⟨266698527978531063017273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2844784298437664672184245 266698527978531063017273)
    ·
      refine ⟨200023895983898297262955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266698527978531063017273 200023895983898297262955)
      ·
        refine ⟨300035843975847445894433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200023895983898297262955 300035843975847445894433)
        ·
          refine ⟨225026882981885584420825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300035843975847445894433 225026882981885584420825)
          ·
            refine ⟨168770162236414188315619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225026882981885584420825 168770162236414188315619)
            ·
              refine ⟨253155243354621282473429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168770162236414188315619 253155243354621282473429)
              ·
                refine ⟨5933326016123936307971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253155243354621282473429 5933326016123936307971)
                ·
                  rfl

theorem cell21_77997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 7].length) (baseStart_77997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_77997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_77997 prefixEnd_77997 := by exact prefixLift 77997
  have htrace : WordTrace (prefixWord ++ tailWord_77997) baseStart_77997 baseEnd_77997 := by
    simpa [prefixWord, tailWord_77997, baseEnd_77997] using wordTrace_append hprefix tailTrace_77997
  have hstable : (prefixWord ++ tailWord_77997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_77997).length < 2 ^ (prefixWord ++ tailWord_77997).sum := by decide
  have hdescent : baseEnd_77997 < baseStart_77997 := by decide
  rcases family_descends (prefixWord ++ tailWord_77997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78014 : List Nat := [4, 2, 1, 1, 5, 1, 7]
def baseStart_78014 : Nat := 118140960795 + 78014 * 2 ^ 59
def prefixEnd_78014 : Nat := 4983230072969 + 3 ^ 40 * 78014 * 2
def baseEnd_78014 : Nat := 1978206408887061904505

theorem tailTrace_78014 : CollatzResearch.WordTrace tailWord_78014 prefixEnd_78014 1978206408887061904505 := by
  unfold tailWord_78014
  simp only [CollatzResearch.WordTrace]
  refine ⟨355675542422009571944137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1896936226250717717035397 355675542422009571944137)
  ·
    refine ⟨266756656816507178958103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355675542422009571944137 266756656816507178958103)
    ·
      refine ⟨400134985224760768437155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266756656816507178958103 400134985224760768437155)
      ·
        refine ⟨600202477837141152655733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400134985224760768437155 600202477837141152655733)
        ·
          refine ⟨56268982297231983061475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 600202477837141152655733 56268982297231983061475)
          ·
            refine ⟨84403473445847974592213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56268982297231983061475 84403473445847974592213)
            ·
              refine ⟨1978206408887061904505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84403473445847974592213 1978206408887061904505)
              ·
                rfl

theorem cell21_78014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 7].length) (baseStart_78014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78014 prefixEnd_78014 := by exact prefixLift 78014
  have htrace : WordTrace (prefixWord ++ tailWord_78014) baseStart_78014 baseEnd_78014 := by
    simpa [prefixWord, tailWord_78014, baseEnd_78014] using wordTrace_append hprefix tailTrace_78014
  have hstable : (prefixWord ++ tailWord_78014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78014).length < 2 ^ (prefixWord ++ tailWord_78014).sum := by decide
  have hdescent : baseEnd_78014 < baseStart_78014 := by decide
  rcases family_descends (prefixWord ++ tailWord_78014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78056 : List Nat := [2, 1, 4, 1, 2, 2, 2, 7]
def baseStart_78056 : Nat := 118140960795 + 78056 * 2 ^ 59
def prefixEnd_78056 : Nat := 4983230072969 + 3 ^ 40 * 78056 * 2
def baseEnd_78056 : Nat := 5937814217400272480153

theorem tailTrace_78056 : CollatzResearch.WordTrace tailWord_78056 prefixEnd_78056 5937814217400272480153 := by
  unfold tailWord_78056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423468102611958874291011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1897957470149278499054681 1423468102611958874291011)
  ·
    refine ⟨2135202153917938311436517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1423468102611958874291011 2135202153917938311436517)
    ·
      refine ⟨400350403859613433394347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2135202153917938311436517 400350403859613433394347)
      ·
        refine ⟨600525605789420150091521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400350403859613433394347 600525605789420150091521)
        ·
          refine ⟨450394204342065112568641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600525605789420150091521 450394204342065112568641)
          ·
            refine ⟨337795653256548834426481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450394204342065112568641 337795653256548834426481)
            ·
              refine ⟨253346739942411625819861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337795653256548834426481 253346739942411625819861)
              ·
                refine ⟨5937814217400272480153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253346739942411625819861 5937814217400272480153)
                ·
                  rfl

theorem cell21_78056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_78056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78056 prefixEnd_78056 := by exact prefixLift 78056
  have htrace : WordTrace (prefixWord ++ tailWord_78056) baseStart_78056 baseEnd_78056 := by
    simpa [prefixWord, tailWord_78056, baseEnd_78056] using wordTrace_append hprefix tailTrace_78056
  have hstable : (prefixWord ++ tailWord_78056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78056).length < 2 ^ (prefixWord ++ tailWord_78056).sum := by decide
  have hdescent : baseEnd_78056 < baseStart_78056 := by decide
  rcases family_descends (prefixWord ++ tailWord_78056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78270 : List Nat := [4, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_78270 : Nat := 118140960795 + 78270 * 2 ^ 59
def prefixEnd_78270 : Nat := 4983230072969 + 3 ^ 40 * 78270 * 2
def baseEnd_78270 : Nat := 17862280367784000873355

theorem tailTrace_78270 : CollatzResearch.WordTrace tailWord_78270 prefixEnd_78270 17862280367784000873355 := by
  unfold tailWord_78270
  simp only [CollatzResearch.WordTrace]
  refine ⟨356842678306079037109033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1903160950965754864581509 356842678306079037109033)
  ·
    refine ⟨267632008729559277831775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 356842678306079037109033 267632008729559277831775)
    ·
      refine ⟨401448013094338916747663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267632008729559277831775 401448013094338916747663)
      ·
        refine ⟨602172019641508375121495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401448013094338916747663 602172019641508375121495)
        ·
          refine ⟨903258029462262562682243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602172019641508375121495 903258029462262562682243)
          ·
            refine ⟨1354887044193393844023365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903258029462262562682243 1354887044193393844023365)
            ·
              refine ⟨254041320786261345754381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1354887044193393844023365 254041320786261345754381)
              ·
                refine ⟨95265495294848004657893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254041320786261345754381 95265495294848004657893)
                ·
                  refine ⟨17862280367784000873355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95265495294848004657893 17862280367784000873355)
                  ·
                    rfl

theorem cell21_78270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_78270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78270 prefixEnd_78270 := by exact prefixLift 78270
  have htrace : WordTrace (prefixWord ++ tailWord_78270) baseStart_78270 baseEnd_78270 := by
    simpa [prefixWord, tailWord_78270, baseEnd_78270] using wordTrace_append hprefix tailTrace_78270
  have hstable : (prefixWord ++ tailWord_78270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78270).length < 2 ^ (prefixWord ++ tailWord_78270).sum := by decide
  have hdescent : baseEnd_78270 < baseStart_78270 := by decide
  rcases family_descends (prefixWord ++ tailWord_78270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78290 : List Nat := [3, 2, 2, 4, 1, 1, 2, 3, 3]
def baseStart_78290 : Nat := 118140960795 + 78290 * 2 ^ 59
def prefixEnd_78290 : Nat := 4983230072969 + 3 ^ 40 * 78290 * 2
def baseEnd_78290 : Nat := 17866844640268410539981

theorem tailTrace_78290 : CollatzResearch.WordTrace tailWord_78290 prefixEnd_78290 17866844640268410539981 := by
  unfold tailWord_78290
  simp only [CollatzResearch.WordTrace]
  refine ⟨713867721594043928150081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1903647257584117141733549 713867721594043928150081)
  ·
    refine ⟨535400791195532946112561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 713867721594043928150081 535400791195532946112561)
    ·
      refine ⟨401550593396649709584421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535400791195532946112561 401550593396649709584421)
      ·
        refine ⟨75290736261871820547079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401550593396649709584421 75290736261871820547079)
        ·
          refine ⟨112936104392807730820619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75290736261871820547079 112936104392807730820619)
          ·
            refine ⟨169404156589211596230929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112936104392807730820619 169404156589211596230929)
            ·
              refine ⟨127053117441908697173197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169404156589211596230929 127053117441908697173197)
              ·
                refine ⟨47644919040715761439949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127053117441908697173197 47644919040715761439949)
                ·
                  refine ⟨17866844640268410539981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47644919040715761439949 17866844640268410539981)
                  ·
                    rfl

theorem cell21_78290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_78290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78290 prefixEnd_78290 := by exact prefixLift 78290
  have htrace : WordTrace (prefixWord ++ tailWord_78290) baseStart_78290 baseEnd_78290 := by
    simpa [prefixWord, tailWord_78290, baseEnd_78290] using wordTrace_append hprefix tailTrace_78290
  have hstable : (prefixWord ++ tailWord_78290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78290).length < 2 ^ (prefixWord ++ tailWord_78290).sum := by decide
  have hdescent : baseEnd_78290 < baseStart_78290 := by decide
  rcases family_descends (prefixWord ++ tailWord_78290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78298 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_78298 : Nat := 118140960795 + 78298 * 2 ^ 59
def prefixEnd_78298 : Nat := 4983230072969 + 3 ^ 40 * 78298 * 2
def baseEnd_78298 : Nat := 17868670349262174406631

theorem tailTrace_78298 : CollatzResearch.WordTrace tailWord_78298 prefixEnd_78298 17868670349262174406631 := by
  unfold tailWord_78298
  simp only [CollatzResearch.WordTrace]
  refine ⟨713940667586798269722887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1903841780231462052594365 713940667586798269722887)
  ·
    refine ⟨1070911001380197404584331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713940667586798269722887 1070911001380197404584331)
    ·
      refine ⟨1606366502070296106876497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1070911001380197404584331 1606366502070296106876497)
      ·
        refine ⟨1204774876552722080157373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1606366502070296106876497 1204774876552722080157373)
        ·
          refine ⟨451790578707270780059015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1204774876552722080157373 451790578707270780059015)
          ·
            refine ⟨677685868060906170088523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451790578707270780059015 677685868060906170088523)
            ·
              refine ⟨1016528802091359255132785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677685868060906170088523 1016528802091359255132785)
              ·
                refine ⟨762396601568519441349589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016528802091359255132785 762396601568519441349589)
                ·
                  refine ⟨17868670349262174406631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 762396601568519441349589 17868670349262174406631)
                  ·
                    rfl

theorem cell21_78298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_78298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78298 prefixEnd_78298 := by exact prefixLift 78298
  have htrace : WordTrace (prefixWord ++ tailWord_78298) baseStart_78298 baseEnd_78298 := by
    simpa [prefixWord, tailWord_78298, baseEnd_78298] using wordTrace_append hprefix tailTrace_78298
  have hstable : (prefixWord ++ tailWord_78298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78298).length < 2 ^ (prefixWord ++ tailWord_78298).sum := by decide
  have hdescent : baseEnd_78298 < baseStart_78298 := by decide
  rcases family_descends (prefixWord ++ tailWord_78298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78315 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 3]
def baseStart_78315 : Nat := 118140960795 + 78315 * 2 ^ 59
def prefixEnd_78315 : Nat := 4983230072969 + 3 ^ 40 * 78315 * 2
def baseEnd_78315 : Nat := 17872549980873922623263

theorem tailTrace_78315 : CollatzResearch.WordTrace tailWord_78315 prefixEnd_78315 17872549980873922623263 := by
  unfold tailWord_78315
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856382711285604982260399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1904255140857069988173599 2856382711285604982260399)
  ·
    refine ⟨4284574066928407473390599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856382711285604982260399 4284574066928407473390599)
    ·
      refine ⟨6426861100392611210085899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284574066928407473390599 6426861100392611210085899)
      ·
        refine ⟨9640291650588916815128849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426861100392611210085899 9640291650588916815128849)
        ·
          refine ⟨7230218737941687611346637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640291650588916815128849 7230218737941687611346637)
          ·
            refine ⟨2711332026728132854254989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7230218737941687611346637 2711332026728132854254989)
            ·
              refine ⟨1016749510023049820345621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2711332026728132854254989 1016749510023049820345621)
              ·
                refine ⟨47660133282330460328701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1016749510023049820345621 47660133282330460328701)
                ·
                  refine ⟨17872549980873922623263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47660133282330460328701 17872549980873922623263)
                  ·
                    rfl

theorem cell21_78315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 3].length) (baseStart_78315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78315 prefixEnd_78315 := by exact prefixLift 78315
  have htrace : WordTrace (prefixWord ++ tailWord_78315) baseStart_78315 baseEnd_78315 := by
    simpa [prefixWord, tailWord_78315, baseEnd_78315] using wordTrace_append hprefix tailTrace_78315
  have hstable : (prefixWord ++ tailWord_78315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78315).length < 2 ^ (prefixWord ++ tailWord_78315).sum := by decide
  have hdescent : baseEnd_78315 < baseStart_78315 := by decide
  rcases family_descends (prefixWord ++ tailWord_78315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78329 : List Nat := [1, 2, 1, 3, 1, 2, 2, 5, 4]
def baseStart_78329 : Nat := 118140960795 + 78329 * 2 ^ 59
def prefixEnd_78329 : Nat := 4983230072969 + 3 ^ 40 * 78329 * 2
def baseEnd_78329 : Nat := 17875744971613009389901

theorem tailTrace_78329 : CollatzResearch.WordTrace tailWord_78329 prefixEnd_78329 17875744971613009389901 := by
  unfold tailWord_78329
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856893333234885373270041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1904595555489923582180027 2856893333234885373270041)
  ·
    refine ⟨2142669999926164029952531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2856893333234885373270041 2142669999926164029952531)
    ·
      refine ⟨3214004999889246044928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142669999926164029952531 3214004999889246044928797)
      ·
        refine ⟨1205251874958467266848299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3214004999889246044928797 1205251874958467266848299)
        ·
          refine ⟨1807877812437700900272449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205251874958467266848299 1807877812437700900272449)
          ·
            refine ⟨1355908359328275675204337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807877812437700900272449 1355908359328275675204337)
            ·
              refine ⟨1016931269496206756403253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355908359328275675204337 1016931269496206756403253)
              ·
                refine ⟨95337306515269383412805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016931269496206756403253 95337306515269383412805)
                ·
                  refine ⟨17875744971613009389901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95337306515269383412805 17875744971613009389901)
                  ·
                    rfl

theorem cell21_78329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_78329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78329 prefixEnd_78329 := by exact prefixLift 78329
  have htrace : WordTrace (prefixWord ++ tailWord_78329) baseStart_78329 baseEnd_78329 := by
    simpa [prefixWord, tailWord_78329, baseEnd_78329] using wordTrace_append hprefix tailTrace_78329
  have hstable : (prefixWord ++ tailWord_78329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78329).length < 2 ^ (prefixWord ++ tailWord_78329).sum := by decide
  have hdescent : baseEnd_78329 < baseStart_78329 := by decide
  rcases family_descends (prefixWord ++ tailWord_78329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78360 : List Nat := [2, 1, 2, 3, 3, 3, 7]
def baseStart_78360 : Nat := 118140960795 + 78360 * 2 ^ 59
def prefixEnd_78360 : Nat := 4983230072969 + 3 ^ 40 * 78360 * 2
def baseEnd_78360 : Nat := 1986979954884871597019

theorem tailTrace_78360 : CollatzResearch.WordTrace tailWord_78360 prefixEnd_78360 1986979954884871597019 := by
  unfold tailWord_78360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429011998061288833824267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1905349330748385111765689 1429011998061288833824267)
  ·
    refine ⟨2143517997091933250736401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429011998061288833824267 2143517997091933250736401)
    ·
      refine ⟨1607638497818949938052301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143517997091933250736401 1607638497818949938052301)
      ·
        refine ⟨602864436682106226769613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1607638497818949938052301 602864436682106226769613)
        ·
          refine ⟨226074163755789835038605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602864436682106226769613 226074163755789835038605)
          ·
            refine ⟨84777811408421188139477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226074163755789835038605 84777811408421188139477)
            ·
              refine ⟨1986979954884871597019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 84777811408421188139477 1986979954884871597019)
              ·
                rfl

theorem cell21_78360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 7].length) (baseStart_78360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78360 prefixEnd_78360 := by exact prefixLift 78360
  have htrace : WordTrace (prefixWord ++ tailWord_78360) baseStart_78360 baseEnd_78360 := by
    simpa [prefixWord, tailWord_78360, baseEnd_78360] using wordTrace_append hprefix tailTrace_78360
  have hstable : (prefixWord ++ tailWord_78360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78360).length < 2 ^ (prefixWord ++ tailWord_78360).sum := by decide
  have hdescent : baseEnd_78360 < baseStart_78360 := by decide
  rcases family_descends (prefixWord ++ tailWord_78360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78467 : List Nat := [1, 1, 1, 3, 3, 1, 3, 5, 3]
def baseStart_78467 : Nat := 118140960795 + 78467 * 2 ^ 59
def prefixEnd_78467 : Nat := 4983230072969 + 3 ^ 40 * 78467 * 2
def baseEnd_78467 : Nat := 17907238451755436089619

theorem tailTrace_78467 : CollatzResearch.WordTrace tailWord_78467 prefixEnd_78467 17907238451755436089619 := by
  unfold tailWord_78467
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861926606734934941793655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1907951071156623294529103 2861926606734934941793655)
  ·
    refine ⟨4292889910102402412690483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2861926606734934941793655 4292889910102402412690483)
    ·
      refine ⟨6439334865153603619035725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4292889910102402412690483 6439334865153603619035725)
      ·
        refine ⟨2414750574432601357138397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6439334865153603619035725 2414750574432601357138397)
        ·
          refine ⟨905531465412225508926899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2414750574432601357138397 905531465412225508926899)
          ·
            refine ⟨1358297198118338263390349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905531465412225508926899 1358297198118338263390349)
            ·
              refine ⟨509361449294376848771381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358297198118338263390349 509361449294376848771381)
              ·
                refine ⟨47752635871347829572317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 509361449294376848771381 47752635871347829572317)
                ·
                  refine ⟨17907238451755436089619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47752635871347829572317 17907238451755436089619)
                  ·
                    rfl

theorem cell21_78467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 5, 3].length) (baseStart_78467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78467 prefixEnd_78467 := by exact prefixLift 78467
  have htrace : WordTrace (prefixWord ++ tailWord_78467) baseStart_78467 baseEnd_78467 := by
    simpa [prefixWord, tailWord_78467, baseEnd_78467] using wordTrace_append hprefix tailTrace_78467
  have hstable : (prefixWord ++ tailWord_78467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78467).length < 2 ^ (prefixWord ++ tailWord_78467).sum := by decide
  have hdescent : baseEnd_78467 < baseStart_78467 := by decide
  rcases family_descends (prefixWord ++ tailWord_78467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78484 : List Nat := [2, 4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_78484 : Nat := 118140960795 + 78484 * 2 ^ 59
def prefixEnd_78484 : Nat := 4983230072969 + 3 ^ 40 * 78484 * 2
def baseEnd_78484 : Nat := 17911118083367184306251

theorem tailTrace_78484 : CollatzResearch.WordTrace tailWord_78484 prefixEnd_78484 17911118083367184306251 := by
  unfold tailWord_78484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1431273323836673422581253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1908364431782231230108337 1431273323836673422581253)
  ·
    refine ⟨268363748219376266733985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1431273323836673422581253 268363748219376266733985)
    ·
      refine ⟨201272811164532200050489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268363748219376266733985 201272811164532200050489)
      ·
        refine ⟨150954608373399150037867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201272811164532200050489 150954608373399150037867)
        ·
          refine ⟨226431912560098725056801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150954608373399150037867 226431912560098725056801)
          ·
            refine ⟨169823934420074043792601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226431912560098725056801 169823934420074043792601)
            ·
              refine ⟨127367950815055532844451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169823934420074043792601 127367950815055532844451)
              ·
                refine ⟨191051926222583299266677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127367950815055532844451 191051926222583299266677)
                ·
                  refine ⟨17911118083367184306251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191051926222583299266677 17911118083367184306251)
                  ·
                    rfl

theorem cell21_78484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_78484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78484 prefixEnd_78484 := by exact prefixLift 78484
  have htrace : WordTrace (prefixWord ++ tailWord_78484) baseStart_78484 baseEnd_78484 := by
    simpa [prefixWord, tailWord_78484, baseEnd_78484] using wordTrace_append hprefix tailTrace_78484
  have hstable : (prefixWord ++ tailWord_78484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78484).length < 2 ^ (prefixWord ++ tailWord_78484).sum := by decide
  have hdescent : baseEnd_78484 < baseStart_78484 := by decide
  rcases family_descends (prefixWord ++ tailWord_78484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78549 : List Nat := [1, 3, 2, 5, 2, 1, 2, 1, 4]
def baseStart_78549 : Nat := 118140960795 + 78549 * 2 ^ 59
def prefixEnd_78549 : Nat := 4983230072969 + 3 ^ 40 * 78549 * 2
def baseEnd_78549 : Nat := 17925951968941515722785

theorem tailTrace_78549 : CollatzResearch.WordTrace tailWord_78549 prefixEnd_78549 17925951968941515722785 := by
  unfold tailWord_78549
  simp only [CollatzResearch.WordTrace]
  refine ⟨2864917392437862946278701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1909944928291908630852467 2864917392437862946278701)
  ·
    refine ⟨1074344022164198604854513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2864917392437862946278701 1074344022164198604854513)
    ·
      refine ⟨805758016623148953640885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1074344022164198604854513 805758016623148953640885)
      ·
        refine ⟨75539814058420214403833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 805758016623148953640885 75539814058420214403833)
        ·
          refine ⟨56654860543815160802875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75539814058420214403833 56654860543815160802875)
          ·
            refine ⟨84982290815722741204313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56654860543815160802875 84982290815722741204313)
            ·
              refine ⟨63736718111792055903235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84982290815722741204313 63736718111792055903235)
              ·
                refine ⟨95605077167688083854853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63736718111792055903235 95605077167688083854853)
                ·
                  refine ⟨17925951968941515722785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95605077167688083854853 17925951968941515722785)
                  ·
                    rfl

theorem cell21_78549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_78549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78549 prefixEnd_78549 := by exact prefixLift 78549
  have htrace : WordTrace (prefixWord ++ tailWord_78549) baseStart_78549 baseEnd_78549 := by
    simpa [prefixWord, tailWord_78549, baseEnd_78549] using wordTrace_append hprefix tailTrace_78549
  have hstable : (prefixWord ++ tailWord_78549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78549).length < 2 ^ (prefixWord ++ tailWord_78549).sum := by decide
  have hdescent : baseEnd_78549 < baseStart_78549 := by decide
  rcases family_descends (prefixWord ++ tailWord_78549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78594 : List Nat := [3, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_78594 : Nat := 118140960795 + 78594 * 2 ^ 59
def prefixEnd_78594 : Nat := 4983230072969 + 3 ^ 40 * 78594 * 2
def baseEnd_78594 : Nat := 17936221582031437472693

theorem tailTrace_78594 : CollatzResearch.WordTrace tailWord_78594 prefixEnd_78594 17936221582031437472693 := by
  unfold tailWord_78594
  simp only [CollatzResearch.WordTrace]
  refine ⟨716639669318708907916709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1911039118183223754444557 716639669318708907916709)
  ·
    refine ⟨134369937997257920234383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 716639669318708907916709 134369937997257920234383)
    ·
      refine ⟨201554906995886880351575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134369937997257920234383 201554906995886880351575)
      ·
        refine ⟨302332360493830320527363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201554906995886880351575 302332360493830320527363)
        ·
          refine ⟨453498540740745480791045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302332360493830320527363 453498540740745480791045)
          ·
            refine ⟨85030976388889777648321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 453498540740745480791045 85030976388889777648321)
            ·
              refine ⟨63773232291667333236241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85030976388889777648321 63773232291667333236241)
              ·
                refine ⟨47829924218750499927181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63773232291667333236241 47829924218750499927181)
                ·
                  refine ⟨17936221582031437472693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47829924218750499927181 17936221582031437472693)
                  ·
                    rfl

theorem cell21_78594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_78594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78594 prefixEnd_78594 := by exact prefixLift 78594
  have htrace : WordTrace (prefixWord ++ tailWord_78594) baseStart_78594 baseEnd_78594 := by
    simpa [prefixWord, tailWord_78594, baseEnd_78594] using wordTrace_append hprefix tailTrace_78594
  have hstable : (prefixWord ++ tailWord_78594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78594).length < 2 ^ (prefixWord ++ tailWord_78594).sum := by decide
  have hdescent : baseEnd_78594 < baseStart_78594 := by decide
  rcases family_descends (prefixWord ++ tailWord_78594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78602 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_78602 : Nat := 118140960795 + 78602 * 2 ^ 59
def prefixEnd_78602 : Nat := 4983230072969 + 3 ^ 40 * 78602 * 2
def baseEnd_78602 : Nat := 17938047291025201339343

theorem tailTrace_78602 : CollatzResearch.WordTrace tailWord_78602 prefixEnd_78602 17938047291025201339343 := by
  unfold tailWord_78602
  simp only [CollatzResearch.WordTrace]
  refine ⟨716712615311463249489515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1911233640830568665305373 716712615311463249489515)
  ·
    refine ⟨1075068922967194874234273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 716712615311463249489515 1075068922967194874234273)
    ·
      refine ⟨806301692225396155675705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1075068922967194874234273 806301692225396155675705)
      ·
        refine ⟨604726269169047116756779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 806301692225396155675705 604726269169047116756779)
        ·
          refine ⟨907089403753570675135169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604726269169047116756779 907089403753570675135169)
          ·
            refine ⟨680317052815178006351377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907089403753570675135169 680317052815178006351377)
            ·
              refine ⟨510237789611383504763533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 680317052815178006351377 510237789611383504763533)
              ·
                refine ⟨191339171104268814286325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510237789611383504763533 191339171104268814286325)
                ·
                  refine ⟨17938047291025201339343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191339171104268814286325 17938047291025201339343)
                  ·
                    rfl

theorem cell21_78602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_78602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78602 prefixEnd_78602 := by exact prefixLift 78602
  have htrace : WordTrace (prefixWord ++ tailWord_78602) baseStart_78602 baseEnd_78602 := by
    simpa [prefixWord, tailWord_78602, baseEnd_78602] using wordTrace_append hprefix tailTrace_78602
  have hstable : (prefixWord ++ tailWord_78602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78602).length < 2 ^ (prefixWord ++ tailWord_78602).sum := by decide
  have hdescent : baseEnd_78602 < baseStart_78602 := by decide
  rcases family_descends (prefixWord ++ tailWord_78602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78616 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_78616 : Nat := 118140960795 + 78616 * 2 ^ 59
def prefixEnd_78616 : Nat := 4983230072969 + 3 ^ 40 * 78616 * 2
def baseEnd_78616 : Nat := 17941242281764288105981

theorem tailTrace_78616 : CollatzResearch.WordTrace tailWord_78616 prefixEnd_78616 17941242281764288105981 := by
  unfold tailWord_78616
  simp only [CollatzResearch.WordTrace]
  refine ⟨1433680541597566694483851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1911574055463422259311801 1433680541597566694483851)
  ·
    refine ⟨2150520812396350041725777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1433680541597566694483851 2150520812396350041725777)
    ·
      refine ⟨1612890609297262531294333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2150520812396350041725777 1612890609297262531294333)
      ·
        refine ⟨604833978486473449235375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1612890609297262531294333 604833978486473449235375)
        ·
          refine ⟨907250967729710173853063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604833978486473449235375 907250967729710173853063)
          ·
            refine ⟨1360876451594565260779595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907250967729710173853063 1360876451594565260779595)
            ·
              refine ⟨2041314677391847891169393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1360876451594565260779595 2041314677391847891169393)
              ·
                refine ⟨1530986008043885918377045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2041314677391847891169393 1530986008043885918377045)
                ·
                  refine ⟨17941242281764288105981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1530986008043885918377045 17941242281764288105981)
                  ·
                    rfl

theorem cell21_78616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_78616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78616 prefixEnd_78616 := by exact prefixLift 78616
  have htrace : WordTrace (prefixWord ++ tailWord_78616) baseStart_78616 baseEnd_78616 := by
    simpa [prefixWord, tailWord_78616, baseEnd_78616] using wordTrace_append hprefix tailTrace_78616
  have hstable : (prefixWord ++ tailWord_78616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78616).length < 2 ^ (prefixWord ++ tailWord_78616).sum := by decide
  have hdescent : baseEnd_78616 < baseStart_78616 := by decide
  rcases family_descends (prefixWord ++ tailWord_78616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78709 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 6]
def baseStart_78709 : Nat := 118140960795 + 78709 * 2 ^ 59
def prefixEnd_78709 : Nat := 4983230072969 + 3 ^ 40 * 78709 * 2
def baseEnd_78709 : Nat := 17962466148816793055791

theorem tailTrace_78709 : CollatzResearch.WordTrace tailWord_78709 prefixEnd_78709 17962466148816793055791 := by
  unfold tailWord_78709
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870753071858210272103181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1913835381238806848068787 2870753071858210272103181)
  ·
    refine ⟨1076532401946828852038693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2870753071858210272103181 1076532401946828852038693)
    ·
      refine ⟨201849825365030409757255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1076532401946828852038693 201849825365030409757255)
      ·
        refine ⟨302774738047545614635883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201849825365030409757255 302774738047545614635883)
        ·
          refine ⟨454162107071318421953825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302774738047545614635883 454162107071318421953825)
          ·
            refine ⟨340621580303488816465369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454162107071318421953825 340621580303488816465369)
            ·
              refine ⟨255466185227616612349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340621580303488816465369 255466185227616612349027)
              ·
                refine ⟨383199277841424918523541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255466185227616612349027 383199277841424918523541)
                ·
                  refine ⟨17962466148816793055791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383199277841424918523541 17962466148816793055791)
                  ·
                    rfl

theorem cell21_78709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_78709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78709 prefixEnd_78709 := by exact prefixLift 78709
  have htrace : WordTrace (prefixWord ++ tailWord_78709) baseStart_78709 baseEnd_78709 := by
    simpa [prefixWord, tailWord_78709, baseEnd_78709] using wordTrace_append hprefix tailTrace_78709
  have hstable : (prefixWord ++ tailWord_78709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78709).length < 2 ^ (prefixWord ++ tailWord_78709).sum := by decide
  have hdescent : baseEnd_78709 < baseStart_78709 := by decide
  rcases family_descends (prefixWord ++ tailWord_78709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78723 : List Nat := [1, 1, 1, 3, 4, 1, 4, 6]
def baseStart_78723 : Nat := 118140960795 + 78723 * 2 ^ 59
def prefixEnd_78723 : Nat := 4983230072969 + 3 ^ 40 * 78723 * 2
def baseEnd_78723 : Nat := 5988553713185293274143

theorem tailTrace_78723 : CollatzResearch.WordTrace tailWord_78723 prefixEnd_78723 5988553713185293274143 := by
  unfold tailWord_78723
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871263693807490663112823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1914175795871660442075215 2871263693807490663112823)
  ·
    refine ⟨4306895540711235994669235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2871263693807490663112823 4306895540711235994669235)
    ·
      refine ⟨6460343311066853992003853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4306895540711235994669235 6460343311066853992003853)
      ·
        refine ⟨2422628741650070247001445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6460343311066853992003853 2422628741650070247001445)
        ·
          refine ⟨454242889059388171312771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2422628741650070247001445 454242889059388171312771)
          ·
            refine ⟨681364333589082256969157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454242889059388171312771 681364333589082256969157)
            ·
              refine ⟨127755812547952923181717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 681364333589082256969157 127755812547952923181717)
              ·
                refine ⟨5988553713185293274143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127755812547952923181717 5988553713185293274143)
                ·
                  rfl

theorem cell21_78723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 6].length) (baseStart_78723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78723 prefixEnd_78723 := by exact prefixLift 78723
  have htrace : WordTrace (prefixWord ++ tailWord_78723) baseStart_78723 baseEnd_78723 := by
    simpa [prefixWord, tailWord_78723, baseEnd_78723] using wordTrace_append hprefix tailTrace_78723
  have hstable : (prefixWord ++ tailWord_78723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78723).length < 2 ^ (prefixWord ++ tailWord_78723).sum := by decide
  have hdescent : baseEnd_78723 < baseStart_78723 := by decide
  rcases family_descends (prefixWord ++ tailWord_78723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78737 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 7]
def baseStart_78737 : Nat := 118140960795 + 78737 * 2 ^ 59
def prefixEnd_78737 : Nat := 4983230072969 + 3 ^ 40 * 78737 * 2
def baseEnd_78737 : Nat := 17968856130294966589067

theorem tailTrace_78737 : CollatzResearch.WordTrace tailWord_78737 prefixEnd_78737 17968856130294966589067 := by
  unfold tailWord_78737
  simp only [CollatzResearch.WordTrace]
  refine ⟨2871774315756771054122465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1914516210504514036081643 2871774315756771054122465)
  ·
    refine ⟨2153830736817578290591849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2871774315756771054122465 2153830736817578290591849)
    ·
      refine ⟨1615373052613183717943887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2153830736817578290591849 1615373052613183717943887)
      ·
        refine ⟨2423059578919775576915831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1615373052613183717943887 2423059578919775576915831)
        ·
          refine ⟨3634589368379663365373747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2423059578919775576915831 3634589368379663365373747)
          ·
            refine ⟨5451884052569495048060621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3634589368379663365373747 5451884052569495048060621)
            ·
              refine ⟨2044456519713560643022733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5451884052569495048060621 2044456519713560643022733)
              ·
                refine ⟨766671194892585241133525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2044456519713560643022733 766671194892585241133525)
                ·
                  refine ⟨17968856130294966589067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 766671194892585241133525 17968856130294966589067)
                  ·
                    rfl

theorem cell21_78737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_78737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78737 prefixEnd_78737 := by exact prefixLift 78737
  have htrace : WordTrace (prefixWord ++ tailWord_78737) baseStart_78737 baseEnd_78737 := by
    simpa [prefixWord, tailWord_78737, baseEnd_78737] using wordTrace_append hprefix tailTrace_78737
  have hstable : (prefixWord ++ tailWord_78737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78737).length < 2 ^ (prefixWord ++ tailWord_78737).sum := by decide
  have hdescent : baseEnd_78737 < baseStart_78737 := by decide
  rcases family_descends (prefixWord ++ tailWord_78737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78788 : List Nat := [2, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_78788 : Nat := 118140960795 + 78788 * 2 ^ 59
def prefixEnd_78788 : Nat := 4983230072969 + 3 ^ 40 * 78788 * 2
def baseEnd_78788 : Nat := 17980495025130211238963

theorem tailTrace_78788 : CollatzResearch.WordTrace tailWord_78788 prefixEnd_78788 17980495025130211238963 := by
  unfold tailWord_78788
  simp only [CollatzResearch.WordTrace]
  refine ⟨1436817219286003382114509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1915756292381337842819345 1436817219286003382114509)
  ·
    refine ⟨538806457232251268292941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1436817219286003382114509 538806457232251268292941)
    ·
      refine ⟨202052421462094225609853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 538806457232251268292941 202052421462094225609853)
      ·
        refine ⟨75769658048285334603695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 202052421462094225609853 75769658048285334603695)
        ·
          refine ⟨113654487072428001905543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75769658048285334603695 113654487072428001905543)
          ·
            refine ⟨170481730608642002858315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113654487072428001905543 170481730608642002858315)
            ·
              refine ⟨255722595912963004287473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170481730608642002858315 255722595912963004287473)
              ·
                refine ⟨191791946934722253215605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255722595912963004287473 191791946934722253215605)
                ·
                  refine ⟨17980495025130211238963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191791946934722253215605 17980495025130211238963)
                  ·
                    rfl

theorem cell21_78788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_78788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78788 prefixEnd_78788 := by exact prefixLift 78788
  have htrace : WordTrace (prefixWord ++ tailWord_78788) baseStart_78788 baseEnd_78788 := by
    simpa [prefixWord, tailWord_78788, baseEnd_78788] using wordTrace_append hprefix tailTrace_78788
  have hstable : (prefixWord ++ tailWord_78788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78788).length < 2 ^ (prefixWord ++ tailWord_78788).sum := by decide
  have hdescent : baseEnd_78788 < baseStart_78788 := by decide
  rcases family_descends (prefixWord ++ tailWord_78788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78951 : List Nat := [1, 1, 5, 1, 1, 3, 3, 6]
def baseStart_78951 : Nat := 118140960795 + 78951 * 2 ^ 59
def prefixEnd_78951 : Nat := 4983230072969 + 3 ^ 40 * 78951 * 2
def baseEnd_78951 : Nat := 6005897948626050007321

theorem tailTrace_78951 : CollatzResearch.WordTrace tailWord_78951 prefixEnd_78951 6005897948626050007321 := by
  unfold tailWord_78951
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879579536981485602412707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1919719691320990401608471 2879579536981485602412707)
  ·
    refine ⟨4319369305472228403619061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879579536981485602412707 4319369305472228403619061)
    ·
      refine ⟨404940872388021412839287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4319369305472228403619061 404940872388021412839287)
      ·
        refine ⟨607411308582032119258931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404940872388021412839287 607411308582032119258931)
        ·
          refine ⟨911116962873048178888397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607411308582032119258931 911116962873048178888397)
          ·
            refine ⟨341668861077393067083149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 911116962873048178888397 341668861077393067083149)
            ·
              refine ⟨128125822904022400156181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 341668861077393067083149 128125822904022400156181)
              ·
                refine ⟨6005897948626050007321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128125822904022400156181 6005897948626050007321)
                ·
                  rfl

theorem cell21_78951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 6].length) (baseStart_78951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78951 prefixEnd_78951 := by exact prefixLift 78951
  have htrace : WordTrace (prefixWord ++ tailWord_78951) baseStart_78951 baseEnd_78951 := by
    simpa [prefixWord, tailWord_78951, baseEnd_78951] using wordTrace_append hprefix tailTrace_78951
  have hstable : (prefixWord ++ tailWord_78951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78951).length < 2 ^ (prefixWord ++ tailWord_78951).sum := by decide
  have hdescent : baseEnd_78951 < baseStart_78951 := by decide
  rcases family_descends (prefixWord ++ tailWord_78951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78999 : List Nat := [1, 1, 3, 3, 3, 1, 2, 4, 3]
def baseStart_78999 : Nat := 118140960795 + 78999 * 2 ^ 59
def prefixEnd_78999 : Nat := 4983230072969 + 3 ^ 40 * 78999 * 2
def baseEnd_78999 : Nat := 18028648099840733221865

theorem tailTrace_78999 : CollatzResearch.WordTrace tailWord_78999 prefixEnd_78999 18028648099840733221865 := by
  unfold tailWord_78999
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881330240807589800160051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1920886827205059866773367 2881330240807589800160051)
  ·
    refine ⟨4321995361211384700240077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2881330240807589800160051 4321995361211384700240077)
    ·
      refine ⟨1620748260454269262590029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4321995361211384700240077 1620748260454269262590029)
      ·
        refine ⟨607780597670350973471261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1620748260454269262590029 607780597670350973471261)
        ·
          refine ⟨227917724126381615051723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 607780597670350973471261 227917724126381615051723)
          ·
            refine ⟨341876586189572422577585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227917724126381615051723 341876586189572422577585)
            ·
              refine ⟨256407439642179316933189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341876586189572422577585 256407439642179316933189)
              ·
                refine ⟨48076394932908621924973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 256407439642179316933189 48076394932908621924973)
                ·
                  refine ⟨18028648099840733221865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48076394932908621924973 18028648099840733221865)
                  ·
                    rfl

theorem cell21_78999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 3].length) (baseStart_78999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_78999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_78999 prefixEnd_78999 := by exact prefixLift 78999
  have htrace : WordTrace (prefixWord ++ tailWord_78999) baseStart_78999 baseEnd_78999 := by
    simpa [prefixWord, tailWord_78999, baseEnd_78999] using wordTrace_append hprefix tailTrace_78999
  have hstable : (prefixWord ++ tailWord_78999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78999).length < 2 ^ (prefixWord ++ tailWord_78999).sum := by decide
  have hdescent : baseEnd_78999 < baseStart_78999 := by decide
  rcases family_descends (prefixWord ++ tailWord_78999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79027 : List Nat := [1, 1, 1, 2, 3, 2, 6, 5]
def baseStart_79027 : Nat := 118140960795 + 79027 * 2 ^ 59
def prefixEnd_79027 : Nat := 4983230072969 + 3 ^ 40 * 79027 * 2
def baseEnd_79027 : Nat := 6011679360439635585047

theorem tailTrace_79027 : CollatzResearch.WordTrace tailWord_79027 prefixEnd_79027 6011679360439635585047 := by
  unfold tailWord_79027
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882351484706150582179335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921567656470767054786223 2882351484706150582179335)
  ·
    refine ⟨4323527227059225873269003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882351484706150582179335 4323527227059225873269003)
    ·
      refine ⟨6485290840588838809903505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323527227059225873269003 6485290840588838809903505)
      ·
        refine ⟨4863968130441629107427629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6485290840588838809903505 4863968130441629107427629)
        ·
          refine ⟨1823988048915610915285361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4863968130441629107427629 1823988048915610915285361)
          ·
            refine ⟨1367991036686708186464021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1823988048915610915285361 1367991036686708186464021)
            ·
              refine ⟨64124579844689446240501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1367991036686708186464021 64124579844689446240501)
              ·
                refine ⟨6011679360439635585047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64124579844689446240501 6011679360439635585047)
                ·
                  rfl

theorem cell21_79027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 5].length) (baseStart_79027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79027 prefixEnd_79027 := by exact prefixLift 79027
  have htrace : WordTrace (prefixWord ++ tailWord_79027) baseStart_79027 baseEnd_79027 := by
    simpa [prefixWord, tailWord_79027, baseEnd_79027] using wordTrace_append hprefix tailTrace_79027
  have hstable : (prefixWord ++ tailWord_79027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79027).length < 2 ^ (prefixWord ++ tailWord_79027).sum := by decide
  have hdescent : baseEnd_79027 < baseStart_79027 := by decide
  rcases family_descends (prefixWord ++ tailWord_79027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79044 : List Nat := [2, 3, 3, 1, 3, 2, 7]
def baseStart_79044 : Nat := 118140960795 + 79044 * 2 ^ 59
def prefixEnd_79044 : Nat := 4983230072969 + 3 ^ 40 * 79044 * 2
def baseEnd_79044 : Nat := 2004324190325628330197

theorem tailTrace_79044 : CollatzResearch.WordTrace tailWord_79044 prefixEnd_79044 2004324190325628330197 := by
  unfold tailWord_79044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441485762822281242774093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1921981017096374990365457 1441485762822281242774093)
  ·
    refine ⟨540557161058355466040285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1441485762822281242774093 540557161058355466040285)
    ·
      refine ⟨202708935396883299765107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 540557161058355466040285 202708935396883299765107)
      ·
        refine ⟨304063403095324949647661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202708935396883299765107 304063403095324949647661)
        ·
          refine ⟨114023776160746856117873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304063403095324949647661 114023776160746856117873)
          ·
            refine ⟨85517832120560142088405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114023776160746856117873 85517832120560142088405)
            ·
              refine ⟨2004324190325628330197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 85517832120560142088405 2004324190325628330197)
              ·
                rfl

theorem cell21_79044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 7].length) (baseStart_79044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79044 prefixEnd_79044 := by exact prefixLift 79044
  have htrace : WordTrace (prefixWord ++ tailWord_79044) baseStart_79044 baseEnd_79044 := by
    simpa [prefixWord, tailWord_79044, baseEnd_79044] using wordTrace_append hprefix tailTrace_79044
  have hstable : (prefixWord ++ tailWord_79044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79044).length < 2 ^ (prefixWord ++ tailWord_79044).sum := by decide
  have hdescent : baseEnd_79044 < baseStart_79044 := by decide
  rcases family_descends (prefixWord ++ tailWord_79044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79131 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 8]
def baseStart_79131 : Nat := 118140960795 + 79131 * 2 ^ 59
def prefixEnd_79131 : Nat := 4983230072969 + 3 ^ 40 * 79131 * 2
def baseEnd_79131 : Nat := 18058772298237837021595

theorem tailTrace_79131 : CollatzResearch.WordTrace tailWord_79131 prefixEnd_79131 18058772298237837021595 := by
  unfold tailWord_79131
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886144676329376343965247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1924096450886250895976831 2886144676329376343965247)
  ·
    refine ⟨4329217014494064515947871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2886144676329376343965247 4329217014494064515947871)
    ·
      refine ⟨6493825521741096773921807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4329217014494064515947871 6493825521741096773921807)
      ·
        refine ⟨9740738282611645160882711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6493825521741096773921807 9740738282611645160882711)
        ·
          refine ⟨14611107423917467741324067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9740738282611645160882711 14611107423917467741324067)
          ·
            refine ⟨21916661135876201611986101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14611107423917467741324067 21916661135876201611986101)
            ·
              refine ⟨2054686981488393901123697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21916661135876201611986101 2054686981488393901123697)
              ·
                refine ⟨1541015236116295425842773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2054686981488393901123697 1541015236116295425842773)
                ·
                  refine ⟨18058772298237837021595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1541015236116295425842773 18058772298237837021595)
                  ·
                    rfl

theorem cell21_79131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_79131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79131 prefixEnd_79131 := by exact prefixLift 79131
  have htrace : WordTrace (prefixWord ++ tailWord_79131) baseStart_79131 baseEnd_79131 := by
    simpa [prefixWord, tailWord_79131, baseEnd_79131] using wordTrace_append hprefix tailTrace_79131
  have hstable : (prefixWord ++ tailWord_79131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79131).length < 2 ^ (prefixWord ++ tailWord_79131).sum := by decide
  have hdescent : baseEnd_79131 < baseStart_79131 := by decide
  rcases family_descends (prefixWord ++ tailWord_79131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79162 : List Nat := [3, 1, 1, 1, 4, 1, 10]
def baseStart_79162 : Nat := 118140960795 + 79162 * 2 ^ 59
def prefixEnd_79162 : Nat := 4983230072969 + 3 ^ 40 * 79162 * 2
def baseEnd_79162 : Nat := 2007316324509852444985

theorem tailTrace_79162 : CollatzResearch.WordTrace tailWord_79162 prefixEnd_79162 2007316324509852444985 := by
  unfold tailWord_79162
  simp only [CollatzResearch.WordTrace]
  refine ⟨721818834804267159585935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1924850226144712425562493 721818834804267159585935)
  ·
    refine ⟨1082728252206400739378903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721818834804267159585935 1082728252206400739378903)
    ·
      refine ⟨1624092378309601109068355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1082728252206400739378903 1624092378309601109068355)
      ·
        refine ⟨2436138567464401663602533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624092378309601109068355 2436138567464401663602533)
        ·
          refine ⟨456775981399575311925475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2436138567464401663602533 456775981399575311925475)
          ·
            refine ⟨685163972099362967888213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456775981399575311925475 685163972099362967888213)
            ·
              refine ⟨2007316324509852444985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 685163972099362967888213 2007316324509852444985)
              ·
                rfl

theorem cell21_79162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 10].length) (baseStart_79162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79162 prefixEnd_79162 := by exact prefixLift 79162
  have htrace : WordTrace (prefixWord ++ tailWord_79162) baseStart_79162 baseEnd_79162 := by
    simpa [prefixWord, tailWord_79162, baseEnd_79162] using wordTrace_append hprefix tailTrace_79162
  have hstable : (prefixWord ++ tailWord_79162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79162).length < 2 ^ (prefixWord ++ tailWord_79162).sum := by decide
  have hdescent : baseEnd_79162 < baseStart_79162 := by decide
  rcases family_descends (prefixWord ++ tailWord_79162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79193 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 5]
def baseStart_79193 : Nat := 118140960795 + 79193 * 2 ^ 59
def prefixEnd_79193 : Nat := 4983230072969 + 3 ^ 40 * 79193 * 2
def baseEnd_79193 : Nat := 18072921542939506988135

theorem tailTrace_79193 : CollatzResearch.WordTrace tailWord_79193 prefixEnd_79193 18072921542939506988135 := by
  unfold tailWord_79193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2888406002104760932722233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1925604001403173955148155 2888406002104760932722233)
  ·
    refine ⟨2166304501578570699541675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2888406002104760932722233 2166304501578570699541675)
    ·
      refine ⟨3249456752367856049312513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166304501578570699541675 3249456752367856049312513)
      ·
        refine ⟨2437092564275892036984385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249456752367856049312513 2437092564275892036984385)
        ·
          refine ⟨1827819423206919027738289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2437092564275892036984385 1827819423206919027738289)
          ·
            refine ⟨1370864567405189270803717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827819423206919027738289 1370864567405189270803717)
            ·
              refine ⟨257037106388472988275697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1370864567405189270803717 257037106388472988275697)
              ·
                refine ⟨192777829791354741206773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 257037106388472988275697 192777829791354741206773)
                ·
                  refine ⟨18072921542939506988135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192777829791354741206773 18072921542939506988135)
                  ·
                    rfl

theorem cell21_79193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_79193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79193 prefixEnd_79193 := by exact prefixLift 79193
  have htrace : WordTrace (prefixWord ++ tailWord_79193) baseStart_79193 baseEnd_79193 := by
    simpa [prefixWord, tailWord_79193, baseEnd_79193] using wordTrace_append hprefix tailTrace_79193
  have hstable : (prefixWord ++ tailWord_79193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79193).length < 2 ^ (prefixWord ++ tailWord_79193).sum := by decide
  have hdescent : baseEnd_79193 < baseStart_79193 := by decide
  rcases family_descends (prefixWord ++ tailWord_79193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79227 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 3]
def baseStart_79227 : Nat := 118140960795 + 79227 * 2 ^ 59
def prefixEnd_79227 : Nat := 4983230072969 + 3 ^ 40 * 79227 * 2
def baseEnd_79227 : Nat := 18080680806163003421399

theorem tailTrace_79227 : CollatzResearch.WordTrace tailWord_79227 prefixEnd_79227 18080680806163003421399 := by
  unfold tailWord_79227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2889646083981584739459935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1926430722654389826306623 2889646083981584739459935)
  ·
    refine ⟨4334469125972377109189903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2889646083981584739459935 4334469125972377109189903)
    ·
      refine ⟨6501703688958565663784855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4334469125972377109189903 6501703688958565663784855)
      ·
        refine ⟨9752555533437848495677283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501703688958565663784855 9752555533437848495677283)
        ·
          refine ⟨14628833300156772743515925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752555533437848495677283 14628833300156772743515925)
          ·
            refine ⟨685726560944848722352309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14628833300156772743515925 685726560944848722352309)
            ·
              refine ⟨64286865088579567720529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 685726560944848722352309 64286865088579567720529)
              ·
                refine ⟨48215148816434675790397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64286865088579567720529 48215148816434675790397)
                ·
                  refine ⟨18080680806163003421399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48215148816434675790397 18080680806163003421399)
                  ·
                    rfl

theorem cell21_79227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 3].length) (baseStart_79227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79227 prefixEnd_79227 := by exact prefixLift 79227
  have htrace : WordTrace (prefixWord ++ tailWord_79227) baseStart_79227 baseEnd_79227 := by
    simpa [prefixWord, tailWord_79227, baseEnd_79227] using wordTrace_append hprefix tailTrace_79227
  have hstable : (prefixWord ++ tailWord_79227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79227).length < 2 ^ (prefixWord ++ tailWord_79227).sum := by decide
  have hdescent : baseEnd_79227 < baseStart_79227 := by decide
  rcases family_descends (prefixWord ++ tailWord_79227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79241 : List Nat := [1, 2, 1, 1, 7, 1, 1, 3, 4]
def baseStart_79241 : Nat := 118140960795 + 79241 * 2 ^ 59
def prefixEnd_79241 : Nat := 4983230072969 + 3 ^ 40 * 79241 * 2
def baseEnd_79241 : Nat := 18083875796902090188037

theorem tailTrace_79241 : CollatzResearch.WordTrace tailWord_79241 prefixEnd_79241 18083875796902090188037 := by
  unfold tailWord_79241
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890156705930865130469577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1926771137287243420313051 2890156705930865130469577)
  ·
    refine ⟨2167617529448148847852183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2890156705930865130469577 2167617529448148847852183)
    ·
      refine ⟨3251426294172223271778275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167617529448148847852183 3251426294172223271778275)
      ·
        refine ⟨4877139441258334907667413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3251426294172223271778275 4877139441258334907667413)
        ·
          refine ⟨114307955654492224398455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4877139441258334907667413 114307955654492224398455)
          ·
            refine ⟨171461933481738336597683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114307955654492224398455 171461933481738336597683)
            ·
              refine ⟨257192900222607504896525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171461933481738336597683 257192900222607504896525)
              ·
                refine ⟨96447337583477814336197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257192900222607504896525 96447337583477814336197)
                ·
                  refine ⟨18083875796902090188037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96447337583477814336197 18083875796902090188037)
                  ·
                    rfl

theorem cell21_79241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_79241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79241 prefixEnd_79241 := by exact prefixLift 79241
  have htrace : WordTrace (prefixWord ++ tailWord_79241) baseStart_79241 baseEnd_79241 := by
    simpa [prefixWord, tailWord_79241, baseEnd_79241] using wordTrace_append hprefix tailTrace_79241
  have hstable : (prefixWord ++ tailWord_79241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79241).length < 2 ^ (prefixWord ++ tailWord_79241).sum := by decide
  have hdescent : baseEnd_79241 < baseStart_79241 := by decide
  rcases family_descends (prefixWord ++ tailWord_79241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79272 : List Nat := [2, 1, 6, 1, 3, 8]
def baseStart_79272 : Nat := 118140960795 + 79272 * 2 ^ 59
def prefixEnd_79272 : Nat := 4983230072969 + 3 ^ 40 * 79272 * 2
def baseEnd_79272 : Nat := 670035200713071302641

theorem tailTrace_79272 : CollatzResearch.WordTrace tailWord_79272 prefixEnd_79272 670035200713071302641 := by
  unfold tailWord_79272
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445643684409278712424035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1927524912545704949898713 1445643684409278712424035)
  ·
    refine ⟨2168465526613918068636053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1445643684409278712424035 2168465526613918068636053)
    ·
      refine ⟨101646821560027409467315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2168465526613918068636053 101646821560027409467315)
      ·
        refine ⟨152470232340041114200973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101646821560027409467315 152470232340041114200973)
        ·
          refine ⟨57176337127515417825365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152470232340041114200973 57176337127515417825365)
          ·
            refine ⟨670035200713071302641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 57176337127515417825365 670035200713071302641)
            ·
              rfl

theorem cell21_79272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 8].length) (baseStart_79272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79272 prefixEnd_79272 := by exact prefixLift 79272
  have htrace : WordTrace (prefixWord ++ tailWord_79272) baseStart_79272 baseEnd_79272 := by
    simpa [prefixWord, tailWord_79272, baseEnd_79272] using wordTrace_append hprefix tailTrace_79272
  have hstable : (prefixWord ++ tailWord_79272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79272).length < 2 ^ (prefixWord ++ tailWord_79272).sum := by decide
  have hdescent : baseEnd_79272 < baseStart_79272 := by decide
  rcases family_descends (prefixWord ++ tailWord_79272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79283 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 6]
def baseStart_79283 : Nat := 118140960795 + 79283 * 2 ^ 59
def prefixEnd_79283 : Nat := 4983230072969 + 3 ^ 40 * 79283 * 2
def baseEnd_79283 : Nat := 18093460769119350487951

theorem tailTrace_79283 : CollatzResearch.WordTrace tailWord_79283 prefixEnd_79283 18093460769119350487951 := by
  unfold tailWord_79283
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891688571778706303498503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927792381185804202332335 2891688571778706303498503)
  ·
    refine ⟨4337532857668059455247755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891688571778706303498503 4337532857668059455247755)
    ·
      refine ⟨6506299286502089182871633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4337532857668059455247755 6506299286502089182871633)
      ·
        refine ⟨4879724464876566887153725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6506299286502089182871633 4879724464876566887153725)
        ·
          refine ⟨1829896674328712582682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4879724464876566887153725 1829896674328712582682647)
          ·
            refine ⟨2744845011493068874023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1829896674328712582682647 2744845011493068874023971)
            ·
              refine ⟨4117267517239603311035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2744845011493068874023971 4117267517239603311035957)
              ·
                refine ⟨385993829741212810409621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4117267517239603311035957 385993829741212810409621)
                ·
                  refine ⟨18093460769119350487951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 385993829741212810409621 18093460769119350487951)
                  ·
                    rfl

theorem cell21_79283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_79283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79283 prefixEnd_79283 := by exact prefixLift 79283
  have htrace : WordTrace (prefixWord ++ tailWord_79283) baseStart_79283 baseEnd_79283 := by
    simpa [prefixWord, tailWord_79283, baseEnd_79283] using wordTrace_append hprefix tailTrace_79283
  have hstable : (prefixWord ++ tailWord_79283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79283).length < 2 ^ (prefixWord ++ tailWord_79283).sum := by decide
  have hdescent : baseEnd_79283 < baseStart_79283 := by decide
  rcases family_descends (prefixWord ++ tailWord_79283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79345 : List Nat := [1, 2, 2, 2, 3, 2, 1, 3, 5]
def baseStart_79345 : Nat := 118140960795 + 79345 * 2 ^ 59
def prefixEnd_79345 : Nat := 4983230072969 + 3 ^ 40 * 79345 * 2
def baseEnd_79345 : Nat := 18107610013821020454491

theorem tailTrace_79345 : CollatzResearch.WordTrace tailWord_79345 prefixEnd_79345 18107610013821020454491 := by
  unfold tailWord_79345
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893949897554090892255489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929299931702727261503659 2893949897554090892255489)
  ·
    refine ⟨2170462423165568169191617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2893949897554090892255489 2170462423165568169191617)
    ·
      refine ⟨1627846817374176126893713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2170462423165568169191617 1627846817374176126893713)
      ·
        refine ⟨1220885113030632095170285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627846817374176126893713 1220885113030632095170285)
        ·
          refine ⟨457831917386487035688857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220885113030632095170285 457831917386487035688857)
          ·
            refine ⟨343373938039865276766643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 457831917386487035688857 343373938039865276766643)
            ·
              refine ⟨515060907059797915149965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343373938039865276766643 515060907059797915149965)
              ·
                refine ⟨193147840147424218181237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515060907059797915149965 193147840147424218181237)
                ·
                  refine ⟨18107610013821020454491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193147840147424218181237 18107610013821020454491)
                  ·
                    rfl

theorem cell21_79345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_79345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79345 prefixEnd_79345 := by exact prefixLift 79345
  have htrace : WordTrace (prefixWord ++ tailWord_79345) baseStart_79345 baseEnd_79345 := by
    simpa [prefixWord, tailWord_79345, baseEnd_79345] using wordTrace_append hprefix tailTrace_79345
  have hstable : (prefixWord ++ tailWord_79345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79345).length < 2 ^ (prefixWord ++ tailWord_79345).sum := by decide
  have hdescent : baseEnd_79345 < baseStart_79345 := by decide
  rcases family_descends (prefixWord ++ tailWord_79345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79379 : List Nat := [1, 1, 1, 2, 1, 8, 1, 3, 3]
def baseStart_79379 : Nat := 118140960795 + 79379 * 2 ^ 59
def prefixEnd_79379 : Nat := 4983230072969 + 3 ^ 40 * 79379 * 2
def baseEnd_79379 : Nat := 18115369277044516887755

theorem tailTrace_79379 : CollatzResearch.WordTrace tailWord_79379 prefixEnd_79379 18115369277044516887755 := by
  unfold tailWord_79379
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895189979430914698993191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1930126652953943132662127 2895189979430914698993191)
  ·
    refine ⟨4342784969146372048489787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2895189979430914698993191 4342784969146372048489787)
    ·
      refine ⟨6514177453719558072734681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4342784969146372048489787 6514177453719558072734681)
      ·
        refine ⟨4885633090289668554551011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6514177453719558072734681 4885633090289668554551011)
        ·
          refine ⟨7328449635434502831826517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4885633090289668554551011 7328449635434502831826517)
          ·
            refine ⟨85880269165248080060467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 7328449635434502831826517 85880269165248080060467)
            ·
              refine ⟨128820403747872120090701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85880269165248080060467 128820403747872120090701)
              ·
                refine ⟨48307651405452045034013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128820403747872120090701 48307651405452045034013)
                ·
                  refine ⟨18115369277044516887755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48307651405452045034013 18115369277044516887755)
                  ·
                    rfl

theorem cell21_79379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 3, 3].length) (baseStart_79379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79379 prefixEnd_79379 := by exact prefixLift 79379
  have htrace : WordTrace (prefixWord ++ tailWord_79379) baseStart_79379 baseEnd_79379 := by
    simpa [prefixWord, tailWord_79379, baseEnd_79379] using wordTrace_append hprefix tailTrace_79379
  have hstable : (prefixWord ++ tailWord_79379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79379).length < 2 ^ (prefixWord ++ tailWord_79379).sum := by decide
  have hdescent : baseEnd_79379 < baseStart_79379 := by decide
  rcases family_descends (prefixWord ++ tailWord_79379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_79438 : Nat := 118140960795 + 79438 * 2 ^ 59
def prefixEnd_79438 : Nat := 4983230072969 + 3 ^ 40 * 79438 * 2
def baseEnd_79438 : Nat := 18128833880873525404301

theorem tailTrace_79438 : CollatzResearch.WordTrace tailWord_79438 prefixEnd_79438 18128833880873525404301 := by
  unfold tailWord_79438
  simp only [CollatzResearch.WordTrace]
  refine ⟨362167735777145971923871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1931561257478111850260645 362167735777145971923871)
  ·
    refine ⟨543251603665718957885807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362167735777145971923871 543251603665718957885807)
    ·
      refine ⟨814877405498578436828711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543251603665718957885807 814877405498578436828711)
      ·
        refine ⟨1222316108247867655243067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814877405498578436828711 1222316108247867655243067)
        ·
          refine ⟨1833474162371801482864601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222316108247867655243067 1833474162371801482864601)
          ·
            refine ⟨1375105621778851112148451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1833474162371801482864601 1375105621778851112148451)
            ·
              refine ⟨2062658432668276668222677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1375105621778851112148451 2062658432668276668222677)
              ·
                refine ⟨48343557015662734411469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2062658432668276668222677 48343557015662734411469)
                ·
                  refine ⟨18128833880873525404301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48343557015662734411469 18128833880873525404301)
                  ·
                    rfl

theorem cell21_79438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_79438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79438 prefixEnd_79438 := by exact prefixLift 79438
  have htrace : WordTrace (prefixWord ++ tailWord_79438) baseStart_79438 baseEnd_79438 := by
    simpa [prefixWord, tailWord_79438, baseEnd_79438] using wordTrace_append hprefix tailTrace_79438
  have hstable : (prefixWord ++ tailWord_79438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79438).length < 2 ^ (prefixWord ++ tailWord_79438).sum := by decide
  have hdescent : baseEnd_79438 < baseStart_79438 := by decide
  rcases family_descends (prefixWord ++ tailWord_79438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79534 : List Nat := [4, 1, 4, 1, 3, 1, 2, 5]
def baseStart_79534 : Nat := 118140960795 + 79534 * 2 ^ 59
def prefixEnd_79534 : Nat := 4983230072969 + 3 ^ 40 * 79534 * 2
def baseEnd_79534 : Nat := 6050247462932897268035

theorem tailTrace_79534 : CollatzResearch.WordTrace tailWord_79534 prefixEnd_79534 6050247462932897268035 := by
  unfold tailWord_79534
  simp only [CollatzResearch.WordTrace]
  refine ⟨362605411733672021360707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1933895529246250780590437 362605411733672021360707)
  ·
    refine ⟨543908117600508032041061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362605411733672021360707 543908117600508032041061)
    ·
      refine ⟨101982772050095256007699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 543908117600508032041061 101982772050095256007699)
      ·
        refine ⟨152974158075142884011549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101982772050095256007699 152974158075142884011549)
        ·
          refine ⟨57365309278178581504331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152974158075142884011549 57365309278178581504331)
          ·
            refine ⟨86047963917267872256497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57365309278178581504331 86047963917267872256497)
            ·
              refine ⟨64535972937950904192373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86047963917267872256497 64535972937950904192373)
              ·
                refine ⟨6050247462932897268035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64535972937950904192373 6050247462932897268035)
                ·
                  rfl

theorem cell21_79534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_79534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79534 prefixEnd_79534 := by exact prefixLift 79534
  have htrace : WordTrace (prefixWord ++ tailWord_79534) baseStart_79534 baseEnd_79534 := by
    simpa [prefixWord, tailWord_79534, baseEnd_79534] using wordTrace_append hprefix tailTrace_79534
  have hstable : (prefixWord ++ tailWord_79534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79534).length < 2 ^ (prefixWord ++ tailWord_79534).sum := by decide
  have hdescent : baseEnd_79534 < baseStart_79534 := by decide
  rcases family_descends (prefixWord ++ tailWord_79534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79565 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 3]
def baseStart_79565 : Nat := 118140960795 + 79565 * 2 ^ 59
def prefixEnd_79565 : Nat := 4983230072969 + 3 ^ 40 * 79565 * 2
def baseEnd_79565 : Nat := 18157817011149526787375

theorem tailTrace_79565 : CollatzResearch.WordTrace tailWord_79565 prefixEnd_79565 18157817011149526787375 := by
  unfold tailWord_79565
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901973956757068465264149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1934649304504712310176099 2901973956757068465264149)
  ·
    refine ⟨136030029222987584309257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2901973956757068465264149 136030029222987584309257)
    ·
      refine ⟨102022521917240688231943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136030029222987584309257 102022521917240688231943)
      ·
        refine ⟨153033782875861032347915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102022521917240688231943 153033782875861032347915)
        ·
          refine ⟨229550674313791548521873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153033782875861032347915 229550674313791548521873)
          ·
            refine ⟨172163005735343661391405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229550674313791548521873 172163005735343661391405)
            ·
              refine ⟨64561127150753873021777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172163005735343661391405 64561127150753873021777)
              ·
                refine ⟨48420845363065404766333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64561127150753873021777 48420845363065404766333)
                ·
                  refine ⟨18157817011149526787375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48420845363065404766333 18157817011149526787375)
                  ·
                    rfl

theorem cell21_79565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_79565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79565 prefixEnd_79565 := by exact prefixLift 79565
  have htrace : WordTrace (prefixWord ++ tailWord_79565) baseStart_79565 baseEnd_79565 := by
    simpa [prefixWord, tailWord_79565, baseEnd_79565] using wordTrace_append hprefix tailTrace_79565
  have hstable : (prefixWord ++ tailWord_79565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79565).length < 2 ^ (prefixWord ++ tailWord_79565).sum := by decide
  have hdescent : baseEnd_79565 < baseStart_79565 := by decide
  rcases family_descends (prefixWord ++ tailWord_79565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79649 : List Nat := [1, 2, 3, 2, 1, 4, 1, 2, 5]
def baseStart_79649 : Nat := 118140960795 + 79649 * 2 ^ 59
def prefixEnd_79649 : Nat := 4983230072969 + 3 ^ 40 * 79649 * 2
def baseEnd_79649 : Nat := 18176986955584047387203

theorem tailTrace_79649 : CollatzResearch.WordTrace tailWord_79649 prefixEnd_79649 18176986955584047387203 := by
  unfold tailWord_79649
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905037688452750811322001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1936691792301833874214667 2905037688452750811322001)
  ·
    refine ⟨2178778266339563108491501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2905037688452750811322001 2178778266339563108491501)
    ·
      refine ⟨817041849877336165684313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2178778266339563108491501 817041849877336165684313)
      ·
        refine ⟨612781387408002124263235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 817041849877336165684313 612781387408002124263235)
        ·
          refine ⟨919172081112003186394853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612781387408002124263235 919172081112003186394853)
          ·
            refine ⟨172344765208500597449035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 919172081112003186394853 172344765208500597449035)
            ·
              refine ⟨258517147812750896173553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172344765208500597449035 258517147812750896173553)
              ·
                refine ⟨193887860859563172130165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258517147812750896173553 193887860859563172130165)
                ·
                  refine ⟨18176986955584047387203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193887860859563172130165 18176986955584047387203)
                  ·
                    rfl

theorem cell21_79649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_79649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79649 prefixEnd_79649 := by exact prefixLift 79649
  have htrace : WordTrace (prefixWord ++ tailWord_79649) baseStart_79649 baseEnd_79649 := by
    simpa [prefixWord, tailWord_79649, baseEnd_79649] using wordTrace_append hprefix tailTrace_79649
  have hstable : (prefixWord ++ tailWord_79649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79649).length < 2 ^ (prefixWord ++ tailWord_79649).sum := by decide
  have hdescent : baseEnd_79649 < baseStart_79649 := by decide
  rcases family_descends (prefixWord ++ tailWord_79649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79666 : List Nat := [3, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_79666 : Nat := 118140960795 + 79666 * 2 ^ 59
def prefixEnd_79666 : Nat := 4983230072969 + 3 ^ 40 * 79666 * 2
def baseEnd_79666 : Nat := 18180866587195795603835

theorem tailTrace_79666 : CollatzResearch.WordTrace tailWord_79666 prefixEnd_79666 18180866587195795603835 := by
  unfold tailWord_79666
  simp only [CollatzResearch.WordTrace]
  refine ⟨726414432347790678672713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1937105152927441809793901 726414432347790678672713)
  ·
    refine ⟨544810824260843009004535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 726414432347790678672713 544810824260843009004535)
    ·
      refine ⟨817216236391264513506803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544810824260843009004535 817216236391264513506803)
      ·
        refine ⟨1225824354586896770260205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817216236391264513506803 1225824354586896770260205)
        ·
          refine ⟨459684132970086288847577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1225824354586896770260205 459684132970086288847577)
          ·
            refine ⟨344763099727564716635683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459684132970086288847577 344763099727564716635683)
            ·
              refine ⟨517144649591347074953525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344763099727564716635683 517144649591347074953525)
              ·
                refine ⟨48482310899188788276893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 517144649591347074953525 48482310899188788276893)
                ·
                  refine ⟨18180866587195795603835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48482310899188788276893 18180866587195795603835)
                  ·
                    rfl

theorem cell21_79666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_79666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79666 prefixEnd_79666 := by exact prefixLift 79666
  have htrace : WordTrace (prefixWord ++ tailWord_79666) baseStart_79666 baseEnd_79666 := by
    simpa [prefixWord, tailWord_79666, baseEnd_79666] using wordTrace_append hprefix tailTrace_79666
  have hstable : (prefixWord ++ tailWord_79666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79666).length < 2 ^ (prefixWord ++ tailWord_79666).sum := by decide
  have hdescent : baseEnd_79666 < baseStart_79666 := by decide
  rcases family_descends (prefixWord ++ tailWord_79666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79697 : List Nat := [1, 2, 2, 1, 5, 2, 3, 1, 4]
def baseStart_79697 : Nat := 118140960795 + 79697 * 2 ^ 59
def prefixEnd_79697 : Nat := 4983230072969 + 3 ^ 40 * 79697 * 2
def baseEnd_79697 : Nat := 18187941209546630587105

theorem tailTrace_79697 : CollatzResearch.WordTrace tailWord_79697 prefixEnd_79697 18187941209546630587105 := by
  unfold tailWord_79697
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906788392278855009069345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1937858928185903339379563 2906788392278855009069345)
  ·
    refine ⟨2180091294209141256802009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2906788392278855009069345 2180091294209141256802009)
    ·
      refine ⟨1635068470656855942601507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2180091294209141256802009 1635068470656855942601507)
      ·
        refine ⟨2452602705985283913902261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635068470656855942601507 2452602705985283913902261)
        ·
          refine ⟨229931503686120366928337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2452602705985283913902261 229931503686120366928337)
          ·
            refine ⟨172448627764590275196253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229931503686120366928337 172448627764590275196253)
            ·
              refine ⟨64668235411721353198595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172448627764590275196253 64668235411721353198595)
              ·
                refine ⟨97002353117582029797893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64668235411721353198595 97002353117582029797893)
                ·
                  refine ⟨18187941209546630587105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97002353117582029797893 18187941209546630587105)
                  ·
                    rfl

theorem cell21_79697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_79697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79697 prefixEnd_79697 := by exact prefixLift 79697
  have htrace : WordTrace (prefixWord ++ tailWord_79697) baseStart_79697 baseEnd_79697 := by
    simpa [prefixWord, tailWord_79697, baseEnd_79697] using wordTrace_append hprefix tailTrace_79697
  have hstable : (prefixWord ++ tailWord_79697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79697).length < 2 ^ (prefixWord ++ tailWord_79697).sum := by decide
  have hdescent : baseEnd_79697 < baseStart_79697 := by decide
  rcases family_descends (prefixWord ++ tailWord_79697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79711 : List Nat := [1, 1, 2, 3, 1, 6, 2, 5]
def baseStart_79711 : Nat := 118140960795 + 79711 * 2 ^ 59
def prefixEnd_79711 : Nat := 4983230072969 + 3 ^ 40 * 79711 * 2
def baseEnd_79711 : Nat := 6063712066761905784581

theorem tailTrace_79711 : CollatzResearch.WordTrace tailWord_79711 prefixEnd_79711 6063712066761905784581 := by
  unfold tailWord_79711
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907299014228135400078987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1938199342818756933385991 2907299014228135400078987)
  ·
    refine ⟨4360948521342203100118481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2907299014228135400078987 4360948521342203100118481)
    ·
      refine ⟨3270711391006652325088861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360948521342203100118481 3270711391006652325088861)
      ·
        refine ⟨1226516771627494621908323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3270711391006652325088861 1226516771627494621908323)
        ·
          refine ⟨1839775157441241932862485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1226516771627494621908323 1839775157441241932862485)
          ·
            refine ⟨86239460505058215602929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1839775157441241932862485 86239460505058215602929)
            ·
              refine ⟨64679595378793661702197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86239460505058215602929 64679595378793661702197)
              ·
                refine ⟨6063712066761905784581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64679595378793661702197 6063712066761905784581)
                ·
                  rfl

theorem cell21_79711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 5].length) (baseStart_79711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79711 prefixEnd_79711 := by exact prefixLift 79711
  have htrace : WordTrace (prefixWord ++ tailWord_79711) baseStart_79711 baseEnd_79711 := by
    simpa [prefixWord, tailWord_79711, baseEnd_79711] using wordTrace_append hprefix tailTrace_79711
  have hstable : (prefixWord ++ tailWord_79711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79711).length < 2 ^ (prefixWord ++ tailWord_79711).sum := by decide
  have hdescent : baseEnd_79711 < baseStart_79711 := by decide
  rcases family_descends (prefixWord ++ tailWord_79711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79739 : List Nat := [1, 1, 1, 1, 1, 5, 1, 6, 4]
def baseStart_79739 : Nat := 118140960795 + 79739 * 2 ^ 59
def prefixEnd_79739 : Nat := 4983230072969 + 3 ^ 40 * 79739 * 2
def baseEnd_79739 : Nat := 18197526181763890887019

theorem tailTrace_79739 : CollatzResearch.WordTrace tailWord_79739 prefixEnd_79739 18197526181763890887019 := by
  unfold tailWord_79739
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908320258126696182098271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1938880172084464121398847 2908320258126696182098271)
  ·
    refine ⟨4362480387190044273147407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908320258126696182098271 4362480387190044273147407)
    ·
      refine ⟨6543720580785066409721111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4362480387190044273147407 6543720580785066409721111)
      ·
        refine ⟨9815580871177599614581667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6543720580785066409721111 9815580871177599614581667)
        ·
          refine ⟨14723371306766399421872501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9815580871177599614581667 14723371306766399421872501)
          ·
            refine ⟨1380316060009349945800547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14723371306766399421872501 1380316060009349945800547)
            ·
              refine ⟨2070474090014024918700821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1380316060009349945800547 2070474090014024918700821)
              ·
                refine ⟨97053472969407418064101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070474090014024918700821 97053472969407418064101)
                ·
                  refine ⟨18197526181763890887019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97053472969407418064101 18197526181763890887019)
                  ·
                    rfl

theorem cell21_79739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_79739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79739 prefixEnd_79739 := by exact prefixLift 79739
  have htrace : WordTrace (prefixWord ++ tailWord_79739) baseStart_79739 baseEnd_79739 := by
    simpa [prefixWord, tailWord_79739, baseEnd_79739] using wordTrace_append hprefix tailTrace_79739
  have hstable : (prefixWord ++ tailWord_79739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79739).length < 2 ^ (prefixWord ++ tailWord_79739).sum := by decide
  have hdescent : baseEnd_79739 < baseStart_79739 := by decide
  rcases family_descends (prefixWord ++ tailWord_79739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79770 : List Nat := [3, 1, 1, 4, 2, 1, 2, 7]
def baseStart_79770 : Nat := 118140960795 + 79770 * 2 ^ 59
def prefixEnd_79770 : Nat := 4983230072969 + 3 ^ 40 * 79770 * 2
def baseEnd_79770 : Nat := 6068200268038241956763

theorem tailTrace_79770 : CollatzResearch.WordTrace tailWord_79770 prefixEnd_79770 6068200268038241956763 := by
  unfold tailWord_79770
  simp only [CollatzResearch.WordTrace]
  refine ⟨727362730253597119119191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1939633947342925650984509 727362730253597119119191)
  ·
    refine ⟨1091044095380395678678787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727362730253597119119191 1091044095380395678678787)
    ·
      refine ⟨1636566143070593518018181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091044095380395678678787 1636566143070593518018181)
      ·
        refine ⟨306856151825736284628409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1636566143070593518018181 306856151825736284628409)
        ·
          refine ⟨230142113869302213471307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306856151825736284628409 230142113869302213471307)
          ·
            refine ⟨345213170803953320206961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230142113869302213471307 345213170803953320206961)
            ·
              refine ⟨258909878102964990155221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345213170803953320206961 258909878102964990155221)
              ·
                refine ⟨6068200268038241956763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 258909878102964990155221 6068200268038241956763)
                ·
                  rfl

theorem cell21_79770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 7].length) (baseStart_79770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79770 prefixEnd_79770 := by exact prefixLift 79770
  have htrace : WordTrace (prefixWord ++ tailWord_79770) baseStart_79770 baseEnd_79770 := by
    simpa [prefixWord, tailWord_79770, baseEnd_79770] using wordTrace_append hprefix tailTrace_79770
  have hstable : (prefixWord ++ tailWord_79770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79770).length < 2 ^ (prefixWord ++ tailWord_79770).sum := by decide
  have hdescent : baseEnd_79770 < baseStart_79770 := by decide
  rcases family_descends (prefixWord ++ tailWord_79770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79804 : List Nat := [2, 2, 2, 5, 1, 2, 1, 6]
def baseStart_79804 : Nat := 118140960795 + 79804 * 2 ^ 59
def prefixEnd_79804 : Nat := 4983230072969 + 3 ^ 40 * 79804 * 2
def baseEnd_79804 : Nat := 6070786689112740767851

theorem tailTrace_79804 : CollatzResearch.WordTrace tailWord_79804 prefixEnd_79804 6070786689112740767851 := by
  unfold tailWord_79804
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455345501445606141607233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1940460668594141522142977 1455345501445606141607233)
  ·
    refine ⟨1091509126084204606205425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1455345501445606141607233 1091509126084204606205425)
    ·
      refine ⟨818631844563153454654069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091509126084204606205425 818631844563153454654069)
      ·
        refine ⟨76746735427795636373819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 818631844563153454654069 76746735427795636373819)
        ·
          refine ⟨115120103141693454560729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76746735427795636373819 115120103141693454560729)
          ·
            refine ⟨86340077356270090920547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115120103141693454560729 86340077356270090920547)
            ·
              refine ⟨129510116034405136380821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86340077356270090920547 129510116034405136380821)
              ·
                refine ⟨6070786689112740767851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129510116034405136380821 6070786689112740767851)
                ·
                  rfl

theorem cell21_79804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_79804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79804 prefixEnd_79804 := by exact prefixLift 79804
  have htrace : WordTrace (prefixWord ++ tailWord_79804) baseStart_79804 baseEnd_79804 := by
    simpa [prefixWord, tailWord_79804, baseEnd_79804] using wordTrace_append hprefix tailTrace_79804
  have hstable : (prefixWord ++ tailWord_79804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79804).length < 2 ^ (prefixWord ++ tailWord_79804).sum := by decide
  have hdescent : baseEnd_79804 < baseStart_79804 := by decide
  rcases family_descends (prefixWord ++ tailWord_79804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79911 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 5]
def baseStart_79911 : Nat := 118140960795 + 79911 * 2 ^ 59
def prefixEnd_79911 : Nat := 4983230072969 + 3 ^ 40 * 79911 * 2
def baseEnd_79911 : Nat := 18236778925129814020001

theorem tailTrace_79911 : CollatzResearch.WordTrace tailWord_79911 prefixEnd_79911 18236778925129814020001 := by
  unfold tailWord_79911
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914593613503569557359587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1943062409002379704906391 2914593613503569557359587)
  ·
    refine ⟨4371890420255354336039381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2914593613503569557359587 4371890420255354336039381)
    ·
      refine ⟨102466181724734867250923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4371890420255354336039381 102466181724734867250923)
      ·
        refine ⟨153699272587102300876385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102466181724734867250923 153699272587102300876385)
        ·
          refine ⟨115274454440326725657289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153699272587102300876385 115274454440326725657289)
          ·
            refine ⟨86455840830245044242967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115274454440326725657289 86455840830245044242967)
            ·
              refine ⟨129683761245367566364451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86455840830245044242967 129683761245367566364451)
              ·
                refine ⟨194525641868051349546677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129683761245367566364451 194525641868051349546677)
                ·
                  refine ⟨18236778925129814020001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194525641868051349546677 18236778925129814020001)
                  ·
                    rfl

theorem cell21_79911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_79911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79911 prefixEnd_79911 := by exact prefixLift 79911
  have htrace : WordTrace (prefixWord ++ tailWord_79911) baseStart_79911 baseEnd_79911 := by
    simpa [prefixWord, tailWord_79911, baseEnd_79911] using wordTrace_append hprefix tailTrace_79911
  have hstable : (prefixWord ++ tailWord_79911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79911).length < 2 ^ (prefixWord ++ tailWord_79911).sum := by decide
  have hdescent : baseEnd_79911 < baseStart_79911 := by decide
  rcases family_descends (prefixWord ++ tailWord_79911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79922 : List Nat := [3, 2, 1, 1, 2, 4, 2, 6]
def baseStart_79922 : Nat := 118140960795 + 79922 * 2 ^ 59
def prefixEnd_79922 : Nat := 4983230072969 + 3 ^ 40 * 79922 * 2
def baseEnd_79922 : Nat := 6079763091665413112215

theorem tailTrace_79922 : CollatzResearch.WordTrace tailWord_79922 prefixEnd_79922 6079763091665413112215 := by
  unfold tailWord_79922
  simp only [CollatzResearch.WordTrace]
  refine ⟨728748704115929609002505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1943329877642478957340013 728748704115929609002505)
  ·
    refine ⟨546561528086947206751879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 728748704115929609002505 546561528086947206751879)
    ·
      refine ⟨819842292130420810127819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546561528086947206751879 819842292130420810127819)
      ·
        refine ⟨1229763438195631215191729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 819842292130420810127819 1229763438195631215191729)
        ·
          refine ⟨922322578646723411393797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229763438195631215191729 922322578646723411393797)
          ·
            refine ⟨172935483496260639636337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 922322578646723411393797 172935483496260639636337)
            ·
              refine ⟨129701612622195479727253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172935483496260639636337 129701612622195479727253)
              ·
                refine ⟨6079763091665413112215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129701612622195479727253 6079763091665413112215)
                ·
                  rfl

theorem cell21_79922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_79922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79922 prefixEnd_79922 := by exact prefixLift 79922
  have htrace : WordTrace (prefixWord ++ tailWord_79922) baseStart_79922 baseEnd_79922 := by
    simpa [prefixWord, tailWord_79922, baseEnd_79922] using wordTrace_append hprefix tailTrace_79922
  have hstable : (prefixWord ++ tailWord_79922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79922).length < 2 ^ (prefixWord ++ tailWord_79922).sum := by decide
  have hdescent : baseEnd_79922 < baseStart_79922 := by decide
  rcases family_descends (prefixWord ++ tailWord_79922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79953 : List Nat := [1, 2, 2, 1, 3, 1, 1, 7, 3]
def baseStart_79953 : Nat := 118140960795 + 79953 * 2 ^ 59
def prefixEnd_79953 : Nat := 4983230072969 + 3 ^ 40 * 79953 * 2
def baseEnd_79953 : Nat := 18246363897347074319915

theorem tailTrace_79953 : CollatzResearch.WordTrace tailWord_79953 prefixEnd_79953 18246363897347074319915 := by
  unfold tailWord_79953
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916125479351410730388513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1944083652900940486925675 2916125479351410730388513)
  ·
    refine ⟨2187094109513558047791385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2916125479351410730388513 2187094109513558047791385)
    ·
      refine ⟨1640320582135168535843539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187094109513558047791385 1640320582135168535843539)
      ·
        refine ⟨2460480873202752803765309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640320582135168535843539 2460480873202752803765309)
        ·
          refine ⟨922680327451032301411991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2460480873202752803765309 922680327451032301411991)
          ·
            refine ⟨1384020491176548452117987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922680327451032301411991 1384020491176548452117987)
            ·
              refine ⟨2076030736764822678176981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1384020491176548452117987 2076030736764822678176981)
              ·
                refine ⟨48656970392925531519773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2076030736764822678176981 48656970392925531519773)
                ·
                  refine ⟨18246363897347074319915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48656970392925531519773 18246363897347074319915)
                  ·
                    rfl

theorem cell21_79953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_79953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_79953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_79953 prefixEnd_79953 := by exact prefixLift 79953
  have htrace : WordTrace (prefixWord ++ tailWord_79953) baseStart_79953 baseEnd_79953 := by
    simpa [prefixWord, tailWord_79953, baseEnd_79953] using wordTrace_append hprefix tailTrace_79953
  have hstable : (prefixWord ++ tailWord_79953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79953).length < 2 ^ (prefixWord ++ tailWord_79953).sum := by decide
  have hdescent : baseEnd_79953 < baseStart_79953 := by decide
  rcases family_descends (prefixWord ++ tailWord_79953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80029 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 5]
def baseStart_80029 : Nat := 118140960795 + 80029 * 2 ^ 59
def prefixEnd_80029 : Nat := 4983230072969 + 3 ^ 40 * 80029 * 2
def baseEnd_80029 : Nat := 18263708132787831053093

theorem tailTrace_80029 : CollatzResearch.WordTrace tailWord_80029 prefixEnd_80029 18263708132787831053093 := by
  unfold tailWord_80029
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918897427076075710155141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1945931618050717140103427 2918897427076075710155141)
  ·
    refine ⟨547293267576764195654089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2918897427076075710155141 547293267576764195654089)
    ·
      refine ⟨410469950682573146740567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547293267576764195654089 410469950682573146740567)
      ·
        refine ⟨615704926023859720110851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410469950682573146740567 615704926023859720110851)
        ·
          refine ⟨923557389035789580166277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615704926023859720110851 923557389035789580166277)
          ·
            refine ⟨173167010444210546281177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 923557389035789580166277 173167010444210546281177)
            ·
              refine ⟨129875257833157909710883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173167010444210546281177 129875257833157909710883)
              ·
                refine ⟨194812886749736864566325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129875257833157909710883 194812886749736864566325)
                ·
                  refine ⟨18263708132787831053093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 194812886749736864566325 18263708132787831053093)
                  ·
                    rfl

theorem cell21_80029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_80029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80029 prefixEnd_80029 := by exact prefixLift 80029
  have htrace : WordTrace (prefixWord ++ tailWord_80029) baseStart_80029 baseEnd_80029 := by
    simpa [prefixWord, tailWord_80029, baseEnd_80029] using wordTrace_append hprefix tailTrace_80029
  have hstable : (prefixWord ++ tailWord_80029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80029).length < 2 ^ (prefixWord ++ tailWord_80029).sum := by decide
  have hdescent : baseEnd_80029 < baseStart_80029 := by decide
  rcases family_descends (prefixWord ++ tailWord_80029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80057 : List Nat := [1, 2, 1, 4, 1, 2, 3, 7]
def baseStart_80057 : Nat := 118140960795 + 80057 * 2 ^ 59
def prefixEnd_80057 : Nat := 4983230072969 + 3 ^ 40 * 80057 * 2
def baseEnd_80057 : Nat := 6090032704755334862123

theorem tailTrace_80057 : CollatzResearch.WordTrace tailWord_80057 prefixEnd_80057 6090032704755334862123 := by
  unfold tailWord_80057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919918670974636492174425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1946612447316424328116283 2919918670974636492174425)
  ·
    refine ⟨2189939003230977369130819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2919918670974636492174425 2189939003230977369130819)
    ·
      refine ⟨3284908504846466053696229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189939003230977369130819 3284908504846466053696229)
      ·
        refine ⟨615920344658712385068043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3284908504846466053696229 615920344658712385068043)
        ·
          refine ⟨923880516988068577602065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615920344658712385068043 923880516988068577602065)
          ·
            refine ⟨692910387741051433201549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 923880516988068577602065 692910387741051433201549)
            ·
              refine ⟨259841395402894287450581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 692910387741051433201549 259841395402894287450581)
              ·
                refine ⟨6090032704755334862123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 259841395402894287450581 6090032704755334862123)
                ·
                  rfl

theorem cell21_80057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 7].length) (baseStart_80057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80057 prefixEnd_80057 := by exact prefixLift 80057
  have htrace : WordTrace (prefixWord ++ tailWord_80057) baseStart_80057 baseEnd_80057 := by
    simpa [prefixWord, tailWord_80057, baseEnd_80057] using wordTrace_append hprefix tailTrace_80057
  have hstable : (prefixWord ++ tailWord_80057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80057).length < 2 ^ (prefixWord ++ tailWord_80057).sum := by decide
  have hdescent : baseEnd_80057 < baseStart_80057 := by decide
  rcases family_descends (prefixWord ++ tailWord_80057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80136 : List Nat := [2, 1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_80136 : Nat := 118140960795 + 80136 * 2 ^ 59
def prefixEnd_80136 : Nat := 4983230072969 + 3 ^ 40 * 80136 * 2
def baseEnd_80136 : Nat := 18288126990579422769541

theorem tailTrace_80136 : CollatzResearch.WordTrace tailWord_80136 prefixEnd_80136 18288126990579422769541 := by
  unfold tailWord_80136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461400018844216492150131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1948533358458955322866841 1461400018844216492150131)
  ·
    refine ⟨2192100028266324738225197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461400018844216492150131 2192100028266324738225197)
    ·
      refine ⟨822037510599871776834449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2192100028266324738225197 822037510599871776834449)
      ·
        refine ⟨616528132949903832625837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822037510599871776834449 616528132949903832625837)
        ·
          refine ⟨231198049856213937234689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616528132949903832625837 231198049856213937234689)
          ·
            refine ⟨173398537392160452926017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231198049856213937234689 173398537392160452926017)
            ·
              refine ⟨130048903044120339694513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173398537392160452926017 130048903044120339694513)
              ·
                refine ⟨97536677283090254770885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130048903044120339694513 97536677283090254770885)
                ·
                  refine ⟨18288126990579422769541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97536677283090254770885 18288126990579422769541)
                  ·
                    rfl

theorem cell21_80136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_80136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80136 prefixEnd_80136 := by exact prefixLift 80136
  have htrace : WordTrace (prefixWord ++ tailWord_80136) baseStart_80136 baseEnd_80136 := by
    simpa [prefixWord, tailWord_80136, baseEnd_80136] using wordTrace_append hprefix tailTrace_80136
  have hstable : (prefixWord ++ tailWord_80136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80136).length < 2 ^ (prefixWord ++ tailWord_80136).sum := by decide
  have hdescent : baseEnd_80136 < baseStart_80136 := by decide
  rcases family_descends (prefixWord ++ tailWord_80136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80147 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 9]
def baseStart_80147 : Nat := 118140960795 + 80147 * 2 ^ 59
def prefixEnd_80147 : Nat := 4983230072969 + 3 ^ 40 * 80147 * 2
def baseEnd_80147 : Nat := 18290637340445848086185

theorem tailTrace_80147 : CollatzResearch.WordTrace tailWord_80147 prefixEnd_80147 18290637340445848086185 := by
  unfold tailWord_80147
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923201240648581862950695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948800827099054575300463 2923201240648581862950695)
  ·
    refine ⟨4384801860972872794426043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923201240648581862950695 4384801860972872794426043)
    ·
      refine ⟨6577202791459309191639065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4384801860972872794426043 6577202791459309191639065)
      ·
        refine ⟨4932902093594481893729299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6577202791459309191639065 4932902093594481893729299)
        ·
          refine ⟨7399353140391722840593949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4932902093594481893729299 7399353140391722840593949)
          ·
            refine ⟨2774757427646896065222731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7399353140391722840593949 2774757427646896065222731)
            ·
              refine ⟨4162136141470344097834097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2774757427646896065222731 4162136141470344097834097)
              ·
                refine ⟨3121602106102758073375573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4162136141470344097834097 3121602106102758073375573)
                ·
                  refine ⟨18290637340445848086185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3121602106102758073375573 18290637340445848086185)
                  ·
                    rfl

theorem cell21_80147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_80147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80147 prefixEnd_80147 := by exact prefixLift 80147
  have htrace : WordTrace (prefixWord ++ tailWord_80147) baseStart_80147 baseEnd_80147 := by
    simpa [prefixWord, tailWord_80147, baseEnd_80147] using wordTrace_append hprefix tailTrace_80147
  have hstable : (prefixWord ++ tailWord_80147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80147).length < 2 ^ (prefixWord ++ tailWord_80147).sum := by decide
  have hdescent : baseEnd_80147 < baseStart_80147 := by decide
  rcases family_descends (prefixWord ++ tailWord_80147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80164 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_80164 : Nat := 118140960795 + 80164 * 2 ^ 59
def prefixEnd_80164 : Nat := 4983230072969 + 3 ^ 40 * 80164 * 2
def baseEnd_80164 : Nat := 18294516972057596302817

theorem tailTrace_80164 : CollatzResearch.WordTrace tailWord_80164 prefixEnd_80164 18294516972057596302817 := by
  unfold tailWord_80164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461910640793496883159773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1949214187724662510879697 1461910640793496883159773)
  ·
    refine ⟨548216490297561331184915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1461910640793496883159773 548216490297561331184915)
    ·
      refine ⟨822324735446341996777373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548216490297561331184915 822324735446341996777373)
      ·
        refine ⟨308371775792378248791515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 822324735446341996777373 308371775792378248791515)
        ·
          refine ⟨462557663688567373187273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308371775792378248791515 462557663688567373187273)
          ·
            refine ⟨346918247766425529890455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462557663688567373187273 346918247766425529890455)
            ·
              refine ⟨520377371649638294835683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346918247766425529890455 520377371649638294835683)
              ·
                refine ⟨780566057474457442253525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520377371649638294835683 780566057474457442253525)
                ·
                  refine ⟨18294516972057596302817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 780566057474457442253525 18294516972057596302817)
                  ·
                    rfl

theorem cell21_80164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_80164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80164 prefixEnd_80164 := by exact prefixLift 80164
  have htrace : WordTrace (prefixWord ++ tailWord_80164) baseStart_80164 baseEnd_80164 := by
    simpa [prefixWord, tailWord_80164, baseEnd_80164] using wordTrace_append hprefix tailTrace_80164
  have hstable : (prefixWord ++ tailWord_80164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80164).length < 2 ^ (prefixWord ++ tailWord_80164).sum := by decide
  have hdescent : baseEnd_80164 < baseStart_80164 := by decide
  rcases family_descends (prefixWord ++ tailWord_80164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80195 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 4]
def baseStart_80195 : Nat := 118140960795 + 80195 * 2 ^ 59
def prefixEnd_80195 : Nat := 4983230072969 + 3 ^ 40 * 80195 * 2
def baseEnd_80195 : Nat := 18301591594408431286087

theorem tailTrace_80195 : CollatzResearch.WordTrace tailWord_80195 prefixEnd_80195 18301591594408431286087 := by
  unfold tailWord_80195
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924951944474686060698039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1949967962983124040465359 2924951944474686060698039)
  ·
    refine ⟨4387427916712029091047059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2924951944474686060698039 4387427916712029091047059)
    ·
      refine ⟨6581141875068043636570589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387427916712029091047059 6581141875068043636570589)
      ·
        refine ⟨2467928203150516363713971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6581141875068043636570589 2467928203150516363713971)
        ·
          refine ⟨3701892304725774545570957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2467928203150516363713971 3701892304725774545570957)
          ·
            refine ⟨1388209614272165454589109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3701892304725774545570957 1388209614272165454589109)
            ·
              refine ⟨130144651338015511367729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1388209614272165454589109 130144651338015511367729)
              ·
                refine ⟨97608488503511633525797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130144651338015511367729 97608488503511633525797)
                ·
                  refine ⟨18301591594408431286087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97608488503511633525797 18301591594408431286087)
                  ·
                    rfl

theorem cell21_80195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_80195 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80195 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80195 prefixEnd_80195 := by exact prefixLift 80195
  have htrace : WordTrace (prefixWord ++ tailWord_80195) baseStart_80195 baseEnd_80195 := by
    simpa [prefixWord, tailWord_80195, baseEnd_80195] using wordTrace_append hprefix tailTrace_80195
  have hstable : (prefixWord ++ tailWord_80195).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80195).length < 2 ^ (prefixWord ++ tailWord_80195).sum := by decide
  have hdescent : baseEnd_80195 < baseStart_80195 := by decide
  rcases family_descends (prefixWord ++ tailWord_80195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80226 : List Nat := [3, 3, 2, 1, 1, 3, 1, 7]
def baseStart_80226 : Nat := 118140960795 + 80226 * 2 ^ 59
def prefixEnd_80226 : Nat := 4983230072969 + 3 ^ 40 * 80226 * 2
def baseEnd_80226 : Nat := 6102888738919755423119

theorem tailTrace_80226 : CollatzResearch.WordTrace tailWord_80226 prefixEnd_80226 6102888738919755423119 := by
  unfold tailWord_80226
  simp only [CollatzResearch.WordTrace]
  refine ⟨731520651840594588769133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1950721738241585570051021 731520651840594588769133)
  ·
    refine ⟨274320244440222970788425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 731520651840594588769133 274320244440222970788425)
    ·
      refine ⟨205740183330167228091319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274320244440222970788425 205740183330167228091319)
      ·
        refine ⟨308610274995250842136979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205740183330167228091319 308610274995250842136979)
        ·
          refine ⟨462915412492876263205469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308610274995250842136979 462915412492876263205469)
          ·
            refine ⟨173593279684828598702051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 462915412492876263205469 173593279684828598702051)
            ·
              refine ⟨260389919527242898053077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173593279684828598702051 260389919527242898053077)
              ·
                refine ⟨6102888738919755423119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 260389919527242898053077 6102888738919755423119)
                ·
                  rfl

theorem cell21_80226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_80226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80226 prefixEnd_80226 := by exact prefixLift 80226
  have htrace : WordTrace (prefixWord ++ tailWord_80226) baseStart_80226 baseEnd_80226 := by
    simpa [prefixWord, tailWord_80226, baseEnd_80226] using wordTrace_append hprefix tailTrace_80226
  have hstable : (prefixWord ++ tailWord_80226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80226).length < 2 ^ (prefixWord ++ tailWord_80226).sum := by decide
  have hdescent : baseEnd_80226 < baseStart_80226 := by decide
  rcases family_descends (prefixWord ++ tailWord_80226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80257 : List Nat := [1, 2, 4, 3, 1, 1, 3, 1, 5]
def baseStart_80257 : Nat := 118140960795 + 80257 * 2 ^ 59
def prefixEnd_80257 : Nat := 4983230072969 + 3 ^ 40 * 80257 * 2
def baseEnd_80257 : Nat := 18315740839110101252627

theorem tailTrace_80257 : CollatzResearch.WordTrace tailWord_80257 prefixEnd_80257 18315740839110101252627 := by
  unfold tailWord_80257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927213270250070649455025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1951475513500047099636683 2927213270250070649455025)
  ·
    refine ⟨2195409952687552987091269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2927213270250070649455025 2195409952687552987091269)
    ·
      refine ⟨411639366128916185079613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2195409952687552987091269 411639366128916185079613)
      ·
        refine ⟨154364762298343569404855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411639366128916185079613 154364762298343569404855)
        ·
          refine ⟨231547143447515354107283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154364762298343569404855 231547143447515354107283)
          ·
            refine ⟨347320715171273031160925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231547143447515354107283 347320715171273031160925)
            ·
              refine ⟨130245268189227386685347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347320715171273031160925 130245268189227386685347)
              ·
                refine ⟨195367902283841080028021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130245268189227386685347 195367902283841080028021)
                ·
                  refine ⟨18315740839110101252627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195367902283841080028021 18315740839110101252627)
                  ·
                    rfl

theorem cell21_80257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_80257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80257 prefixEnd_80257 := by exact prefixLift 80257
  have htrace : WordTrace (prefixWord ++ tailWord_80257) baseStart_80257 baseEnd_80257 := by
    simpa [prefixWord, tailWord_80257, baseEnd_80257] using wordTrace_append hprefix tailTrace_80257
  have hstable : (prefixWord ++ tailWord_80257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80257).length < 2 ^ (prefixWord ++ tailWord_80257).sum := by decide
  have hdescent : baseEnd_80257 < baseStart_80257 := by decide
  rcases family_descends (prefixWord ++ tailWord_80257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80308 : List Nat := [2, 5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_80308 : Nat := 118140960795 + 80308 * 2 ^ 59
def prefixEnd_80308 : Nat := 4983230072969 + 3 ^ 40 * 80308 * 2
def baseEnd_80308 : Nat := 18327379733945345902523

theorem tailTrace_80308 : CollatzResearch.WordTrace tailWord_80308 prefixEnd_80308 18327379733945345902523 := by
  unfold tailWord_80308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464536696532653179780789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1952715595376870906374385 1464536696532653179780789)
  ·
    refine ⟨137300315299936235604449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1464536696532653179780789 137300315299936235604449)
    ·
      refine ⟨102975236474952176703337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137300315299936235604449 102975236474952176703337)
      ·
        refine ⟨77231427356214132527503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102975236474952176703337 77231427356214132527503)
        ·
          refine ⟨115847141034321198791255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77231427356214132527503 115847141034321198791255)
          ·
            refine ⟨173770711551481798186883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115847141034321198791255 173770711551481798186883)
            ·
              refine ⟨260656067327222697280325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173770711551481798186883 260656067327222697280325)
              ·
                refine ⟨48873012623854255740061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260656067327222697280325 48873012623854255740061)
                ·
                  refine ⟨18327379733945345902523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48873012623854255740061 18327379733945345902523)
                  ·
                    rfl

theorem cell21_80308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_80308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80308 prefixEnd_80308 := by exact prefixLift 80308
  have htrace : WordTrace (prefixWord ++ tailWord_80308) baseStart_80308 baseEnd_80308 := by
    simpa [prefixWord, tailWord_80308, baseEnd_80308] using wordTrace_append hprefix tailTrace_80308
  have hstable : (prefixWord ++ tailWord_80308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80308).length < 2 ^ (prefixWord ++ tailWord_80308).sum := by decide
  have hdescent : baseEnd_80308 < baseStart_80308 := by decide
  rcases family_descends (prefixWord ++ tailWord_80308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80437 : List Nat := [1, 3, 3, 1, 1, 2, 4, 6]
def baseStart_80437 : Nat := 118140960795 + 80437 * 2 ^ 59
def prefixEnd_80437 : Nat := 4983230072969 + 3 ^ 40 * 80437 * 2
def baseEnd_80437 : Nat := 6118939763823262750753

theorem tailTrace_80437 : CollatzResearch.WordTrace tailWord_80437 prefixEnd_80437 6118939763823262750753 := by
  unfold tailWord_80437
  simp only [CollatzResearch.WordTrace]
  refine ⟨2933778409597961391007565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1955852273065307594005043 2933778409597961391007565)
  ·
    refine ⟨1100166903599235521627837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2933778409597961391007565 1100166903599235521627837)
    ·
      refine ⟨412562588849713320610439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1100166903599235521627837 412562588849713320610439)
      ·
        refine ⟨618843883274569980915659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412562588849713320610439 618843883274569980915659)
        ·
          refine ⟨928265824911854971373489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 618843883274569980915659 928265824911854971373489)
          ·
            refine ⟨696199368683891228530117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 928265824911854971373489 696199368683891228530117)
            ·
              refine ⟨130537381628229605349397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 696199368683891228530117 130537381628229605349397)
              ·
                refine ⟨6118939763823262750753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130537381628229605349397 6118939763823262750753)
                ·
                  rfl

theorem cell21_80437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 6].length) (baseStart_80437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80437 prefixEnd_80437 := by exact prefixLift 80437
  have htrace : WordTrace (prefixWord ++ tailWord_80437) baseStart_80437 baseEnd_80437 := by
    simpa [prefixWord, tailWord_80437, baseEnd_80437] using wordTrace_append hprefix tailTrace_80437
  have hstable : (prefixWord ++ tailWord_80437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80437).length < 2 ^ (prefixWord ++ tailWord_80437).sum := by decide
  have hdescent : baseEnd_80437 < baseStart_80437 := by decide
  rcases family_descends (prefixWord ++ tailWord_80437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80451 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 5]
def baseStart_80451 : Nat := 118140960795 + 80451 * 2 ^ 59
def prefixEnd_80451 : Nat := 4983230072969 + 3 ^ 40 * 80451 * 2
def baseEnd_80451 : Nat := 18360014282208875018897

theorem tailTrace_80451 : CollatzResearch.WordTrace tailWord_80451 prefixEnd_80451 18360014282208875018897 := by
  unfold tailWord_80451
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934289031547241782017207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1956192687698161188011471 2934289031547241782017207)
  ·
    refine ⟨4401433547320862673025811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934289031547241782017207 4401433547320862673025811)
    ·
      refine ⟨6602150320981294009538717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4401433547320862673025811 6602150320981294009538717)
      ·
        refine ⟨2475806370367985253577019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6602150320981294009538717 2475806370367985253577019)
        ·
          refine ⟨3713709555551977880365529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2475806370367985253577019 3713709555551977880365529)
          ·
            refine ⟨2785282166663983410274147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3713709555551977880365529 2785282166663983410274147)
            ·
              refine ⟨4177923249995975115411221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2785282166663983410274147 4177923249995975115411221)
              ·
                refine ⟨195840152343561333534901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4177923249995975115411221 195840152343561333534901)
                ·
                  refine ⟨18360014282208875018897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195840152343561333534901 18360014282208875018897)
                  ·
                    rfl

theorem cell21_80451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_80451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80451 prefixEnd_80451 := by exact prefixLift 80451
  have htrace : WordTrace (prefixWord ++ tailWord_80451) baseStart_80451 baseEnd_80451 := by
    simpa [prefixWord, tailWord_80451, baseEnd_80451] using wordTrace_append hprefix tailTrace_80451
  have hstable : (prefixWord ++ tailWord_80451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80451).length < 2 ^ (prefixWord ++ tailWord_80451).sum := by decide
  have hdescent : baseEnd_80451 < baseStart_80451 := by decide
  rcases family_descends (prefixWord ++ tailWord_80451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80648 : List Nat := [2, 1, 3, 2, 2, 11]
def baseStart_80648 : Nat := 118140960795 + 80648 * 2 ^ 59
def prefixEnd_80648 : Nat := 4983230072969 + 3 ^ 40 * 80648 * 2
def baseEnd_80648 : Nat := 681665643191863342043

theorem tailTrace_80648 : CollatzResearch.WordTrace tailWord_80648 prefixEnd_80648 681665643191863342043 := by
  unfold tailWord_80648
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470737105916772213469299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1960982807889029617959065 1470737105916772213469299)
  ·
    refine ⟨2206105658875158320203949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470737105916772213469299 2206105658875158320203949)
    ·
      refine ⟨827289622078184370076481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2206105658875158320203949 827289622078184370076481)
      ·
        refine ⟨620467216558638277557361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827289622078184370076481 620467216558638277557361)
        ·
          refine ⟨465350412418978708168021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620467216558638277557361 465350412418978708168021)
          ·
            refine ⟨681665643191863342043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 465350412418978708168021 681665643191863342043)
            ·
              rfl

theorem cell21_80648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 11].length) (baseStart_80648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80648 prefixEnd_80648 := by exact prefixLift 80648
  have htrace : WordTrace (prefixWord ++ tailWord_80648) baseStart_80648 baseEnd_80648 := by
    simpa [prefixWord, tailWord_80648, baseEnd_80648] using wordTrace_append hprefix tailTrace_80648
  have hstable : (prefixWord ++ tailWord_80648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80648).length < 2 ^ (prefixWord ++ tailWord_80648).sum := by decide
  have hdescent : baseEnd_80648 < baseStart_80648 := by decide
  rcases family_descends (prefixWord ++ tailWord_80648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80741 : List Nat := [1, 3, 1, 3, 1, 1, 6, 5]
def baseStart_80741 : Nat := 118140960795 + 80741 * 2 ^ 59
def prefixEnd_80741 : Nat := 4983230072969 + 3 ^ 40 * 80741 * 2
def baseEnd_80741 : Nat := 6142065411077605061657

theorem tailTrace_80741 : CollatzResearch.WordTrace tailWord_80741 prefixEnd_80741 6142065411077605061657 := by
  unfold tailWord_80741
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944866200496621310074077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1963244133664414206716051 2944866200496621310074077)
  ·
    refine ⟨1104324825186232991277779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2944866200496621310074077 1104324825186232991277779)
    ·
      refine ⟨1656487237779349486916669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1104324825186232991277779 1656487237779349486916669)
      ·
        refine ⟨621182714167256057593751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1656487237779349486916669 621182714167256057593751)
        ·
          refine ⟨931774071250884086390627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621182714167256057593751 931774071250884086390627)
          ·
            refine ⟨1397661106876326129585941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931774071250884086390627 1397661106876326129585941)
            ·
              refine ⟨65515364384827787324341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1397661106876326129585941 65515364384827787324341)
              ·
                refine ⟨6142065411077605061657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65515364384827787324341 6142065411077605061657)
                ·
                  rfl

theorem cell21_80741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 5].length) (baseStart_80741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80741 prefixEnd_80741 := by exact prefixLift 80741
  have htrace : WordTrace (prefixWord ++ tailWord_80741) baseStart_80741 baseEnd_80741 := by
    simpa [prefixWord, tailWord_80741, baseEnd_80741] using wordTrace_append hprefix tailTrace_80741
  have hstable : (prefixWord ++ tailWord_80741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80741).length < 2 ^ (prefixWord ++ tailWord_80741).sum := by decide
  have hdescent : baseEnd_80741 < baseStart_80741 := by decide
  rcases family_descends (prefixWord ++ tailWord_80741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80758 : List Nat := [5, 1, 1, 3, 1, 3, 7]
def baseStart_80758 : Nat := 118140960795 + 80758 * 2 ^ 59
def prefixEnd_80758 : Nat := 4983230072969 + 3 ^ 40 * 80758 * 2
def baseEnd_80758 : Nat := 2047786207204951489067

theorem tailTrace_80758 : CollatzResearch.WordTrace tailWord_80758 prefixEnd_80758 2047786207204951489067 := by
  unfold tailWord_80758
  simp only [CollatzResearch.WordTrace]
  refine ⟨184092890089689575840183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1963657494290022142295285 184092890089689575840183)
  ·
    refine ⟨276139335134534363760275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184092890089689575840183 276139335134534363760275)
    ·
      refine ⟨414209002701801545640413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276139335134534363760275 414209002701801545640413)
      ·
        refine ⟨155328376013175579615155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 414209002701801545640413 155328376013175579615155)
        ·
          refine ⟨232992564019763369422733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155328376013175579615155 232992564019763369422733)
          ·
            refine ⟨87372211507411263533525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232992564019763369422733 87372211507411263533525)
            ·
              refine ⟨2047786207204951489067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 87372211507411263533525 2047786207204951489067)
              ·
                rfl

theorem cell21_80758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 7].length) (baseStart_80758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80758 prefixEnd_80758 := by exact prefixLift 80758
  have htrace : WordTrace (prefixWord ++ tailWord_80758) baseStart_80758 baseEnd_80758 := by
    simpa [prefixWord, tailWord_80758, baseEnd_80758] using wordTrace_append hprefix tailTrace_80758
  have hstable : (prefixWord ++ tailWord_80758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80758).length < 2 ^ (prefixWord ++ tailWord_80758).sum := by decide
  have hdescent : baseEnd_80758 < baseStart_80758 := by decide
  rcases family_descends (prefixWord ++ tailWord_80758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80800 : List Nat := [2, 1, 1, 4, 1, 1, 4, 7]
def baseStart_80800 : Nat := 118140960795 + 80800 * 2 ^ 59
def prefixEnd_80800 : Nat := 4983230072969 + 3 ^ 40 * 80800 * 2
def baseEnd_80800 : Nat := 6146553612353941233839

theorem tailTrace_80800 : CollatzResearch.WordTrace tailWord_80800 prefixEnd_80800 6146553612353941233839 := by
  unfold tailWord_80800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473509053641437193235927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1964678738188582924314569 1473509053641437193235927)
  ·
    refine ⟨2210263580462155789853891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473509053641437193235927 2210263580462155789853891)
    ·
      refine ⟨3315395370693233684780837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210263580462155789853891 3315395370693233684780837)
      ·
        refine ⟨621636632004981315896407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3315395370693233684780837 621636632004981315896407)
        ·
          refine ⟨932454948007471973844611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621636632004981315896407 932454948007471973844611)
          ·
            refine ⟨1398682422011207960766917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932454948007471973844611 1398682422011207960766917)
            ·
              refine ⟨262252954127101492643797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1398682422011207960766917 262252954127101492643797)
              ·
                refine ⟨6146553612353941233839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 262252954127101492643797 6146553612353941233839)
                ·
                  rfl

theorem cell21_80800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_80800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80800 prefixEnd_80800 := by exact prefixLift 80800
  have htrace : WordTrace (prefixWord ++ tailWord_80800) baseStart_80800 baseEnd_80800 := by
    simpa [prefixWord, tailWord_80800, baseEnd_80800] using wordTrace_append hprefix tailTrace_80800
  have hstable : (prefixWord ++ tailWord_80800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80800).length < 2 ^ (prefixWord ++ tailWord_80800).sum := by decide
  have hdescent : baseEnd_80800 < baseStart_80800 := by decide
  rcases family_descends (prefixWord ++ tailWord_80800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80817 : List Nat := [1, 2, 2, 4, 4, 8]
def baseStart_80817 : Nat := 118140960795 + 80817 * 2 ^ 59
def prefixEnd_80817 : Nat := 4983230072969 + 3 ^ 40 * 80817 * 2
def baseEnd_80817 : Nat := 683094091432354515487

theorem tailTrace_80817 : CollatzResearch.WordTrace tailWord_80817 prefixEnd_80817 683094091432354515487 := by
  unfold tailWord_80817
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947638148221286289840705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1965092098814190859893803 2947638148221286289840705)
  ·
    refine ⟨2210728611165964717380529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2947638148221286289840705 2210728611165964717380529)
    ·
      refine ⟨1658046458374473538035397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2210728611165964717380529 1658046458374473538035397)
      ·
        refine ⟨310883710945213788381637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1658046458374473538035397 310883710945213788381637)
        ·
          refine ⟨58290695802227585321557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 310883710945213788381637 58290695802227585321557)
          ·
            refine ⟨683094091432354515487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 58290695802227585321557 683094091432354515487)
            ·
              rfl

theorem cell21_80817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 8].length) (baseStart_80817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80817 prefixEnd_80817 := by exact prefixLift 80817
  have htrace : WordTrace (prefixWord ++ tailWord_80817) baseStart_80817 baseEnd_80817 := by
    simpa [prefixWord, tailWord_80817, baseEnd_80817] using wordTrace_append hprefix tailTrace_80817
  have hstable : (prefixWord ++ tailWord_80817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80817).length < 2 ^ (prefixWord ++ tailWord_80817).sum := by decide
  have hdescent : baseEnd_80817 < baseStart_80817 := by decide
  rcases family_descends (prefixWord ++ tailWord_80817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80820 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_80820 : Nat := 118140960795 + 80820 * 2 ^ 59
def prefixEnd_80820 : Nat := 4983230072969 + 3 ^ 40 * 80820 * 2
def baseEnd_80820 : Nat := 18444225109546233368143

theorem tailTrace_80820 : CollatzResearch.WordTrace tailWord_80820 prefixEnd_80820 18444225109546233368143 := by
  unfold tailWord_80820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473873783605208901099957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1965165044806945201466609 1473873783605208901099957)
  ·
    refine ⟨138175667212988334478121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1473873783605208901099957 138175667212988334478121)
    ·
      refine ⟨103631750409741250858591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 138175667212988334478121 103631750409741250858591)
      ·
        refine ⟨155447625614611876287887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103631750409741250858591 155447625614611876287887)
        ·
          refine ⟨233171438421917814431831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155447625614611876287887 233171438421917814431831)
          ·
            refine ⟨349757157632876721647747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233171438421917814431831 349757157632876721647747)
            ·
              refine ⟨524635736449315082471621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349757157632876721647747 524635736449315082471621)
              ·
                refine ⟨98369200584246577963429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524635736449315082471621 98369200584246577963429)
                ·
                  refine ⟨18444225109546233368143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98369200584246577963429 18444225109546233368143)
                  ·
                    rfl

theorem cell21_80820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_80820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80820 prefixEnd_80820 := by exact prefixLift 80820
  have htrace : WordTrace (prefixWord ++ tailWord_80820) baseStart_80820 baseEnd_80820 := by
    simpa [prefixWord, tailWord_80820, baseEnd_80820] using wordTrace_append hprefix tailTrace_80820
  have hstable : (prefixWord ++ tailWord_80820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80820).length < 2 ^ (prefixWord ++ tailWord_80820).sum := by decide
  have hdescent : baseEnd_80820 < baseStart_80820 := by decide
  rcases family_descends (prefixWord ++ tailWord_80820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80879 : List Nat := [1, 1, 2, 1, 4, 5, 1, 2, 4]
def baseStart_80879 : Nat := 118140960795 + 80879 * 2 ^ 59
def prefixEnd_80879 : Nat := 4983230072969 + 3 ^ 40 * 80879 * 2
def baseEnd_80879 : Nat := 18457689713375241884689

theorem tailTrace_80879 : CollatzResearch.WordTrace tailWord_80879 prefixEnd_80879 18457689713375241884689 := by
  unfold tailWord_80879
  simp only [CollatzResearch.WordTrace]
  refine ⟨2949899473996670878597691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1966599649331113919065127 2949899473996670878597691)
  ·
    refine ⟨4424849210995006317896537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2949899473996670878597691 4424849210995006317896537)
    ·
      refine ⟨3318636908246254738422403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4424849210995006317896537 3318636908246254738422403)
      ·
        refine ⟨4977955362369382107633605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3318636908246254738422403 4977955362369382107633605)
        ·
          refine ⟨933366630444259145181301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4977955362369382107633605 933366630444259145181301)
          ·
            refine ⟨87503121604149294860747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 933366630444259145181301 87503121604149294860747)
            ·
              refine ⟨131254682406223942291121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87503121604149294860747 131254682406223942291121)
              ·
                refine ⟨98441011804667956718341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131254682406223942291121 98441011804667956718341)
                ·
                  refine ⟨18457689713375241884689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98441011804667956718341 18457689713375241884689)
                  ·
                    rfl

theorem cell21_80879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 2, 4].length) (baseStart_80879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80879 prefixEnd_80879 := by exact prefixLift 80879
  have htrace : WordTrace (prefixWord ++ tailWord_80879) baseStart_80879 baseEnd_80879 := by
    simpa [prefixWord, tailWord_80879, baseEnd_80879] using wordTrace_append hprefix tailTrace_80879
  have hstable : (prefixWord ++ tailWord_80879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80879).length < 2 ^ (prefixWord ++ tailWord_80879).sum := by decide
  have hdescent : baseEnd_80879 < baseStart_80879 := by decide
  rcases family_descends (prefixWord ++ tailWord_80879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80907 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 5]
def baseStart_80907 : Nat := 118140960795 + 80907 * 2 ^ 59
def prefixEnd_80907 : Nat := 4983230072969 + 3 ^ 40 * 80907 * 2
def baseEnd_80907 : Nat := 18464079694853415417965

theorem tailTrace_80907 : CollatzResearch.WordTrace tailWord_80907 prefixEnd_80907 18464079694853415417965 := by
  unfold tailWord_80907
  simp only [CollatzResearch.WordTrace]
  refine ⟨2950920717895231660616975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1967280478596821107077983 2950920717895231660616975)
  ·
    refine ⟨4426381076842847490925463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2950920717895231660616975 4426381076842847490925463)
    ·
      refine ⟨6639571615264271236388195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4426381076842847490925463 6639571615264271236388195)
      ·
        refine ⟨9959357422896406854582293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6639571615264271236388195 9959357422896406854582293)
        ·
          refine ⟨466844879198269071308545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9959357422896406854582293 466844879198269071308545)
          ·
            refine ⟨350133659398701803481409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 466844879198269071308545 350133659398701803481409)
            ·
              refine ⟨262600244549026352611057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 350133659398701803481409 262600244549026352611057)
              ·
                refine ⟨196950183411769764458293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262600244549026352611057 196950183411769764458293)
                ·
                  refine ⟨18464079694853415417965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 196950183411769764458293 18464079694853415417965)
                  ·
                    rfl

theorem cell21_80907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_80907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80907 prefixEnd_80907 := by exact prefixLift 80907
  have htrace : WordTrace (prefixWord ++ tailWord_80907) baseStart_80907 baseEnd_80907 := by
    simpa [prefixWord, tailWord_80907, baseEnd_80907] using wordTrace_append hprefix tailTrace_80907
  have hstable : (prefixWord ++ tailWord_80907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80907).length < 2 ^ (prefixWord ++ tailWord_80907).sum := by decide
  have hdescent : baseEnd_80907 < baseStart_80907 := by decide
  rcases family_descends (prefixWord ++ tailWord_80907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80910 : List Nat := [4, 1, 1, 2, 2, 4, 2, 5]
def baseStart_80910 : Nat := 118140960795 + 80910 * 2 ^ 59
def prefixEnd_80910 : Nat := 4983230072969 + 3 ^ 40 * 80910 * 2
def baseEnd_80910 : Nat := 6154921445242025622653

theorem tailTrace_80910 : CollatzResearch.WordTrace tailWord_80910 prefixEnd_80910 6154921445242025622653 := by
  unfold tailWord_80910
  simp only [CollatzResearch.WordTrace]
  refine ⟨368878767110545396622023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1967353424589575448650789 368878767110545396622023)
  ·
    refine ⟨553318150665818094933035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 368878767110545396622023 553318150665818094933035)
    ·
      refine ⟨829977225998727142399553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553318150665818094933035 829977225998727142399553)
      ·
        refine ⟨622482919499045356799665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 829977225998727142399553 622482919499045356799665)
        ·
          refine ⟨466862189624284017599749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622482919499045356799665 466862189624284017599749)
          ·
            refine ⟨87536660554553253299953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 466862189624284017599749 87536660554553253299953)
            ·
              refine ⟨65652495415914939974965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87536660554553253299953 65652495415914939974965)
              ·
                refine ⟨6154921445242025622653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65652495415914939974965 6154921445242025622653)
                ·
                  rfl

theorem cell21_80910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_80910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80910 prefixEnd_80910 := by exact prefixLift 80910
  have htrace : WordTrace (prefixWord ++ tailWord_80910) baseStart_80910 baseEnd_80910 := by
    simpa [prefixWord, tailWord_80910, baseEnd_80910] using wordTrace_append hprefix tailTrace_80910
  have hstable : (prefixWord ++ tailWord_80910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80910).length < 2 ^ (prefixWord ++ tailWord_80910).sum := by decide
  have hdescent : baseEnd_80910 < baseStart_80910 := by decide
  rcases family_descends (prefixWord ++ tailWord_80910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80921 : List Nat := [1, 2, 1, 2, 1, 1, 5, 2, 6]
def baseStart_80921 : Nat := 118140960795 + 80921 * 2 ^ 59
def prefixEnd_80921 : Nat := 4983230072969 + 3 ^ 40 * 80921 * 2
def baseEnd_80921 : Nat := 18467274685592502184603

theorem tailTrace_80921 : CollatzResearch.WordTrace tailWord_80921 prefixEnd_80921 18467274685592502184603 := by
  unfold tailWord_80921
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951431339844512051626617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1967620893229674701084411 2951431339844512051626617)
  ·
    refine ⟨2213573504883384038719963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2951431339844512051626617 2213573504883384038719963)
    ·
      refine ⟨3320360257325076058079945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2213573504883384038719963 3320360257325076058079945)
      ·
        refine ⟨2490270192993807043559959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3320360257325076058079945 2490270192993807043559959)
        ·
          refine ⟨3735405289490710565339939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490270192993807043559959 3735405289490710565339939)
          ·
            refine ⟨5603107934236065848009909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3735405289490710565339939 5603107934236065848009909)
            ·
              refine ⟨525291368834631173250929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5603107934236065848009909 525291368834631173250929)
              ·
                refine ⟨393968526625973379938197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525291368834631173250929 393968526625973379938197)
                ·
                  refine ⟨18467274685592502184603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 393968526625973379938197 18467274685592502184603)
                  ·
                    rfl

theorem cell21_80921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_80921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80921 prefixEnd_80921 := by exact prefixLift 80921
  have htrace : WordTrace (prefixWord ++ tailWord_80921) baseStart_80921 baseEnd_80921 := by
    simpa [prefixWord, tailWord_80921, baseEnd_80921] using wordTrace_append hprefix tailTrace_80921
  have hstable : (prefixWord ++ tailWord_80921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80921).length < 2 ^ (prefixWord ++ tailWord_80921).sum := by decide
  have hdescent : baseEnd_80921 < baseStart_80921 := by decide
  rcases family_descends (prefixWord ++ tailWord_80921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80952 : List Nat := [2, 1, 2, 1, 5, 1, 1, 8]
def baseStart_80952 : Nat := 118140960795 + 80952 * 2 ^ 59
def prefixEnd_80952 : Nat := 4983230072969 + 3 ^ 40 * 80952 * 2
def baseEnd_80952 : Nat := 6158116435981112389291

theorem tailTrace_80952 : CollatzResearch.WordTrace tailWord_80952 prefixEnd_80952 6158116435981112389291 := by
  unfold tailWord_80952
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476281001366102173002555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968374668488136230670073 1476281001366102173002555)
  ·
    refine ⟨2214421502049153259503833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476281001366102173002555 2214421502049153259503833)
    ·
      refine ⟨1660816126536864944627875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214421502049153259503833 1660816126536864944627875)
      ·
        refine ⟨2491224189805297416941813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660816126536864944627875 2491224189805297416941813)
        ·
          refine ⟨233552267794246632838295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2491224189805297416941813 233552267794246632838295)
          ·
            refine ⟨350328401691369949257443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233552267794246632838295 350328401691369949257443)
            ·
              refine ⟨525492602537054923886165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350328401691369949257443 525492602537054923886165)
              ·
                refine ⟨6158116435981112389291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 525492602537054923886165 6158116435981112389291)
                ·
                  rfl

theorem cell21_80952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_80952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_80952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_80952 prefixEnd_80952 := by exact prefixLift 80952
  have htrace : WordTrace (prefixWord ++ tailWord_80952) baseStart_80952 baseEnd_80952 := by
    simpa [prefixWord, tailWord_80952, baseEnd_80952] using wordTrace_append hprefix tailTrace_80952
  have hstable : (prefixWord ++ tailWord_80952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80952).length < 2 ^ (prefixWord ++ tailWord_80952).sum := by decide
  have hdescent : baseEnd_80952 < baseStart_80952 := by decide
  rcases family_descends (prefixWord ++ tailWord_80952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81110 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_81110 : Nat := 118140960795 + 81110 * 2 ^ 59
def prefixEnd_81110 : Nat := 4983230072969 + 3 ^ 40 * 81110 * 2
def baseEnd_81110 : Nat := 18510407060570173534217

theorem tailTrace_81110 : CollatzResearch.WordTrace tailWord_81110 prefixEnd_81110 18510407060570173534217 := by
  unfold tailWord_81110
  simp only [CollatzResearch.WordTrace]
  refine ⟨184895296009987333141049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1972216490773198220171189 184895296009987333141049)
  ·
    refine ⟨138671472007490499855787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 184895296009987333141049 138671472007490499855787)
    ·
      refine ⟨208007208011235749783681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138671472007490499855787 208007208011235749783681)
      ·
        refine ⟨156005406008426812337761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208007208011235749783681 156005406008426812337761)
        ·
          refine ⟨117004054506320109253321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156005406008426812337761 117004054506320109253321)
          ·
            refine ⟨87753040879740081939991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117004054506320109253321 87753040879740081939991)
            ·
              refine ⟨131629561319610122909987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87753040879740081939991 131629561319610122909987)
              ·
                refine ⟨197444341979415184364981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131629561319610122909987 197444341979415184364981)
                ·
                  refine ⟨18510407060570173534217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197444341979415184364981 18510407060570173534217)
                  ·
                    rfl

theorem cell21_81110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_81110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81110 prefixEnd_81110 := by exact prefixLift 81110
  have htrace : WordTrace (prefixWord ++ tailWord_81110) baseStart_81110 baseEnd_81110 := by
    simpa [prefixWord, tailWord_81110, baseEnd_81110] using wordTrace_append hprefix tailTrace_81110
  have hstable : (prefixWord ++ tailWord_81110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81110).length < 2 ^ (prefixWord ++ tailWord_81110).sum := by decide
  have hdescent : baseEnd_81110 < baseStart_81110 := by decide
  rcases family_descends (prefixWord ++ tailWord_81110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81163 : List Nat := [1, 1, 1, 1, 5, 12]
def baseStart_81163 : Nat := 118140960795 + 81163 * 2 ^ 59
def prefixEnd_81163 : Nat := 4983230072969 + 3 ^ 40 * 81163 * 2
def baseEnd_81163 : Nat := 686018606764957746325

theorem tailTrace_81163 : CollatzResearch.WordTrace tailWord_81163 prefixEnd_81163 686018606764957746325 := by
  unfold tailWord_81163
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960257804967787381936143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1973505203311858254624095 2960257804967787381936143)
  ·
    refine ⟨4440386707451681072904215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2960257804967787381936143 4440386707451681072904215)
    ·
      refine ⟨6660580061177521609356323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440386707451681072904215 6660580061177521609356323)
      ·
        refine ⟨9990870091766282414034485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6660580061177521609356323 9990870091766282414034485)
        ·
          refine ⟨936644071103088976315733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9990870091766282414034485 936644071103088976315733)
          ·
            refine ⟨686018606764957746325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 936644071103088976315733 686018606764957746325)
            ·
              rfl

theorem cell21_81163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 12].length) (baseStart_81163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81163 prefixEnd_81163 := by exact prefixLift 81163
  have htrace : WordTrace (prefixWord ++ tailWord_81163) baseStart_81163 baseEnd_81163 := by
    simpa [prefixWord, tailWord_81163, baseEnd_81163] using wordTrace_append hprefix tailTrace_81163
  have hstable : (prefixWord ++ tailWord_81163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81163).length < 2 ^ (prefixWord ++ tailWord_81163).sum := by decide
  have hdescent : baseEnd_81163 < baseStart_81163 := by decide
  rcases family_descends (prefixWord ++ tailWord_81163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81166 : List Nat := [4, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_81166 : Nat := 118140960795 + 81166 * 2 ^ 59
def prefixEnd_81166 : Nat := 4983230072969 + 3 ^ 40 * 81166 * 2
def baseEnd_81166 : Nat := 18523187023526520600769

theorem tailTrace_81166 : CollatzResearch.WordTrace tailWord_81166 prefixEnd_81166 18523187023526520600769 := by
  unfold tailWord_81166
  simp only [CollatzResearch.WordTrace]
  refine ⟨370045902994614861786919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1973578149304612596196901 370045902994614861786919)
  ·
    refine ⟨555068854491922292680379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370045902994614861786919 555068854491922292680379)
    ·
      refine ⟨832603281737883439020569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555068854491922292680379 832603281737883439020569)
      ·
        refine ⟨624452461303412579265427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 832603281737883439020569 624452461303412579265427)
        ·
          refine ⟨936678691955118868898141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624452461303412579265427 936678691955118868898141)
          ·
            refine ⟨351254509483169575836803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 936678691955118868898141 351254509483169575836803)
            ·
              refine ⟨526881764224754363755205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351254509483169575836803 526881764224754363755205)
              ·
                refine ⟨98790330792141443204101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 526881764224754363755205 98790330792141443204101)
                ·
                  refine ⟨18523187023526520600769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 98790330792141443204101 18523187023526520600769)
                  ·
                    rfl

theorem cell21_81166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_81166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81166 prefixEnd_81166 := by exact prefixLift 81166
  have htrace : WordTrace (prefixWord ++ tailWord_81166) baseStart_81166 baseEnd_81166 := by
    simpa [prefixWord, tailWord_81166, baseEnd_81166] using wordTrace_append hprefix tailTrace_81166
  have hstable : (prefixWord ++ tailWord_81166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81166).length < 2 ^ (prefixWord ++ tailWord_81166).sum := by decide
  have hdescent : baseEnd_81166 < baseStart_81166 := by decide
  rcases family_descends (prefixWord ++ tailWord_81166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81180 : List Nat := [2, 2, 3, 1, 1, 1, 5, 6]
def baseStart_81180 : Nat := 118140960795 + 81180 * 2 ^ 59
def prefixEnd_81180 : Nat := 4983230072969 + 3 ^ 40 * 81180 * 2
def baseEnd_81180 : Nat := 6175460671421869122469

theorem tailTrace_81180 : CollatzResearch.WordTrace tailWord_81180 prefixEnd_81180 6175460671421869122469 := by
  unfold tailWord_81180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480438922953099642652497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1973918563937466190203329 1480438922953099642652497)
  ·
    refine ⟨1110329192214824731989373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1480438922953099642652497 1110329192214824731989373)
    ·
      refine ⟨416373447080559274496015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1110329192214824731989373 416373447080559274496015)
      ·
        refine ⟨624560170620838911744023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416373447080559274496015 624560170620838911744023)
        ·
          refine ⟨936840255931258367616035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624560170620838911744023 936840255931258367616035)
          ·
            refine ⟨1405260383896887551424053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936840255931258367616035 1405260383896887551424053)
            ·
              refine ⟨131743160990333207946005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1405260383896887551424053 131743160990333207946005)
              ·
                refine ⟨6175460671421869122469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 131743160990333207946005 6175460671421869122469)
                ·
                  rfl

theorem cell21_81180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_81180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81180 prefixEnd_81180 := by exact prefixLift 81180
  have htrace : WordTrace (prefixWord ++ tailWord_81180) baseStart_81180 baseEnd_81180 := by
    simpa [prefixWord, tailWord_81180, baseEnd_81180] using wordTrace_append hprefix tailTrace_81180
  have hstable : (prefixWord ++ tailWord_81180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81180).length < 2 ^ (prefixWord ++ tailWord_81180).sum := by decide
  have hdescent : baseEnd_81180 < baseStart_81180 := by decide
  rcases family_descends (prefixWord ++ tailWord_81180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81228 : List Nat := [2, 2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_81228 : Nat := 118140960795 + 81228 * 2 ^ 59
def prefixEnd_81228 : Nat := 4983230072969 + 3 ^ 40 * 81228 * 2
def baseEnd_81228 : Nat := 18537336268228190567309

theorem tailTrace_81228 : CollatzResearch.WordTrace tailWord_81228 prefixEnd_81228 18537336268228190567309 := by
  unfold tailWord_81228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481314274866151741526169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1975085699821535655368225 1481314274866151741526169)
  ·
    refine ⟨1110985706149613806144627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1481314274866151741526169 1110985706149613806144627)
    ·
      refine ⟨1666478559224420709216941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110985706149613806144627 1666478559224420709216941)
      ·
        refine ⟨624929459709157765956353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1666478559224420709216941 624929459709157765956353)
        ·
          refine ⟨468697094781868324467265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624929459709157765956353 468697094781868324467265)
          ·
            refine ⟨351522821086401243350449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468697094781868324467265 351522821086401243350449)
            ·
              refine ⟨263642115814800932512837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351522821086401243350449 263642115814800932512837)
              ·
                refine ⟨49432896715275174846157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 263642115814800932512837 49432896715275174846157)
                ·
                  refine ⟨18537336268228190567309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49432896715275174846157 18537336268228190567309)
                  ·
                    rfl

theorem cell21_81228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_81228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81228 prefixEnd_81228 := by exact prefixLift 81228
  have htrace : WordTrace (prefixWord ++ tailWord_81228) baseStart_81228 baseEnd_81228 := by
    simpa [prefixWord, tailWord_81228, baseEnd_81228] using wordTrace_append hprefix tailTrace_81228
  have hstable : (prefixWord ++ tailWord_81228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81228).length < 2 ^ (prefixWord ++ tailWord_81228).sum := by decide
  have hdescent : baseEnd_81228 < baseStart_81228 := by decide
  rcases family_descends (prefixWord ++ tailWord_81228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81287 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 5]
def baseStart_81287 : Nat := 118140960795 + 81287 * 2 ^ 59
def prefixEnd_81287 : Nat := 4983230072969 + 3 ^ 40 * 81287 * 2
def baseEnd_81287 : Nat := 18550800872057199083855

theorem tailTrace_81287 : CollatzResearch.WordTrace tailWord_81287 prefixEnd_81287 18550800872057199083855 := by
  unfold tailWord_81287
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964780456518556559450115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1976520304345704372966743 2964780456518556559450115)
  ·
    refine ⟨4447170684777834839175173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2964780456518556559450115 4447170684777834839175173)
    ·
      refine ⟨833844503395844032345345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4447170684777834839175173 833844503395844032345345)
      ·
        refine ⟨625383377546883024259009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 833844503395844032345345 625383377546883024259009)
        ·
          refine ⟨469037533160162268194257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625383377546883024259009 469037533160162268194257)
          ·
            refine ⟨351778149870121701145693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469037533160162268194257 351778149870121701145693)
            ·
              refine ⟨131916806201295637929635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351778149870121701145693 131916806201295637929635)
              ·
                refine ⟨197875209301943456894453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131916806201295637929635 197875209301943456894453)
                ·
                  refine ⟨18550800872057199083855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 197875209301943456894453 18550800872057199083855)
                  ·
                    rfl

theorem cell21_81287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_81287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81287 prefixEnd_81287 := by exact prefixLift 81287
  have htrace : WordTrace (prefixWord ++ tailWord_81287) baseStart_81287 baseEnd_81287 := by
    simpa [prefixWord, tailWord_81287, baseEnd_81287] using wordTrace_append hprefix tailTrace_81287
  have hstable : (prefixWord ++ tailWord_81287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81287).length < 2 ^ (prefixWord ++ tailWord_81287).sum := by decide
  have hdescent : baseEnd_81287 < baseStart_81287 := by decide
  rcases family_descends (prefixWord ++ tailWord_81287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81315 : List Nat := [1, 1, 1, 4, 1, 3, 1, 9]
def baseStart_81315 : Nat := 118140960795 + 81315 * 2 ^ 59
def prefixEnd_81315 : Nat := 4983230072969 + 3 ^ 40 * 81315 * 2
def baseEnd_81315 : Nat := 6185730284511790872377

theorem tailTrace_81315 : CollatzResearch.WordTrace tailWord_81315 prefixEnd_81315 6185730284511790872377 := by
  unfold tailWord_81315
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965801700417117341469399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1977201133611411560979599 2965801700417117341469399)
  ·
    refine ⟨4448702550625676012204099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965801700417117341469399 4448702550625676012204099)
    ·
      refine ⟨6673053825938514018306149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448702550625676012204099 6673053825938514018306149)
      ·
        refine ⟨1251197592363471378432403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6673053825938514018306149 1251197592363471378432403)
        ·
          refine ⟨1876796388545207067648605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251197592363471378432403 1876796388545207067648605)
          ·
            refine ⟨703798645704452650368227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1876796388545207067648605 703798645704452650368227)
            ·
              refine ⟨1055697968556678975552341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703798645704452650368227 1055697968556678975552341)
              ·
                refine ⟨6185730284511790872377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1055697968556678975552341 6185730284511790872377)
                ·
                  rfl

theorem cell21_81315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 9].length) (baseStart_81315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81315 prefixEnd_81315 := by exact prefixLift 81315
  have htrace : WordTrace (prefixWord ++ tailWord_81315) baseStart_81315 baseEnd_81315 := by
    simpa [prefixWord, tailWord_81315, baseEnd_81315] using wordTrace_append hprefix tailTrace_81315
  have hstable : (prefixWord ++ tailWord_81315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81315).length < 2 ^ (prefixWord ++ tailWord_81315).sum := by decide
  have hdescent : baseEnd_81315 < baseStart_81315 := by decide
  rcases family_descends (prefixWord ++ tailWord_81315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81332 : List Nat := [2, 5, 2, 12]
def baseStart_81332 : Nat := 118140960795 + 81332 * 2 ^ 59
def prefixEnd_81332 : Nat := 4983230072969 + 3 ^ 40 * 81332 * 2
def baseEnd_81332 : Nat := 76383006111716546641

theorem tailTrace_81332 : CollatzResearch.WordTrace tailWord_81332 prefixEnd_81332 76383006111716546641 := by
  unfold tailWord_81332
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483210870677764622419125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1977614494237019496558833 1483210870677764622419125)
  ·
    refine ⟨139051019126040433351793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1483210870677764622419125 139051019126040433351793)
    ·
      refine ⟨104288264344530325013845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139051019126040433351793 104288264344530325013845)
      ·
        refine ⟨76383006111716546641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 104288264344530325013845 76383006111716546641)
        ·
          rfl

theorem cell21_81332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 12].length) (baseStart_81332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81332 prefixEnd_81332 := by exact prefixLift 81332
  have htrace : WordTrace (prefixWord ++ tailWord_81332) baseStart_81332 baseEnd_81332 := by
    simpa [prefixWord, tailWord_81332, baseEnd_81332] using wordTrace_append hprefix tailTrace_81332
  have hstable : (prefixWord ++ tailWord_81332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81332).length < 2 ^ (prefixWord ++ tailWord_81332).sum := by decide
  have hdescent : baseEnd_81332 < baseStart_81332 := by decide
  rcases family_descends (prefixWord ++ tailWord_81332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81366 : List Nat := [5, 2, 1, 1, 1, 3, 3, 5]
def baseStart_81366 : Nat := 118140960795 + 81366 * 2 ^ 59
def prefixEnd_81366 : Nat := 4983230072969 + 3 ^ 40 * 81366 * 2
def baseEnd_81366 : Nat := 6189609916123539089009

theorem tailTrace_81366 : CollatzResearch.WordTrace tailWord_81366 prefixEnd_81366 6189609916123539089009 := by
  unfold tailWord_81366
  simp only [CollatzResearch.WordTrace]
  refine ⟨185478863952022065723497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1978441215488235367717301 185478863952022065723497)
  ·
    refine ⟨139109147964016549292623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 185478863952022065723497 139109147964016549292623)
    ·
      refine ⟨208663721946024823938935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139109147964016549292623 208663721946024823938935)
      ·
        refine ⟨312995582919037235908403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208663721946024823938935 312995582919037235908403)
        ·
          refine ⟨469493374378555853862605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312995582919037235908403 469493374378555853862605)
          ·
            refine ⟨176060015391958445198477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 469493374378555853862605 176060015391958445198477)
            ·
              refine ⟨66022505771984416949429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176060015391958445198477 66022505771984416949429)
              ·
                refine ⟨6189609916123539089009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66022505771984416949429 6189609916123539089009)
                ·
                  rfl

theorem cell21_81366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_81366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81366 prefixEnd_81366 := by exact prefixLift 81366
  have htrace : WordTrace (prefixWord ++ tailWord_81366) baseStart_81366 baseEnd_81366 := by
    simpa [prefixWord, tailWord_81366, baseEnd_81366] using wordTrace_append hprefix tailTrace_81366
  have hstable : (prefixWord ++ tailWord_81366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81366).length < 2 ^ (prefixWord ++ tailWord_81366).sum := by decide
  have hdescent : baseEnd_81366 < baseStart_81366 := by decide
  rcases family_descends (prefixWord ++ tailWord_81366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81394 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_81394 : Nat := 118140960795 + 81394 * 2 ^ 59
def prefixEnd_81394 : Nat := 4983230072969 + 3 ^ 40 * 81394 * 2
def baseEnd_81394 : Nat := 18575219729848790800303

theorem tailTrace_81394 : CollatzResearch.WordTrace tailWord_81394 prefixEnd_81394 18575219729848790800303 := by
  unfold tailWord_81394
  simp only [CollatzResearch.WordTrace]
  refine ⟨742170766782728458398809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1979122044753942555730157 742170766782728458398809)
  ·
    refine ⟨556628075087046343799107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 742170766782728458398809 556628075087046343799107)
    ·
      refine ⟨834942112630569515698661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556628075087046343799107 834942112630569515698661)
      ·
        refine ⟨156551646118231784193499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 834942112630569515698661 156551646118231784193499)
        ·
          refine ⟨234827469177347676290249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156551646118231784193499 234827469177347676290249)
          ·
            refine ⟨176120601883010757217687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234827469177347676290249 176120601883010757217687)
            ·
              refine ⟨264180902824516135826531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176120601883010757217687 264180902824516135826531)
              ·
                refine ⟨396271354236774203739797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264180902824516135826531 396271354236774203739797)
                ·
                  refine ⟨18575219729848790800303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 396271354236774203739797 18575219729848790800303)
                  ·
                    rfl

theorem cell21_81394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_81394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81394 prefixEnd_81394 := by exact prefixLift 81394
  have htrace : WordTrace (prefixWord ++ tailWord_81394) baseStart_81394 baseEnd_81394 := by
    simpa [prefixWord, tailWord_81394, baseEnd_81394] using wordTrace_append hprefix tailTrace_81394
  have hstable : (prefixWord ++ tailWord_81394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81394).length < 2 ^ (prefixWord ++ tailWord_81394).sum := by decide
  have hdescent : baseEnd_81394 < baseStart_81394 := by decide
  rcases family_descends (prefixWord ++ tailWord_81394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81397 : List Nat := [1, 3, 5, 1, 1, 1, 2, 4, 3]
def baseStart_81397 : Nat := 118140960795 + 81397 * 2 ^ 59
def prefixEnd_81397 : Nat := 4983230072969 + 3 ^ 40 * 81397 * 2
def baseEnd_81397 : Nat := 18575904370721452250297

theorem tailTrace_81397 : CollatzResearch.WordTrace tailWord_81397 prefixEnd_81397 18575904370721452250297 := by
  unfold tailWord_81397
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968792486120045345954445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1979194990746696897302963 2968792486120045345954445)
  ·
    refine ⟨1113297182295017004732917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2968792486120045345954445 1113297182295017004732917)
    ·
      refine ⟨104371610840157844193711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1113297182295017004732917 104371610840157844193711)
      ·
        refine ⟨156557416260236766290567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104371610840157844193711 156557416260236766290567)
        ·
          refine ⟨234836124390355149435851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156557416260236766290567 234836124390355149435851)
          ·
            refine ⟨352254186585532724153777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234836124390355149435851 352254186585532724153777)
            ·
              refine ⟨264190639939149543115333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352254186585532724153777 264190639939149543115333)
              ·
                refine ⟨49535744988590539334125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264190639939149543115333 49535744988590539334125)
                ·
                  refine ⟨18575904370721452250297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49535744988590539334125 18575904370721452250297)
                  ·
                    rfl

theorem cell21_81397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_81397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81397 prefixEnd_81397 := by exact prefixLift 81397
  have htrace : WordTrace (prefixWord ++ tailWord_81397) baseStart_81397 baseEnd_81397 := by
    simpa [prefixWord, tailWord_81397, baseEnd_81397] using wordTrace_append hprefix tailTrace_81397
  have hstable : (prefixWord ++ tailWord_81397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81397).length < 2 ^ (prefixWord ++ tailWord_81397).sum := by decide
  have hdescent : baseEnd_81397 < baseStart_81397 := by decide
  rcases family_descends (prefixWord ++ tailWord_81397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81501 : List Nat := [1, 4, 4, 2, 1, 9]
def baseStart_81501 : Nat := 118140960795 + 81501 * 2 ^ 59
def prefixEnd_81501 : Nat := 4983230072969 + 3 ^ 40 * 81501 * 2
def baseEnd_81501 : Nat := 688875503245940093213

theorem tailTrace_81501 : CollatzResearch.WordTrace tailWord_81501 prefixEnd_81501 688875503245940093213 := by
  unfold tailWord_81501
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972585677743271107740357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1981723785162180738493571 2972585677743271107740357)
  ·
    refine ⟨557359814576863332701317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2972585677743271107740357 557359814576863332701317)
    ·
      refine ⟨104504965233161874881497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 557359814576863332701317 104504965233161874881497)
      ·
        refine ⟨78378723924871406161123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104504965233161874881497 78378723924871406161123)
        ·
          refine ⟨117568085887307109241685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78378723924871406161123 117568085887307109241685)
          ·
            refine ⟨688875503245940093213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 117568085887307109241685 688875503245940093213)
            ·
              rfl

theorem cell21_81501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 9].length) (baseStart_81501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81501 prefixEnd_81501 := by exact prefixLift 81501
  have htrace : WordTrace (prefixWord ++ tailWord_81501) baseStart_81501 baseEnd_81501 := by
    simpa [prefixWord, tailWord_81501, baseEnd_81501] using wordTrace_append hprefix tailTrace_81501
  have hstable : (prefixWord ++ tailWord_81501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81501).length < 2 ^ (prefixWord ++ tailWord_81501).sum := by decide
  have hdescent : baseEnd_81501 < baseStart_81501 := by decide
  rcases family_descends (prefixWord ++ tailWord_81501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81518 : List Nat := [4, 1, 2, 2, 4, 1, 1, 6]
def baseStart_81518 : Nat := 118140960795 + 81518 * 2 ^ 59
def prefixEnd_81518 : Nat := 4983230072969 + 3 ^ 40 * 81518 * 2
def baseEnd_81518 : Nat := 6201172739750710244461

theorem tailTrace_81518 : CollatzResearch.WordTrace tailWord_81518 prefixEnd_81518 6201172739750710244461 := by
  unfold tailWord_81518
  simp only [CollatzResearch.WordTrace]
  refine ⟨371650714835210376388651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1982137145787788674072805 371650714835210376388651)
  ·
    refine ⟨557476072252815564582977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 371650714835210376388651 557476072252815564582977)
    ·
      refine ⟨418107054189611673437233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557476072252815564582977 418107054189611673437233)
      ·
        refine ⟨313580290642208755077925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 418107054189611673437233 313580290642208755077925)
        ·
          refine ⟨58796304495414141577111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 313580290642208755077925 58796304495414141577111)
          ·
            refine ⟨88194456743121212365667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58796304495414141577111 88194456743121212365667)
            ·
              refine ⟨132291685114681818548501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88194456743121212365667 132291685114681818548501)
              ·
                refine ⟨6201172739750710244461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132291685114681818548501 6201172739750710244461)
                ·
                  rfl

theorem cell21_81518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_81518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81518 prefixEnd_81518 := by exact prefixLift 81518
  have htrace : WordTrace (prefixWord ++ tailWord_81518) baseStart_81518 baseEnd_81518 := by
    simpa [prefixWord, tailWord_81518, baseEnd_81518] using wordTrace_append hprefix tailTrace_81518
  have hstable : (prefixWord ++ tailWord_81518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81518).length < 2 ^ (prefixWord ++ tailWord_81518).sum := by decide
  have hdescent : baseEnd_81518 < baseStart_81518 := by decide
  rcases family_descends (prefixWord ++ tailWord_81518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81529 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 4]
def baseStart_81529 : Nat := 118140960795 + 81529 * 2 ^ 59
def prefixEnd_81529 : Nat := 4983230072969 + 3 ^ 40 * 81529 * 2
def baseEnd_81529 : Nat := 18606028569118556050027

theorem tailTrace_81529 : CollatzResearch.WordTrace tailWord_81529 prefixEnd_81529 18606028569118556050027 := by
  unfold tailWord_81529
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973606921641831889759641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1982404614427887926506427 2973606921641831889759641)
  ·
    refine ⟨2230205191231373917319731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2973606921641831889759641 2230205191231373917319731)
    ·
      refine ⟨3345307786847060875979597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230205191231373917319731 3345307786847060875979597)
      ·
        refine ⟨1254490420067647828492349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3345307786847060875979597 1254490420067647828492349)
        ·
          refine ⟨470433907525367935684631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1254490420067647828492349 470433907525367935684631)
          ·
            refine ⟨705650861288051903526947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470433907525367935684631 705650861288051903526947)
            ·
              refine ⟨1058476291932077855290421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705650861288051903526947 1058476291932077855290421)
              ·
                refine ⟨99232152368632298933477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1058476291932077855290421 99232152368632298933477)
                ·
                  refine ⟨18606028569118556050027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99232152368632298933477 18606028569118556050027)
                  ·
                    rfl

theorem cell21_81529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_81529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81529 prefixEnd_81529 := by exact prefixLift 81529
  have htrace : WordTrace (prefixWord ++ tailWord_81529) baseStart_81529 baseEnd_81529 := by
    simpa [prefixWord, tailWord_81529, baseEnd_81529] using wordTrace_append hprefix tailTrace_81529
  have hstable : (prefixWord ++ tailWord_81529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81529).length < 2 ^ (prefixWord ++ tailWord_81529).sum := by decide
  have hdescent : baseEnd_81529 < baseStart_81529 := by decide
  rcases family_descends (prefixWord ++ tailWord_81529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81639 : List Nat := [1, 1, 5, 4, 1, 1, 1, 3, 4]
def baseStart_81639 : Nat := 118140960795 + 81639 * 2 ^ 59
def prefixEnd_81639 : Nat := 4983230072969 + 3 ^ 40 * 81639 * 2
def baseEnd_81639 : Nat := 18631132067782809216469

theorem tailTrace_81639 : CollatzResearch.WordTrace tailWord_81639 prefixEnd_81639 18631132067782809216469 := by
  unfold tailWord_81639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977618951243320676263971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1985079300828880450842647 2977618951243320676263971)
  ·
    refine ⟨4466428426864981014395957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2977618951243320676263971 4466428426864981014395957)
    ·
      refine ⟨418727665018591970099621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4466428426864981014395957 418727665018591970099621)
      ·
        refine ⟨78511437190985994393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 418727665018591970099621 78511437190985994393679)
        ·
          refine ⟨117767155786478991590519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78511437190985994393679 117767155786478991590519)
          ·
            refine ⟨176650733679718487385779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117767155786478991590519 176650733679718487385779)
            ·
              refine ⟨264976100519577731078669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176650733679718487385779 264976100519577731078669)
              ·
                refine ⟨99366037694841649154501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264976100519577731078669 99366037694841649154501)
                ·
                  refine ⟨18631132067782809216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99366037694841649154501 18631132067782809216469)
                  ·
                    rfl

theorem cell21_81639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_81639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81639 prefixEnd_81639 := by exact prefixLift 81639
  have htrace : WordTrace (prefixWord ++ tailWord_81639) baseStart_81639 baseEnd_81639 := by
    simpa [prefixWord, tailWord_81639, baseEnd_81639] using wordTrace_append hprefix tailTrace_81639
  have hstable : (prefixWord ++ tailWord_81639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81639).length < 2 ^ (prefixWord ++ tailWord_81639).sum := by decide
  have hdescent : baseEnd_81639 < baseStart_81639 := by decide
  rcases family_descends (prefixWord ++ tailWord_81639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81650 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_81650 : Nat := 118140960795 + 81650 * 2 ^ 59
def prefixEnd_81650 : Nat := 4983230072969 + 3 ^ 40 * 81650 * 2
def baseEnd_81650 : Nat := 18633642417649234533113

theorem tailTrace_81650 : CollatzResearch.WordTrace tailWord_81650 prefixEnd_81650 18633642417649234533113 := by
  unfold tailWord_81650
  simp only [CollatzResearch.WordTrace]
  refine ⟨744505038550867388728601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1985346769468979703276269 744505038550867388728601)
  ·
    refine ⟨558378778913150541546451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 744505038550867388728601 558378778913150541546451)
    ·
      refine ⟨837568168369725812319677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558378778913150541546451 837568168369725812319677)
      ·
        refine ⟨314088063138647179619879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 837568168369725812319677 314088063138647179619879)
        ·
          refine ⟨471132094707970769429819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314088063138647179619879 471132094707970769429819)
          ·
            refine ⟨706698142061956154144729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471132094707970769429819 706698142061956154144729)
            ·
              refine ⟨530023606546467115608547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706698142061956154144729 530023606546467115608547)
              ·
                refine ⟨795035409819700673412821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 530023606546467115608547 795035409819700673412821)
                ·
                  refine ⟨18633642417649234533113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 795035409819700673412821 18633642417649234533113)
                  ·
                    rfl

theorem cell21_81650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_81650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81650 prefixEnd_81650 := by exact prefixLift 81650
  have htrace : WordTrace (prefixWord ++ tailWord_81650) baseStart_81650 baseEnd_81650 := by
    simpa [prefixWord, tailWord_81650, baseEnd_81650] using wordTrace_append hprefix tailTrace_81650
  have hstable : (prefixWord ++ tailWord_81650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81650).length < 2 ^ (prefixWord ++ tailWord_81650).sum := by decide
  have hdescent : baseEnd_81650 < baseStart_81650 := by decide
  rcases family_descends (prefixWord ++ tailWord_81650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81853 : List Nat := [1, 4, 1, 2, 3, 3, 2, 2, 3]
def baseStart_81853 : Nat := 118140960795 + 81853 * 2 ^ 59
def prefixEnd_81853 : Nat := 4983230072969 + 3 ^ 40 * 81853 * 2
def baseEnd_81853 : Nat := 18679969783365992649365

theorem tailTrace_81853 : CollatzResearch.WordTrace tailWord_81853 prefixEnd_81853 18679969783365992649365 := by
  unfold tailWord_81853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985424172468035224554213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1990282781645356816369475 2985424172468035224554213)
  ·
    refine ⟨559767032337756604603915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2985424172468035224554213 559767032337756604603915)
    ·
      refine ⟨839650548506634906905873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559767032337756604603915 839650548506634906905873)
      ·
        refine ⟨629737911379976180179405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839650548506634906905873 629737911379976180179405)
        ·
          refine ⟨236151716767491067567277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 629737911379976180179405 236151716767491067567277)
          ·
            refine ⟨88556893787809150337729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236151716767491067567277 88556893787809150337729)
            ·
              refine ⟨66417670340856862753297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88556893787809150337729 66417670340856862753297)
              ·
                refine ⟨49813252755642647064973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66417670340856862753297 49813252755642647064973)
                ·
                  refine ⟨18679969783365992649365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49813252755642647064973 18679969783365992649365)
                  ·
                    rfl

theorem cell21_81853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_81853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81853 prefixEnd_81853 := by exact prefixLift 81853
  have htrace : WordTrace (prefixWord ++ tailWord_81853) baseStart_81853 baseEnd_81853 := by
    simpa [prefixWord, tailWord_81853, baseEnd_81853] using wordTrace_append hprefix tailTrace_81853
  have hstable : (prefixWord ++ tailWord_81853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81853).length < 2 ^ (prefixWord ++ tailWord_81853).sum := by decide
  have hdescent : baseEnd_81853 < baseStart_81853 := by decide
  rcases family_descends (prefixWord ++ tailWord_81853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81864 : List Nat := [2, 1, 3, 1, 4, 3, 1, 6]
def baseStart_81864 : Nat := 118140960795 + 81864 * 2 ^ 59
def prefixEnd_81864 : Nat := 4983230072969 + 3 ^ 40 * 81864 * 2
def baseEnd_81864 : Nat := 6227493377744139322003

theorem tailTrace_81864 : CollatzResearch.WordTrace tailWord_81864 prefixEnd_81864 6227493377744139322003 := by
  unfold tailWord_81864
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492912687714092051602323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1990550250285456068803097 1492912687714092051602323)
  ·
    refine ⟨2239369031571138077403485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1492912687714092051602323 2239369031571138077403485)
    ·
      refine ⟨839763386839176779026307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239369031571138077403485 839763386839176779026307)
      ·
        refine ⟨1259645080258765168539461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839763386839176779026307 1259645080258765168539461)
        ·
          refine ⟨236183452548518469101149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1259645080258765168539461 236183452548518469101149)
          ·
            refine ⟨88568794705694425912931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236183452548518469101149 88568794705694425912931)
            ·
              refine ⟨132853192058541638869397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88568794705694425912931 132853192058541638869397)
              ·
                refine ⟨6227493377744139322003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132853192058541638869397 6227493377744139322003)
                ·
                  rfl

theorem cell21_81864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_81864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81864 prefixEnd_81864 := by exact prefixLift 81864
  have htrace : WordTrace (prefixWord ++ tailWord_81864) baseStart_81864 baseEnd_81864 := by
    simpa [prefixWord, tailWord_81864, baseEnd_81864] using wordTrace_append hprefix tailTrace_81864
  have hstable : (prefixWord ++ tailWord_81864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81864).length < 2 ^ (prefixWord ++ tailWord_81864).sum := by decide
  have hdescent : baseEnd_81864 < baseStart_81864 := by decide
  rcases family_descends (prefixWord ++ tailWord_81864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81892 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_81892 : Nat := 118140960795 + 81892 * 2 ^ 59
def prefixEnd_81892 : Nat := 4983230072969 + 3 ^ 40 * 81892 * 2
def baseEnd_81892 : Nat := 18688870114710591499285

theorem tailTrace_81892 : CollatzResearch.WordTrace tailWord_81892 prefixEnd_81892 18688870114710591499285 := by
  unfold tailWord_81892
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493423309663372442611965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1991231079551163256815953 1493423309663372442611965)
  ·
    refine ⟨560033741123764665979487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1493423309663372442611965 560033741123764665979487)
    ·
      refine ⟨840050611685646998969231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560033741123764665979487 840050611685646998969231)
      ·
        refine ⟨1260075917528470498453847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840050611685646998969231 1260075917528470498453847)
        ·
          refine ⟨1890113876292705747680771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260075917528470498453847 1890113876292705747680771)
          ·
            refine ⟨2835170814439058621521157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1890113876292705747680771 2835170814439058621521157)
            ·
              refine ⟨531594527707323491535217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2835170814439058621521157 531594527707323491535217)
              ·
                refine ⟨398695895780492618651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531594527707323491535217 398695895780492618651413)
                ·
                  refine ⟨18688870114710591499285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 398695895780492618651413 18688870114710591499285)
                  ·
                    rfl

theorem cell21_81892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_81892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81892 prefixEnd_81892 := by exact prefixLift 81892
  have htrace : WordTrace (prefixWord ++ tailWord_81892) baseStart_81892 baseEnd_81892 := by
    simpa [prefixWord, tailWord_81892, baseEnd_81892] using wordTrace_append hprefix tailTrace_81892
  have hstable : (prefixWord ++ tailWord_81892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81892).length < 2 ^ (prefixWord ++ tailWord_81892).sum := by decide
  have hdescent : baseEnd_81892 < baseStart_81892 := by decide
  rcases family_descends (prefixWord ++ tailWord_81892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81968 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_81968 : Nat := 118140960795 + 81968 * 2 ^ 59
def prefixEnd_81968 : Nat := 4983230072969 + 3 ^ 40 * 81968 * 2
def baseEnd_81968 : Nat := 18706214350151348232463

theorem tailTrace_81968 : CollatzResearch.WordTrace tailWord_81968 prefixEnd_81968 18706214350151348232463 := by
  unfold tailWord_81968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1494809283525704932495279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1993079044700939909993705 1494809283525704932495279)
  ·
    refine ⟨2242213925288557398742919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1494809283525704932495279 2242213925288557398742919)
    ·
      refine ⟨3363320887932836098114379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2242213925288557398742919 3363320887932836098114379)
      ·
        refine ⟨5044981331899254147171569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363320887932836098114379 5044981331899254147171569)
        ·
          refine ⟨3783735998924440610378677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044981331899254147171569 3783735998924440610378677)
          ·
            refine ⟨354725249899166307223001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3783735998924440610378677 354725249899166307223001)
            ·
              refine ⟨266043937424374730417251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354725249899166307223001 266043937424374730417251)
              ·
                refine ⟨399065906136562095625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266043937424374730417251 399065906136562095625877)
                ·
                  refine ⟨18706214350151348232463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399065906136562095625877 18706214350151348232463)
                  ·
                    rfl

theorem cell21_81968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_81968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_81968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_81968 prefixEnd_81968 := by exact prefixLift 81968
  have htrace : WordTrace (prefixWord ++ tailWord_81968) baseStart_81968 baseEnd_81968 := by
    simpa [prefixWord, tailWord_81968, baseEnd_81968] using wordTrace_append hprefix tailTrace_81968
  have hstable : (prefixWord ++ tailWord_81968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81968).length < 2 ^ (prefixWord ++ tailWord_81968).sum := by decide
  have hdescent : baseEnd_81968 < baseStart_81968 := by decide
  rcases family_descends (prefixWord ++ tailWord_81968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82030 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_82030 : Nat := 118140960795 + 82030 * 2 ^ 59
def prefixEnd_82030 : Nat := 4983230072969 + 3 ^ 40 * 82030 * 2
def baseEnd_82030 : Nat := 18720363594853018199003

theorem tailTrace_82030 : CollatzResearch.WordTrace tailWord_82030 prefixEnd_82030 18720363594853018199003 := by
  unfold tailWord_82030
  simp only [CollatzResearch.WordTrace]
  refine ⟨373984986603349306718443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1994586595217862969165029 373984986603349306718443)
  ·
    refine ⟨560977479905023960077665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373984986603349306718443 560977479905023960077665)
    ·
      refine ⟨420733109928767970058249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 560977479905023960077665 420733109928767970058249)
      ·
        refine ⟨315549832446575977543687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420733109928767970058249 315549832446575977543687)
        ·
          refine ⟨473324748669863966315531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315549832446575977543687 473324748669863966315531)
          ·
            refine ⟨709987123004795949473297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473324748669863966315531 709987123004795949473297)
            ·
              refine ⟨532490342253596962104973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709987123004795949473297 532490342253596962104973)
              ·
                refine ⟨199683878345098860789365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 532490342253596962104973 199683878345098860789365)
                ·
                  refine ⟨18720363594853018199003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 199683878345098860789365 18720363594853018199003)
                  ·
                    rfl

theorem cell21_82030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_82030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82030 prefixEnd_82030 := by exact prefixLift 82030
  have htrace : WordTrace (prefixWord ++ tailWord_82030) baseStart_82030 baseEnd_82030 := by
    simpa [prefixWord, tailWord_82030, baseEnd_82030] using wordTrace_append hprefix tailTrace_82030
  have hstable : (prefixWord ++ tailWord_82030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82030).length < 2 ^ (prefixWord ++ tailWord_82030).sum := by decide
  have hdescent : baseEnd_82030 < baseStart_82030 := by decide
  rcases family_descends (prefixWord ++ tailWord_82030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82070 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_82070 : Nat := 118140960795 + 82070 * 2 ^ 59
def prefixEnd_82070 : Nat := 4983230072969 + 3 ^ 40 * 82070 * 2
def baseEnd_82070 : Nat := 18729492139821837532255

theorem tailTrace_82070 : CollatzResearch.WordTrace tailWord_82070 prefixEnd_82070 18729492139821837532255 := by
  unfold tailWord_82070
  simp only [CollatzResearch.WordTrace]
  refine ⟨187083675792617580325229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1995559208454587523469109 187083675792617580325229)
  ·
    refine ⟨70156378422231592621961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 187083675792617580325229 70156378422231592621961)
    ·
      refine ⟨52617283816673694466471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70156378422231592621961 52617283816673694466471)
      ·
        refine ⟨78925925725010541699707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52617283816673694466471 78925925725010541699707)
        ·
          refine ⟨118388888587515812549561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78925925725010541699707 118388888587515812549561)
          ·
            refine ⟨88791666440636859412171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 118388888587515812549561 88791666440636859412171)
            ·
              refine ⟨133187499660955289118257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88791666440636859412171 133187499660955289118257)
              ·
                refine ⟨99890624745716466838693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133187499660955289118257 99890624745716466838693)
                ·
                  refine ⟨18729492139821837532255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99890624745716466838693 18729492139821837532255)
                  ·
                    rfl

theorem cell21_82070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_82070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82070 prefixEnd_82070 := by exact prefixLift 82070
  have htrace : WordTrace (prefixWord ++ tailWord_82070) baseStart_82070 baseEnd_82070 := by
    simpa [prefixWord, tailWord_82070, baseEnd_82070] using wordTrace_append hprefix tailTrace_82070
  have hstable : (prefixWord ++ tailWord_82070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82070).length < 2 ^ (prefixWord ++ tailWord_82070).sum := by decide
  have hdescent : baseEnd_82070 < baseStart_82070 := by decide
  rcases family_descends (prefixWord ++ tailWord_82070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82078 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_82078 : Nat := 118140960795 + 82078 * 2 ^ 59
def prefixEnd_82078 : Nat := 4983230072969 + 3 ^ 40 * 82078 * 2
def baseEnd_82078 : Nat := 18731317848815601398905

theorem tailTrace_82078 : CollatzResearch.WordTrace tailWord_82078 prefixEnd_82078 18731317848815601398905 := by
  unfold tailWord_82078
  simp only [CollatzResearch.WordTrace]
  refine ⟨374203824581612331436861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1995753731101932434329925 374203824581612331436861)
  ·
    refine ⟨140326434218104624288823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 374203824581612331436861 140326434218104624288823)
    ·
      refine ⟨210489651327156936433235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140326434218104624288823 210489651327156936433235)
      ·
        refine ⟨315734476990735404649853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210489651327156936433235 315734476990735404649853)
        ·
          refine ⟨118400428871525776743695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315734476990735404649853 118400428871525776743695)
          ·
            refine ⟨177600643307288665115543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118400428871525776743695 177600643307288665115543)
            ·
              refine ⟨266400964960932997673315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177600643307288665115543 266400964960932997673315)
              ·
                refine ⟨399601447441399496509973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266400964960932997673315 399601447441399496509973)
                ·
                  refine ⟨18731317848815601398905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 399601447441399496509973 18731317848815601398905)
                  ·
                    rfl

theorem cell21_82078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_82078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82078 prefixEnd_82078 := by exact prefixLift 82078
  have htrace : WordTrace (prefixWord ++ tailWord_82078) baseStart_82078 baseEnd_82078 := by
    simpa [prefixWord, tailWord_82078, baseEnd_82078] using wordTrace_append hprefix tailTrace_82078
  have hstable : (prefixWord ++ tailWord_82078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82078).length < 2 ^ (prefixWord ++ tailWord_82078).sum := by decide
  have hdescent : baseEnd_82078 < baseStart_82078 := by decide
  rcases family_descends (prefixWord ++ tailWord_82078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82146 : List Nat := [3, 3, 4, 1, 2, 1, 2, 1, 4]
def baseStart_82146 : Nat := 118140960795 + 82146 * 2 ^ 59
def prefixEnd_82146 : Nat := 4983230072969 + 3 ^ 40 * 82146 * 2
def baseEnd_82146 : Nat := 18746836375262594265433

theorem tailTrace_82146 : CollatzResearch.WordTrace tailWord_82146 prefixEnd_82146 18746836375262594265433 := by
  unfold tailWord_82146
  simp only [CollatzResearch.WordTrace]
  refine ⟨749027690101636566242573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1997407173604364176646861 749027690101636566242573)
  ·
    refine ⟨280885383788113712340965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 749027690101636566242573 280885383788113712340965)
    ·
      refine ⟨52666009460271321063931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 280885383788113712340965 52666009460271321063931)
      ·
        refine ⟨78999014190406981595897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52666009460271321063931 78999014190406981595897)
        ·
          refine ⟨59249260642805236196923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78999014190406981595897 59249260642805236196923)
          ·
            refine ⟨88873890964207854295385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59249260642805236196923 88873890964207854295385)
            ·
              refine ⟨66655418223155890721539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88873890964207854295385 66655418223155890721539)
              ·
                refine ⟨99983127334733836082309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66655418223155890721539 99983127334733836082309)
                ·
                  refine ⟨18746836375262594265433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99983127334733836082309 18746836375262594265433)
                  ·
                    rfl

theorem cell21_82146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_82146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82146 prefixEnd_82146 := by exact prefixLift 82146
  have htrace : WordTrace (prefixWord ++ tailWord_82146) baseStart_82146 baseEnd_82146 := by
    simpa [prefixWord, tailWord_82146, baseEnd_82146] using wordTrace_append hprefix tailTrace_82146
  have hstable : (prefixWord ++ tailWord_82146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82146).length < 2 ^ (prefixWord ++ tailWord_82146).sum := by decide
  have hdescent : baseEnd_82146 < baseStart_82146 := by decide
  rcases family_descends (prefixWord ++ tailWord_82146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82151 : List Nat := [1, 1, 5, 3, 1, 1, 1, 8]
def baseStart_82151 : Nat := 118140960795 + 82151 * 2 ^ 59
def prefixEnd_82151 : Nat := 4983230072969 + 3 ^ 40 * 82151 * 2
def baseEnd_82151 : Nat := 6249325814461232227363

theorem tailTrace_82151 : CollatzResearch.WordTrace tailWord_82151 prefixEnd_82151 6249325814461232227363 := by
  unfold tailWord_82151
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996293125388432118902307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1997528750258954745934871 2996293125388432118902307)
  ·
    refine ⟨4494439688082648178353461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2996293125388432118902307 4494439688082648178353461)
    ·
      refine ⟨421353720757748266720637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4494439688082648178353461 421353720757748266720637)
      ·
        refine ⟨158007645284155600020239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 421353720757748266720637 158007645284155600020239)
        ·
          refine ⟨237011467926233400030359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158007645284155600020239 237011467926233400030359)
          ·
            refine ⟨355517201889350100045539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237011467926233400030359 355517201889350100045539)
            ·
              refine ⟨533275802834025150068309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355517201889350100045539 533275802834025150068309)
              ·
                refine ⟨6249325814461232227363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 533275802834025150068309 6249325814461232227363)
                ·
                  rfl

theorem cell21_82151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 8].length) (baseStart_82151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82151 prefixEnd_82151 := by exact prefixLift 82151
  have htrace : WordTrace (prefixWord ++ tailWord_82151) baseStart_82151 baseEnd_82151 := by
    simpa [prefixWord, tailWord_82151, baseEnd_82151] using wordTrace_append hprefix tailTrace_82151
  have hstable : (prefixWord ++ tailWord_82151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82151).length < 2 ^ (prefixWord ++ tailWord_82151).sum := by decide
  have hdescent : baseEnd_82151 < baseStart_82151 := by decide
  rcases family_descends (prefixWord ++ tailWord_82151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82199 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 3]
def baseStart_82199 : Nat := 118140960795 + 82199 * 2 ^ 59
def prefixEnd_82199 : Nat := 4983230072969 + 3 ^ 40 * 82199 * 2
def baseEnd_82199 : Nat := 18758931697346279881991

theorem tailTrace_82199 : CollatzResearch.WordTrace tailWord_82199 prefixEnd_82199 18758931697346279881991 := by
  unfold tailWord_82199
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998043829214536316649651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1998695886143024211099767 2998043829214536316649651)
  ·
    refine ⟨4497065743821804474974477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2998043829214536316649651 4497065743821804474974477)
    ·
      refine ⟨1686399653933176678115429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4497065743821804474974477 1686399653933176678115429)
      ·
        refine ⟨316199935112470627146643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1686399653933176678115429 316199935112470627146643)
        ·
          refine ⟨474299902668705940719965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316199935112470627146643 474299902668705940719965)
          ·
            refine ⟨177862463500764727769987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474299902668705940719965 177862463500764727769987)
            ·
              refine ⟨266793695251147091654981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177862463500764727769987 266793695251147091654981)
              ·
                refine ⟨50023817859590079685309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266793695251147091654981 50023817859590079685309)
                ·
                  refine ⟨18758931697346279881991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50023817859590079685309 18758931697346279881991)
                  ·
                    rfl

theorem cell21_82199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 3].length) (baseStart_82199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82199 prefixEnd_82199 := by exact prefixLift 82199
  have htrace : WordTrace (prefixWord ++ tailWord_82199) baseStart_82199 baseEnd_82199 := by
    simpa [prefixWord, tailWord_82199, baseEnd_82199] using wordTrace_append hprefix tailTrace_82199
  have hstable : (prefixWord ++ tailWord_82199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82199).length < 2 ^ (prefixWord ++ tailWord_82199).sum := by decide
  have hdescent : baseEnd_82199 < baseStart_82199 := by decide
  rcases family_descends (prefixWord ++ tailWord_82199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82227 : List Nat := [1, 1, 1, 2, 5, 1, 5, 5]
def baseStart_82227 : Nat := 118140960795 + 82227 * 2 ^ 59
def prefixEnd_82227 : Nat := 4983230072969 + 3 ^ 40 * 82227 * 2
def baseEnd_82227 : Nat := 6255107226274817805089

theorem tailTrace_82227 : CollatzResearch.WordTrace tailWord_82227 prefixEnd_82227 6255107226274817805089 := by
  unfold tailWord_82227
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999065073113097098668935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1999376715408731399112623 2999065073113097098668935)
  ·
    refine ⟨4498597609669645648003403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2999065073113097098668935 4498597609669645648003403)
    ·
      refine ⟨6747896414504468472005105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498597609669645648003403 6747896414504468472005105)
      ·
        refine ⟨5060922310878351354003829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6747896414504468472005105 5060922310878351354003829)
        ·
          refine ⟨474461466644845439437859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5060922310878351354003829 474461466644845439437859)
          ·
            refine ⟨711692199967268159156789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474461466644845439437859 711692199967268159156789)
            ·
              refine ⟨66721143746931389920949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 711692199967268159156789 66721143746931389920949)
              ·
                refine ⟨6255107226274817805089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66721143746931389920949 6255107226274817805089)
                ·
                  rfl

theorem cell21_82227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 5].length) (baseStart_82227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82227 prefixEnd_82227 := by exact prefixLift 82227
  have htrace : WordTrace (prefixWord ++ tailWord_82227) baseStart_82227 baseEnd_82227 := by
    simpa [prefixWord, tailWord_82227, baseEnd_82227] using wordTrace_append hprefix tailTrace_82227
  have hstable : (prefixWord ++ tailWord_82227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82227).length < 2 ^ (prefixWord ++ tailWord_82227).sum := by decide
  have hdescent : baseEnd_82227 < baseStart_82227 := by decide
  rcases family_descends (prefixWord ++ tailWord_82227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82244 : List Nat := [2, 3, 4, 1, 2, 1, 8]
def baseStart_82244 : Nat := 118140960795 + 82244 * 2 ^ 59
def prefixEnd_82244 : Nat := 4983230072969 + 3 ^ 40 * 82244 * 2
def baseEnd_82244 : Nat := 2085466812270689070211

theorem tailTrace_82244 : CollatzResearch.WordTrace tailWord_82244 prefixEnd_82244 2085466812270689070211 := by
  unfold tailWord_82244
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499842557025754501018893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1999790076034339334691857 1499842557025754501018893)
  ·
    refine ⟨562440958884657937882085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1499842557025754501018893 562440958884657937882085)
    ·
      refine ⟨105457679790873363352891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 562440958884657937882085 105457679790873363352891)
      ·
        refine ⟨158186519686310045029337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105457679790873363352891 158186519686310045029337)
        ·
          refine ⟨118639889764732533772003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158186519686310045029337 118639889764732533772003)
          ·
            refine ⟨177959834647098800658005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118639889764732533772003 177959834647098800658005)
            ·
              refine ⟨2085466812270689070211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 177959834647098800658005 2085466812270689070211)
              ·
                rfl

theorem cell21_82244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 8].length) (baseStart_82244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82244 prefixEnd_82244 := by exact prefixLift 82244
  have htrace : WordTrace (prefixWord ++ tailWord_82244) baseStart_82244 baseEnd_82244 := by
    simpa [prefixWord, tailWord_82244, baseEnd_82244] using wordTrace_append hprefix tailTrace_82244
  have hstable : (prefixWord ++ tailWord_82244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82244).length < 2 ^ (prefixWord ++ tailWord_82244).sum := by decide
  have hdescent : baseEnd_82244 < baseStart_82244 := by decide
  rcases family_descends (prefixWord ++ tailWord_82244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82365 : List Nat := [1, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_82365 : Nat := 118140960795 + 82365 * 2 ^ 59
def prefixEnd_82365 : Nat := 4983230072969 + 3 ^ 40 * 82365 * 2
def baseEnd_82365 : Nat := 18796815158966880114985

theorem tailTrace_82365 : CollatzResearch.WordTrace tailWord_82365 prefixEnd_82365 18796815158966880114985 := by
  unfold tailWord_82365
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004098346613146667192549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2002732231075431111461699 3004098346613146667192549)
  ·
    refine ⟨563268439989965000098603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3004098346613146667192549 563268439989965000098603)
    ·
      refine ⟨844902659984947500147905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563268439989965000098603 844902659984947500147905)
      ·
        refine ⟨633676994988710625110929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844902659984947500147905 633676994988710625110929)
        ·
          refine ⟨475257746241532968833197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633676994988710625110929 475257746241532968833197)
          ·
            refine ⟨178221654840574863312449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475257746241532968833197 178221654840574863312449)
            ·
              refine ⟨133666241130431147484337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178221654840574863312449 133666241130431147484337)
              ·
                refine ⟨100249680847823360613253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133666241130431147484337 100249680847823360613253)
                ·
                  refine ⟨18796815158966880114985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100249680847823360613253 18796815158966880114985)
                  ·
                    rfl

theorem cell21_82365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_82365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82365 prefixEnd_82365 := by exact prefixLift 82365
  have htrace : WordTrace (prefixWord ++ tailWord_82365) baseStart_82365 baseEnd_82365 := by
    simpa [prefixWord, tailWord_82365, baseEnd_82365] using wordTrace_append hprefix tailTrace_82365
  have hstable : (prefixWord ++ tailWord_82365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82365).length < 2 ^ (prefixWord ++ tailWord_82365).sum := by decide
  have hdescent : baseEnd_82365 < baseStart_82365 := by decide
  rcases family_descends (prefixWord ++ tailWord_82365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82393 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 5]
def baseStart_82393 : Nat := 118140960795 + 82393 * 2 ^ 59
def prefixEnd_82393 : Nat := 4983230072969 + 3 ^ 40 * 82393 * 2
def baseEnd_82393 : Nat := 18803205140445053648261

theorem tailTrace_82393 : CollatzResearch.WordTrace tailWord_82393 prefixEnd_82393 18803205140445053648261 := by
  unfold tailWord_82393
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005119590511707449211833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2003413060341138299474555 3005119590511707449211833)
  ·
    refine ⟨2253839692883780586908875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3005119590511707449211833 2253839692883780586908875)
    ·
      refine ⟨3380759539325670880363313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253839692883780586908875 3380759539325670880363313)
      ·
        refine ⟨2535569654494253160272485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3380759539325670880363313 2535569654494253160272485)
        ·
          refine ⟨475419310217672467551091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2535569654494253160272485 475419310217672467551091)
          ·
            refine ⟨713128965326508701326637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475419310217672467551091 713128965326508701326637)
            ·
              refine ⟨267423361997440762997489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713128965326508701326637 267423361997440762997489)
              ·
                refine ⟨200567521498080572248117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267423361997440762997489 200567521498080572248117)
                ·
                  refine ⟨18803205140445053648261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 200567521498080572248117 18803205140445053648261)
                  ·
                    rfl

theorem cell21_82393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_82393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82393 prefixEnd_82393 := by exact prefixLift 82393
  have htrace : WordTrace (prefixWord ++ tailWord_82393) baseStart_82393 baseEnd_82393 := by
    simpa [prefixWord, tailWord_82393, baseEnd_82393] using wordTrace_append hprefix tailTrace_82393
  have hstable : (prefixWord ++ tailWord_82393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82393).length < 2 ^ (prefixWord ++ tailWord_82393).sum := by decide
  have hdescent : baseEnd_82393 < baseStart_82393 := by decide
  rcases family_descends (prefixWord ++ tailWord_82393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82483 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 6]
def baseStart_82483 : Nat := 118140960795 + 82483 * 2 ^ 59
def prefixEnd_82483 : Nat := 4983230072969 + 3 ^ 40 * 82483 * 2
def baseEnd_82483 : Nat := 18823744366624897148077

theorem tailTrace_82483 : CollatzResearch.WordTrace tailWord_82483 prefixEnd_82483 18823744366624897148077 := by
  unfold tailWord_82483
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008402160185652819988103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005601440123768546658735 3008402160185652819988103)
  ·
    refine ⟨4512603240278479229982155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008402160185652819988103 4512603240278479229982155)
    ·
      refine ⟨6768904860417718844973233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512603240278479229982155 6768904860417718844973233)
      ·
        refine ⟨5076678645313289133729925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6768904860417718844973233 5076678645313289133729925)
        ·
          refine ⟨951877245996241712574361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5076678645313289133729925 951877245996241712574361)
          ·
            refine ⟨713907934497181284430771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951877245996241712574361 713907934497181284430771)
            ·
              refine ⟨1070861901745771926646157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713907934497181284430771 1070861901745771926646157)
              ·
                refine ⟨401573213154664472492309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1070861901745771926646157 401573213154664472492309)
                ·
                  refine ⟨18823744366624897148077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 401573213154664472492309 18823744366624897148077)
                  ·
                    rfl

theorem cell21_82483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 6].length) (baseStart_82483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82483 prefixEnd_82483 := by exact prefixLift 82483
  have htrace : WordTrace (prefixWord ++ tailWord_82483) baseStart_82483 baseEnd_82483 := by
    simpa [prefixWord, tailWord_82483, baseEnd_82483] using wordTrace_append hprefix tailTrace_82483
  have hstable : (prefixWord ++ tailWord_82483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82483).length < 2 ^ (prefixWord ++ tailWord_82483).sum := by decide
  have hdescent : baseEnd_82483 < baseStart_82483 := by decide
  rcases family_descends (prefixWord ++ tailWord_82483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82514 : List Nat := [3, 2, 2, 1, 2, 1, 1, 9]
def baseStart_82514 : Nat := 118140960795 + 82514 * 2 ^ 59
def prefixEnd_82514 : Nat := 4983230072969 + 3 ^ 40 * 82514 * 2
def baseEnd_82514 : Nat := 6276939662991910710449

theorem tailTrace_82514 : CollatzResearch.WordTrace tailWord_82514 prefixEnd_82514 6276939662991910710449 := by
  unfold tailWord_82514
  simp only [CollatzResearch.WordTrace]
  refine ⟨752383205768336278591649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2006355215382230076244397 752383205768336278591649)
  ·
    refine ⟨564287404326252208943737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 752383205768336278591649 564287404326252208943737)
    ·
      refine ⟨423215553244689156707803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 564287404326252208943737 423215553244689156707803)
      ·
        refine ⟨634823329867033735061705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423215553244689156707803 634823329867033735061705)
        ·
          refine ⟨476117497400275301296279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634823329867033735061705 476117497400275301296279)
          ·
            refine ⟨714176246100412951944419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476117497400275301296279 714176246100412951944419)
            ·
              refine ⟨1071264369150619427916629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714176246100412951944419 1071264369150619427916629)
              ·
                refine ⟨6276939662991910710449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1071264369150619427916629 6276939662991910710449)
                ·
                  rfl

theorem cell21_82514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_82514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82514 prefixEnd_82514 := by exact prefixLift 82514
  have htrace : WordTrace (prefixWord ++ tailWord_82514) baseStart_82514 baseEnd_82514 := by
    simpa [prefixWord, tailWord_82514, baseEnd_82514] using wordTrace_append hprefix tailTrace_82514
  have hstable : (prefixWord ++ tailWord_82514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82514).length < 2 ^ (prefixWord ++ tailWord_82514).sum := by decide
  have hdescent : baseEnd_82514 < baseStart_82514 := by decide
  rcases family_descends (prefixWord ++ tailWord_82514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82621 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 5]
def baseStart_82621 : Nat := 118140960795 + 82621 * 2 ^ 59
def prefixEnd_82621 : Nat := 4983230072969 + 3 ^ 40 * 82621 * 2
def baseEnd_82621 : Nat := 18855237846767323847795

theorem tailTrace_82621 : CollatzResearch.WordTrace tailWord_82621 prefixEnd_82621 18855237846767323847795 := by
  unfold tailWord_82621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013435433685702388511717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2008956955790468259007811 3013435433685702388511717)
  ·
    refine ⟨565019143816069197845947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3013435433685702388511717 565019143816069197845947)
    ·
      refine ⟨847528715724103796768921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565019143816069197845947 847528715724103796768921)
      ·
        refine ⟨635646536793077847576691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847528715724103796768921 635646536793077847576691)
        ·
          refine ⟨953469805189616771365037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635646536793077847576691 953469805189616771365037)
          ·
            refine ⟨357551176946106289261889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 953469805189616771365037 357551176946106289261889)
            ·
              refine ⟨268163382709579716946417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357551176946106289261889 268163382709579716946417)
              ·
                refine ⟨201122537032184787709813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268163382709579716946417 201122537032184787709813)
                ·
                  refine ⟨18855237846767323847795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201122537032184787709813 18855237846767323847795)
                  ·
                    rfl

theorem cell21_82621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_82621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82621 prefixEnd_82621 := by exact prefixLift 82621
  have htrace : WordTrace (prefixWord ++ tailWord_82621) baseStart_82621 baseEnd_82621 := by
    simpa [prefixWord, tailWord_82621, baseEnd_82621] using wordTrace_append hprefix tailTrace_82621
  have hstable : (prefixWord ++ tailWord_82621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82621).length < 2 ^ (prefixWord ++ tailWord_82621).sum := by decide
  have hdescent : baseEnd_82621 < baseStart_82621 := by decide
  rcases family_descends (prefixWord ++ tailWord_82621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82630 : List Nat := [6, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_82630 : Nat := 118140960795 + 82630 * 2 ^ 59
def prefixEnd_82630 : Nat := 4983230072969 + 3 ^ 40 * 82630 * 2
def baseEnd_82630 : Nat := 18857291769385308197777

theorem tailTrace_82630 : CollatzResearch.WordTrace tailWord_82630 prefixEnd_82630 18857291769385308197777 := by
  unfold tailWord_82630
  simp only [CollatzResearch.WordTrace]
  refine ⟨94180115332909278924667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2009175793768731283726229 94180115332909278924667)
  ·
    refine ⟨141270172999363918387001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94180115332909278924667 141270172999363918387001)
    ·
      refine ⟨105952629749522938790251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 141270172999363918387001 105952629749522938790251)
      ·
        refine ⟨158928944624284408185377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105952629749522938790251 158928944624284408185377)
        ·
          refine ⟨119196708468213306139033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158928944624284408185377 119196708468213306139033)
          ·
            refine ⟨89397531351159979604275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119196708468213306139033 89397531351159979604275)
            ·
              refine ⟨134096297026739969406413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89397531351159979604275 134096297026739969406413)
              ·
                refine ⟨50286111385027488527405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134096297026739969406413 50286111385027488527405)
                ·
                  refine ⟨18857291769385308197777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50286111385027488527405 18857291769385308197777)
                  ·
                    rfl

theorem cell21_82630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_82630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82630 prefixEnd_82630 := by exact prefixLift 82630
  have htrace : WordTrace (prefixWord ++ tailWord_82630) baseStart_82630 baseEnd_82630 := by
    simpa [prefixWord, tailWord_82630, baseEnd_82630] using wordTrace_append hprefix tailTrace_82630
  have hstable : (prefixWord ++ tailWord_82630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82630).length < 2 ^ (prefixWord ++ tailWord_82630).sum := by decide
  have hdescent : baseEnd_82630 < baseStart_82630 := by decide
  rcases family_descends (prefixWord ++ tailWord_82630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82655 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 3]
def baseStart_82655 : Nat := 118140960795 + 82655 * 2 ^ 59
def prefixEnd_82655 : Nat := 4983230072969 + 3 ^ 40 * 82655 * 2
def baseEnd_82655 : Nat := 18862997109990820281059

theorem tailTrace_82655 : CollatzResearch.WordTrace tailWord_82655 prefixEnd_82655 18862997109990820281059 := by
  unfold tailWord_82655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014675515562526195249419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2009783677041684130166279 3014675515562526195249419)
  ·
    refine ⟨4522013273343789292874129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014675515562526195249419 4522013273343789292874129)
    ·
      refine ⟨3391509955007841969655597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522013273343789292874129 3391509955007841969655597)
      ·
        refine ⟨1271816233127940738620849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3391509955007841969655597 1271816233127940738620849)
        ·
          refine ⟨953862174845955553965637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271816233127940738620849 953862174845955553965637)
          ·
            refine ⟨178849157783616666368557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 953862174845955553965637 178849157783616666368557)
            ·
              refine ⟨67068434168856249888209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178849157783616666368557 67068434168856249888209)
              ·
                refine ⟨50301325626642187416157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67068434168856249888209 50301325626642187416157)
                ·
                  refine ⟨18862997109990820281059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50301325626642187416157 18862997109990820281059)
                  ·
                    rfl

theorem cell21_82655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 3].length) (baseStart_82655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82655 prefixEnd_82655 := by exact prefixLift 82655
  have htrace : WordTrace (prefixWord ++ tailWord_82655) baseStart_82655 baseEnd_82655 := by
    simpa [prefixWord, tailWord_82655, baseEnd_82655] using wordTrace_append hprefix tailTrace_82655
  have hstable : (prefixWord ++ tailWord_82655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82655).length < 2 ^ (prefixWord ++ tailWord_82655).sum := by decide
  have hdescent : baseEnd_82655 < baseStart_82655 := by decide
  rcases family_descends (prefixWord ++ tailWord_82655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82680 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_82680 : Nat := 118140960795 + 82680 * 2 ^ 59
def prefixEnd_82680 : Nat := 4983230072969 + 3 ^ 40 * 82680 * 2
def baseEnd_82680 : Nat := 18868702450596332364341

theorem tailTrace_82680 : CollatzResearch.WordTrace tailWord_82680 prefixEnd_82680 18868702450596332364341 := by
  unfold tailWord_82680
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507793670235977732454747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2010391560314636976606329 1507793670235977732454747)
  ·
    refine ⟨2261690505353966598682121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507793670235977732454747 2261690505353966598682121)
    ·
      refine ⟨1696267879015474949011591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261690505353966598682121 1696267879015474949011591)
      ·
        refine ⟨2544401818523212423517387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696267879015474949011591 2544401818523212423517387)
        ·
          refine ⟨3816602727784818635276081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544401818523212423517387 3816602727784818635276081)
          ·
            refine ⟨2862452045838613976457061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3816602727784818635276081 2862452045838613976457061)
            ·
              refine ⟨536709758594740120585699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2862452045838613976457061 536709758594740120585699)
              ·
                refine ⟨805064637892110180878549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536709758594740120585699 805064637892110180878549)
                ·
                  refine ⟨18868702450596332364341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 805064637892110180878549 18868702450596332364341)
                  ·
                    rfl

theorem cell21_82680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_82680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82680 prefixEnd_82680 := by exact prefixLift 82680
  have htrace : WordTrace (prefixWord ++ tailWord_82680) baseStart_82680 baseEnd_82680 := by
    simpa [prefixWord, tailWord_82680, baseEnd_82680] using wordTrace_append hprefix tailTrace_82680
  have hstable : (prefixWord ++ tailWord_82680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82680).length < 2 ^ (prefixWord ++ tailWord_82680).sum := by decide
  have hdescent : baseEnd_82680 < baseStart_82680 := by decide
  rcases family_descends (prefixWord ++ tailWord_82680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82706 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 3]
def baseStart_82706 : Nat := 118140960795 + 82706 * 2 ^ 59
def prefixEnd_82706 : Nat := 4983230072969 + 3 ^ 40 * 82706 * 2
def baseEnd_82706 : Nat := 18874636004826064930955

theorem tailTrace_82706 : CollatzResearch.WordTrace tailWord_82706 prefixEnd_82706 18874636004826064930955 := by
  unfold tailWord_82706
  simp only [CollatzResearch.WordTrace]
  refine ⟨754133909594440476338993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2011023758918507936903981 754133909594440476338993)
  ·
    refine ⟨565600432195830357254245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 754133909594440476338993 565600432195830357254245)
    ·
      refine ⟨106050081036718191985171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 565600432195830357254245 106050081036718191985171)
      ·
        refine ⟨159075121555077287977757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106050081036718191985171 159075121555077287977757)
        ·
          refine ⟨59653170583153982991659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159075121555077287977757 59653170583153982991659)
          ·
            refine ⟨89479755874730974487489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59653170583153982991659 89479755874730974487489)
            ·
              refine ⟨67109816906048230865617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89479755874730974487489 67109816906048230865617)
              ·
                refine ⟨50332362679536173149213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67109816906048230865617 50332362679536173149213)
                ·
                  refine ⟨18874636004826064930955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50332362679536173149213 18874636004826064930955)
                  ·
                    rfl

theorem cell21_82706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_82706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82706 prefixEnd_82706 := by exact prefixLift 82706
  have htrace : WordTrace (prefixWord ++ tailWord_82706) baseStart_82706 baseEnd_82706 := by
    simpa [prefixWord, tailWord_82706, baseEnd_82706] using wordTrace_append hprefix tailTrace_82706
  have hstable : (prefixWord ++ tailWord_82706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82706).length < 2 ^ (prefixWord ++ tailWord_82706).sum := by decide
  have hdescent : baseEnd_82706 < baseStart_82706 := by decide
  rcases family_descends (prefixWord ++ tailWord_82706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82714 : List Nat := [3, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_82714 : Nat := 118140960795 + 82714 * 2 ^ 59
def prefixEnd_82714 : Nat := 4983230072969 + 3 ^ 40 * 82714 * 2
def baseEnd_82714 : Nat := 18876461713819828797605

theorem tailTrace_82714 : CollatzResearch.WordTrace tailWord_82714 prefixEnd_82714 18876461713819828797605 := by
  unfold tailWord_82714
  simp only [CollatzResearch.WordTrace]
  refine ⟨754206855587194817911799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2011218281565852847764797 754206855587194817911799)
  ·
    refine ⟨1131310283380792226867699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754206855587194817911799 1131310283380792226867699)
    ·
      refine ⟨1696965425071188340301549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131310283380792226867699 1696965425071188340301549)
      ·
        refine ⟨636362034401695627613081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1696965425071188340301549 636362034401695627613081)
        ·
          refine ⟨477271525801271720709811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636362034401695627613081 477271525801271720709811)
          ·
            refine ⟨715907288701907581064717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477271525801271720709811 715907288701907581064717)
            ·
              refine ⟨268465233263215342899269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715907288701907581064717 268465233263215342899269)
              ·
                refine ⟨50337231236852876793613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 268465233263215342899269 50337231236852876793613)
                ·
                  refine ⟨18876461713819828797605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50337231236852876793613 18876461713819828797605)
                  ·
                    rfl

theorem cell21_82714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_82714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82714 prefixEnd_82714 := by exact prefixLift 82714
  have htrace : WordTrace (prefixWord ++ tailWord_82714) baseStart_82714 baseEnd_82714 := by
    simpa [prefixWord, tailWord_82714, baseEnd_82714] using wordTrace_append hprefix tailTrace_82714
  have hstable : (prefixWord ++ tailWord_82714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82714).length < 2 ^ (prefixWord ++ tailWord_82714).sum := by decide
  have hdescent : baseEnd_82714 < baseStart_82714 := by decide
  rcases family_descends (prefixWord ++ tailWord_82714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82717 : List Nat := [1, 4, 2, 4, 2, 1, 1, 6]
def baseStart_82717 : Nat := 118140960795 + 82717 * 2 ^ 59
def prefixEnd_82717 : Nat := 4983230072969 + 3 ^ 40 * 82717 * 2
def baseEnd_82717 : Nat := 6292382118230830082533

theorem tailTrace_82717 : CollatzResearch.WordTrace tailWord_82717 prefixEnd_82717 6292382118230830082533 := by
  unfold tailWord_82717
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016936841337910784006405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2011291227558607189337603 3016936841337910784006405)
  ·
    refine ⟨565675657750858272001201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3016936841337910784006405 565675657750858272001201)
    ·
      refine ⟨424256743313143704000901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565675657750858272001201 424256743313143704000901)
      ·
        refine ⟨79548139371214444500169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 424256743313143704000901 79548139371214444500169)
        ·
          refine ⟨59661104528410833375127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79548139371214444500169 59661104528410833375127)
          ·
            refine ⟨89491656792616250062691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59661104528410833375127 89491656792616250062691)
            ·
              refine ⟨134237485188924375094037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89491656792616250062691 134237485188924375094037)
              ·
                refine ⟨6292382118230830082533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134237485188924375094037 6292382118230830082533)
                ·
                  rfl

theorem cell21_82717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 6].length) (baseStart_82717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82717 prefixEnd_82717 := by exact prefixLift 82717
  have htrace : WordTrace (prefixWord ++ tailWord_82717) baseStart_82717 baseEnd_82717 := by
    simpa [prefixWord, tailWord_82717, baseEnd_82717] using wordTrace_append hprefix tailTrace_82717
  have hstable : (prefixWord ++ tailWord_82717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82717).length < 2 ^ (prefixWord ++ tailWord_82717).sum := by decide
  have hdescent : baseEnd_82717 < baseStart_82717 := by decide
  rcases family_descends (prefixWord ++ tailWord_82717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82728 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_82728 : Nat := 118140960795 + 82728 * 2 ^ 59
def prefixEnd_82728 : Nat := 4983230072969 + 3 ^ 40 * 82728 * 2
def baseEnd_82728 : Nat := 18879656704558915564243

theorem tailTrace_82728 : CollatzResearch.WordTrace tailWord_82728 prefixEnd_82728 18879656704558915564243 := by
  unfold tailWord_82728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508669022149029831328419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2011558696198706441771225 1508669022149029831328419)
  ·
    refine ⟨2263003533223544746992629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508669022149029831328419 2263003533223544746992629)
    ·
      refine ⟨212156581239707320030559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2263003533223544746992629 212156581239707320030559)
      ·
        refine ⟨318234871859560980045839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212156581239707320030559 318234871859560980045839)
        ·
          refine ⟨477352307789341470068759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318234871859560980045839 477352307789341470068759)
          ·
            refine ⟨716028461684012205103139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477352307789341470068759 716028461684012205103139)
            ·
              refine ⟨1074042692526018307654709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716028461684012205103139 1074042692526018307654709)
              ·
                refine ⟨100691502424314216342629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1074042692526018307654709 100691502424314216342629)
                ·
                  refine ⟨18879656704558915564243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100691502424314216342629 18879656704558915564243)
                  ·
                    rfl

theorem cell21_82728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_82728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82728 prefixEnd_82728 := by exact prefixLift 82728
  have htrace : WordTrace (prefixWord ++ tailWord_82728) baseStart_82728 baseEnd_82728 := by
    simpa [prefixWord, tailWord_82728, baseEnd_82728] using wordTrace_append hprefix tailTrace_82728
  have hstable : (prefixWord ++ tailWord_82728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82728).length < 2 ^ (prefixWord ++ tailWord_82728).sum := by decide
  have hdescent : baseEnd_82728 < baseStart_82728 := by decide
  rcases family_descends (prefixWord ++ tailWord_82728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82773 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_82773 : Nat := 118140960795 + 82773 * 2 ^ 59
def prefixEnd_82773 : Nat := 4983230072969 + 3 ^ 40 * 82773 * 2
def baseEnd_82773 : Nat := 18889926317648837314151

theorem tailTrace_82773 : CollatzResearch.WordTrace tailWord_82773 prefixEnd_82773 18889926317648837314151 := by
  unfold tailWord_82773
  simp only [CollatzResearch.WordTrace]
  refine ⟨3018979329135032348044973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2012652886090021565363315 3018979329135032348044973)
  ·
    refine ⟨1132117248425637130516865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3018979329135032348044973 1132117248425637130516865)
    ·
      refine ⟨849087936319227847887649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1132117248425637130516865 849087936319227847887649)
      ·
        refine ⟨636815952239420885915737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 849087936319227847887649 636815952239420885915737)
        ·
          refine ⟨477611964179565664436803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636815952239420885915737 477611964179565664436803)
          ·
            refine ⟨716417946269348496655205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477611964179565664436803 716417946269348496655205)
            ·
              refine ⟨134328364925502843122851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 716417946269348496655205 134328364925502843122851)
              ·
                refine ⟨201492547388254264684277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134328364925502843122851 201492547388254264684277)
                ·
                  refine ⟨18889926317648837314151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 201492547388254264684277 18889926317648837314151)
                  ·
                    rfl

theorem cell21_82773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_82773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82773 prefixEnd_82773 := by exact prefixLift 82773
  have htrace : WordTrace (prefixWord ++ tailWord_82773) baseStart_82773 baseEnd_82773 := by
    simpa [prefixWord, tailWord_82773, baseEnd_82773] using wordTrace_append hprefix tailTrace_82773
  have hstable : (prefixWord ++ tailWord_82773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82773).length < 2 ^ (prefixWord ++ tailWord_82773).sum := by decide
  have hdescent : baseEnd_82773 < baseStart_82773 := by decide
  rcases family_descends (prefixWord ++ tailWord_82773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82877 : List Nat := [1, 4, 1, 2, 13]
def baseStart_82877 : Nat := 118140960795 + 82877 * 2 ^ 59
def prefixEnd_82877 : Nat := 4983230072969 + 3 ^ 40 * 82877 * 2
def baseEnd_82877 : Nat := 233501981908244044205

theorem tailTrace_82877 : CollatzResearch.WordTrace tailWord_82877 prefixEnd_82877 233501981908244044205 := by
  unfold tailWord_82877
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022772520758258109830885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2015181680505505406553923 3022772520758258109830885)
  ·
    refine ⟨566769847642173395593291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3022772520758258109830885 566769847642173395593291)
    ·
      refine ⟨850154771463260093389937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566769847642173395593291 850154771463260093389937)
      ·
        refine ⟨637616078597445070042453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850154771463260093389937 637616078597445070042453)
        ·
          refine ⟨233501981908244044205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 637616078597445070042453 233501981908244044205)
          ·
            rfl

theorem cell21_82877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 13].length) (baseStart_82877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82877 prefixEnd_82877 := by exact prefixLift 82877
  have htrace : WordTrace (prefixWord ++ tailWord_82877) baseStart_82877 baseEnd_82877 := by
    simpa [prefixWord, tailWord_82877, baseEnd_82877] using wordTrace_append hprefix tailTrace_82877
  have hstable : (prefixWord ++ tailWord_82877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82877).length < 2 ^ (prefixWord ++ tailWord_82877).sum := by decide
  have hdescent : baseEnd_82877 < baseStart_82877 := by decide
  rcases family_descends (prefixWord ++ tailWord_82877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82880 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_82880 : Nat := 118140960795 + 82880 * 2 ^ 59
def prefixEnd_82880 : Nat := 4983230072969 + 3 ^ 40 * 82880 * 2
def baseEnd_82880 : Nat := 18914345175440429030599

theorem tailTrace_82880 : CollatzResearch.WordTrace tailWord_82880 prefixEnd_82880 18914345175440429030599 := by
  unfold tailWord_82880
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511440969873694811095047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2015254626498259748126729 1511440969873694811095047)
  ·
    refine ⟨2267161454810542216642571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511440969873694811095047 2267161454810542216642571)
    ·
      refine ⟨3400742182215813324963857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267161454810542216642571 3400742182215813324963857)
      ·
        refine ⟨2550556636661859993722893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3400742182215813324963857 2550556636661859993722893)
        ·
          refine ⟨956458738748197497646085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2550556636661859993722893 956458738748197497646085)
          ·
            refine ⟨179336013515287030808641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 956458738748197497646085 179336013515287030808641)
            ·
              refine ⟨134502010136465273106481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179336013515287030808641 134502010136465273106481)
              ·
                refine ⟨100876507602348954829861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134502010136465273106481 100876507602348954829861)
                ·
                  refine ⟨18914345175440429030599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 100876507602348954829861 18914345175440429030599)
                  ·
                    rfl

theorem cell21_82880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_82880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82880 prefixEnd_82880 := by exact prefixLift 82880
  have htrace : WordTrace (prefixWord ++ tailWord_82880) baseStart_82880 baseEnd_82880 := by
    simpa [prefixWord, tailWord_82880, baseEnd_82880] using wordTrace_append hprefix tailTrace_82880
  have hstable : (prefixWord ++ tailWord_82880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82880).length < 2 ^ (prefixWord ++ tailWord_82880).sum := by decide
  have hdescent : baseEnd_82880 < baseStart_82880 := by decide
  rcases family_descends (prefixWord ++ tailWord_82880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82894 : List Nat := [4, 1, 1, 1, 2, 3, 3, 6]
def baseStart_82894 : Nat := 118140960795 + 82894 * 2 ^ 59
def prefixEnd_82894 : Nat := 4983230072969 + 3 ^ 40 * 82894 * 2
def baseEnd_82894 : Nat := 6305846722059838599079

theorem tailTrace_82894 : CollatzResearch.WordTrace tailWord_82894 prefixEnd_82894 6305846722059838599079 := by
  unfold tailWord_82894
  simp only [CollatzResearch.WordTrace]
  refine ⟨377924070212083751649967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2015595041131113342133157 377924070212083751649967)
  ·
    refine ⟨566886105318125627474951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 377924070212083751649967 566886105318125627474951)
    ·
      refine ⟨850329157977188441212427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566886105318125627474951 850329157977188441212427)
      ·
        refine ⟨1275493736965782661818641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850329157977188441212427 1275493736965782661818641)
        ·
          refine ⟨956620302724336996363981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275493736965782661818641 956620302724336996363981)
          ·
            refine ⟨358732613521626373636493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 956620302724336996363981 358732613521626373636493)
            ·
              refine ⟨134524730070609890113685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358732613521626373636493 134524730070609890113685)
              ·
                refine ⟨6305846722059838599079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 134524730070609890113685 6305846722059838599079)
                ·
                  rfl

theorem cell21_82894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_82894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82894 prefixEnd_82894 := by exact prefixLift 82894
  have htrace : WordTrace (prefixWord ++ tailWord_82894) baseStart_82894 baseEnd_82894 := by
    simpa [prefixWord, tailWord_82894, baseEnd_82894] using wordTrace_append hprefix tailTrace_82894
  have hstable : (prefixWord ++ tailWord_82894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82894).length < 2 ^ (prefixWord ++ tailWord_82894).sum := by decide
  have hdescent : baseEnd_82894 < baseStart_82894 := by decide
  rcases family_descends (prefixWord ++ tailWord_82894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82911 : List Nat := [1, 1, 2, 3, 5, 1, 3, 5]
def baseStart_82911 : Nat := 118140960795 + 82911 * 2 ^ 59
def prefixEnd_82911 : Nat := 4983230072969 + 3 ^ 40 * 82911 * 2
def baseEnd_82911 : Nat := 6307139932597088004623

theorem tailTrace_82911 : CollatzResearch.WordTrace tailWord_82911 prefixEnd_82911 6307139932597088004623 := by
  unfold tailWord_82911
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024012602635081916568587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2016008401756721277712391 3024012602635081916568587)
  ·
    refine ⟨4536018903952622874852881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024012602635081916568587 4536018903952622874852881)
    ·
      refine ⟨3402014177964467156139661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536018903952622874852881 3402014177964467156139661)
      ·
        refine ⟨1275755316736675183552373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3402014177964467156139661 1275755316736675183552373)
        ·
          refine ⟨119602060944063298458035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1275755316736675183552373 119602060944063298458035)
          ·
            refine ⟨179403091416094947687053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119602060944063298458035 179403091416094947687053)
            ·
              refine ⟨67276159281035605382645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179403091416094947687053 67276159281035605382645)
              ·
                refine ⟨6307139932597088004623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67276159281035605382645 6307139932597088004623)
                ·
                  rfl

theorem cell21_82911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 5].length) (baseStart_82911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82911 prefixEnd_82911 := by exact prefixLift 82911
  have htrace : WordTrace (prefixWord ++ tailWord_82911) baseStart_82911 baseEnd_82911 := by
    simpa [prefixWord, tailWord_82911, baseEnd_82911] using wordTrace_append hprefix tailTrace_82911
  have hstable : (prefixWord ++ tailWord_82911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82911).length < 2 ^ (prefixWord ++ tailWord_82911).sum := by decide
  have hdescent : baseEnd_82911 < baseStart_82911 := by decide
  rcases family_descends (prefixWord ++ tailWord_82911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82962 : List Nat := [3, 2, 5, 1, 1, 2, 2, 5]
def baseStart_82962 : Nat := 118140960795 + 82962 * 2 ^ 59
def prefixEnd_82962 : Nat := 4983230072969 + 3 ^ 40 * 82962 * 2
def baseEnd_82962 : Nat := 6311019564208836221255

theorem tailTrace_82962 : CollatzResearch.WordTrace tailWord_82962 prefixEnd_82962 6311019564208836221255 := by
  unfold tailWord_82962
  simp only [CollatzResearch.WordTrace]
  refine ⟨756468181362579406668785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2017248483633545084450093 756468181362579406668785)
  ·
    refine ⟨567351136021934555001589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756468181362579406668785 567351136021934555001589)
    ·
      refine ⟨53189169002056364531399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 567351136021934555001589 53189169002056364531399)
      ·
        refine ⟨79783753503084546797099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53189169002056364531399 79783753503084546797099)
        ·
          refine ⟨119675630254626820195649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79783753503084546797099 119675630254626820195649)
          ·
            refine ⟨89756722690970115146737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119675630254626820195649 89756722690970115146737)
            ·
              refine ⟨67317542018227586360053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89756722690970115146737 67317542018227586360053)
              ·
                refine ⟨6311019564208836221255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 67317542018227586360053 6311019564208836221255)
                ·
                  rfl

theorem cell21_82962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 5].length) (baseStart_82962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82962 prefixEnd_82962 := by exact prefixLift 82962
  have htrace : WordTrace (prefixWord ++ tailWord_82962) baseStart_82962 baseEnd_82962 := by
    simpa [prefixWord, tailWord_82962, baseEnd_82962] using wordTrace_append hprefix tailTrace_82962
  have hstable : (prefixWord ++ tailWord_82962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82962).length < 2 ^ (prefixWord ++ tailWord_82962).sum := by decide
  have hdescent : baseEnd_82962 < baseStart_82962 := by decide
  rcases family_descends (prefixWord ++ tailWord_82962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82976 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_82976 : Nat := 118140960795 + 82976 * 2 ^ 59
def prefixEnd_82976 : Nat := 4983230072969 + 3 ^ 40 * 82976 * 2
def baseEnd_82976 : Nat := 18936253683365595430403

theorem tailTrace_82976 : CollatzResearch.WordTrace tailWord_82976 prefixEnd_82976 18936253683365595430403 := by
  unfold tailWord_82976
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513191673699799008842391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2017588898266398678456521 1513191673699799008842391)
  ·
    refine ⟨2269787510549698513263587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513191673699799008842391 2269787510549698513263587)
    ·
      refine ⟨3404681265824547769895381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269787510549698513263587 3404681265824547769895381)
      ·
        refine ⟨79797217167762838356923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 3404681265824547769895381 79797217167762838356923)
        ·
          refine ⟨119695825751644257535385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79797217167762838356923 119695825751644257535385)
          ·
            refine ⟨89771869313733193151539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119695825751644257535385 89771869313733193151539)
            ·
              refine ⟨134657803970599789727309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89771869313733193151539 134657803970599789727309)
              ·
                refine ⟨50496676488974921147741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134657803970599789727309 50496676488974921147741)
                ·
                  refine ⟨18936253683365595430403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50496676488974921147741 18936253683365595430403)
                  ·
                    rfl

theorem cell21_82976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_82976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_82976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_82976 prefixEnd_82976 := by exact prefixLift 82976
  have htrace : WordTrace (prefixWord ++ tailWord_82976) baseStart_82976 baseEnd_82976 := by
    simpa [prefixWord, tailWord_82976, baseEnd_82976] using wordTrace_append hprefix tailTrace_82976
  have hstable : (prefixWord ++ tailWord_82976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82976).length < 2 ^ (prefixWord ++ tailWord_82976).sum := by decide
  have hdescent : baseEnd_82976 < baseStart_82976 := by decide
  rcases family_descends (prefixWord ++ tailWord_82976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83001 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_83001 : Nat := 118140960795 + 83001 * 2 ^ 59
def prefixEnd_83001 : Nat := 4983230072969 + 3 ^ 40 * 83001 * 2
def baseEnd_83001 : Nat := 18941959023971107513685

theorem tailTrace_83001 : CollatzResearch.WordTrace tailWord_83001 prefixEnd_83001 18941959023971107513685 := by
  unfold tailWord_83001
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027295172309027287344857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018196781539351524896571 3027295172309027287344857)
  ·
    refine ⟨2270471379231770465508643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3027295172309027287344857 2270471379231770465508643)
    ·
      refine ⟨3405707068847655698262965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270471379231770465508643 3405707068847655698262965)
      ·
        refine ⟨319285037704467721712153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3405707068847655698262965 319285037704467721712153)
        ·
          refine ⟨239463778278350791284115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319285037704467721712153 239463778278350791284115)
          ·
            refine ⟨359195667417526186926173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239463778278350791284115 359195667417526186926173)
            ·
              refine ⟨134698375281572320097315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359195667417526186926173 134698375281572320097315)
              ·
                refine ⟨202047562922358480145973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134698375281572320097315 202047562922358480145973)
                ·
                  refine ⟨18941959023971107513685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202047562922358480145973 18941959023971107513685)
                  ·
                    rfl

theorem cell21_83001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_83001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83001 prefixEnd_83001 := by exact prefixLift 83001
  have htrace : WordTrace (prefixWord ++ tailWord_83001) baseStart_83001 baseEnd_83001 := by
    simpa [prefixWord, tailWord_83001, baseEnd_83001] using wordTrace_append hprefix tailTrace_83001
  have hstable : (prefixWord ++ tailWord_83001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83001).length < 2 ^ (prefixWord ++ tailWord_83001).sum := by decide
  have hdescent : baseEnd_83001 < baseStart_83001 := by decide
  rcases family_descends (prefixWord ++ tailWord_83001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83029 : List Nat := [1, 3, 2, 2, 1, 2, 1, 9]
def baseStart_83029 : Nat := 118140960795 + 83029 * 2 ^ 59
def prefixEnd_83029 : Nat := 4983230072969 + 3 ^ 40 * 83029 * 2
def baseEnd_83029 : Nat := 6316116335149760348987

theorem tailTrace_83029 : CollatzResearch.WordTrace tailWord_83029 prefixEnd_83029 6316116335149760348987 := by
  unfold tailWord_83029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028316416207588069364141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018877610805058712909427 3028316416207588069364141)
  ·
    refine ⟨1135618656077845526011553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3028316416207588069364141 1135618656077845526011553)
    ·
      refine ⟨851713992058384144508665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1135618656077845526011553 851713992058384144508665)
      ·
        refine ⟨638785494043788108381499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 851713992058384144508665 638785494043788108381499)
        ·
          refine ⟨958178241065682162572249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638785494043788108381499 958178241065682162572249)
          ·
            refine ⟨718633680799261621929187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958178241065682162572249 718633680799261621929187)
            ·
              refine ⟨1077950521198892432893781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 718633680799261621929187 1077950521198892432893781)
              ·
                refine ⟨6316116335149760348987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1077950521198892432893781 6316116335149760348987)
                ·
                  rfl

theorem cell21_83029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 9].length) (baseStart_83029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83029 prefixEnd_83029 := by exact prefixLift 83029
  have htrace : WordTrace (prefixWord ++ tailWord_83029) baseStart_83029 baseEnd_83029 := by
    simpa [prefixWord, tailWord_83029, baseEnd_83029] using wordTrace_append hprefix tailTrace_83029
  have hstable : (prefixWord ++ tailWord_83029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83029).length < 2 ^ (prefixWord ++ tailWord_83029).sum := by decide
  have hdescent : baseEnd_83029 < baseStart_83029 := by decide
  rcases family_descends (prefixWord ++ tailWord_83029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83077 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 5]
def baseStart_83077 : Nat := 118140960795 + 83077 * 2 ^ 59
def prefixEnd_83077 : Nat := 4983230072969 + 3 ^ 40 * 83077 * 2
def baseEnd_83077 : Nat := 18959303259411864246863

theorem tailTrace_83077 : CollatzResearch.WordTrace tailWord_83077 prefixEnd_83077 18959303259411864246863 := by
  unfold tailWord_83077
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030067120033692267111485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2020044746689128178074323 3030067120033692267111485)
  ·
    refine ⟨1136275170012634600166807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3030067120033692267111485 1136275170012634600166807)
    ·
      refine ⟨1704412755018951900250211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136275170012634600166807 1704412755018951900250211)
      ·
        refine ⟨2556619132528427850375317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1704412755018951900250211 2556619132528427850375317)
        ·
          refine ⟨119841521837270055486343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2556619132528427850375317 119841521837270055486343)
          ·
            refine ⟨179762282755905083229515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119841521837270055486343 179762282755905083229515)
            ·
              refine ⟨269643424133857624844273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179762282755905083229515 269643424133857624844273)
              ·
                refine ⟨202232568100393218633205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269643424133857624844273 202232568100393218633205)
                ·
                  refine ⟨18959303259411864246863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202232568100393218633205 18959303259411864246863)
                  ·
                    rfl

theorem cell21_83077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_83077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83077 prefixEnd_83077 := by exact prefixLift 83077
  have htrace : WordTrace (prefixWord ++ tailWord_83077) baseStart_83077 baseEnd_83077 := by
    simpa [prefixWord, tailWord_83077, baseEnd_83077] using wordTrace_append hprefix tailTrace_83077
  have hstable : (prefixWord ++ tailWord_83077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83077).length < 2 ^ (prefixWord ++ tailWord_83077).sum := by decide
  have hdescent : baseEnd_83077 < baseStart_83077 := by decide
  rcases family_descends (prefixWord ++ tailWord_83077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83105 : List Nat := [1, 2, 3, 3, 1, 1, 10]
def baseStart_83105 : Nat := 118140960795 + 83105 * 2 ^ 59
def prefixEnd_83105 : Nat := 4983230072969 + 3 ^ 40 * 83105 * 2
def baseEnd_83105 : Nat := 2107299248987781975571

theorem tailTrace_83105 : CollatzResearch.WordTrace tailWord_83105 prefixEnd_83105 2107299248987781975571 := by
  unfold tailWord_83105
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031088363932253049130769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2020725575954835366087179 3031088363932253049130769)
  ·
    refine ⟨2273316272949189786848077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3031088363932253049130769 2273316272949189786848077)
    ·
      refine ⟨852493602355946170068029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2273316272949189786848077 852493602355946170068029)
      ·
        refine ⟨319685100883479813775511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 852493602355946170068029 319685100883479813775511)
        ·
          refine ⟨479527651325219720663267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319685100883479813775511 479527651325219720663267)
          ·
            refine ⟨719291476987829580994901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479527651325219720663267 719291476987829580994901)
            ·
              refine ⟨2107299248987781975571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 719291476987829580994901 2107299248987781975571)
              ·
                rfl

theorem cell21_83105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 10].length) (baseStart_83105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83105 prefixEnd_83105 := by exact prefixLift 83105
  have htrace : WordTrace (prefixWord ++ tailWord_83105) baseStart_83105 baseEnd_83105 := by
    simpa [prefixWord, tailWord_83105, baseEnd_83105] using wordTrace_append hprefix tailTrace_83105
  have hstable : (prefixWord ++ tailWord_83105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83105).length < 2 ^ (prefixWord ++ tailWord_83105).sum := by decide
  have hdescent : baseEnd_83105 < baseStart_83105 := by decide
  rcases family_descends (prefixWord ++ tailWord_83105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83108 : List Nat := [2, 3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_83108 : Nat := 118140960795 + 83108 * 2 ^ 59
def prefixEnd_83108 : Nat := 4983230072969 + 3 ^ 40 * 83108 * 2
def baseEnd_83108 : Nat := 18966377881762699230133

theorem tailTrace_83108 : CollatzResearch.WordTrace tailWord_83108 prefixEnd_83108 18966377881762699230133 := by
  unfold tailWord_83108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1515598891460692280744989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2020798521947589707659985 1515598891460692280744989)
  ·
    refine ⟨568349584297759605279371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1515598891460692280744989 568349584297759605279371)
    ·
      refine ⟨852524376446639407919057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568349584297759605279371 852524376446639407919057)
      ·
        refine ⟨639393282334979555939293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852524376446639407919057 639393282334979555939293)
        ·
          refine ⟨239772480875617333477235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639393282334979555939293 239772480875617333477235)
          ·
            refine ⟨359658721313426000215853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239772480875617333477235 359658721313426000215853)
            ·
              refine ⟨134872020492534750080945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359658721313426000215853 134872020492534750080945)
              ·
                refine ⟨101154015369401062560709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134872020492534750080945 101154015369401062560709)
                ·
                  refine ⟨18966377881762699230133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101154015369401062560709 18966377881762699230133)
                  ·
                    rfl

theorem cell21_83108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_83108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83108 prefixEnd_83108 := by exact prefixLift 83108
  have htrace : WordTrace (prefixWord ++ tailWord_83108) baseStart_83108 baseEnd_83108 := by
    simpa [prefixWord, tailWord_83108, baseEnd_83108] using wordTrace_append hprefix tailTrace_83108
  have hstable : (prefixWord ++ tailWord_83108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83108).length < 2 ^ (prefixWord ++ tailWord_83108).sum := by decide
  have hdescent : baseEnd_83108 < baseStart_83108 := by decide
  rcases family_descends (prefixWord ++ tailWord_83108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83156 : List Nat := [2, 4, 1, 4, 2, 1, 7]
def baseStart_83156 : Nat := 118140960795 + 83156 * 2 ^ 59
def prefixEnd_83156 : Nat := 4983230072969 + 3 ^ 40 * 83156 * 2
def baseEnd_83156 : Nat := 2108592459525031381115

theorem tailTrace_83156 : CollatzResearch.WordTrace tailWord_83156 prefixEnd_83156 2108592459525031381115 := by
  unfold tailWord_83156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516474243373744379618661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2021965657831659172824881 1516474243373744379618661)
  ·
    refine ⟨284338920632577071178499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1516474243373744379618661 284338920632577071178499)
    ·
      refine ⟨426508380948865606767749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284338920632577071178499 426508380948865606767749)
      ·
        refine ⟨79970321427912301268953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 426508380948865606767749 79970321427912301268953)
        ·
          refine ⟨59977741070934225951715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79970321427912301268953 59977741070934225951715)
          ·
            refine ⟨89966611606401338927573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59977741070934225951715 89966611606401338927573)
            ·
              refine ⟨2108592459525031381115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 89966611606401338927573 2108592459525031381115)
              ·
                rfl

theorem cell21_83156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 7].length) (baseStart_83156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83156 prefixEnd_83156 := by exact prefixLift 83156
  have htrace : WordTrace (prefixWord ++ tailWord_83156) baseStart_83156 baseEnd_83156 := by
    simpa [prefixWord, tailWord_83156, baseEnd_83156] using wordTrace_append hprefix tailTrace_83156
  have hstable : (prefixWord ++ tailWord_83156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83156).length < 2 ^ (prefixWord ++ tailWord_83156).sum := by decide
  have hdescent : baseEnd_83156 < baseStart_83156 := by decide
  rcases family_descends (prefixWord ++ tailWord_83156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83198 : List Nat := [4, 2, 2, 1, 1, 2, 2, 7]
def baseStart_83198 : Nat := 118140960795 + 83198 * 2 ^ 59
def prefixEnd_83198 : Nat := 4983230072969 + 3 ^ 40 * 83198 * 2
def baseEnd_83198 : Nat := 6328972369314180909983

theorem tailTrace_83198 : CollatzResearch.WordTrace tailWord_83198 prefixEnd_83198 6328972369314180909983 := by
  unfold tailWord_83198
  simp only [CollatzResearch.WordTrace]
  refine ⟨379310044074416241533281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2022986901730219954844165 379310044074416241533281)
  ·
    refine ⟨284482533055812181149961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379310044074416241533281 284482533055812181149961)
    ·
      refine ⟨213361899791859135862471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 284482533055812181149961 213361899791859135862471)
      ·
        refine ⟨320042849687788703793707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213361899791859135862471 320042849687788703793707)
        ·
          refine ⟨480064274531683055690561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320042849687788703793707 480064274531683055690561)
          ·
            refine ⟨360048205898762291767921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480064274531683055690561 360048205898762291767921)
            ·
              refine ⟨270036154424071718825941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360048205898762291767921 270036154424071718825941)
              ·
                refine ⟨6328972369314180909983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 270036154424071718825941 6328972369314180909983)
                ·
                  rfl

theorem cell21_83198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_83198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83198 prefixEnd_83198 := by exact prefixLift 83198
  have htrace : WordTrace (prefixWord ++ tailWord_83198) baseStart_83198 baseEnd_83198 := by
    simpa [prefixWord, tailWord_83198, baseEnd_83198] using wordTrace_append hprefix tailTrace_83198
  have hstable : (prefixWord ++ tailWord_83198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83198).length < 2 ^ (prefixWord ++ tailWord_83198).sum := by decide
  have hdescent : baseEnd_83198 < baseStart_83198 := by decide
  rcases family_descends (prefixWord ++ tailWord_83198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83218 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_83218 : Nat := 118140960795 + 83218 * 2 ^ 59
def prefixEnd_83218 : Nat := 4983230072969 + 3 ^ 40 * 83218 * 2
def baseEnd_83218 : Nat := 18991481380426952396575

theorem tailTrace_83218 : CollatzResearch.WordTrace tailWord_83218 prefixEnd_83218 18991481380426952396575 := by
  unfold tailWord_83218
  simp only [CollatzResearch.WordTrace]
  refine ⟨758802453130718336998577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2023473208348582231996205 758802453130718336998577)
  ·
    refine ⟨569101839848038752748933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 758802453130718336998577 569101839848038752748933)
    ·
      refine ⟨106706594971507266140425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 569101839848038752748933 106706594971507266140425)
      ·
        refine ⟨80029946228630449605319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106706594971507266140425 80029946228630449605319)
        ·
          refine ⟨120044919342945674407979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80029946228630449605319 120044919342945674407979)
          ·
            refine ⟨180067379014418511611969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120044919342945674407979 180067379014418511611969)
            ·
              refine ⟨135050534260813883708977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180067379014418511611969 135050534260813883708977)
              ·
                refine ⟨101287900695610412781733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135050534260813883708977 101287900695610412781733)
                ·
                  refine ⟨18991481380426952396575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101287900695610412781733 18991481380426952396575)
                  ·
                    rfl

theorem cell21_83218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_83218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83218 prefixEnd_83218 := by exact prefixLift 83218
  have htrace : WordTrace (prefixWord ++ tailWord_83218) baseStart_83218 baseEnd_83218 := by
    simpa [prefixWord, tailWord_83218, baseEnd_83218] using wordTrace_append hprefix tailTrace_83218
  have hstable : (prefixWord ++ tailWord_83218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83218).length < 2 ^ (prefixWord ++ tailWord_83218).sum := by decide
  have hdescent : baseEnd_83218 < baseStart_83218 := by decide
  rcases family_descends (prefixWord ++ tailWord_83218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83277 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_83277 : Nat := 118140960795 + 83277 * 2 ^ 59
def prefixEnd_83277 : Nat := 4983230072969 + 3 ^ 40 * 83277 * 2
def baseEnd_83277 : Nat := 19004945984255960913121

theorem tailTrace_83277 : CollatzResearch.WordTrace tailWord_83277 prefixEnd_83277 19004945984255960913121 := by
  unfold tailWord_83277
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037361719309126424392085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2024907812872750949594723 3037361719309126424392085)
  ·
    refine ⟨142376330592615301143379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3037361719309126424392085 142376330592615301143379)
    ·
      refine ⟨213564495888922951715069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142376330592615301143379 213564495888922951715069)
      ·
        refine ⟨80086685958346106893151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213564495888922951715069 80086685958346106893151)
        ·
          refine ⟨120130028937519160339727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80086685958346106893151 120130028937519160339727)
          ·
            refine ⟨180195043406278740509591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120130028937519160339727 180195043406278740509591)
            ·
              refine ⟨270292565109418110764387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180195043406278740509591 270292565109418110764387)
              ·
                refine ⟨405438847664127166146581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270292565109418110764387 405438847664127166146581)
                ·
                  refine ⟨19004945984255960913121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405438847664127166146581 19004945984255960913121)
                  ·
                    rfl

theorem cell21_83277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_83277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83277 prefixEnd_83277 := by exact prefixLift 83277
  have htrace : WordTrace (prefixWord ++ tailWord_83277) baseStart_83277 baseEnd_83277 := by
    simpa [prefixWord, tailWord_83277, baseEnd_83277] using wordTrace_append hprefix tailTrace_83277
  have hstable : (prefixWord ++ tailWord_83277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83277).length < 2 ^ (prefixWord ++ tailWord_83277).sum := by decide
  have hdescent : baseEnd_83277 < baseStart_83277 := by decide
  rcases family_descends (prefixWord ++ tailWord_83277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83288 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_83288 : Nat := 118140960795 + 83288 * 2 ^ 59
def prefixEnd_83288 : Nat := 4983230072969 + 3 ^ 40 * 83288 * 2
def baseEnd_83288 : Nat := 19007456334122386229765

theorem tailTrace_83288 : CollatzResearch.WordTrace tailWord_83288 prefixEnd_83288 19007456334122386229765 := by
  unfold tailWord_83288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518881461134637651521259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2025175281512850202028345 1518881461134637651521259)
  ·
    refine ⟨2278322191701956477281889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518881461134637651521259 2278322191701956477281889)
    ·
      refine ⟨1708741643776467357961417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2278322191701956477281889 1708741643776467357961417)
      ·
        refine ⟨1281556232832350518471063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1708741643776467357961417 1281556232832350518471063)
        ·
          refine ⟨1922334349248525777706595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1281556232832350518471063 1922334349248525777706595)
          ·
            refine ⟨2883501523872788666559893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1922334349248525777706595 2883501523872788666559893)
            ·
              refine ⟨135164133931536968744995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2883501523872788666559893 135164133931536968744995)
              ·
                refine ⟨202746200897305453117493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135164133931536968744995 202746200897305453117493)
                ·
                  refine ⟨19007456334122386229765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 202746200897305453117493 19007456334122386229765)
                  ·
                    rfl

theorem cell21_83288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_83288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83288 prefixEnd_83288 := by exact prefixLift 83288
  have htrace : WordTrace (prefixWord ++ tailWord_83288) baseStart_83288 baseEnd_83288 := by
    simpa [prefixWord, tailWord_83288, baseEnd_83288] using wordTrace_append hprefix tailTrace_83288
  have hstable : (prefixWord ++ tailWord_83288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83288).length < 2 ^ (prefixWord ++ tailWord_83288).sum := by decide
  have hdescent : baseEnd_83288 < baseStart_83288 := by decide
  rcases family_descends (prefixWord ++ tailWord_83288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83378 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_83378 : Nat := 118140960795 + 83378 * 2 ^ 59
def prefixEnd_83378 : Nat := 4983230072969 + 3 ^ 40 * 83378 * 2
def baseEnd_83378 : Nat := 19027995560302229729581

theorem tailTrace_83378 : CollatzResearch.WordTrace tailWord_83378 prefixEnd_83378 19027995560302229729581 := by
  unfold tailWord_83378
  simp only [CollatzResearch.WordTrace]
  refine ⟨760261372985805168454697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2027363661295480449212525 760261372985805168454697)
  ·
    refine ⟨570196029739353876341023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 760261372985805168454697 570196029739353876341023)
    ·
      refine ⟨855294044609030814511535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570196029739353876341023 855294044609030814511535)
      ·
        refine ⟨1282941066913546221767303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855294044609030814511535 1282941066913546221767303)
        ·
          refine ⟨1924411600370319332650955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1282941066913546221767303 1924411600370319332650955)
          ·
            refine ⟨2886617400555478998976433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924411600370319332650955 2886617400555478998976433)
            ·
              refine ⟨2164963050416609249232325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2886617400555478998976433 2164963050416609249232325)
              ·
                refine ⟨405930571953114234231061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2164963050416609249232325 405930571953114234231061)
                ·
                  refine ⟨19027995560302229729581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 405930571953114234231061 19027995560302229729581)
                  ·
                    rfl

theorem cell21_83378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_83378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83378 prefixEnd_83378 := by exact prefixLift 83378
  have htrace : WordTrace (prefixWord ++ tailWord_83378) baseStart_83378 baseEnd_83378 := by
    simpa [prefixWord, tailWord_83378, baseEnd_83378] using wordTrace_append hprefix tailTrace_83378
  have hstable : (prefixWord ++ tailWord_83378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83378).length < 2 ^ (prefixWord ++ tailWord_83378).sum := by decide
  have hdescent : baseEnd_83378 < baseStart_83378 := by decide
  rcases family_descends (prefixWord ++ tailWord_83378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83457 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_83457 : Nat := 118140960795 + 83457 * 2 ^ 59
def prefixEnd_83457 : Nat := 4983230072969 + 3 ^ 40 * 83457 * 2
def baseEnd_83457 : Nat := 19046024436615647912753

theorem tailTrace_83457 : CollatzResearch.WordTrace tailWord_83457 prefixEnd_83457 19046024436615647912753 := by
  unfold tailWord_83457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043926858657017165944625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2029284572438011443963083 3043926858657017165944625)
  ·
    refine ⟨2282945143992762874458469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3043926858657017165944625 2282945143992762874458469)
    ·
      refine ⟨428052214498643038960963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2282945143992762874458469 428052214498643038960963)
      ·
        refine ⟨642078321747964558441445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428052214498643038960963 642078321747964558441445)
        ·
          refine ⟨120389685327743354707771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 642078321747964558441445 120389685327743354707771)
          ·
            refine ⟨180584527991615032061657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120389685327743354707771 180584527991615032061657)
            ·
              refine ⟨135438395993711274046243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180584527991615032061657 135438395993711274046243)
              ·
                refine ⟨203157593990566911069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135438395993711274046243 203157593990566911069365)
                ·
                  refine ⟨19046024436615647912753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203157593990566911069365 19046024436615647912753)
                  ·
                    rfl

theorem cell21_83457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_83457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83457 prefixEnd_83457 := by exact prefixLift 83457
  have htrace : WordTrace (prefixWord ++ tailWord_83457) baseStart_83457 baseEnd_83457 := by
    simpa [prefixWord, tailWord_83457, baseEnd_83457] using wordTrace_append hprefix tailTrace_83457
  have hstable : (prefixWord ++ tailWord_83457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83457).length < 2 ^ (prefixWord ++ tailWord_83457).sum := by decide
  have hdescent : baseEnd_83457 < baseStart_83457 := by decide
  rcases family_descends (prefixWord ++ tailWord_83457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83485 : List Nat := [1, 4, 2, 2, 1, 1, 3, 7]
def baseStart_83485 : Nat := 118140960795 + 83485 * 2 ^ 59
def prefixEnd_83485 : Nat := 4983230072969 + 3 ^ 40 * 83485 * 2
def baseEnd_83485 : Nat := 6350804806031273815343

theorem tailTrace_83485 : CollatzResearch.WordTrace tailWord_83485 prefixEnd_83485 6350804806031273815343 := by
  unfold tailWord_83485
  simp only [CollatzResearch.WordTrace]
  refine ⟨3044948102555577947963909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2029965401703718631975939 3044948102555577947963909)
  ·
    refine ⟨570927769229170865243233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3044948102555577947963909 570927769229170865243233)
    ·
      refine ⟨428195826921878148932425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 570927769229170865243233 428195826921878148932425)
      ·
        refine ⟨321146870191408611699319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428195826921878148932425 321146870191408611699319)
        ·
          refine ⟨481720305287112917548979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321146870191408611699319 481720305287112917548979)
          ·
            refine ⟨722580457930669376323469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481720305287112917548979 722580457930669376323469)
            ·
              refine ⟨270967671724001016121301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722580457930669376323469 270967671724001016121301)
              ·
                refine ⟨6350804806031273815343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 270967671724001016121301 6350804806031273815343)
                ·
                  rfl

theorem cell21_83485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 7].length) (baseStart_83485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83485 prefixEnd_83485 := by exact prefixLift 83485
  have htrace : WordTrace (prefixWord ++ tailWord_83485) baseStart_83485 baseEnd_83485 := by
    simpa [prefixWord, tailWord_83485, baseEnd_83485] using wordTrace_append hprefix tailTrace_83485
  have hstable : (prefixWord ++ tailWord_83485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83485).length < 2 ^ (prefixWord ++ tailWord_83485).sum := by decide
  have hdescent : baseEnd_83485 < baseStart_83485 := by decide
  rcases family_descends (prefixWord ++ tailWord_83485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83491 : List Nat := [1, 1, 1, 4, 6, 1, 1, 3, 3]
def baseStart_83491 : Nat := 118140960795 + 83491 * 2 ^ 59
def prefixEnd_83491 : Nat := 4983230072969 + 3 ^ 40 * 83491 * 2
def baseEnd_83491 : Nat := 19053783699839144346017

theorem tailTrace_83491 : CollatzResearch.WordTrace tailWord_83491 prefixEnd_83491 19053783699839144346017 := by
  unfold tailWord_83491
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045166940533840972682327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2030111293689227315121551 3045166940533840972682327)
  ·
    refine ⟨4567750410800761459023491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3045166940533840972682327 4567750410800761459023491)
    ·
      refine ⟨6851625616201142188535237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4567750410800761459023491 6851625616201142188535237)
      ·
        refine ⟨1284679803037714160350357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6851625616201142188535237 1284679803037714160350357)
        ·
          refine ⟨60219365767392851266423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1284679803037714160350357 60219365767392851266423)
          ·
            refine ⟨90329048651089276899635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60219365767392851266423 90329048651089276899635)
            ·
              refine ⟨135493572976633915349453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90329048651089276899635 135493572976633915349453)
              ·
                refine ⟨50810089866237718256045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 135493572976633915349453 50810089866237718256045)
                ·
                  refine ⟨19053783699839144346017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50810089866237718256045 19053783699839144346017)
                  ·
                    rfl

theorem cell21_83491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 3, 3].length) (baseStart_83491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83491 prefixEnd_83491 := by exact prefixLift 83491
  have htrace : WordTrace (prefixWord ++ tailWord_83491) baseStart_83491 baseEnd_83491 := by
    simpa [prefixWord, tailWord_83491, baseEnd_83491] using wordTrace_append hprefix tailTrace_83491
  have hstable : (prefixWord ++ tailWord_83491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83491).length < 2 ^ (prefixWord ++ tailWord_83491).sum := by decide
  have hdescent : baseEnd_83491 < baseStart_83491 := by decide
  rcases family_descends (prefixWord ++ tailWord_83491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83502 : List Nat := [4, 1, 3, 1, 2, 3, 7]
def baseStart_83502 : Nat := 118140960795 + 83502 * 2 ^ 59
def prefixEnd_83502 : Nat := 4983230072969 + 3 ^ 40 * 83502 * 2
def baseEnd_83502 : Nat := 2117366005522841073629

theorem tailTrace_83502 : CollatzResearch.WordTrace tailWord_83502 prefixEnd_83502 2117366005522841073629 := by
  unfold tailWord_83502
  simp only [CollatzResearch.WordTrace]
  refine ⟨380696017936748731416595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2030378762329326567555173 380696017936748731416595)
  ·
    refine ⟨571044026905123097124893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380696017936748731416595 571044026905123097124893)
    ·
      refine ⟨214141510089421161421835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 571044026905123097124893 214141510089421161421835)
      ·
        refine ⟨321212265134131742132753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214141510089421161421835 321212265134131742132753)
        ·
          refine ⟨240909198850598806599565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321212265134131742132753 240909198850598806599565)
          ·
            refine ⟨90340949568974552474837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 240909198850598806599565 90340949568974552474837)
            ·
              refine ⟨2117366005522841073629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 90340949568974552474837 2117366005522841073629)
              ·
                rfl

theorem cell21_83502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 7].length) (baseStart_83502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83502 prefixEnd_83502 := by exact prefixLift 83502
  have htrace : WordTrace (prefixWord ++ tailWord_83502) baseStart_83502 baseEnd_83502 := by
    simpa [prefixWord, tailWord_83502, baseEnd_83502] using wordTrace_append hprefix tailTrace_83502
  have hstable : (prefixWord ++ tailWord_83502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83502).length < 2 ^ (prefixWord ++ tailWord_83502).sum := by decide
  have hdescent : baseEnd_83502 < baseStart_83502 := by decide
  rcases family_descends (prefixWord ++ tailWord_83502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83575 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 5]
def baseStart_83575 : Nat := 118140960795 + 83575 * 2 ^ 59
def prefixEnd_83575 : Nat := 4983230072969 + 3 ^ 40 * 83575 * 2
def baseEnd_83575 : Nat := 19072953644273664945845

theorem tailTrace_83575 : CollatzResearch.WordTrace tailWord_83575 prefixEnd_83575 19072953644273664945845 := by
  unfold tailWord_83575
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048230672229523318740179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2032153781486348879160119 3048230672229523318740179)
  ·
    refine ⟨4572346008344284978110269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048230672229523318740179 4572346008344284978110269)
    ·
      refine ⟨1714629753129106866791351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4572346008344284978110269 1714629753129106866791351)
      ·
        refine ⟨2571944629693660300187027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1714629753129106866791351 2571944629693660300187027)
        ·
          refine ⟨3857916944540490450280541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571944629693660300187027 3857916944540490450280541)
          ·
            refine ⟨1446718854202683918855203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3857916944540490450280541 1446718854202683918855203)
            ·
              refine ⟨2170078281304025878282805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1446718854202683918855203 2170078281304025878282805)
              ·
                refine ⟨203444838872252426089013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2170078281304025878282805 203444838872252426089013)
                ·
                  refine ⟨19072953644273664945845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 203444838872252426089013 19072953644273664945845)
                  ·
                    rfl

theorem cell21_83575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 5].length) (baseStart_83575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83575 prefixEnd_83575 := by exact prefixLift 83575
  have htrace : WordTrace (prefixWord ++ tailWord_83575) baseStart_83575 baseEnd_83575 := by
    simpa [prefixWord, tailWord_83575, baseEnd_83575] using wordTrace_append hprefix tailTrace_83575
  have hstable : (prefixWord ++ tailWord_83575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83575).length < 2 ^ (prefixWord ++ tailWord_83575).sum := by decide
  have hdescent : baseEnd_83575 < baseStart_83575 := by decide
  rcases family_descends (prefixWord ++ tailWord_83575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83699 : List Nat := [1, 1, 1, 2, 2, 3, 6, 1, 4]
def baseStart_83699 : Nat := 118140960795 + 83699 * 2 ^ 59
def prefixEnd_83699 : Nat := 4983230072969 + 3 ^ 40 * 83699 * 2
def baseEnd_83699 : Nat := 19101252133677004878925

theorem tailTrace_83699 : CollatzResearch.WordTrace tailWord_83699 prefixEnd_83699 19101252133677004878925 := by
  unfold tailWord_83699
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052753323780292496254151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035168882520194997502767 3052753323780292496254151)
  ·
    refine ⟨4579129985670438744381227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3052753323780292496254151 4579129985670438744381227)
    ·
      refine ⟨6868694978505658116571841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4579129985670438744381227 6868694978505658116571841)
      ·
        refine ⟨5151521233879243587428881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6868694978505658116571841 5151521233879243587428881)
        ·
          refine ⟨3863640925409432690571661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5151521233879243587428881 3863640925409432690571661)
          ·
            refine ⟨1448865347028537258964373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3863640925409432690571661 1448865347028537258964373)
            ·
              refine ⟨67915563141962684013955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1448865347028537258964373 67915563141962684013955)
              ·
                refine ⟨101873344712944026020933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67915563141962684013955 101873344712944026020933)
                ·
                  refine ⟨19101252133677004878925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101873344712944026020933 19101252133677004878925)
                  ·
                    rfl

theorem cell21_83699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6, 1, 4].length) (baseStart_83699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83699 prefixEnd_83699 := by exact prefixLift 83699
  have htrace : WordTrace (prefixWord ++ tailWord_83699) baseStart_83699 baseEnd_83699 := by
    simpa [prefixWord, tailWord_83699, baseEnd_83699] using wordTrace_append hprefix tailTrace_83699
  have hstable : (prefixWord ++ tailWord_83699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83699).length < 2 ^ (prefixWord ++ tailWord_83699).sum := by decide
  have hdescent : baseEnd_83699 < baseStart_83699 := by decide
  rcases family_descends (prefixWord ++ tailWord_83699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83772 : List Nat := [2, 2, 2, 2, 1, 1, 2, 9]
def baseStart_83772 : Nat := 118140960795 + 83772 * 2 ^ 59
def prefixEnd_83772 : Nat := 4983230072969 + 3 ^ 40 * 83772 * 2
def baseEnd_83772 : Nat := 6372637242748366720703

theorem tailTrace_83772 : CollatzResearch.WordTrace tailWord_83772 prefixEnd_83772 6372637242748366720703 := by
  unfold tailWord_83772
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527707926257912981830785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2036943901677217309107713 1527707926257912981830785)
  ·
    refine ⟨1145780944693434736373089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1527707926257912981830785 1145780944693434736373089)
    ·
      refine ⟨859335708520076052279817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1145780944693434736373089 859335708520076052279817)
      ·
        refine ⟨644501781390057039209863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 859335708520076052279817 644501781390057039209863)
        ·
          refine ⟨966752672085085558814795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644501781390057039209863 966752672085085558814795)
          ·
            refine ⟨1450129008127628338222193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 966752672085085558814795 1450129008127628338222193)
            ·
              refine ⟨1087596756095721253666645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1450129008127628338222193 1087596756095721253666645)
              ·
                refine ⟨6372637242748366720703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1087596756095721253666645 6372637242748366720703)
                ·
                  rfl

theorem cell21_83772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_83772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83772 prefixEnd_83772 := by exact prefixLift 83772
  have htrace : WordTrace (prefixWord ++ tailWord_83772) baseStart_83772 baseEnd_83772 := by
    simpa [prefixWord, tailWord_83772, baseEnd_83772] using wordTrace_append hprefix tailTrace_83772
  have hstable : (prefixWord ++ tailWord_83772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83772).length < 2 ^ (prefixWord ++ tailWord_83772).sum := by decide
  have hdescent : baseEnd_83772 < baseStart_83772 := by decide
  rcases family_descends (prefixWord ++ tailWord_83772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83854 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_83854 : Nat := 118140960795 + 83854 * 2 ^ 59
def prefixEnd_83854 : Nat := 4983230072969 + 3 ^ 40 * 83854 * 2
def baseEnd_83854 : Nat := 19136625245431179795275

theorem tailTrace_83854 : CollatzResearch.WordTrace tailWord_83854 prefixEnd_83854 19136625245431179795275 := by
  unfold tailWord_83854
  simp only [CollatzResearch.WordTrace]
  refine ⟨382300829777344246018327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2038937758812502645431077 382300829777344246018327)
  ·
    refine ⟨573451244666016369027491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 382300829777344246018327 573451244666016369027491)
    ·
      refine ⟨860176866999024553541237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573451244666016369027491 860176866999024553541237)
      ·
        refine ⟨80641581281158551894491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 860176866999024553541237 80641581281158551894491)
        ·
          refine ⟨120962371921737827841737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80641581281158551894491 120962371921737827841737)
          ·
            refine ⟨90721778941303370881303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120962371921737827841737 90721778941303370881303)
            ·
              refine ⟨136082668411955056321955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90721778941303370881303 136082668411955056321955)
              ·
                refine ⟨204124002617932584482933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136082668411955056321955 204124002617932584482933)
                ·
                  refine ⟨19136625245431179795275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204124002617932584482933 19136625245431179795275)
                  ·
                    rfl

theorem cell21_83854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_83854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83854 prefixEnd_83854 := by exact prefixLift 83854
  have htrace : WordTrace (prefixWord ++ tailWord_83854) baseStart_83854 baseEnd_83854 := by
    simpa [prefixWord, tailWord_83854, baseEnd_83854] using wordTrace_append hprefix tailTrace_83854
  have hstable : (prefixWord ++ tailWord_83854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83854).length < 2 ^ (prefixWord ++ tailWord_83854).sum := by decide
  have hdescent : baseEnd_83854 < baseStart_83854 := by decide
  rcases family_descends (prefixWord ++ tailWord_83854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83868 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_83868 : Nat := 118140960795 + 83868 * 2 ^ 59
def prefixEnd_83868 : Nat := 4983230072969 + 3 ^ 40 * 83868 * 2
def baseEnd_83868 : Nat := 19139820236170266561913

theorem tailTrace_83868 : CollatzResearch.WordTrace tailWord_83868 prefixEnd_83868 19139820236170266561913 := by
  unfold tailWord_83868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529458630084017179578129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2039278173445356239437505 1529458630084017179578129)
  ·
    refine ⟨1147093972563012884683597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1529458630084017179578129 1147093972563012884683597)
    ·
      refine ⟨430160239711129831756349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1147093972563012884683597 430160239711129831756349)
      ·
        refine ⟨161310089891673686908631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 430160239711129831756349 161310089891673686908631)
        ·
          refine ⟨241965134837510530362947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161310089891673686908631 241965134837510530362947)
          ·
            refine ⟨362947702256265795544421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241965134837510530362947 362947702256265795544421)
            ·
              refine ⟨68052694173049836664579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362947702256265795544421 68052694173049836664579)
              ·
                refine ⟨102079041259574754996869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68052694173049836664579 102079041259574754996869)
                ·
                  refine ⟨19139820236170266561913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102079041259574754996869 19139820236170266561913)
                  ·
                    rfl

theorem cell21_83868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_83868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83868 prefixEnd_83868 := by exact prefixLift 83868
  have htrace : WordTrace (prefixWord ++ tailWord_83868) baseStart_83868 baseEnd_83868 := by
    simpa [prefixWord, tailWord_83868, baseEnd_83868] using wordTrace_append hprefix tailTrace_83868
  have hstable : (prefixWord ++ tailWord_83868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83868).length < 2 ^ (prefixWord ++ tailWord_83868).sum := by decide
  have hdescent : baseEnd_83868 < baseStart_83868 := by decide
  rcases family_descends (prefixWord ++ tailWord_83868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83896 : List Nat := [2, 1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_83896 : Nat := 118140960795 + 83896 * 2 ^ 59
def prefixEnd_83896 : Nat := 4983230072969 + 3 ^ 40 * 83896 * 2
def baseEnd_83896 : Nat := 19146210217648440095189

theorem tailTrace_83896 : CollatzResearch.WordTrace tailWord_83896 prefixEnd_83896 19146210217648440095189 := by
  unfold tailWord_83896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529969252033297570587771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2039959002711063427450361 1529969252033297570587771)
  ·
    refine ⟨2294953878049946355881657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529969252033297570587771 2294953878049946355881657)
    ·
      refine ⟨1721215408537459766911243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2294953878049946355881657 1721215408537459766911243)
      ·
        refine ⟨2581823112806189650366865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1721215408537459766911243 2581823112806189650366865)
        ·
          refine ⟨1936367334604642237775149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581823112806189650366865 1936367334604642237775149)
          ·
            refine ⟨726137750476740839165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1936367334604642237775149 726137750476740839165681)
            ·
              refine ⟨544603312857555629374261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 726137750476740839165681 544603312857555629374261)
              ·
                refine ⟨51056560580395840253837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 544603312857555629374261 51056560580395840253837)
                ·
                  refine ⟨19146210217648440095189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51056560580395840253837 19146210217648440095189)
                  ·
                    rfl

theorem cell21_83896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_83896 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_83896 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_83896 prefixEnd_83896 := by exact prefixLift 83896
  have htrace : WordTrace (prefixWord ++ tailWord_83896) baseStart_83896 baseEnd_83896 := by
    simpa [prefixWord, tailWord_83896, baseEnd_83896] using wordTrace_append hprefix tailTrace_83896
  have hstable : (prefixWord ++ tailWord_83896).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83896).length < 2 ^ (prefixWord ++ tailWord_83896).sum := by decide
  have hdescent : baseEnd_83896 < baseStart_83896 := by decide
  rcases family_descends (prefixWord ++ tailWord_83896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84031 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 5]
def baseStart_84031 : Nat := 118140960795 + 84031 * 2 ^ 59
def prefixEnd_84031 : Nat := 4983230072969 + 3 ^ 40 * 84031 * 2
def baseEnd_84031 : Nat := 19177019056918205344913

theorem tailTrace_84031 : CollatzResearch.WordTrace tailWord_84031 prefixEnd_84031 19177019056918205344913 := by
  unfold tailWord_84031
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064862358577513197339947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2043241572385008798226631 3064862358577513197339947)
  ·
    refine ⟨4597293537866269796009921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064862358577513197339947 4597293537866269796009921)
    ·
      refine ⟨3447970153399702347007441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4597293537866269796009921 3447970153399702347007441)
      ·
        refine ⟨2585977615049776760255581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3447970153399702347007441 2585977615049776760255581)
        ·
          refine ⟨969741605643666285095843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2585977615049776760255581 969741605643666285095843)
          ·
            refine ⟨1454612408465499427643765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969741605643666285095843 1454612408465499427643765)
            ·
              refine ⟨136369913293640571341603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1454612408465499427643765 136369913293640571341603)
              ·
                refine ⟨204554869940460857012405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136369913293640571341603 204554869940460857012405)
                ·
                  refine ⟨19177019056918205344913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204554869940460857012405 19177019056918205344913)
                  ·
                    rfl

theorem cell21_84031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 5].length) (baseStart_84031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84031 prefixEnd_84031 := by exact prefixLift 84031
  have htrace : WordTrace (prefixWord ++ tailWord_84031) baseStart_84031 baseEnd_84031 := by
    simpa [prefixWord, tailWord_84031, baseEnd_84031] using wordTrace_append hprefix tailTrace_84031
  have hstable : (prefixWord ++ tailWord_84031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84031).length < 2 ^ (prefixWord ++ tailWord_84031).sum := by decide
  have hdescent : baseEnd_84031 < baseStart_84031 := by decide
  rcases family_descends (prefixWord ++ tailWord_84031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84082 : List Nat := [3, 2, 1, 2, 2, 4, 2, 2, 3]
def baseStart_84082 : Nat := 118140960795 + 84082 * 2 ^ 59
def prefixEnd_84082 : Nat := 4983230072969 + 3 ^ 40 * 84082 * 2
def baseEnd_84082 : Nat := 19188657951753449994809

theorem tailTrace_84082 : CollatzResearch.WordTrace tailWord_84082 prefixEnd_84082 19188657951753449994809 := by
  unfold tailWord_84082
  simp only [CollatzResearch.WordTrace]
  refine ⟨766680620348187226861625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2044481654261832604964333 766680620348187226861625)
  ·
    refine ⟨575010465261140420146219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 766680620348187226861625 575010465261140420146219)
    ·
      refine ⟨862515697891710630219329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575010465261140420146219 862515697891710630219329)
      ·
        refine ⟨646886773418782972664497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862515697891710630219329 646886773418782972664497)
        ·
          refine ⟨485165080064087229498373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646886773418782972664497 485165080064087229498373)
          ·
            refine ⟨90968452512016355530945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485165080064087229498373 90968452512016355530945)
            ·
              refine ⟨68226339384012266648209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90968452512016355530945 68226339384012266648209)
              ·
                refine ⟨51169754538009199986157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68226339384012266648209 51169754538009199986157)
                ·
                  refine ⟨19188657951753449994809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51169754538009199986157 19188657951753449994809)
                  ·
                    rfl

theorem cell21_84082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_84082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84082 prefixEnd_84082 := by exact prefixLift 84082
  have htrace : WordTrace (prefixWord ++ tailWord_84082) baseStart_84082 baseEnd_84082 := by
    simpa [prefixWord, tailWord_84082, baseEnd_84082] using wordTrace_append hprefix tailTrace_84082
  have hstable : (prefixWord ++ tailWord_84082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84082).length < 2 ^ (prefixWord ++ tailWord_84082).sum := by decide
  have hdescent : baseEnd_84082 < baseStart_84082 := by decide
  rcases family_descends (prefixWord ++ tailWord_84082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84090 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_84090 : Nat := 118140960795 + 84090 * 2 ^ 59
def prefixEnd_84090 : Nat := 4983230072969 + 3 ^ 40 * 84090 * 2
def baseEnd_84090 : Nat := 19190483660747213861459

theorem tailTrace_84090 : CollatzResearch.WordTrace tailWord_84090 prefixEnd_84090 19190483660747213861459 := by
  unfold tailWord_84090
  simp only [CollatzResearch.WordTrace]
  refine ⟨766753566340941568434431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2044676176909177515825149 766753566340941568434431)
  ·
    refine ⟨1150130349511412352651647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766753566340941568434431 1150130349511412352651647)
    ·
      refine ⟨1725195524267118528977471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150130349511412352651647 1725195524267118528977471)
      ·
        refine ⟨2587793286400677793466207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725195524267118528977471 2587793286400677793466207)
        ·
          refine ⟨3881689929601016690199311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2587793286400677793466207 3881689929601016690199311)
          ·
            refine ⟨5822534894401525035298967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3881689929601016690199311 5822534894401525035298967)
            ·
              refine ⟨8733802341602287552948451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5822534894401525035298967 8733802341602287552948451)
              ·
                refine ⟨13100703512403431329422677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8733802341602287552948451 13100703512403431329422677)
                ·
                  refine ⟨19190483660747213861459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 13100703512403431329422677 19190483660747213861459)
                  ·
                    rfl

theorem cell21_84090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_84090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84090 prefixEnd_84090 := by exact prefixLift 84090
  have htrace : WordTrace (prefixWord ++ tailWord_84090) baseStart_84090 baseEnd_84090 := by
    simpa [prefixWord, tailWord_84090, baseEnd_84090] using wordTrace_append hprefix tailTrace_84090
  have hstable : (prefixWord ++ tailWord_84090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84090).length < 2 ^ (prefixWord ++ tailWord_84090).sum := by decide
  have hdescent : baseEnd_84090 < baseStart_84090 := by decide
  rcases family_descends (prefixWord ++ tailWord_84090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84093 : List Nat := [1, 4, 1, 1, 3, 4, 1, 6]
def baseStart_84093 : Nat := 118140960795 + 84093 * 2 ^ 59
def prefixEnd_84093 : Nat := 4983230072969 + 3 ^ 40 * 84093 * 2
def baseEnd_84093 : Nat := 6397056100539958437151

theorem tailTrace_84093 : CollatzResearch.WordTrace tailWord_84093 prefixEnd_84093 6397056100539958437151 := by
  unfold tailWord_84093
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067123684352897786096933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2044749122901931857397955 3067123684352897786096933)
  ·
    refine ⟨575085690816168334893175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3067123684352897786096933 575085690816168334893175)
    ·
      refine ⟨862628536224252502339763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575085690816168334893175 862628536224252502339763)
      ·
        refine ⟨1293942804336378753509645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 862628536224252502339763 1293942804336378753509645)
        ·
          refine ⟨485228551626142032566117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1293942804336378753509645 485228551626142032566117)
          ·
            refine ⟨90980353429901631106147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485228551626142032566117 90980353429901631106147)
            ·
              refine ⟨136470530144852446659221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90980353429901631106147 136470530144852446659221)
              ·
                refine ⟨6397056100539958437151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136470530144852446659221 6397056100539958437151)
                ·
                  rfl

theorem cell21_84093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_84093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84093 prefixEnd_84093 := by exact prefixLift 84093
  have htrace : WordTrace (prefixWord ++ tailWord_84093) baseStart_84093 baseEnd_84093 := by
    simpa [prefixWord, tailWord_84093, baseEnd_84093] using wordTrace_append hprefix tailTrace_84093
  have hstable : (prefixWord ++ tailWord_84093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84093).length < 2 ^ (prefixWord ++ tailWord_84093).sum := by decide
  have hdescent : baseEnd_84093 < baseStart_84093 := by decide
  rcases family_descends (prefixWord ++ tailWord_84093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84110 : List Nat := [4, 1, 1, 3, 3, 1, 3, 5]
def baseStart_84110 : Nat := 118140960795 + 84110 * 2 ^ 59
def prefixEnd_84110 : Nat := 4983230072969 + 3 ^ 40 * 84110 * 2
def baseEnd_84110 : Nat := 6398349311077207842695

theorem tailTrace_84110 : CollatzResearch.WordTrace tailWord_84110 prefixEnd_84110 6398349311077207842695 := by
  unfold tailWord_84110
  simp only [CollatzResearch.WordTrace]
  refine ⟨383467965661413711183223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2045162483527539792977189 383467965661413711183223)
  ·
    refine ⟨575201948492120566774835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 383467965661413711183223 575201948492120566774835)
    ·
      refine ⟨862802922738180850162253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575201948492120566774835 862802922738180850162253)
      ·
        refine ⟨323551096026817818810845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 862802922738180850162253 323551096026817818810845)
        ·
          refine ⟨121331661010056682054067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323551096026817818810845 121331661010056682054067)
          ·
            refine ⟨181997491515085023081101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121331661010056682054067 181997491515085023081101)
            ·
              refine ⟨68249059318156883655413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181997491515085023081101 68249059318156883655413)
              ·
                refine ⟨6398349311077207842695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68249059318156883655413 6398349311077207842695)
                ·
                  rfl

theorem cell21_84110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_84110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84110 prefixEnd_84110 := by exact prefixLift 84110
  have htrace : WordTrace (prefixWord ++ tailWord_84110) baseStart_84110 baseEnd_84110 := by
    simpa [prefixWord, tailWord_84110, baseEnd_84110] using wordTrace_append hprefix tailTrace_84110
  have hstable : (prefixWord ++ tailWord_84110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84110).length < 2 ^ (prefixWord ++ tailWord_84110).sum := by decide
  have hdescent : baseEnd_84110 < baseStart_84110 := by decide
  rcases family_descends (prefixWord ++ tailWord_84110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84141 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 3]
def baseStart_84141 : Nat := 118140960795 + 84141 * 2 ^ 59
def prefixEnd_84141 : Nat := 4983230072969 + 3 ^ 40 * 84141 * 2
def baseEnd_84141 : Nat := 19202122555582458511355

theorem tailTrace_84141 : CollatzResearch.WordTrace tailWord_84141 prefixEnd_84141 19202122555582458511355 := by
  unfold tailWord_84141
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068874388179001983844277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2045916258786001322562851 3068874388179001983844277)
  ·
    refine ⟨287706973891781435985401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3068874388179001983844277 287706973891781435985401)
    ·
      refine ⟨215780230418836076989051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287706973891781435985401 215780230418836076989051)
      ·
        refine ⟨323670345628254115483577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215780230418836076989051 323670345628254115483577)
        ·
          refine ⟨242752759221190586612683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323670345628254115483577 242752759221190586612683)
          ·
            refine ⟨364129138831785879919025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242752759221190586612683 364129138831785879919025)
            ·
              refine ⟨273096854123839409939269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364129138831785879919025 273096854123839409939269)
              ·
                refine ⟨51205660148219889363613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273096854123839409939269 51205660148219889363613)
                ·
                  refine ⟨19202122555582458511355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51205660148219889363613 19202122555582458511355)
                  ·
                    rfl

theorem cell21_84141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_84141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84141 prefixEnd_84141 := by exact prefixLift 84141
  have htrace : WordTrace (prefixWord ++ tailWord_84141) baseStart_84141 baseEnd_84141 := by
    simpa [prefixWord, tailWord_84141, baseEnd_84141] using wordTrace_append hprefix tailTrace_84141
  have hstable : (prefixWord ++ tailWord_84141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84141).length < 2 ^ (prefixWord ++ tailWord_84141).sum := by decide
  have hdescent : baseEnd_84141 < baseStart_84141 := by decide
  rcases family_descends (prefixWord ++ tailWord_84141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84200 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_84200 : Nat := 118140960795 + 84200 * 2 ^ 59
def prefixEnd_84200 : Nat := 4983230072969 + 3 ^ 40 * 84200 * 2
def baseEnd_84200 : Nat := 19215587159411467027901

theorem tailTrace_84200 : CollatzResearch.WordTrace tailWord_84200 prefixEnd_84200 19215587159411467027901 := by
  unfold tailWord_84200
  simp only [CollatzResearch.WordTrace]
  refine ⟨1535513147482627530121027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2047350863310170040161369 1535513147482627530121027)
  ·
    refine ⟨2303269721223941295181541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1535513147482627530121027 2303269721223941295181541)
    ·
      refine ⟨431863072729488992846539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2303269721223941295181541 431863072729488992846539)
      ·
        refine ⟨647794609094233489269809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431863072729488992846539 647794609094233489269809)
        ·
          refine ⟨485845956820675116952357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 647794609094233489269809 485845956820675116952357)
          ·
            refine ⟨91096116903876584428567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 485845956820675116952357 91096116903876584428567)
            ·
              refine ⟨136644175355814876642851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91096116903876584428567 136644175355814876642851)
              ·
                refine ⟨204966263033722314964277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136644175355814876642851 204966263033722314964277)
                ·
                  refine ⟨19215587159411467027901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 204966263033722314964277 19215587159411467027901)
                  ·
                    rfl

theorem cell21_84200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_84200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84200 prefixEnd_84200 := by exact prefixLift 84200
  have htrace : WordTrace (prefixWord ++ tailWord_84200) baseStart_84200 baseEnd_84200 := by
    simpa [prefixWord, tailWord_84200, baseEnd_84200] using wordTrace_append hprefix tailTrace_84200
  have hstable : (prefixWord ++ tailWord_84200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84200).length < 2 ^ (prefixWord ++ tailWord_84200).sum := by decide
  have hdescent : baseEnd_84200 < baseStart_84200 := by decide
  rcases family_descends (prefixWord ++ tailWord_84200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84276 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_84276 : Nat := 118140960795 + 84276 * 2 ^ 59
def prefixEnd_84276 : Nat := 4983230072969 + 3 ^ 40 * 84276 * 2
def baseEnd_84276 : Nat := 19232931394852223761079

theorem tailTrace_84276 : CollatzResearch.WordTrace tailWord_84276 prefixEnd_84276 19232931394852223761079 := by
  unfold tailWord_84276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536899121344960020004341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2049198828459946693339121 1536899121344960020004341)
  ·
    refine ⟨144084292626090001875407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1536899121344960020004341 144084292626090001875407)
    ·
      refine ⟨216126438939135002813111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144084292626090001875407 216126438939135002813111)
      ·
        refine ⟨324189658408702504219667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216126438939135002813111 324189658408702504219667)
        ·
          refine ⟨486284487613053756329501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324189658408702504219667 486284487613053756329501)
          ·
            refine ⟨182356682854895158623563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 486284487613053756329501 182356682854895158623563)
            ·
              refine ⟨273535024282342737935345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182356682854895158623563 273535024282342737935345)
              ·
                refine ⟨205151268211757053451509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273535024282342737935345 205151268211757053451509)
                ·
                  refine ⟨19232931394852223761079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 205151268211757053451509 19232931394852223761079)
                  ·
                    rfl

theorem cell21_84276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_84276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84276 prefixEnd_84276 := by exact prefixLift 84276
  have htrace : WordTrace (prefixWord ++ tailWord_84276) baseStart_84276 baseEnd_84276 := by
    simpa [prefixWord, tailWord_84276, baseEnd_84276] using wordTrace_append hprefix tailTrace_84276
  have hstable : (prefixWord ++ tailWord_84276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84276).length < 2 ^ (prefixWord ++ tailWord_84276).sum := by decide
  have hdescent : baseEnd_84276 < baseStart_84276 := by decide
  rcases family_descends (prefixWord ++ tailWord_84276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84349 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 6]
def baseStart_84349 : Nat := 118140960795 + 84349 * 2 ^ 59
def prefixEnd_84349 : Nat := 4983230072969 + 3 ^ 40 * 84349 * 2
def baseEnd_84349 : Nat := 19249590989420319044263

theorem tailTrace_84349 : CollatzResearch.WordTrace tailWord_84349 prefixEnd_84349 19249590989420319044263 := by
  unfold tailWord_84349
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076460771425453507416101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050973847616969004944067 3076460771425453507416101)
  ·
    refine ⟨576836394642272532640519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3076460771425453507416101 576836394642272532640519)
    ·
      refine ⟨865254591963408798960779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576836394642272532640519 865254591963408798960779)
      ·
        refine ⟨1297881887945113198441169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 865254591963408798960779 1297881887945113198441169)
        ·
          refine ⟨973411415958834898830877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297881887945113198441169 973411415958834898830877)
          ·
            refine ⟨365029280984563087061579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 973411415958834898830877 365029280984563087061579)
            ·
              refine ⟨547543921476844630592369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365029280984563087061579 547543921476844630592369)
              ·
                refine ⟨410657941107633472944277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 547543921476844630592369 410657941107633472944277)
                ·
                  refine ⟨19249590989420319044263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 410657941107633472944277 19249590989420319044263)
                  ·
                    rfl

theorem cell21_84349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_84349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84349 prefixEnd_84349 := by exact prefixLift 84349
  have htrace : WordTrace (prefixWord ++ tailWord_84349) baseStart_84349 baseEnd_84349 := by
    simpa [prefixWord, tailWord_84349, baseEnd_84349] using wordTrace_append hprefix tailTrace_84349
  have hstable : (prefixWord ++ tailWord_84349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84349).length < 2 ^ (prefixWord ++ tailWord_84349).sum := by decide
  have hdescent : baseEnd_84349 < baseStart_84349 := by decide
  rcases family_descends (prefixWord ++ tailWord_84349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84363 : List Nat := [1, 1, 1, 1, 4, 4, 9]
def baseStart_84363 : Nat := 118140960795 + 84363 * 2 ^ 59
def prefixEnd_84363 : Nat := 4983230072969 + 3 ^ 40 * 84363 * 2
def baseEnd_84363 : Nat := 2139198442239933978989

theorem tailTrace_84363 : CollatzResearch.WordTrace tailWord_84363 prefixEnd_84363 2139198442239933978989 := by
  unfold tailWord_84363
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076971393374733898425743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2051314262249822598950495 3076971393374733898425743)
  ·
    refine ⟨4615457090062100847638615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076971393374733898425743 4615457090062100847638615)
    ·
      refine ⟨6923185635093151271457923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615457090062100847638615 6923185635093151271457923)
      ·
        refine ⟨10384778452639726907186885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923185635093151271457923 10384778452639726907186885)
        ·
          refine ⟨1947145959869948795097541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10384778452639726907186885 1947145959869948795097541)
          ·
            refine ⟨365089867475615399080789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1947145959869948795097541 365089867475615399080789)
            ·
              refine ⟨2139198442239933978989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 365089867475615399080789 2139198442239933978989)
              ·
                rfl

theorem cell21_84363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_84363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84363 prefixEnd_84363 := by exact prefixLift 84363
  have htrace : WordTrace (prefixWord ++ tailWord_84363) baseStart_84363 baseEnd_84363 := by
    simpa [prefixWord, tailWord_84363, baseEnd_84363] using wordTrace_append hprefix tailTrace_84363
  have hstable : (prefixWord ++ tailWord_84363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84363).length < 2 ^ (prefixWord ++ tailWord_84363).sum := by decide
  have hdescent : baseEnd_84363 < baseStart_84363 := by decide
  rcases family_descends (prefixWord ++ tailWord_84363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84366 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_84366 : Nat := 118140960795 + 84366 * 2 ^ 59
def prefixEnd_84366 : Nat := 4983230072969 + 3 ^ 40 * 84366 * 2
def baseEnd_84366 : Nat := 19253470621032067260895

theorem tailTrace_84366 : CollatzResearch.WordTrace tailWord_84366 prefixEnd_84366 19253470621032067260895 := by
  unfold tailWord_84366
  simp only [CollatzResearch.WordTrace]
  refine ⟨384635101545483176348119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2051387208242576940523301 384635101545483176348119)
  ·
    refine ⟨576952652318224764522179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384635101545483176348119 576952652318224764522179)
    ·
      refine ⟨865428978477337146783269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576952652318224764522179 865428978477337146783269)
      ·
        refine ⟨162267933464500715021863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 865428978477337146783269 162267933464500715021863)
        ·
          refine ⟨243401900196751072532795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162267933464500715021863 243401900196751072532795)
          ·
            refine ⟨365102850295126608799193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243401900196751072532795 365102850295126608799193)
            ·
              refine ⟨273827137721344956599395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365102850295126608799193 273827137721344956599395)
              ·
                refine ⟨410740706582017434899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273827137721344956599395 410740706582017434899093)
                ·
                  refine ⟨19253470621032067260895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 410740706582017434899093 19253470621032067260895)
                  ·
                    rfl

theorem cell21_84366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_84366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84366 prefixEnd_84366 := by exact prefixLift 84366
  have htrace : WordTrace (prefixWord ++ tailWord_84366) baseStart_84366 baseEnd_84366 := by
    simpa [prefixWord, tailWord_84366, baseEnd_84366] using wordTrace_append hprefix tailTrace_84366
  have hstable : (prefixWord ++ tailWord_84366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84366).length < 2 ^ (prefixWord ++ tailWord_84366).sum := by decide
  have hdescent : baseEnd_84366 < baseStart_84366 := by decide
  rcases family_descends (prefixWord ++ tailWord_84366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84417 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 4]
def baseStart_84417 : Nat := 118140960795 + 84417 * 2 ^ 59
def prefixEnd_84417 : Nat := 4983230072969 + 3 ^ 40 * 84417 * 2
def baseEnd_84417 : Nat := 19265109515867311910791

theorem tailTrace_84417 : CollatzResearch.WordTrace tailWord_84417 prefixEnd_84417 19265109515867311910791 := by
  unfold tailWord_84417
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078940935179101120891505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2052627290119400747261003 3078940935179101120891505)
  ·
    refine ⟨2309205701384325840668629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3078940935179101120891505 2309205701384325840668629)
    ·
      refine ⟨54122008626195136890671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2309205701384325840668629 54122008626195136890671)
      ·
        refine ⟨81183012939292705336007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54122008626195136890671 81183012939292705336007)
        ·
          refine ⟨121774519408939058004011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81183012939292705336007 121774519408939058004011)
          ·
            refine ⟨182661779113408587006017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121774519408939058004011 182661779113408587006017)
            ·
              refine ⟨136996334335056440254513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182661779113408587006017 136996334335056440254513)
              ·
                refine ⟨102747250751292330190885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136996334335056440254513 102747250751292330190885)
                ·
                  refine ⟨19265109515867311910791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102747250751292330190885 19265109515867311910791)
                  ·
                    rfl

theorem cell21_84417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_84417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84417 prefixEnd_84417 := by exact prefixLift 84417
  have htrace : WordTrace (prefixWord ++ tailWord_84417) baseStart_84417 baseEnd_84417 := by
    simpa [prefixWord, tailWord_84417, baseEnd_84417] using wordTrace_append hprefix tailTrace_84417
  have hstable : (prefixWord ++ tailWord_84417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84417).length < 2 ^ (prefixWord ++ tailWord_84417).sum := by decide
  have hdescent : baseEnd_84417 < baseStart_84417 := by decide
  rcases family_descends (prefixWord ++ tailWord_84417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84425 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 4]
def baseStart_84425 : Nat := 118140960795 + 84425 * 2 ^ 59
def prefixEnd_84425 : Nat := 4983230072969 + 3 ^ 40 * 84425 * 2
def baseEnd_84425 : Nat := 19266935224861075777441

theorem tailTrace_84425 : CollatzResearch.WordTrace tailWord_84425 prefixEnd_84425 19266935224861075777441 := by
  unfold tailWord_84425
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079232719150118487182729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2052821812766745658121819 3079232719150118487182729)
  ·
    refine ⟨2309424539362588865387047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3079232719150118487182729 2309424539362588865387047)
    ·
      refine ⟨3464136809043883298080571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309424539362588865387047 3464136809043883298080571)
      ·
        refine ⟨5196205213565824947120857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464136809043883298080571 5196205213565824947120857)
        ·
          refine ⟨3897153910174368710340643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5196205213565824947120857 3897153910174368710340643)
          ·
            refine ⟨5845730865261553065510965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897153910174368710340643 5845730865261553065510965)
            ·
              refine ⟨548037268618270599891653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5845730865261553065510965 548037268618270599891653)
              ·
                refine ⟨102756987865925737479685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 548037268618270599891653 102756987865925737479685)
                ·
                  refine ⟨19266935224861075777441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102756987865925737479685 19266935224861075777441)
                  ·
                    rfl

theorem cell21_84425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_84425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84425 prefixEnd_84425 := by exact prefixLift 84425
  have htrace : WordTrace (prefixWord ++ tailWord_84425) baseStart_84425 baseEnd_84425 := by
    simpa [prefixWord, tailWord_84425, baseEnd_84425] using wordTrace_append hprefix tailTrace_84425
  have hstable : (prefixWord ++ tailWord_84425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84425).length < 2 ^ (prefixWord ++ tailWord_84425).sum := by decide
  have hdescent : baseEnd_84425 < baseStart_84425 := by decide
  rcases family_descends (prefixWord ++ tailWord_84425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84493 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 4]
def baseStart_84493 : Nat := 118140960795 + 84493 * 2 ^ 59
def prefixEnd_84493 : Nat := 4983230072969 + 3 ^ 40 * 84493 * 2
def baseEnd_84493 : Nat := 19282453751308068643969

theorem tailTrace_84493 : CollatzResearch.WordTrace tailWord_84493 prefixEnd_84493 19282453751308068643969 := by
  unfold tailWord_84493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081712882903766100658133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2054475255269177400438755 3081712882903766100658133)
  ·
    refine ⟨72227645693057017984175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 3081712882903766100658133 72227645693057017984175)
    ·
      refine ⟨108341468539585526976263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72227645693057017984175 108341468539585526976263)
      ·
        refine ⟨162512202809378290464395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108341468539585526976263 162512202809378290464395)
        ·
          refine ⟨243768304214067435696593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162512202809378290464395 243768304214067435696593)
          ·
            refine ⟨182826228160550576772445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243768304214067435696593 182826228160550576772445)
            ·
              refine ⟨68559835560206466289667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182826228160550576772445 68559835560206466289667)
              ·
                refine ⟨102839753340309699434501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68559835560206466289667 102839753340309699434501)
                ·
                  refine ⟨19282453751308068643969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 102839753340309699434501 19282453751308068643969)
                  ·
                    rfl

theorem cell21_84493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_84493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84493 prefixEnd_84493 := by exact prefixLift 84493
  have htrace : WordTrace (prefixWord ++ tailWord_84493) baseStart_84493 baseEnd_84493 := by
    simpa [prefixWord, tailWord_84493, baseEnd_84493] using wordTrace_append hprefix tailTrace_84493
  have hstable : (prefixWord ++ tailWord_84493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84493).length < 2 ^ (prefixWord ++ tailWord_84493).sum := by decide
  have hdescent : baseEnd_84493 < baseStart_84493 := by decide
  rcases family_descends (prefixWord ++ tailWord_84493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84560 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_84560 : Nat := 118140960795 + 84560 * 2 ^ 59
def prefixEnd_84560 : Nat := 4983230072969 + 3 ^ 40 * 84560 * 2
def baseEnd_84560 : Nat := 19297744064130841027165

theorem tailTrace_84560 : CollatzResearch.WordTrace tailWord_84560 prefixEnd_84560 19297744064130841027165 := by
  unfold tailWord_84560
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542078286830518271673567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2056104382440691028898089 1542078286830518271673567)
  ·
    refine ⟨2313117430245777407510351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542078286830518271673567 2313117430245777407510351)
    ·
      refine ⟨3469676145368666111265527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313117430245777407510351 3469676145368666111265527)
      ·
        refine ⟨5204514218052999166898291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469676145368666111265527 5204514218052999166898291)
        ·
          refine ⟨7806771327079498750347437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204514218052999166898291 7806771327079498750347437)
          ·
            refine ⟨2927539247654812031380289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7806771327079498750347437 2927539247654812031380289)
            ·
              refine ⟨2195654435741109023535217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927539247654812031380289 2195654435741109023535217)
              ·
                refine ⟨1646740826805831767651413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195654435741109023535217 1646740826805831767651413)
                ·
                  refine ⟨19297744064130841027165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1646740826805831767651413 19297744064130841027165)
                  ·
                    rfl

theorem cell21_84560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_84560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84560 prefixEnd_84560 := by exact prefixLift 84560
  have htrace : WordTrace (prefixWord ++ tailWord_84560) baseStart_84560 baseEnd_84560 := by
    simpa [prefixWord, tailWord_84560, baseEnd_84560] using wordTrace_append hprefix tailTrace_84560
  have hstable : (prefixWord ++ tailWord_84560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84560).length < 2 ^ (prefixWord ++ tailWord_84560).sum := by decide
  have hdescent : baseEnd_84560 < baseStart_84560 := by decide
  rcases family_descends (prefixWord ++ tailWord_84560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84597 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 3]
def baseStart_84597 : Nat := 118140960795 + 84597 * 2 ^ 59
def prefixEnd_84597 : Nat := 4983230072969 + 3 ^ 40 * 84597 * 2
def baseEnd_84597 : Nat := 19306187968226998910423

theorem tailTrace_84597 : CollatzResearch.WordTrace tailWord_84597 prefixEnd_84597 19306187968226998910423 := by
  unfold tailWord_84597
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085506074526991862444045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2057004049684661241629363 3085506074526991862444045)
  ·
    refine ⟨1157064777947621948416517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3085506074526991862444045 1157064777947621948416517)
    ·
      refine ⟨216949645865179115328097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1157064777947621948416517 216949645865179115328097)
      ·
        refine ⟨162712234398884336496073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 216949645865179115328097 162712234398884336496073)
        ·
          refine ⟨122034175799163252372055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162712234398884336496073 122034175799163252372055)
          ·
            refine ⟨183051263698744878558083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122034175799163252372055 183051263698744878558083)
            ·
              refine ⟨274576895548117317837125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183051263698744878558083 274576895548117317837125)
              ·
                refine ⟨51483167915271997094461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274576895548117317837125 51483167915271997094461)
                ·
                  refine ⟨19306187968226998910423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51483167915271997094461 19306187968226998910423)
                  ·
                    rfl

theorem cell21_84597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_84597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84597 prefixEnd_84597 := by exact prefixLift 84597
  have htrace : WordTrace (prefixWord ++ tailWord_84597) baseStart_84597 baseEnd_84597 := by
    simpa [prefixWord, tailWord_84597, baseEnd_84597] using wordTrace_append hprefix tailTrace_84597
  have hstable : (prefixWord ++ tailWord_84597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84597).length < 2 ^ (prefixWord ++ tailWord_84597).sum := by decide
  have hdescent : baseEnd_84597 < baseStart_84597 := by decide
  rcases family_descends (prefixWord ++ tailWord_84597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84608 : List Nat := [2, 1, 1, 2, 1, 7, 1, 6]
def baseStart_84608 : Nat := 118140960795 + 84608 * 2 ^ 59
def prefixEnd_84608 : Nat := 4983230072969 + 3 ^ 40 * 84608 * 2
def baseEnd_84608 : Nat := 6436232772697808075689

theorem tailTrace_84608 : CollatzResearch.WordTrace tailWord_84608 prefixEnd_84608 6436232772697808075689 := by
  unfold tailWord_84608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542953638743570370547239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2057271518324760494062985 1542953638743570370547239)
  ·
    refine ⟨2314430458115355555820859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542953638743570370547239 2314430458115355555820859)
    ·
      refine ⟨3471645687173033333731289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314430458115355555820859 3471645687173033333731289)
      ·
        refine ⟨2603734265379775000298467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471645687173033333731289 2603734265379775000298467)
        ·
          refine ⟨3905601398069662500447701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603734265379775000298467 3905601398069662500447701)
          ·
            refine ⟨91537532767257714854243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 3905601398069662500447701 91537532767257714854243)
            ·
              refine ⟨137306299150886572281365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91537532767257714854243 137306299150886572281365)
              ·
                refine ⟨6436232772697808075689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 137306299150886572281365 6436232772697808075689)
                ·
                  rfl

theorem cell21_84608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_84608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84608 prefixEnd_84608 := by exact prefixLift 84608
  have htrace : WordTrace (prefixWord ++ tailWord_84608) baseStart_84608 baseEnd_84608 := by
    simpa [prefixWord, tailWord_84608, baseEnd_84608] using wordTrace_append hprefix tailTrace_84608
  have hstable : (prefixWord ++ tailWord_84608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84608).length < 2 ^ (prefixWord ++ tailWord_84608).sum := by decide
  have hdescent : baseEnd_84608 < baseStart_84608 := by decide
  rcases family_descends (prefixWord ++ tailWord_84608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84684 : List Nat := [2, 2, 1, 5, 1, 2, 1, 7]
def baseStart_84684 : Nat := 118140960795 + 84684 * 2 ^ 59
def prefixEnd_84684 : Nat := 4983230072969 + 3 ^ 40 * 84684 * 2
def baseEnd_84684 : Nat := 6442014184511393653415

theorem tailTrace_84684 : CollatzResearch.WordTrace tailWord_84684 prefixEnd_84684 6442014184511393653415 := by
  unfold tailWord_84684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544339612605902860430553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2059119483474537147240737 1544339612605902860430553)
  ·
    refine ⟨1158254709454427145322915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1544339612605902860430553 1158254709454427145322915)
    ·
      refine ⟨1737382064181640717984373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1158254709454427145322915 1737382064181640717984373)
      ·
        refine ⟨162879568517028817311035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1737382064181640717984373 162879568517028817311035)
        ·
          refine ⟨244319352775543225966553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162879568517028817311035 244319352775543225966553)
          ·
            refine ⟨183239514581657419474915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244319352775543225966553 183239514581657419474915)
            ·
              refine ⟨274859271872486129212373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183239514581657419474915 274859271872486129212373)
              ·
                refine ⟨6442014184511393653415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 274859271872486129212373 6442014184511393653415)
                ·
                  rfl

theorem cell21_84684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_84684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84684 prefixEnd_84684 := by exact prefixLift 84684
  have htrace : WordTrace (prefixWord ++ tailWord_84684) baseStart_84684 baseEnd_84684 := by
    simpa [prefixWord, tailWord_84684, baseEnd_84684] using wordTrace_append hprefix tailTrace_84684
  have hstable : (prefixWord ++ tailWord_84684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84684).length < 2 ^ (prefixWord ++ tailWord_84684).sum := by decide
  have hdescent : baseEnd_84684 < baseStart_84684 := by decide
  rcases family_descends (prefixWord ++ tailWord_84684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84690 : List Nat := [3, 2, 2, 2, 4, 1, 1, 3, 3]
def baseStart_84690 : Nat := 118140960795 + 84690 * 2 ^ 59
def prefixEnd_84690 : Nat := 4983230072969 + 3 ^ 40 * 84690 * 2
def baseEnd_84690 : Nat := 19327411835279503860233

theorem tailTrace_84690 : CollatzResearch.WordTrace tailWord_84690 prefixEnd_84690 19327411835279503860233 := by
  unfold tailWord_84690
  simp only [CollatzResearch.WordTrace]
  refine ⟨772224515797517186394881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2059265375460045830386349 772224515797517186394881)
  ·
    refine ⟨579168386848137889796161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772224515797517186394881 579168386848137889796161)
    ·
      refine ⟨434376290136103417347121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579168386848137889796161 434376290136103417347121)
      ·
        refine ⟨325782217602077563010341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434376290136103417347121 325782217602077563010341)
        ·
          refine ⟨61084165800389543064439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 325782217602077563010341 61084165800389543064439)
          ·
            refine ⟨91626248700584314596659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61084165800389543064439 91626248700584314596659)
            ·
              refine ⟨137439373050876471894989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91626248700584314596659 137439373050876471894989)
              ·
                refine ⟨51539764894078676960621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137439373050876471894989 51539764894078676960621)
                ·
                  refine ⟨19327411835279503860233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51539764894078676960621 19327411835279503860233)
                  ·
                    rfl

theorem cell21_84690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_84690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84690 prefixEnd_84690 := by exact prefixLift 84690
  have htrace : WordTrace (prefixWord ++ tailWord_84690) baseStart_84690 baseEnd_84690 := by
    simpa [prefixWord, tailWord_84690, baseEnd_84690] using wordTrace_append hprefix tailTrace_84690
  have hstable : (prefixWord ++ tailWord_84690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84690).length < 2 ^ (prefixWord ++ tailWord_84690).sum := by decide
  have hdescent : baseEnd_84690 < baseStart_84690 := by decide
  rcases family_descends (prefixWord ++ tailWord_84690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
