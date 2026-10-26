import V185TrunkScan21Chunk110

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1348637 : List Nat := [1, 4, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1348637 : Nat := 118140960795 + 1348637 * 2 ^ 59
def prefixEnd_1348637 : Nat := 4983230072969 + 3 ^ 40 * 1348637 * 2
def baseEnd_1348637 : Nat := 307777337527886748993439

theorem tailTrace_1348637 : CollatzResearch.WordTrace tailWord_1348637 prefixEnd_1348637 307777337527886748993439 := by
  unfold tailWord_1348637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49188832415125952707292165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32792554943417301804861443 49188832415125952707292165)
  ·
    refine ⟨9222906077836116132617281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49188832415125952707292165 9222906077836116132617281)
    ·
      refine ⟨6917179558377087099462961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9222906077836116132617281 6917179558377087099462961)
      ·
        refine ⟨5187884668782815324597221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6917179558377087099462961 5187884668782815324597221)
        ·
          refine ⟨972728375396777873361979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5187884668782815324597221 972728375396777873361979)
          ·
            refine ⟨1459092563095166810042969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972728375396777873361979 1459092563095166810042969)
            ·
              refine ⟨1094319422321375107532227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1459092563095166810042969 1094319422321375107532227)
              ·
                refine ⟨1641479133482062661298341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094319422321375107532227 1641479133482062661298341)
                ·
                  refine ⟨307777337527886748993439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641479133482062661298341 307777337527886748993439)
                  ·
                    rfl

theorem cell21_1348637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1348637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348637 prefixEnd_1348637 := by exact prefixLift 1348637
  have htrace : WordTrace (prefixWord ++ tailWord_1348637) baseStart_1348637 baseEnd_1348637 := by
    simpa [prefixWord, tailWord_1348637, baseEnd_1348637] using wordTrace_append hprefix tailTrace_1348637
  have hstable : (prefixWord ++ tailWord_1348637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348637).length < 2 ^ (prefixWord ++ tailWord_1348637).sum := by decide
  have hdescent : baseEnd_1348637 < baseStart_1348637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348797 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1348797 : Nat := 118140960795 + 1348797 * 2 ^ 59
def prefixEnd_1348797 : Nat := 4983230072969 + 3 ^ 40 * 1348797 * 2
def baseEnd_1348797 : Nat := 307813851707762026326445

theorem tailTrace_1348797 : CollatzResearch.WordTrace tailWord_1348797 prefixEnd_1348797 307813851707762026326445 := by
  unfold tailWord_1348797
  simp only [CollatzResearch.WordTrace]
  refine ⟨49194668094546300033116645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32796445396364200022077763 49194668094546300033116645)
  ·
    refine ⟨9224000267727431256209371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49194668094546300033116645 9224000267727431256209371)
    ·
      refine ⟨13836000401591146884314057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9224000267727431256209371 13836000401591146884314057)
      ·
        refine ⟨10377000301193360163235543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13836000401591146884314057 10377000301193360163235543)
        ·
          refine ⟨15565500451790040244853315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10377000301193360163235543 15565500451790040244853315)
          ·
            refine ⟨23348250677685060367279973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15565500451790040244853315 23348250677685060367279973)
            ·
              refine ⟨4377797002065948818864995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23348250677685060367279973 4377797002065948818864995)
              ·
                refine ⟨6566695503098923228297493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4377797002065948818864995 6566695503098923228297493)
                ·
                  refine ⟨307813851707762026326445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6566695503098923228297493 307813851707762026326445)
                  ·
                    rfl

theorem cell21_1348797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1348797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348797 prefixEnd_1348797 := by exact prefixLift 1348797
  have htrace : WordTrace (prefixWord ++ tailWord_1348797) baseStart_1348797 baseEnd_1348797 := by
    simpa [prefixWord, tailWord_1348797, baseEnd_1348797] using wordTrace_append hprefix tailTrace_1348797
  have hstable : (prefixWord ++ tailWord_1348797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348797).length < 2 ^ (prefixWord ++ tailWord_1348797).sum := by decide
  have hdescent : baseEnd_1348797 < baseStart_1348797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348800 : List Nat := [2, 1, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1348800 : Nat := 118140960795 + 1348800 * 2 ^ 59
def prefixEnd_1348800 : Nat := 4983230072969 + 3 ^ 40 * 1348800 * 2
def baseEnd_1348800 : Nat := 307814536348634687776439

theorem tailTrace_1348800 : CollatzResearch.WordTrace tailWord_1348800 prefixEnd_1348800 307814536348634687776439 := by
  unfold tailWord_1348800
  simp only [CollatzResearch.WordTrace]
  refine ⟨24597388756767715772737927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32796518342356954363650569 24597388756767715772737927)
  ·
    refine ⟨36896083135151573659106891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24597388756767715772737927 36896083135151573659106891)
    ·
      refine ⟨55344124702727360488660337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36896083135151573659106891 55344124702727360488660337)
      ·
        refine ⟨41508093527045520366495253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55344124702727360488660337 41508093527045520366495253)
        ·
          refine ⟨1945691884080258767179465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41508093527045520366495253 1945691884080258767179465)
          ·
            refine ⟨1459268913060194075384599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1945691884080258767179465 1459268913060194075384599)
            ·
              refine ⟨2188903369590291113076899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459268913060194075384599 2188903369590291113076899)
              ·
                refine ⟨3283355054385436669615349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2188903369590291113076899 3283355054385436669615349)
                ·
                  refine ⟨307814536348634687776439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3283355054385436669615349 307814536348634687776439)
                  ·
                    rfl

theorem cell21_1348800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1348800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348800 prefixEnd_1348800 := by exact prefixLift 1348800
  have htrace : WordTrace (prefixWord ++ tailWord_1348800) baseStart_1348800 baseEnd_1348800 := by
    simpa [prefixWord, tailWord_1348800, baseEnd_1348800] using wordTrace_append hprefix tailTrace_1348800
  have hstable : (prefixWord ++ tailWord_1348800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348800).length < 2 ^ (prefixWord ++ tailWord_1348800).sum := by decide
  have hdescent : baseEnd_1348800 < baseStart_1348800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348873 : List Nat := [1, 2, 1, 1, 3, 3, 1, 5, 4]
def baseStart_1348873 : Nat := 118140960795 + 1348873 * 2 ^ 59
def prefixEnd_1348873 : Nat := 4983230072969 + 3 ^ 40 * 1348873 * 2
def baseEnd_1348873 : Nat := 307831195943202783059623

theorem tailTrace_1348873 : CollatzResearch.WordTrace tailWord_1348873 prefixEnd_1348873 307831195943202783059623 := by
  unfold tailWord_1348873
  simp only [CollatzResearch.WordTrace]
  refine ⟨49197440042270965012883273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32798293361513976675255515 49197440042270965012883273)
  ·
    refine ⟨36898080031703223759662455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49197440042270965012883273 36898080031703223759662455)
    ·
      refine ⟨55347120047554835639493683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36898080031703223759662455 55347120047554835639493683)
      ·
        refine ⟨83020680071332253459240525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55347120047554835639493683 83020680071332253459240525)
        ·
          refine ⟨31132755026749595047215197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83020680071332253459240525 31132755026749595047215197)
          ·
            refine ⟨11674783135031098142705699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31132755026749595047215197 11674783135031098142705699)
            ·
              refine ⟨17512174702546647214058549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11674783135031098142705699 17512174702546647214058549)
              ·
                refine ⟨1641766378363748176317989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17512174702546647214058549 1641766378363748176317989)
                ·
                  refine ⟨307831195943202783059623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1641766378363748176317989 307831195943202783059623)
                  ·
                    rfl

theorem cell21_1348873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_1348873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348873 prefixEnd_1348873 := by exact prefixLift 1348873
  have htrace : WordTrace (prefixWord ++ tailWord_1348873) baseStart_1348873 baseEnd_1348873 := by
    simpa [prefixWord, tailWord_1348873, baseEnd_1348873] using wordTrace_append hprefix tailTrace_1348873
  have hstable : (prefixWord ++ tailWord_1348873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348873).length < 2 ^ (prefixWord ++ tailWord_1348873).sum := by decide
  have hdescent : baseEnd_1348873 < baseStart_1348873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348893 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 3]
def baseStart_1348893 : Nat := 118140960795 + 1348893 * 2 ^ 59
def prefixEnd_1348893 : Nat := 4983230072969 + 3 ^ 40 * 1348893 * 2
def baseEnd_1348893 : Nat := 307835760215687192726249

theorem tailTrace_1348893 : CollatzResearch.WordTrace tailWord_1348893 prefixEnd_1348893 307835760215687192726249 := by
  unfold tailWord_1348893
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198169502198508428611333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32798779668132338952407555 49198169502198508428611333)
  ·
    refine ⟨9224656781662220330364625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49198169502198508428611333 9224656781662220330364625)
    ·
      refine ⟨6918492586246665247773469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9224656781662220330364625 6918492586246665247773469)
      ·
        refine ⟨2594434719842499467915051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6918492586246665247773469 2594434719842499467915051)
        ·
          refine ⟨3891652079763749201872577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594434719842499467915051 3891652079763749201872577)
          ·
            refine ⟨2918739059822811901404433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891652079763749201872577 2918739059822811901404433)
            ·
              refine ⟨2189054294867108926053325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2918739059822811901404433 2189054294867108926053325)
              ·
                refine ⟨820895360575165847269997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189054294867108926053325 820895360575165847269997)
                ·
                  refine ⟨307835760215687192726249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 820895360575165847269997 307835760215687192726249)
                  ·
                    rfl

theorem cell21_1348893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_1348893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348893 prefixEnd_1348893 := by exact prefixLift 1348893
  have htrace : WordTrace (prefixWord ++ tailWord_1348893) baseStart_1348893 baseEnd_1348893 := by
    simpa [prefixWord, tailWord_1348893, baseEnd_1348893] using wordTrace_append hprefix tailTrace_1348893
  have hstable : (prefixWord ++ tailWord_1348893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348893).length < 2 ^ (prefixWord ++ tailWord_1348893).sum := by decide
  have hdescent : baseEnd_1348893 < baseStart_1348893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348904 : List Nat := [2, 1, 5, 1, 2, 2, 8]
def baseStart_1348904 : Nat := 118140960795 + 1348904 * 2 ^ 59
def prefixEnd_1348904 : Nat := 4983230072969 + 3 ^ 40 * 1348904 * 2
def baseEnd_1348904 : Nat := 34204252285061513115877

theorem tailTrace_1348904 : CollatzResearch.WordTrace tailWord_1348904 prefixEnd_1348904 34204252285061513115877 := by
  unfold tailWord_1348904
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599285352579328653630883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32799047136772438204841177 24599285352579328653630883)
  ·
    refine ⟨36898928028868992980446325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24599285352579328653630883 36898928028868992980446325)
    ·
      refine ⟨3459274502706468091916843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36898928028868992980446325 3459274502706468091916843)
      ·
        refine ⟨5188911754059702137875265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3459274502706468091916843 5188911754059702137875265)
        ·
          refine ⟨3891683815544776603406449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5188911754059702137875265 3891683815544776603406449)
          ·
            refine ⟨2918762861658582452554837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891683815544776603406449 2918762861658582452554837)
            ·
              refine ⟨34204252285061513115877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2918762861658582452554837 34204252285061513115877)
              ·
                rfl

theorem cell21_1348904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 8].length) (baseStart_1348904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348904 prefixEnd_1348904 := by exact prefixLift 1348904
  have htrace : WordTrace (prefixWord ++ tailWord_1348904) baseStart_1348904 baseEnd_1348904 := by
    simpa [prefixWord, tailWord_1348904, baseEnd_1348904] using wordTrace_append hprefix tailTrace_1348904
  have hstable : (prefixWord ++ tailWord_1348904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348904).length < 2 ^ (prefixWord ++ tailWord_1348904).sum := by decide
  have hdescent : baseEnd_1348904 < baseStart_1348904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348949 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 6]
def baseStart_1348949 : Nat := 118140960795 + 1348949 * 2 ^ 59
def prefixEnd_1348949 : Nat := 4983230072969 + 3 ^ 40 * 1348949 * 2
def baseEnd_1348949 : Nat := 307848540178643539792801

theorem tailTrace_1348949 : CollatzResearch.WordTrace tailWord_1348949 prefixEnd_1348949 307848540178643539792801 := by
  unfold tailWord_1348949
  simp only [CollatzResearch.WordTrace]
  refine ⟨49200211989995629992649901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32800141326663753328433267 49200211989995629992649901)
  ·
    refine ⟨18450079496248361247243713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49200211989995629992649901 18450079496248361247243713)
    ·
      refine ⟨13837559622186270935432785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18450079496248361247243713 13837559622186270935432785)
      ·
        refine ⟨10378169716639703201574589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13837559622186270935432785 10378169716639703201574589)
        ·
          refine ⟨3891813643739888700590471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10378169716639703201574589 3891813643739888700590471)
          ·
            refine ⟨5837720465609833050885707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891813643739888700590471 5837720465609833050885707)
            ·
              refine ⟨8756580698414749576328561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5837720465609833050885707 8756580698414749576328561)
              ·
                refine ⟨6567435523811062182246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756580698414749576328561 6567435523811062182246421)
                ·
                  refine ⟨307848540178643539792801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6567435523811062182246421 307848540178643539792801)
                  ·
                    rfl

theorem cell21_1348949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_1348949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348949 prefixEnd_1348949 := by exact prefixLift 1348949
  have htrace : WordTrace (prefixWord ++ tailWord_1348949) baseStart_1348949 baseEnd_1348949 := by
    simpa [prefixWord, tailWord_1348949, baseEnd_1348949] using wordTrace_append hprefix tailTrace_1348949
  have hstable : (prefixWord ++ tailWord_1348949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348949).length < 2 ^ (prefixWord ++ tailWord_1348949).sum := by decide
  have hdescent : baseEnd_1348949 < baseStart_1348949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348963 : List Nat := [1, 1, 1, 5, 2, 2, 9]
def baseStart_1348963 : Nat := 118140960795 + 1348963 * 2 ^ 59
def prefixEnd_1348963 : Nat := 4983230072969 + 3 ^ 40 * 1348963 * 2
def baseEnd_1348963 : Nat := 34205748352153625173271

theorem tailTrace_1348963 : CollatzResearch.WordTrace tailWord_1348963 prefixEnd_1348963 34205748352153625173271 := by
  unfold tailWord_1348963
  simp only [CollatzResearch.WordTrace]
  refine ⟨49200722611944910383659543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32800481741296606922439695 49200722611944910383659543)
  ·
    refine ⟨73801083917917365575489315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49200722611944910383659543 73801083917917365575489315)
    ·
      refine ⟨110701625876876048363233973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73801083917917365575489315 110701625876876048363233973)
      ·
        refine ⟨10378277425957129534053185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 110701625876876048363233973 10378277425957129534053185)
        ·
          refine ⟨7783708069467847150539889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10378277425957129534053185 7783708069467847150539889)
          ·
            refine ⟨5837781052100885362904917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7783708069467847150539889 5837781052100885362904917)
            ·
              refine ⟨34205748352153625173271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5837781052100885362904917 34205748352153625173271)
              ·
                rfl

theorem cell21_1348963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 9].length) (baseStart_1348963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1348963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1348963 prefixEnd_1348963 := by exact prefixLift 1348963
  have htrace : WordTrace (prefixWord ++ tailWord_1348963) baseStart_1348963 baseEnd_1348963 := by
    simpa [prefixWord, tailWord_1348963, baseEnd_1348963] using wordTrace_append hprefix tailTrace_1348963
  have hstable : (prefixWord ++ tailWord_1348963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348963).length < 2 ^ (prefixWord ++ tailWord_1348963).sum := by decide
  have hdescent : baseEnd_1348963 < baseStart_1348963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349076 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1349076 : Nat := 118140960795 + 1349076 * 2 ^ 59
def prefixEnd_1349076 : Nat := 4983230072969 + 3 ^ 40 * 1349076 * 2
def baseEnd_1349076 : Nat := 307877523308919541175875

theorem tailTrace_1349076 : CollatzResearch.WordTrace tailWord_1349076 prefixEnd_1349076 307877523308919541175875 := by
  unfold tailWord_1349076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602422030267765341261541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32803229373690353788348721 24602422030267765341261541)
  ·
    refine ⟨4612954130675206001486539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24602422030267765341261541 4612954130675206001486539)
    ·
      refine ⟨6919431196012809002229809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4612954130675206001486539 6919431196012809002229809)
      ·
        refine ⟨5189573397009606751672357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6919431196012809002229809 5189573397009606751672357)
        ·
          refine ⟨973045011939301265938567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5189573397009606751672357 973045011939301265938567)
          ·
            refine ⟨1459567517908951898907851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973045011939301265938567 1459567517908951898907851)
            ·
              refine ⟨2189351276863427848361777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459567517908951898907851 2189351276863427848361777)
              ·
                refine ⟨1642013457647570886271333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189351276863427848361777 1642013457647570886271333)
                ·
                  refine ⟨307877523308919541175875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642013457647570886271333 307877523308919541175875)
                  ·
                    rfl

theorem cell21_1349076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1349076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349076 prefixEnd_1349076 := by exact prefixLift 1349076
  have htrace : WordTrace (prefixWord ++ tailWord_1349076) baseStart_1349076 baseEnd_1349076 := by
    simpa [prefixWord, tailWord_1349076, baseEnd_1349076] using wordTrace_append hprefix tailTrace_1349076
  have hstable : (prefixWord ++ tailWord_1349076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349076).length < 2 ^ (prefixWord ++ tailWord_1349076).sum := by decide
  have hdescent : baseEnd_1349076 < baseStart_1349076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349087 : List Nat := [1, 1, 2, 3, 3, 1, 1, 6, 3]
def baseStart_1349087 : Nat := 118140960795 + 1349087 * 2 ^ 59
def prefixEnd_1349087 : Nat := 4983230072969 + 3 ^ 40 * 1349087 * 2
def baseEnd_1349087 : Nat := 307880033658785966492519

theorem tailTrace_1349087 : CollatzResearch.WordTrace tailWord_1349087 prefixEnd_1349087 307880033658785966492519 := by
  unfold tailWord_1349087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49205245263495679561173515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32803496842330453040782343 49205245263495679561173515)
  ·
    refine ⟨73807867895243519341760273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49205245263495679561173515 73807867895243519341760273)
    ·
      refine ⟨55355900921432639506320205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73807867895243519341760273 55355900921432639506320205)
      ·
        refine ⟨20758462845537239814870077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55355900921432639506320205 20758462845537239814870077)
        ·
          refine ⟨7784423567076464930576279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20758462845537239814870077 7784423567076464930576279)
          ·
            refine ⟨11676635350614697395864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7784423567076464930576279 11676635350614697395864419)
            ·
              refine ⟨17514953025922046093796629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11676635350614697395864419 17514953025922046093796629)
              ·
                refine ⟨821013423090095910646717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17514953025922046093796629 821013423090095910646717)
                ·
                  refine ⟨307880033658785966492519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821013423090095910646717 307880033658785966492519)
                  ·
                    rfl

theorem cell21_1349087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 6, 3].length) (baseStart_1349087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349087 prefixEnd_1349087 := by exact prefixLift 1349087
  have htrace : WordTrace (prefixWord ++ tailWord_1349087) baseStart_1349087 baseEnd_1349087 := by
    simpa [prefixWord, tailWord_1349087, baseEnd_1349087] using wordTrace_append hprefix tailTrace_1349087
  have hstable : (prefixWord ++ tailWord_1349087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349087).length < 2 ^ (prefixWord ++ tailWord_1349087).sum := by decide
  have hdescent : baseEnd_1349087 < baseStart_1349087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349121 : List Nat := [1, 2, 4, 1, 4, 2, 1, 3, 3]
def baseStart_1349121 : Nat := 118140960795 + 1349121 * 2 ^ 59
def prefixEnd_1349121 : Nat := 4983230072969 + 3 ^ 40 * 1349121 * 2
def baseEnd_1349121 : Nat := 307887792922009462925783

theorem tailTrace_1349121 : CollatzResearch.WordTrace tailWord_1349121 prefixEnd_1349121 307887792922009462925783 := by
  unfold tailWord_1349121
  simp only [CollatzResearch.WordTrace]
  refine ⟨49206485345372503367911217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32804323563581668911940811 49206485345372503367911217)
  ·
    refine ⟨36904864009029377525933413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49206485345372503367911217 36904864009029377525933413)
    ·
      refine ⟨6919662001693008286112515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36904864009029377525933413 6919662001693008286112515)
      ·
        refine ⟨10379493002539512429168773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6919662001693008286112515 10379493002539512429168773)
        ·
          refine ⟨1946154937976158580469145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10379493002539512429168773 1946154937976158580469145)
          ·
            refine ⟨1459616203482118935351859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946154937976158580469145 1459616203482118935351859)
            ·
              refine ⟨2189424305223178403027789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459616203482118935351859 2189424305223178403027789)
              ·
                refine ⟨821034114458691901135421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189424305223178403027789 821034114458691901135421)
                ·
                  refine ⟨307887792922009462925783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821034114458691901135421 307887792922009462925783)
                  ·
                    rfl

theorem cell21_1349121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 3, 3].length) (baseStart_1349121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349121 prefixEnd_1349121 := by exact prefixLift 1349121
  have htrace : WordTrace (prefixWord ++ tailWord_1349121) baseStart_1349121 baseEnd_1349121 := by
    simpa [prefixWord, tailWord_1349121, baseEnd_1349121] using wordTrace_append hprefix tailTrace_1349121
  have hstable : (prefixWord ++ tailWord_1349121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349121).length < 2 ^ (prefixWord ++ tailWord_1349121).sum := by decide
  have hdescent : baseEnd_1349121 < baseStart_1349121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349132 : List Nat := [2, 2, 1, 2, 5, 2, 7]
def baseStart_1349132 : Nat := 118140960795 + 1349132 * 2 ^ 59
def prefixEnd_1349132 : Nat := 4983230072969 + 3 ^ 40 * 1349132 * 2
def baseEnd_1349132 : Nat := 34210033696875098693603

theorem tailTrace_1349132 : CollatzResearch.WordTrace tailWord_1349132 prefixEnd_1349132 34210033696875098693603 := by
  unfold tailWord_1349132
  simp only [CollatzResearch.WordTrace]
  refine ⟨24603443274166326123280825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32804591032221768164374433 24603443274166326123280825)
  ·
    refine ⟨18452582455624744592460619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24603443274166326123280825 18452582455624744592460619)
    ·
      refine ⟨27678873683437116888690929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18452582455624744592460619 27678873683437116888690929)
      ·
        refine ⟨20759155262577837666518197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27678873683437116888690929 20759155262577837666518197)
        ·
          refine ⟨1946170805866672281236081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20759155262577837666518197 1946170805866672281236081)
          ·
            refine ⟨1459628104400004210927061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946170805866672281236081 1459628104400004210927061)
            ·
              refine ⟨34210033696875098693603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1459628104400004210927061 34210033696875098693603)
              ·
                rfl

theorem cell21_1349132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 7].length) (baseStart_1349132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349132 prefixEnd_1349132 := by exact prefixLift 1349132
  have htrace : WordTrace (prefixWord ++ tailWord_1349132) baseStart_1349132 baseEnd_1349132 := by
    simpa [prefixWord, tailWord_1349132, baseEnd_1349132] using wordTrace_append hprefix tailTrace_1349132
  have hstable : (prefixWord ++ tailWord_1349132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349132).length < 2 ^ (prefixWord ++ tailWord_1349132).sum := by decide
  have hdescent : baseEnd_1349132 < baseStart_1349132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349191 : List Nat := [1, 1, 4, 1, 5, 9]
def baseStart_1349191 : Nat := 118140960795 + 1349191 * 2 ^ 59
def prefixEnd_1349191 : Nat := 4983230072969 + 3 ^ 40 * 1349191 * 2
def baseEnd_1349191 : Nat := 11403843254655736916999

theorem tailTrace_1349191 : CollatzResearch.WordTrace tailWord_1349191 prefixEnd_1349191 11403843254655736916999 := by
  unfold tailWord_1349191
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209038455118905322959427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32806025636745936881972951 49209038455118905322959427)
  ·
    refine ⟨73813557682678357984439141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49209038455118905322959427 73813557682678357984439141)
    ·
      refine ⟨13840042065502192122082339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73813557682678357984439141 13840042065502192122082339)
      ·
        refine ⟨20760063098253288183123509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13840042065502192122082339 20760063098253288183123509)
        ·
          refine ⟨1946255915461245767167829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20760063098253288183123509 1946255915461245767167829)
          ·
            refine ⟨11403843254655736916999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1946255915461245767167829 11403843254655736916999)
            ·
              rfl

theorem cell21_1349191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 9].length) (baseStart_1349191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349191 prefixEnd_1349191 := by exact prefixLift 1349191
  have htrace : WordTrace (prefixWord ++ tailWord_1349191) baseStart_1349191 baseEnd_1349191 := by
    simpa [prefixWord, tailWord_1349191, baseEnd_1349191] using wordTrace_append hprefix tailTrace_1349191
  have hstable : (prefixWord ++ tailWord_1349191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349191).length < 2 ^ (prefixWord ++ tailWord_1349191).sum := by decide
  have hdescent : baseEnd_1349191 < baseStart_1349191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349197 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 3]
def baseStart_1349197 : Nat := 118140960795 + 1349197 * 2 ^ 59
def prefixEnd_1349197 : Nat := 4983230072969 + 3 ^ 40 * 1349197 * 2
def baseEnd_1349197 : Nat := 307905137157450219658961

theorem tailTrace_1349197 : CollatzResearch.WordTrace tailWord_1349197 prefixEnd_1349197 307905137157450219658961 := by
  unfold tailWord_1349197
  simp only [CollatzResearch.WordTrace]
  refine ⟨49209257293097168347677845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32806171528731445565118563 49209257293097168347677845)
  ·
    refine ⟨2306683935613929766297399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49209257293097168347677845 2306683935613929766297399)
    ·
      refine ⟨3460025903420894649446099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306683935613929766297399 3460025903420894649446099)
      ·
        refine ⟨5190038855131341974169149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460025903420894649446099 5190038855131341974169149)
        ·
          refine ⟨1946264570674253240313431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5190038855131341974169149 1946264570674253240313431)
          ·
            refine ⟨2919396856011379860470147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946264570674253240313431 2919396856011379860470147)
            ·
              refine ⟨4379095284017069790705221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919396856011379860470147 4379095284017069790705221)
              ·
                refine ⟨821080365753200585757229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4379095284017069790705221 821080365753200585757229)
                ·
                  refine ⟨307905137157450219658961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821080365753200585757229 307905137157450219658961)
                  ·
                    rfl

theorem cell21_1349197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_1349197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349197 prefixEnd_1349197 := by exact prefixLift 1349197
  have htrace : WordTrace (prefixWord ++ tailWord_1349197) baseStart_1349197 baseEnd_1349197 := by
    simpa [prefixWord, tailWord_1349197, baseEnd_1349197] using wordTrace_append hprefix tailTrace_1349197
  have hstable : (prefixWord ++ tailWord_1349197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349197).length < 2 ^ (prefixWord ++ tailWord_1349197).sum := by decide
  have hdescent : baseEnd_1349197 < baseStart_1349197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349256 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 5]
def baseStart_1349256 : Nat := 118140960795 + 1349256 * 2 ^ 59
def prefixEnd_1349256 : Nat := 4983230072969 + 3 ^ 40 * 1349256 * 2
def baseEnd_1349256 : Nat := 307918601761279228175507

theorem tailTrace_1349256 : CollatzResearch.WordTrace tailWord_1349256 prefixEnd_1349256 307918601761279228175507 := by
  unfold tailWord_1349256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24605704599941710712037811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32807606133255614282717081 24605704599941710712037811)
  ·
    refine ⟨36908556899912566068056717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24605704599941710712037811 36908556899912566068056717)
    ·
      refine ⟨13840708837467212275521269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36908556899912566068056717 13840708837467212275521269)
      ·
        refine ⟨1297566453512551150830119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13840708837467212275521269 1297566453512551150830119)
        ·
          refine ⟨1946349680268826726245179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1297566453512551150830119 1946349680268826726245179)
          ·
            refine ⟨2919524520403240089367769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946349680268826726245179 2919524520403240089367769)
            ·
              refine ⟨2189643390302430067025827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919524520403240089367769 2189643390302430067025827)
              ·
                refine ⟨3284465085453645100538741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189643390302430067025827 3284465085453645100538741)
                ·
                  refine ⟨307918601761279228175507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3284465085453645100538741 307918601761279228175507)
                  ·
                    rfl

theorem cell21_1349256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_1349256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349256 prefixEnd_1349256 := by exact prefixLift 1349256
  have htrace : WordTrace (prefixWord ++ tailWord_1349256) baseStart_1349256 baseEnd_1349256 := by
    simpa [prefixWord, tailWord_1349256, baseEnd_1349256] using wordTrace_append hprefix tailTrace_1349256
  have hstable : (prefixWord ++ tailWord_1349256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349256).length < 2 ^ (prefixWord ++ tailWord_1349256).sum := by decide
  have hdescent : baseEnd_1349256 < baseStart_1349256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349284 : List Nat := [2, 3, 1, 2, 2, 2, 4, 5]
def baseStart_1349284 : Nat := 118140960795 + 1349284 * 2 ^ 59
def prefixEnd_1349284 : Nat := 4983230072969 + 3 ^ 40 * 1349284 * 2
def baseEnd_1349284 : Nat := 102641663914252467236261

theorem tailTrace_1349284 : CollatzResearch.WordTrace tailWord_1349284 prefixEnd_1349284 102641663914252467236261 := by
  unfold tailWord_1349284
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606215221890991103047453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32808286962521321470729937 24606215221890991103047453)
  ·
    refine ⟨9227330708209121663642795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24606215221890991103047453 9227330708209121663642795)
    ·
      refine ⟨13840996062313682495464193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9227330708209121663642795 13840996062313682495464193)
      ·
        refine ⟨10380747046735261871598145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13840996062313682495464193 10380747046735261871598145)
        ·
          refine ⟨7785560285051446403698609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10380747046735261871598145 7785560285051446403698609)
          ·
            refine ⟨5839170213788584802773957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7785560285051446403698609 5839170213788584802773957)
            ·
              refine ⟨1094844415085359650520117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5839170213788584802773957 1094844415085359650520117)
              ·
                refine ⟨102641663914252467236261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094844415085359650520117 102641663914252467236261)
                ·
                  rfl

theorem cell21_1349284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 5].length) (baseStart_1349284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349284 prefixEnd_1349284 := by exact prefixLift 1349284
  have htrace : WordTrace (prefixWord ++ tailWord_1349284) baseStart_1349284 baseEnd_1349284 := by
    simpa [prefixWord, tailWord_1349284, baseEnd_1349284] using wordTrace_append hprefix tailTrace_1349284
  have hstable : (prefixWord ++ tailWord_1349284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349284).length < 2 ^ (prefixWord ++ tailWord_1349284).sum := by decide
  have hdescent : baseEnd_1349284 < baseStart_1349284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349301 : List Nat := [1, 3, 3, 3, 3, 1, 7]
def baseStart_1349301 : Nat := 118140960795 + 1349301 * 2 ^ 59
def prefixEnd_1349301 : Nat := 4983230072969 + 3 ^ 40 * 1349301 * 2
def baseEnd_1349301 : Nat := 34214319041596572213935

theorem tailTrace_1349301 : CollatzResearch.WordTrace tailWord_1349301 prefixEnd_1349301 34214319041596572213935 := by
  unfold tailWord_1349301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49213050484720394109463757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32808700323146929406309171 49213050484720394109463757)
  ·
    refine ⟨18454893931770147791048909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49213050484720394109463757 18454893931770147791048909)
    ·
      refine ⟨6920585224413805421643341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18454893931770147791048909 6920585224413805421643341)
      ·
        refine ⟨2595219459155177033116253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6920585224413805421643341 2595219459155177033116253)
        ·
          refine ⟨973207297183191387418595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2595219459155177033116253 973207297183191387418595)
          ·
            refine ⟨1459810945774787081127893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973207297183191387418595 1459810945774787081127893)
            ·
              refine ⟨34214319041596572213935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1459810945774787081127893 34214319041596572213935)
              ·
                rfl

theorem cell21_1349301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 7].length) (baseStart_1349301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349301 prefixEnd_1349301 := by exact prefixLift 1349301
  have htrace : WordTrace (prefixWord ++ tailWord_1349301) baseStart_1349301 baseEnd_1349301 := by
    simpa [prefixWord, tailWord_1349301, baseEnd_1349301] using wordTrace_append hprefix tailTrace_1349301
  have hstable : (prefixWord ++ tailWord_1349301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349301).length < 2 ^ (prefixWord ++ tailWord_1349301).sum := by decide
  have hdescent : baseEnd_1349301 < baseStart_1349301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349312 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 6]
def baseStart_1349312 : Nat := 118140960795 + 1349312 * 2 ^ 59
def prefixEnd_1349312 : Nat := 4983230072969 + 3 ^ 40 * 1349312 * 2
def baseEnd_1349312 : Nat := 307931381724235575242059

theorem tailTrace_1349312 : CollatzResearch.WordTrace tailWord_1349312 prefixEnd_1349312 307931381724235575242059 := by
  unfold tailWord_1349312
  simp only [CollatzResearch.WordTrace]
  refine ⟨24606725843840271494057095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32808967791787028658742793 24606725843840271494057095)
  ·
    refine ⟨36910088765760407241085643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24606725843840271494057095 36910088765760407241085643)
    ·
      refine ⟨55365133148640610861628465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36910088765760407241085643 55365133148640610861628465)
      ·
        refine ⟨41523849861480458146221349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55365133148640610861628465 41523849861480458146221349)
        ·
          refine ⟨7785721849027585902416503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41523849861480458146221349 7785721849027585902416503)
          ·
            refine ⟨11678582773541378853624755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7785721849027585902416503 11678582773541378853624755)
            ·
              refine ⟨17517874160312068280437133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11678582773541378853624755 17517874160312068280437133)
              ·
                refine ⟨6569202810117025605163925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17517874160312068280437133 6569202810117025605163925)
                ·
                  refine ⟨307931381724235575242059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6569202810117025605163925 307931381724235575242059)
                  ·
                    rfl

theorem cell21_1349312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_1349312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349312 prefixEnd_1349312 := by exact prefixLift 1349312
  have htrace : WordTrace (prefixWord ++ tailWord_1349312) baseStart_1349312 baseEnd_1349312 := by
    simpa [prefixWord, tailWord_1349312, baseEnd_1349312] using wordTrace_append hprefix tailTrace_1349312
  have hstable : (prefixWord ++ tailWord_1349312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349312).length < 2 ^ (prefixWord ++ tailWord_1349312).sum := by decide
  have hdescent : baseEnd_1349312 < baseStart_1349312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349318 : List Nat := [6, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1349318 : Nat := 118140960795 + 1349318 * 2 ^ 59
def prefixEnd_1349318 : Nat := 4983230072969 + 3 ^ 40 * 1349318 * 2
def baseEnd_1349318 : Nat := 102644250335326966047349

theorem tailTrace_1349318 : CollatzResearch.WordTrace tailWord_1349318 prefixEnd_1349318 102644250335326966047349 := by
  unfold tailWord_1349318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1537927203926837687901019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32809113683772537341888405 1537927203926837687901019)
  ·
    refine ⟨2306890805890256531851529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1537927203926837687901019 2306890805890256531851529)
    ·
      refine ⟨1730168104417692398888647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2306890805890256531851529 1730168104417692398888647)
      ·
        refine ⟨2595252156626538598332971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1730168104417692398888647 2595252156626538598332971)
        ·
          refine ⟨3892878234939807897499457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595252156626538598332971 3892878234939807897499457)
          ·
            refine ⟨2919658676204855923124593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892878234939807897499457 2919658676204855923124593)
            ·
              refine ⟨2189744007153641942343445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919658676204855923124593 2189744007153641942343445)
              ·
                refine ⟨102644250335326966047349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2189744007153641942343445 102644250335326966047349)
                ·
                  rfl

theorem cell21_1349318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1349318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349318 prefixEnd_1349318 := by exact prefixLift 1349318
  have htrace : WordTrace (prefixWord ++ tailWord_1349318) baseStart_1349318 baseEnd_1349318 := by
    simpa [prefixWord, tailWord_1349318, baseEnd_1349318] using wordTrace_append hprefix tailTrace_1349318
  have hstable : (prefixWord ++ tailWord_1349318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349318).length < 2 ^ (prefixWord ++ tailWord_1349318).sum := by decide
  have hdescent : baseEnd_1349318 < baseStart_1349318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349329 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 4]
def baseStart_1349329 : Nat := 118140960795 + 1349329 * 2 ^ 59
def prefixEnd_1349329 : Nat := 4983230072969 + 3 ^ 40 * 1349329 * 2
def baseEnd_1349329 : Nat := 307935261355847323458691

theorem tailTrace_1349329 : CollatzResearch.WordTrace tailWord_1349329 prefixEnd_1349329 307935261355847323458691 := by
  unfold tailWord_1349329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49214071728618954891483041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32809381152412636594322027 49214071728618954891483041)
  ·
    refine ⟨36910553796464216168612281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49214071728618954891483041 36910553796464216168612281)
    ·
      refine ⟨27682915347348162126459211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36910553796464216168612281 27682915347348162126459211)
      ·
        refine ⟨41524373021022243189688817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27682915347348162126459211 41524373021022243189688817)
        ·
          refine ⟨31143279765766682392266613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41524373021022243189688817 31143279765766682392266613)
          ·
            refine ⟨2919682478040626474274995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31143279765766682392266613 2919682478040626474274995)
            ·
              refine ⟨4379523717060939711412493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919682478040626474274995 4379523717060939711412493)
              ·
                refine ⟨1642321393897852391779685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4379523717060939711412493 1642321393897852391779685)
                ·
                  refine ⟨307935261355847323458691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642321393897852391779685 307935261355847323458691)
                  ·
                    rfl

theorem cell21_1349329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_1349329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349329 prefixEnd_1349329 := by exact prefixLift 1349329
  have htrace : WordTrace (prefixWord ++ tailWord_1349329) baseStart_1349329 baseEnd_1349329 := by
    simpa [prefixWord, tailWord_1349329, baseEnd_1349329] using wordTrace_append hprefix tailTrace_1349329
  have hstable : (prefixWord ++ tailWord_1349329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349329).length < 2 ^ (prefixWord ++ tailWord_1349329).sum := by decide
  have hdescent : baseEnd_1349329 < baseStart_1349329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349422 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1349422 : Nat := 118140960795 + 1349422 * 2 ^ 59
def prefixEnd_1349422 : Nat := 4983230072969 + 3 ^ 40 * 1349422 * 2
def baseEnd_1349422 : Nat := 307956485222899828408501

theorem tailTrace_1349422 : CollatzResearch.WordTrace tailWord_1349422 prefixEnd_1349422 307956485222899828408501 := by
  unfold tailWord_1349422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152182964660253971827315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32811642478188021183079013 6152182964660253971827315)
  ·
    refine ⟨9228274446990380957740973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6152182964660253971827315 9228274446990380957740973)
    ·
      refine ⟨3460602917621392859152865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9228274446990380957740973 3460602917621392859152865)
      ·
        refine ⟨2595452188216044644364649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460602917621392859152865 2595452188216044644364649)
        ·
          refine ⟨1946589141162033483273487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595452188216044644364649 1946589141162033483273487)
          ·
            refine ⟨2919883711743050224910231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946589141162033483273487 2919883711743050224910231)
            ·
              refine ⟨4379825567614575337365347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919883711743050224910231 4379825567614575337365347)
              ·
                refine ⟨6569738351421863006048021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4379825567614575337365347 6569738351421863006048021)
                ·
                  refine ⟨307956485222899828408501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6569738351421863006048021 307956485222899828408501)
                  ·
                    rfl

theorem cell21_1349422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1349422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349422 prefixEnd_1349422 := by exact prefixLift 1349422
  have htrace : WordTrace (prefixWord ++ tailWord_1349422) baseStart_1349422 baseEnd_1349422 := by
    simpa [prefixWord, tailWord_1349422, baseEnd_1349422] using wordTrace_append hprefix tailTrace_1349422
  have hstable : (prefixWord ++ tailWord_1349422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349422).length < 2 ^ (prefixWord ++ tailWord_1349422).sum := by decide
  have hdescent : baseEnd_1349422 < baseStart_1349422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349453 : List Nat := [1, 6, 1, 2, 1, 1, 4, 5]
def baseStart_1349453 : Nat := 118140960795 + 1349453 * 2 ^ 59
def prefixEnd_1349453 : Nat := 4983230072969 + 3 ^ 40 * 1349453 * 2
def baseEnd_1349453 : Nat := 102654519948416887797257

theorem tailTrace_1349453 : CollatzResearch.WordTrace tailWord_1349453 prefixEnd_1349453 102654519948416887797257 := by
  unfold tailWord_1349453
  simp only [CollatzResearch.WordTrace]
  refine ⟨49218594380169724068997013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32812396253446482712664675 49218594380169724068997013)
  ·
    refine ⟨2307121611570455815734235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49218594380169724068997013 2307121611570455815734235)
    ·
      refine ⟨3460682417355683723601353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307121611570455815734235 3460682417355683723601353)
      ·
        refine ⟨2595511813016762792701015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460682417355683723601353 2595511813016762792701015)
        ·
          refine ⟨3893267719525144189051523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595511813016762792701015 3893267719525144189051523)
          ·
            refine ⟨5839901579287716283577285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893267719525144189051523 5839901579287716283577285)
            ·
              refine ⟨1094981546116446803170741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5839901579287716283577285 1094981546116446803170741)
              ·
                refine ⟨102654519948416887797257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1094981546116446803170741 102654519948416887797257)
                ·
                  rfl

theorem cell21_1349453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 4, 5].length) (baseStart_1349453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349453 prefixEnd_1349453 := by exact prefixLift 1349453
  have htrace : WordTrace (prefixWord ++ tailWord_1349453) baseStart_1349453 baseEnd_1349453 := by
    simpa [prefixWord, tailWord_1349453, baseEnd_1349453] using wordTrace_append hprefix tailTrace_1349453
  have hstable : (prefixWord ++ tailWord_1349453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349453).length < 2 ^ (prefixWord ++ tailWord_1349453).sum := by decide
  have hdescent : baseEnd_1349453 < baseStart_1349453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349484 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1349484 : Nat := 118140960795 + 1349484 * 2 ^ 59
def prefixEnd_1349484 : Nat := 4983230072969 + 3 ^ 40 * 1349484 * 2
def baseEnd_1349484 : Nat := 307970634467601498375041

theorem tailTrace_1349484 : CollatzResearch.WordTrace tailWord_1349484 prefixEnd_1349484 307970634467601498375041 := by
  unfold tailWord_1349484
  simp only [CollatzResearch.WordTrace]
  refine ⟨24609862521528708181687753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32813150028704944242250337 24609862521528708181687753)
  ·
    refine ⟨18457396891146531136265815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24609862521528708181687753 18457396891146531136265815)
    ·
      refine ⟨27686095336719796704398723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18457396891146531136265815 27686095336719796704398723)
      ·
        refine ⟨41529143005079695056598085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27686095336719796704398723 41529143005079695056598085)
        ·
          refine ⟨7786714313452442823112141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41529143005079695056598085 7786714313452442823112141)
          ·
            refine ⟨2920017867544666058667053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7786714313452442823112141 2920017867544666058667053)
            ·
              refine ⟨1095006700329249772000145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2920017867544666058667053 1095006700329249772000145)
              ·
                refine ⟨821255025246937329000109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095006700329249772000145 821255025246937329000109)
                ·
                  refine ⟨307970634467601498375041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821255025246937329000109 307970634467601498375041)
                  ·
                    rfl

theorem cell21_1349484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1349484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349484 prefixEnd_1349484 := by exact prefixLift 1349484
  have htrace : WordTrace (prefixWord ++ tailWord_1349484) baseStart_1349484 baseEnd_1349484 := by
    simpa [prefixWord, tailWord_1349484, baseEnd_1349484] using wordTrace_append hprefix tailTrace_1349484
  have hstable : (prefixWord ++ tailWord_1349484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349484).length < 2 ^ (prefixWord ++ tailWord_1349484).sum := by decide
  have hdescent : baseEnd_1349484 < baseStart_1349484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349509 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 7]
def baseStart_1349509 : Nat := 118140960795 + 1349509 * 2 ^ 59
def prefixEnd_1349509 : Nat := 4983230072969 + 3 ^ 40 * 1349509 * 2
def baseEnd_1349509 : Nat := 307976339808207010458323

theorem tailTrace_1349509 : CollatzResearch.WordTrace tailWord_1349509 prefixEnd_1349509 307976339808207010458323 := by
  unfold tailWord_1349509
  simp only [CollatzResearch.WordTrace]
  refine ⟨49220636867966845633035581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32813757911977897088690387 49220636867966845633035581)
  ·
    refine ⟨18457738825487567112388343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49220636867966845633035581 18457738825487567112388343)
    ·
      refine ⟨27686608238231350668582515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18457738825487567112388343 27686608238231350668582515)
      ·
        refine ⟨41529912357347026002873773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27686608238231350668582515 41529912357347026002873773)
        ·
          refine ⟨15573717134005134751077665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41529912357347026002873773 15573717134005134751077665)
          ·
            refine ⟨11680287850503851063308249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15573717134005134751077665 11680287850503851063308249)
            ·
              refine ⟨8760215887877888297481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11680287850503851063308249 8760215887877888297481187)
              ·
                refine ⟨13140323831816832446221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8760215887877888297481187 13140323831816832446221781)
                ·
                  refine ⟨307976339808207010458323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13140323831816832446221781 307976339808207010458323)
                  ·
                    rfl

theorem cell21_1349509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_1349509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349509 prefixEnd_1349509 := by exact prefixLift 1349509
  have htrace : WordTrace (prefixWord ++ tailWord_1349509) baseStart_1349509 baseEnd_1349509 := by
    simpa [prefixWord, tailWord_1349509, baseEnd_1349509] using wordTrace_append hprefix tailTrace_1349509
  have hstable : (prefixWord ++ tailWord_1349509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349509).length < 2 ^ (prefixWord ++ tailWord_1349509).sum := by decide
  have hdescent : baseEnd_1349509 < baseStart_1349509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349557 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 4]
def baseStart_1349557 : Nat := 118140960795 + 1349557 * 2 ^ 59
def prefixEnd_1349557 : Nat := 4983230072969 + 3 ^ 40 * 1349557 * 2
def baseEnd_1349557 : Nat := 307987294062169593658225

theorem tailTrace_1349557 : CollatzResearch.WordTrace tailWord_1349557 prefixEnd_1349557 307987294062169593658225 := by
  unfold tailWord_1349557
  simp only [CollatzResearch.WordTrace]
  refine ⟨49222387571792949830782925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32814925047861966553855283 49222387571792949830782925)
  ·
    refine ⟨18458395339422356186543597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49222387571792949830782925 18458395339422356186543597)
    ·
      refine ⟨6921898252283383569953849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18458395339422356186543597 6921898252283383569953849)
      ·
        refine ⟨5191423689212537677465387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6921898252283383569953849 5191423689212537677465387)
        ·
          refine ⟨7787135533818806516198081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191423689212537677465387 7787135533818806516198081)
          ·
            refine ⟨5840351650364104887148561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787135533818806516198081 5840351650364104887148561)
            ·
              refine ⟨4380263737773078665361421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5840351650364104887148561 4380263737773078665361421)
              ·
                refine ⟨1642598901664904499510533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4380263737773078665361421 1642598901664904499510533)
                ·
                  refine ⟨307987294062169593658225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642598901664904499510533 307987294062169593658225)
                  ·
                    rfl

theorem cell21_1349557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_1349557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349557 prefixEnd_1349557 := by exact prefixLift 1349557
  have htrace : WordTrace (prefixWord ++ tailWord_1349557) baseStart_1349557 baseEnd_1349557 := by
    simpa [prefixWord, tailWord_1349557, baseEnd_1349557] using wordTrace_append hprefix tailTrace_1349557
  have hstable : (prefixWord ++ tailWord_1349557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349557).length < 2 ^ (prefixWord ++ tailWord_1349557).sum := by decide
  have hdescent : baseEnd_1349557 < baseStart_1349557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349616 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1349616 : Nat := 118140960795 + 1349616 * 2 ^ 59
def prefixEnd_1349616 : Nat := 4983230072969 + 3 ^ 40 * 1349616 * 2
def baseEnd_1349616 : Nat := 308000758665998602174771

theorem tailTrace_1349616 : CollatzResearch.WordTrace tailWord_1349616 prefixEnd_1349616 308000758665998602174771 := by
  unfold tailWord_1349616
  simp only [CollatzResearch.WordTrace]
  refine ⟨24612269739289601453590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32816359652386135271453801 24612269739289601453590351)
  ·
    refine ⟨36918404608934402180385527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24612269739289601453590351 36918404608934402180385527)
    ·
      refine ⟨55377606913401603270578291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36918404608934402180385527 55377606913401603270578291)
      ·
        refine ⟨83066410370102404905867437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55377606913401603270578291 83066410370102404905867437)
        ·
          refine ⟨31149903888788401839700289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83066410370102404905867437 31149903888788401839700289)
          ·
            refine ⟨23362427916591301379775217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31149903888788401839700289 23362427916591301379775217)
            ·
              refine ⟨17521820937443476034831413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23362427916591301379775217 17521820937443476034831413)
              ·
                refine ⟨1642670712885325878265445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17521820937443476034831413 1642670712885325878265445)
                ·
                  refine ⟨308000758665998602174771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642670712885325878265445 308000758665998602174771)
                  ·
                    rfl

theorem cell21_1349616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1349616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349616 prefixEnd_1349616 := by exact prefixLift 1349616
  have htrace : WordTrace (prefixWord ++ tailWord_1349616) baseStart_1349616 baseEnd_1349616 := by
    simpa [prefixWord, tailWord_1349616, baseEnd_1349616] using wordTrace_append hprefix tailTrace_1349616
  have hstable : (prefixWord ++ tailWord_1349616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349616).length < 2 ^ (prefixWord ++ tailWord_1349616).sum := by decide
  have hdescent : baseEnd_1349616 < baseStart_1349616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349622 : List Nat := [5, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1349622 : Nat := 118140960795 + 1349622 * 2 ^ 59
def prefixEnd_1349622 : Nat := 4983230072969 + 3 ^ 40 * 1349622 * 2
def baseEnd_1349622 : Nat := 102667375982581308358253

theorem tailTrace_1349622 : CollatzResearch.WordTrace tailWord_1349622 prefixEnd_1349622 102667375982581308358253 := by
  unfold tailWord_1349622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076547394784841620743695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32816505544371643954599413 3076547394784841620743695)
  ·
    refine ⟨4614821092177262431115543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076547394784841620743695 4614821092177262431115543)
    ·
      refine ⟨6922231638265893646673315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4614821092177262431115543 6922231638265893646673315)
      ·
        refine ⟨10383347457398840470009973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6922231638265893646673315 10383347457398840470009973)
        ·
          refine ⟨973438824131141294063435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10383347457398840470009973 973438824131141294063435)
          ·
            refine ⟨1460158236196711941095153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973438824131141294063435 1460158236196711941095153)
            ·
              refine ⟨1095118677147533955821365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460158236196711941095153 1095118677147533955821365)
              ·
                refine ⟨102667375982581308358253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1095118677147533955821365 102667375982581308358253)
                ·
                  rfl

theorem cell21_1349622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1349622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349622 prefixEnd_1349622 := by exact prefixLift 1349622
  have htrace : WordTrace (prefixWord ++ tailWord_1349622) baseStart_1349622 baseEnd_1349622 := by
    simpa [prefixWord, tailWord_1349622, baseEnd_1349622] using wordTrace_append hprefix tailTrace_1349622
  have hstable : (prefixWord ++ tailWord_1349622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349622).length < 2 ^ (prefixWord ++ tailWord_1349622).sum := by decide
  have hdescent : baseEnd_1349622 < baseStart_1349622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349675 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 8]
def baseStart_1349675 : Nat := 118140960795 + 1349675 * 2 ^ 59
def prefixEnd_1349675 : Nat := 4983230072969 + 3 ^ 40 * 1349675 * 2
def baseEnd_1349675 : Nat := 308014223269827610691317

theorem tailTrace_1349675 : CollatzResearch.WordTrace tailWord_1349675 prefixEnd_1349675 308014223269827610691317 := by
  unfold tailWord_1349675
  simp only [CollatzResearch.WordTrace]
  refine ⟨49226691385365455983578479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32817794256910303989052319 49226691385365455983578479)
  ·
    refine ⟨73840037078048183975367719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49226691385365455983578479 73840037078048183975367719)
    ·
      refine ⟨110760055617072275963051579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73840037078048183975367719 110760055617072275963051579)
      ·
        refine ⟨166140083425608413944577369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110760055617072275963051579 166140083425608413944577369)
        ·
          refine ⟨124605062569206310458433027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166140083425608413944577369 124605062569206310458433027)
          ·
            refine ⟨186907593853809465687649541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124605062569206310458433027 186907593853809465687649541)
            ·
              refine ⟨35045173847589274816434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 186907593853809465687649541 35045173847589274816434289)
              ·
                refine ⟨26283880385691956112325717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35045173847589274816434289 26283880385691956112325717)
                ·
                  refine ⟨308014223269827610691317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26283880385691956112325717 308014223269827610691317)
                  ·
                    rfl

theorem cell21_1349675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 8].length) (baseStart_1349675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349675 prefixEnd_1349675 := by exact prefixLift 1349675
  have htrace : WordTrace (prefixWord ++ tailWord_1349675) baseStart_1349675 baseEnd_1349675 := by
    simpa [prefixWord, tailWord_1349675, baseEnd_1349675] using wordTrace_append hprefix tailTrace_1349675
  have hstable : (prefixWord ++ tailWord_1349675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349675).length < 2 ^ (prefixWord ++ tailWord_1349675).sum := by decide
  have hdescent : baseEnd_1349675 < baseStart_1349675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349737 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 5]
def baseStart_1349737 : Nat := 118140960795 + 1349737 * 2 ^ 59
def prefixEnd_1349737 : Nat := 4983230072969 + 3 ^ 40 * 1349737 * 2
def baseEnd_1349737 : Nat := 308028372514529280657857

theorem tailTrace_1349737 : CollatzResearch.WordTrace tailWord_1349737 prefixEnd_1349737 308028372514529280657857 := by
  unfold tailWord_1349737
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228952711140840572335465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32819301807427227048223643 49228952711140840572335465)
  ·
    refine ⟨36921714533355630429251599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49228952711140840572335465 36921714533355630429251599)
    ·
      refine ⟨55382571800033445643877399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36921714533355630429251599 55382571800033445643877399)
      ·
        refine ⟨83073857700050168465816099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55382571800033445643877399 83073857700050168465816099)
        ·
          refine ⟨124610786550075252698724149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83073857700050168465816099 124610786550075252698724149)
          ·
            refine ⟨11682261239069554940505389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 124610786550075252698724149 11682261239069554940505389)
            ·
              refine ⟨4380847964651083102689521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11682261239069554940505389 4380847964651083102689521)
              ·
                refine ⟨3285635973488312327017141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4380847964651083102689521 3285635973488312327017141)
                ·
                  refine ⟨308028372514529280657857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3285635973488312327017141 308028372514529280657857)
                  ·
                    rfl

theorem cell21_1349737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_1349737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349737 prefixEnd_1349737 := by exact prefixLift 1349737
  have htrace : WordTrace (prefixWord ++ tailWord_1349737) baseStart_1349737 baseEnd_1349737 := by
    simpa [prefixWord, tailWord_1349737, baseEnd_1349737] using wordTrace_append hprefix tailTrace_1349737
  have hstable : (prefixWord ++ tailWord_1349737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349737).length < 2 ^ (prefixWord ++ tailWord_1349737).sum := by decide
  have hdescent : baseEnd_1349737 < baseStart_1349737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349836 : List Nat := [2, 2, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1349836 : Nat := 118140960795 + 1349836 * 2 ^ 59
def prefixEnd_1349836 : Nat := 4983230072969 + 3 ^ 40 * 1349836 * 2
def baseEnd_1349836 : Nat := 308050965663327108507655

theorem tailTrace_1349836 : CollatzResearch.WordTrace tailWord_1349836 prefixEnd_1349836 308050965663327108507655 := by
  unfold tailWord_1349836
  simp only [CollatzResearch.WordTrace]
  refine ⟨24616281768891090240094681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32821709025188120320126241 24616281768891090240094681)
  ·
    refine ⟨18462211326668317680071011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24616281768891090240094681 18462211326668317680071011)
    ·
      refine ⟨27693316990002476520106517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18462211326668317680071011 27693316990002476520106517)
      ·
        refine ⟨1298124233906366086879993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27693316990002476520106517 1298124233906366086879993)
        ·
          refine ⟨973593175429774565159995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1298124233906366086879993 973593175429774565159995)
          ·
            refine ⟨1460389763144661847739993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973593175429774565159995 1460389763144661847739993)
            ·
              refine ⟨1095292322358496385804995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460389763144661847739993 1095292322358496385804995)
              ·
                refine ⟨1642938483537744578707493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095292322358496385804995 1642938483537744578707493)
                ·
                  refine ⟨308050965663327108507655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1642938483537744578707493 308050965663327108507655)
                  ·
                    rfl

theorem cell21_1349836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1349836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349836 prefixEnd_1349836 := by exact prefixLift 1349836
  have htrace : WordTrace (prefixWord ++ tailWord_1349836) baseStart_1349836 baseEnd_1349836 := by
    simpa [prefixWord, tailWord_1349836, baseEnd_1349836] using wordTrace_append hprefix tailTrace_1349836
  have hstable : (prefixWord ++ tailWord_1349836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349836).length < 2 ^ (prefixWord ++ tailWord_1349836).sum := by decide
  have hdescent : baseEnd_1349836 < baseStart_1349836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349889 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 5]
def baseStart_1349889 : Nat := 118140960795 + 1349889 * 2 ^ 59
def prefixEnd_1349889 : Nat := 4983230072969 + 3 ^ 40 * 1349889 * 2
def baseEnd_1349889 : Nat := 308063060985410794124213

theorem tailTrace_1349889 : CollatzResearch.WordTrace tailWord_1349889 prefixEnd_1349889 308063060985410794124213 := by
  unfold tailWord_1349889
  simp only [CollatzResearch.WordTrace]
  refine ⟨49234496606590170531868721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32822997737726780354579147 49234496606590170531868721)
  ·
    refine ⟨36925872454942627898901541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49234496606590170531868721 36925872454942627898901541)
    ·
      refine ⟨6923601085301742731044039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36925872454942627898901541 6923601085301742731044039)
      ·
        refine ⟨10385401627952614096566059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6923601085301742731044039 10385401627952614096566059)
        ·
          refine ⟨15578102441928921144849089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10385401627952614096566059 15578102441928921144849089)
          ·
            refine ⟨11683576831446690858636817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15578102441928921144849089 11683576831446690858636817)
            ·
              refine ⟨8762682623585018143977613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11683576831446690858636817 8762682623585018143977613)
              ·
                refine ⟨3286005983844381803991605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8762682623585018143977613 3286005983844381803991605)
                ·
                  refine ⟨308063060985410794124213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3286005983844381803991605 308063060985410794124213)
                  ·
                    rfl

theorem cell21_1349889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 5].length) (baseStart_1349889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349889 prefixEnd_1349889 := by exact prefixLift 1349889
  have htrace : WordTrace (prefixWord ++ tailWord_1349889) baseStart_1349889 baseEnd_1349889 := by
    simpa [prefixWord, tailWord_1349889, baseEnd_1349889] using wordTrace_append hprefix tailTrace_1349889
  have hstable : (prefixWord ++ tailWord_1349889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349889).length < 2 ^ (prefixWord ++ tailWord_1349889).sum := by decide
  have hdescent : baseEnd_1349889 < baseStart_1349889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349892 : List Nat := [2, 3, 2, 2, 3, 2, 1, 6]
def baseStart_1349892 : Nat := 118140960795 + 1349892 * 2 ^ 59
def prefixEnd_1349892 : Nat := 4983230072969 + 3 ^ 40 * 1349892 * 2
def baseEnd_1349892 : Nat := 102687915208761151858069

theorem tailTrace_1349892 : CollatzResearch.WordTrace tailWord_1349892 prefixEnd_1349892 102687915208761151858069 := by
  unfold tailWord_1349892
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617303012789651022113965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32823070683719534696151953 24617303012789651022113965)
  ·
    refine ⟨9231488629796119133292737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24617303012789651022113965 9231488629796119133292737)
    ·
      refine ⟨6923616472347089349969553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9231488629796119133292737 6923616472347089349969553)
      ·
        refine ⟨5192712354260317012477165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6923616472347089349969553 5192712354260317012477165)
        ·
          refine ⟨1947267132847618879678937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5192712354260317012477165 1947267132847618879678937)
          ·
            refine ⟨1460450349635714159759203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947267132847618879678937 1460450349635714159759203)
            ·
              refine ⟨2190675524453571239638805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460450349635714159759203 2190675524453571239638805)
              ·
                refine ⟨102687915208761151858069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2190675524453571239638805 102687915208761151858069)
                ·
                  rfl

theorem cell21_1349892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_1349892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1349892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1349892 prefixEnd_1349892 := by exact prefixLift 1349892
  have htrace : WordTrace (prefixWord ++ tailWord_1349892) baseStart_1349892 baseEnd_1349892 := by
    simpa [prefixWord, tailWord_1349892, baseEnd_1349892] using wordTrace_append hprefix tailTrace_1349892
  have hstable : (prefixWord ++ tailWord_1349892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349892).length < 2 ^ (prefixWord ++ tailWord_1349892).sum := by decide
  have hdescent : baseEnd_1349892 < baseStart_1349892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350013 : List Nat := [1, 4, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1350013 : Nat := 118140960795 + 1350013 * 2 ^ 59
def prefixEnd_1350013 : Nat := 4983230072969 + 3 ^ 40 * 1350013 * 2
def baseEnd_1350013 : Nat := 308091359474814134057293

theorem tailTrace_1350013 : CollatzResearch.WordTrace tailWord_1350013 prefixEnd_1350013 308091359474814134057293 := by
  unfold tailWord_1350013
  simp only [CollatzResearch.WordTrace]
  refine ⟨49239019258140939709382693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32826012838760626472921795 49239019258140939709382693)
  ·
    refine ⟨9232316110901426195509255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49239019258140939709382693 9232316110901426195509255)
    ·
      refine ⟨13848474166352139293263883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9232316110901426195509255 13848474166352139293263883)
      ·
        refine ⟨20772711249528208939895825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13848474166352139293263883 20772711249528208939895825)
        ·
          refine ⟨15579533437146156704921869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20772711249528208939895825 15579533437146156704921869)
          ·
            refine ⟨5842325038929808764345701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15579533437146156704921869 5842325038929808764345701)
            ·
              refine ⟨1095435944799339143314819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5842325038929808764345701 1095435944799339143314819)
              ·
                refine ⟨1643153917199008714972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095435944799339143314819 1643153917199008714972229)
                ·
                  refine ⟨308091359474814134057293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643153917199008714972229 308091359474814134057293)
                  ·
                    rfl

theorem cell21_1350013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1350013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350013 prefixEnd_1350013 := by exact prefixLift 1350013
  have htrace : WordTrace (prefixWord ++ tailWord_1350013) baseStart_1350013 baseEnd_1350013 := by
    simpa [prefixWord, tailWord_1350013, baseEnd_1350013] using wordTrace_append hprefix tailTrace_1350013
  have hstable : (prefixWord ++ tailWord_1350013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350013).length < 2 ^ (prefixWord ++ tailWord_1350013).sum := by decide
  have hdescent : baseEnd_1350013 < baseStart_1350013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350061 : List Nat := [1, 5, 2, 2, 3, 1, 1, 6]
def baseStart_1350061 : Nat := 118140960795 + 1350061 * 2 ^ 59
def prefixEnd_1350061 : Nat := 4983230072969 + 3 ^ 40 * 1350061 * 2
def baseEnd_1350061 : Nat := 102700771242925572419065

theorem tailTrace_1350061 : CollatzResearch.WordTrace tailWord_1350061 prefixEnd_1350061 102700771242925572419065 := by
  unfold tailWord_1350061
  simp only [CollatzResearch.WordTrace]
  refine ⟨49240769961967043907130037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32827179974644695938086691 49240769961967043907130037)
  ·
    refine ⟨4616322183934410366293441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49240769961967043907130037 4616322183934410366293441)
    ·
      refine ⟨3462241637950807774720081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4616322183934410366293441 3462241637950807774720081)
      ·
        refine ⟨2596681228463105831040061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3462241637950807774720081 2596681228463105831040061)
        ·
          refine ⟨973755460673664686640023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2596681228463105831040061 973755460673664686640023)
          ·
            refine ⟨1460633191010497029960035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973755460673664686640023 1460633191010497029960035)
            ·
              refine ⟨2190949786515745544940053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460633191010497029960035 2190949786515745544940053)
              ·
                refine ⟨102700771242925572419065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2190949786515745544940053 102700771242925572419065)
                ·
                  rfl

theorem cell21_1350061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 6].length) (baseStart_1350061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350061 prefixEnd_1350061 := by exact prefixLift 1350061
  have htrace : WordTrace (prefixWord ++ tailWord_1350061) baseStart_1350061 baseEnd_1350061 := by
    simpa [prefixWord, tailWord_1350061, baseEnd_1350061] using wordTrace_append hprefix tailTrace_1350061
  have hstable : (prefixWord ++ tailWord_1350061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350061).length < 2 ^ (prefixWord ++ tailWord_1350061).sum := by decide
  have hdescent : baseEnd_1350061 < baseStart_1350061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350148 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1350148 : Nat := 118140960795 + 1350148 * 2 ^ 59
def prefixEnd_1350148 : Nat := 4983230072969 + 3 ^ 40 * 1350148 * 2
def baseEnd_1350148 : Nat := 308122168314083899307017

theorem tailTrace_1350148 : CollatzResearch.WordTrace tailWord_1350148 prefixEnd_1350148 308122168314083899307017 := by
  unfold tailWord_1350148
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621971556325928882773549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32829295408434571843698065 24621971556325928882773549)
  ·
    refine ⟨9233239333622223331040081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24621971556325928882773549 9233239333622223331040081)
    ·
      refine ⟨6924929500216667498280061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9233239333622223331040081 6924929500216667498280061)
      ·
        refine ⟨2596848562581250311855023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6924929500216667498280061 2596848562581250311855023)
        ·
          refine ⟨3895272843871875467782535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2596848562581250311855023 3895272843871875467782535)
          ·
            refine ⟨5842909265807813201673803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895272843871875467782535 5842909265807813201673803)
            ·
              refine ⟨8764363898711719802510705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842909265807813201673803 8764363898711719802510705)
              ·
                refine ⟨6573272924033789851883029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8764363898711719802510705 6573272924033789851883029)
                ·
                  refine ⟨308122168314083899307017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6573272924033789851883029 308122168314083899307017)
                  ·
                    rfl

theorem cell21_1350148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1350148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350148 prefixEnd_1350148 := by exact prefixLift 1350148
  have htrace : WordTrace (prefixWord ++ tailWord_1350148) baseStart_1350148 baseEnd_1350148 := by
    simpa [prefixWord, tailWord_1350148, baseEnd_1350148] using wordTrace_append hprefix tailTrace_1350148
  have hstable : (prefixWord ++ tailWord_1350148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350148).length < 2 ^ (prefixWord ++ tailWord_1350148).sum := by decide
  have hdescent : baseEnd_1350148 < baseStart_1350148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350252 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1350252 : Nat := 118140960795 + 1350252 * 2 ^ 59
def prefixEnd_1350252 : Nat := 4983230072969 + 3 ^ 40 * 1350252 * 2
def baseEnd_1350252 : Nat := 308145902531002829573471

theorem tailTrace_1350252 : CollatzResearch.WordTrace tailWord_1350252 prefixEnd_1350252 308145902531002829573471 := by
  unfold tailWord_1350252
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623868152137541763666505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32831824202850055684888673 24623868152137541763666505)
  ·
    refine ⟨18467901114103156322749879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24623868152137541763666505 18467901114103156322749879)
    ·
      refine ⟨27701851671154734484124819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18467901114103156322749879 27701851671154734484124819)
      ·
        refine ⟨41552777506732101726187229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27701851671154734484124819 41552777506732101726187229)
        ·
          refine ⟨15582291565024538147320211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41552777506732101726187229 15582291565024538147320211)
          ·
            refine ⟨23373437347536807220980317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15582291565024538147320211 23373437347536807220980317)
            ·
              refine ⟨8765039005326302707867619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23373437347536807220980317 8765039005326302707867619)
              ·
                refine ⟨13147558507989454061801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8765039005326302707867619 13147558507989454061801429)
                ·
                  refine ⟨308145902531002829573471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13147558507989454061801429 308145902531002829573471)
                  ·
                    rfl

theorem cell21_1350252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1350252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350252 prefixEnd_1350252 := by exact prefixLift 1350252
  have htrace : WordTrace (prefixWord ++ tailWord_1350252) baseStart_1350252 baseEnd_1350252 := by
    simpa [prefixWord, tailWord_1350252, baseEnd_1350252] using wordTrace_append hprefix tailTrace_1350252
  have hstable : (prefixWord ++ tailWord_1350252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350252).length < 2 ^ (prefixWord ++ tailWord_1350252).sum := by decide
  have hdescent : baseEnd_1350252 < baseStart_1350252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350283 : List Nat := [1, 1, 1, 1, 4, 1, 2, 6, 4]
def baseStart_1350283 : Nat := 118140960795 + 1350283 * 2 ^ 59
def prefixEnd_1350283 : Nat := 4983230072969 + 3 ^ 40 * 1350283 * 2
def baseEnd_1350283 : Nat := 308152977153353664556741

theorem tailTrace_1350283 : CollatzResearch.WordTrace tailWord_1350283 prefixEnd_1350283 308152977153353664556741 := by
  unfold tailWord_1350283
  simp only [CollatzResearch.WordTrace]
  refine ⟨49248866967162775821711503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32832577978108517214474335 49248866967162775821711503)
  ·
    refine ⟨73873300450744163732567255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49248866967162775821711503 73873300450744163732567255)
    ·
      refine ⟨110809950676116245598850883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73873300450744163732567255 110809950676116245598850883)
      ·
        refine ⟨166214926014174368398276325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110809950676116245598850883 166214926014174368398276325)
        ·
          refine ⟨31165298627657694074676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166214926014174368398276325 31165298627657694074676811)
          ·
            refine ⟨46747947941486541112015217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31165298627657694074676811 46747947941486541112015217)
            ·
              refine ⟨35060960956114905834011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46747947941486541112015217 35060960956114905834011413)
              ·
                refine ⟨1643482544817886210969285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35060960956114905834011413 1643482544817886210969285)
                ·
                  refine ⟨308152977153353664556741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643482544817886210969285 308152977153353664556741)
                  ·
                    rfl

theorem cell21_1350283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 6, 4].length) (baseStart_1350283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350283 prefixEnd_1350283 := by exact prefixLift 1350283
  have htrace : WordTrace (prefixWord ++ tailWord_1350283) baseStart_1350283 baseEnd_1350283 := by
    simpa [prefixWord, tailWord_1350283, baseEnd_1350283] using wordTrace_append hprefix tailTrace_1350283
  have hstable : (prefixWord ++ tailWord_1350283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350283).length < 2 ^ (prefixWord ++ tailWord_1350283).sum := by decide
  have hdescent : baseEnd_1350283 < baseStart_1350283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350286 : List Nat := [4, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_1350286 : Nat := 118140960795 + 1350286 * 2 ^ 59
def prefixEnd_1350286 : Nat := 4983230072969 + 3 ^ 40 * 1350286 * 2
def baseEnd_1350286 : Nat := 308153661794226326006735

theorem tailTrace_1350286 : CollatzResearch.WordTrace tailWord_1350286 prefixEnd_1350286 308153661794226326006735 := by
  unfold tailWord_1350286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156122048268988416758839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32832650924101271556047141 6156122048268988416758839)
  ·
    refine ⟨9234183072403482625138259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156122048268988416758839 9234183072403482625138259)
    ·
      refine ⟨13851274608605223937707389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9234183072403482625138259 13851274608605223937707389)
      ·
        refine ⟨5194227978226958976640271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13851274608605223937707389 5194227978226958976640271)
        ·
          refine ⟨7791341967340438464960407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5194227978226958976640271 7791341967340438464960407)
          ·
            refine ⟨11687012951010657697440611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7791341967340438464960407 11687012951010657697440611)
            ·
              refine ⟨17530519426515986546160917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11687012951010657697440611 17530519426515986546160917)
              ·
                refine ⟨821743098117936869351293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17530519426515986546160917 821743098117936869351293)
                ·
                  refine ⟨308153661794226326006735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821743098117936869351293 308153661794226326006735)
                  ·
                    rfl

theorem cell21_1350286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_1350286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350286 prefixEnd_1350286 := by exact prefixLift 1350286
  have htrace : WordTrace (prefixWord ++ tailWord_1350286) baseStart_1350286 baseEnd_1350286 := by
    simpa [prefixWord, tailWord_1350286, baseEnd_1350286] using wordTrace_append hprefix tailTrace_1350286
  have hstable : (prefixWord ++ tailWord_1350286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350286).length < 2 ^ (prefixWord ++ tailWord_1350286).sum := by decide
  have hdescent : baseEnd_1350286 < baseStart_1350286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350297 : List Nat := [1, 2, 1, 2, 1, 2, 4, 8]
def baseStart_1350297 : Nat := 118140960795 + 1350297 * 2 ^ 59
def prefixEnd_1350297 : Nat := 4983230072969 + 3 ^ 40 * 1350297 * 2
def baseEnd_1350297 : Nat := 102718724048030917107793

theorem tailTrace_1350297 : CollatzResearch.WordTrace tailWord_1350297 prefixEnd_1350297 102718724048030917107793 := by
  unfold tailWord_1350297
  simp only [CollatzResearch.WordTrace]
  refine ⟨49249377589112056212721145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32832918392741370808480763 49249377589112056212721145)
  ·
    refine ⟨36937033191834042159540859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49249377589112056212721145 36937033191834042159540859)
    ·
      refine ⟨55405549787751063239311289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36937033191834042159540859 55405549787751063239311289)
      ·
        refine ⟨41554162340813297429483467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55405549787751063239311289 41554162340813297429483467)
        ·
          refine ⟨62331243511219946144225201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41554162340813297429483467 62331243511219946144225201)
          ·
            refine ⟨46748432633414959608168901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62331243511219946144225201 46748432633414959608168901)
            ·
              refine ⟨8765331118765304926531669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46748432633414959608168901 8765331118765304926531669)
              ·
                refine ⟨102718724048030917107793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8765331118765304926531669 102718724048030917107793)
                ·
                  rfl

theorem cell21_1350297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 8].length) (baseStart_1350297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350297 prefixEnd_1350297 := by exact prefixLift 1350297
  have htrace : WordTrace (prefixWord ++ tailWord_1350297) baseStart_1350297 baseEnd_1350297 := by
    simpa [prefixWord, tailWord_1350297, baseEnd_1350297] using wordTrace_append hprefix tailTrace_1350297
  have hstable : (prefixWord ++ tailWord_1350297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350297).length < 2 ^ (prefixWord ++ tailWord_1350297).sum := by decide
  have hdescent : baseEnd_1350297 < baseStart_1350297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350337 : List Nat := [1, 2, 6, 2, 1, 1, 3, 2, 3]
def baseStart_1350337 : Nat := 118140960795 + 1350337 * 2 ^ 59
def prefixEnd_1350337 : Nat := 4983230072969 + 3 ^ 40 * 1350337 * 2
def baseEnd_1350337 : Nat := 308165300689061570656631

theorem tailTrace_1350337 : CollatzResearch.WordTrace tailWord_1350337 prefixEnd_1350337 308165300689061570656631 := by
  unfold tailWord_1350337
  simp only [CollatzResearch.WordTrace]
  refine ⟨49250836508967143044177265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32833891005978095362784843 49250836508967143044177265)
  ·
    refine ⟨36938127381725357283132949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49250836508967143044177265 36938127381725357283132949)
    ·
      refine ⟨1731474721018376122646857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36938127381725357283132949 1731474721018376122646857)
      ·
        refine ⟨1298606040763782091985143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731474721018376122646857 1298606040763782091985143)
        ·
          refine ⟨1947909061145673137977715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298606040763782091985143 1947909061145673137977715)
          ·
            refine ⟨2921863591718509706966573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947909061145673137977715 2921863591718509706966573)
            ·
              refine ⟨1095698846894441140112465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2921863591718509706966573 1095698846894441140112465)
              ·
                refine ⟨821774135170830855084349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095698846894441140112465 821774135170830855084349)
                ·
                  refine ⟨308165300689061570656631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821774135170830855084349 308165300689061570656631)
                  ·
                    rfl

theorem cell21_1350337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 2, 3].length) (baseStart_1350337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350337 prefixEnd_1350337 := by exact prefixLift 1350337
  have htrace : WordTrace (prefixWord ++ tailWord_1350337) baseStart_1350337 baseEnd_1350337 := by
    simpa [prefixWord, tailWord_1350337, baseEnd_1350337] using wordTrace_append hprefix tailTrace_1350337
  have hstable : (prefixWord ++ tailWord_1350337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350337).length < 2 ^ (prefixWord ++ tailWord_1350337).sum := by decide
  have hdescent : baseEnd_1350337 < baseStart_1350337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350407 : List Nat := [1, 1, 4, 4, 1, 3, 1, 6]
def baseStart_1350407 : Nat := 118140960795 + 1350407 * 2 ^ 59
def prefixEnd_1350407 : Nat := 4983230072969 + 3 ^ 40 * 1350407 * 2
def baseEnd_1350407 : Nat := 102727091880919001496607

theorem tailTrace_1350407 : CollatzResearch.WordTrace tailWord_1350407 prefixEnd_1350407 102727091880919001496607 := by
  unfold tailWord_1350407
  simp only [CollatzResearch.WordTrace]
  refine ⟨49253389618713544999225475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32835593079142363332816983 49253389618713544999225475)
  ·
    refine ⟨73880084428070317498838213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49253389618713544999225475 73880084428070317498838213)
    ·
      refine ⟨13852515830263184531032165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73880084428070317498838213 13852515830263184531032165)
      ·
        refine ⟨2597346718174347099568531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13852515830263184531032165 2597346718174347099568531)
        ·
          refine ⟨3896020077261520649352797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597346718174347099568531 3896020077261520649352797)
          ·
            refine ⟨1461007528973070243507299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3896020077261520649352797 1461007528973070243507299)
            ·
              refine ⟨2191511293459605365260949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461007528973070243507299 2191511293459605365260949)
              ·
                refine ⟨102727091880919001496607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2191511293459605365260949 102727091880919001496607)
                ·
                  rfl

theorem cell21_1350407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 6].length) (baseStart_1350407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350407 prefixEnd_1350407 := by exact prefixLift 1350407
  have htrace : WordTrace (prefixWord ++ tailWord_1350407) baseStart_1350407 baseEnd_1350407 := by
    simpa [prefixWord, tailWord_1350407, baseEnd_1350407] using wordTrace_append hprefix tailTrace_1350407
  have hstable : (prefixWord ++ tailWord_1350407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350407).length < 2 ^ (prefixWord ++ tailWord_1350407).sum := by decide
  have hdescent : baseEnd_1350407 < baseStart_1350407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350449 : List Nat := [1, 2, 2, 3, 2, 1, 10]
def baseStart_1350449 : Nat := 118140960795 + 1350449 * 2 ^ 59
def prefixEnd_1350449 : Nat := 4983230072969 + 3 ^ 40 * 1350449 * 2
def baseEnd_1350449 : Nat := 34243428957219362754415

theorem tailTrace_1350449 : CollatzResearch.WordTrace tailWord_1350449 prefixEnd_1350449 34243428957219362754415 := by
  unfold tailWord_1350449
  simp only [CollatzResearch.WordTrace]
  refine ⟨49254921484561386172254401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32836614323040924114836267 49254921484561386172254401)
  ·
    refine ⟨36941191113421039629190801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49254921484561386172254401 36941191113421039629190801)
    ·
      refine ⟨27705893335065779721893101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36941191113421039629190801 27705893335065779721893101)
      ·
        refine ⟨10389710000649667395709913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27705893335065779721893101 10389710000649667395709913)
        ·
          refine ⟨7792282500487250546782435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10389710000649667395709913 7792282500487250546782435)
          ·
            refine ⟨11688423750730875820173653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7792282500487250546782435 11688423750730875820173653)
            ·
              refine ⟨34243428957219362754415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11688423750730875820173653 34243428957219362754415)
              ·
                rfl

theorem cell21_1350449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 10].length) (baseStart_1350449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350449 prefixEnd_1350449 := by exact prefixLift 1350449
  have htrace : WordTrace (prefixWord ++ tailWord_1350449) baseStart_1350449 baseEnd_1350449 := by
    simpa [prefixWord, tailWord_1350449, baseEnd_1350449] using wordTrace_append hprefix tailTrace_1350449
  have hstable : (prefixWord ++ tailWord_1350449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350449).length < 2 ^ (prefixWord ++ tailWord_1350449).sum := by decide
  have hdescent : baseEnd_1350449 < baseStart_1350449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350480 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1350480 : Nat := 118140960795 + 1350480 * 2 ^ 59
def prefixEnd_1350480 : Nat := 4983230072969 + 3 ^ 40 * 1350480 * 2
def baseEnd_1350480 : Nat := 308197935237325099773005

theorem tailTrace_1350480 : CollatzResearch.WordTrace tailWord_1350480 prefixEnd_1350480 308197935237325099773005 := by
  unfold tailWord_1350480
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628026073724539233316447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32837368098299385644421929 24628026073724539233316447)
  ·
    refine ⟨36942039110586808849974671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24628026073724539233316447 36942039110586808849974671)
    ·
      refine ⟨55413058665880213274962007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36942039110586808849974671 55413058665880213274962007)
      ·
        refine ⟨83119587998820319912443011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55413058665880213274962007 83119587998820319912443011)
        ·
          refine ⟨124679381998230479868664517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83119587998820319912443011 124679381998230479868664517)
          ·
            refine ⟨23377384124668214975374597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 124679381998230479868664517 23377384124668214975374597)
            ·
              refine ⟨4383259523375290307882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23377384124668214975374597 4383259523375290307882737)
              ·
                refine ⟨3287444642531467730912053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383259523375290307882737 3287444642531467730912053)
                ·
                  refine ⟨308197935237325099773005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287444642531467730912053 308197935237325099773005)
                  ·
                    rfl

theorem cell21_1350480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1350480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350480 prefixEnd_1350480 := by exact prefixLift 1350480
  have htrace : WordTrace (prefixWord ++ tailWord_1350480) baseStart_1350480 baseEnd_1350480 := by
    simpa [prefixWord, tailWord_1350480, baseEnd_1350480] using wordTrace_append hprefix tailTrace_1350480
  have hstable : (prefixWord ++ tailWord_1350480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350480).length < 2 ^ (prefixWord ++ tailWord_1350480).sum := by decide
  have hdescent : baseEnd_1350480 < baseStart_1350480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350497 : List Nat := [1, 2, 3, 1, 1, 1, 2, 7, 3]
def baseStart_1350497 : Nat := 118140960795 + 1350497 * 2 ^ 59
def prefixEnd_1350497 : Nat := 4983230072969 + 3 ^ 40 * 1350497 * 2
def baseEnd_1350497 : Nat := 308201814868936847989637

theorem tailTrace_1350497 : CollatzResearch.WordTrace tailWord_1350497 prefixEnd_1350497 308201814868936847989637 := by
  unfold tailWord_1350497
  simp only [CollatzResearch.WordTrace]
  refine ⟨49256672188387490370001745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32837781458924993580001163 49256672188387490370001745)
  ·
    refine ⟨36942504141290617777501309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49256672188387490370001745 36942504141290617777501309)
    ·
      refine ⟨13853439052983981666562991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36942504141290617777501309 13853439052983981666562991)
      ·
        refine ⟨20780158579475972499844487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13853439052983981666562991 20780158579475972499844487)
        ·
          refine ⟨31170237869213958749766731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20780158579475972499844487 31170237869213958749766731)
          ·
            refine ⟨46755356803820938124650097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31170237869213958749766731 46755356803820938124650097)
            ·
              refine ⟨35066517602865703593487573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46755356803820938124650097 35066517602865703593487573)
              ·
                refine ⟨821871506317164927972365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35066517602865703593487573 821871506317164927972365)
                ·
                  refine ⟨308201814868936847989637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821871506317164927972365 308201814868936847989637)
                  ·
                    rfl

theorem cell21_1350497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 7, 3].length) (baseStart_1350497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350497 prefixEnd_1350497 := by exact prefixLift 1350497
  have htrace : WordTrace (prefixWord ++ tailWord_1350497) baseStart_1350497 baseEnd_1350497 := by
    simpa [prefixWord, tailWord_1350497, baseEnd_1350497] using wordTrace_append hprefix tailTrace_1350497
  have hstable : (prefixWord ++ tailWord_1350497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350497).length < 2 ^ (prefixWord ++ tailWord_1350497).sum := by decide
  have hdescent : baseEnd_1350497 < baseStart_1350497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350525 : List Nat := [1, 4, 1, 1, 2, 1, 3, 8]
def baseStart_1350525 : Nat := 118140960795 + 1350525 * 2 ^ 59
def prefixEnd_1350525 : Nat := 4983230072969 + 3 ^ 40 * 1350525 * 2
def baseEnd_1350525 : Nat := 102736068283471673840971

theorem tailTrace_1350525 : CollatzResearch.WordTrace tailWord_1350525 prefixEnd_1350525 102736068283471673840971 := by
  unfold tailWord_1350525
  simp only [CollatzResearch.WordTrace]
  refine ⟨49257693432286051152021029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32838462288190700768014019 49257693432286051152021029)
  ·
    refine ⟨9235817518553634591003943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49257693432286051152021029 9235817518553634591003943)
    ·
      refine ⟨13853726277830451886505915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9235817518553634591003943 13853726277830451886505915)
      ·
        refine ⟨20780589416745677829758873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13853726277830451886505915 20780589416745677829758873)
        ·
          refine ⟨15585442062559258372319155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20780589416745677829758873 15585442062559258372319155)
          ·
            refine ⟨23378163093838887558478733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15585442062559258372319155 23378163093838887558478733)
            ·
              refine ⟨8766811160189582834429525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23378163093838887558478733 8766811160189582834429525)
              ·
                refine ⟨102736068283471673840971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8766811160189582834429525 102736068283471673840971)
                ·
                  rfl

theorem cell21_1350525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 8].length) (baseStart_1350525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350525 prefixEnd_1350525 := by exact prefixLift 1350525
  have htrace : WordTrace (prefixWord ++ tailWord_1350525) baseStart_1350525 baseEnd_1350525 := by
    simpa [prefixWord, tailWord_1350525, baseEnd_1350525] using wordTrace_append hprefix tailTrace_1350525
  have hstable : (prefixWord ++ tailWord_1350525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350525).length < 2 ^ (prefixWord ++ tailWord_1350525).sum := by decide
  have hdescent : baseEnd_1350525 < baseStart_1350525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350621 : List Nat := [1, 4, 3, 1, 2, 3, 1, 2, 4]
def baseStart_1350621 : Nat := 118140960795 + 1350621 * 2 ^ 59
def prefixEnd_1350621 : Nat := 4983230072969 + 3 ^ 40 * 1350621 * 2
def baseEnd_1350621 : Nat := 308230113358340187922717

theorem tailTrace_1350621 : CollatzResearch.WordTrace tailWord_1350621 prefixEnd_1350621 308230113358340187922717 := by
  unfold tailWord_1350621
  simp only [CollatzResearch.WordTrace]
  refine ⟨49261194839938259547515717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32840796559958839698343811 49261194839938259547515717)
  ·
    refine ⟨9236474032488423665159197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49261194839938259547515717 9236474032488423665159197)
    ·
      refine ⟨3463677762183158874434699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9236474032488423665159197 3463677762183158874434699)
      ·
        refine ⟨5195516643274738311652049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3463677762183158874434699 5195516643274738311652049)
        ·
          refine ⟨3896637482456053733739037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5195516643274738311652049 3896637482456053733739037)
          ·
            refine ⟨1461239055921020150152139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3896637482456053733739037 1461239055921020150152139)
            ·
              refine ⟨2191858583881530225228209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461239055921020150152139 2191858583881530225228209)
              ·
                refine ⟨1643893937911147668921157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191858583881530225228209 1643893937911147668921157)
                ·
                  refine ⟨308230113358340187922717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1643893937911147668921157 308230113358340187922717)
                  ·
                    rfl

theorem cell21_1350621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_1350621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350621 prefixEnd_1350621 := by exact prefixLift 1350621
  have htrace : WordTrace (prefixWord ++ tailWord_1350621) baseStart_1350621 baseEnd_1350621 := by
    simpa [prefixWord, tailWord_1350621, baseEnd_1350621] using wordTrace_append hprefix tailTrace_1350621
  have hstable : (prefixWord ++ tailWord_1350621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350621).length < 2 ^ (prefixWord ++ tailWord_1350621).sum := by decide
  have hdescent : baseEnd_1350621 < baseStart_1350621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350632 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_1350632 : Nat := 118140960795 + 1350632 * 2 ^ 59
def prefixEnd_1350632 : Nat := 4983230072969 + 3 ^ 40 * 1350632 * 2
def baseEnd_1350632 : Nat := 308232623708206613239361

theorem tailTrace_1350632 : CollatzResearch.WordTrace tailWord_1350632 prefixEnd_1350632 308232623708206613239361 := by
  unfold tailWord_1350632
  simp only [CollatzResearch.WordTrace]
  refine ⟨24630798021449204213083075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32841064028598938950777433 24630798021449204213083075)
  ·
    refine ⟨36946197032173806319624613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24630798021449204213083075 36946197032173806319624613)
    ·
      refine ⟨6927411943532588684929615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36946197032173806319624613 6927411943532588684929615)
      ·
        refine ⟨10391117915298883027394423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927411943532588684929615 10391117915298883027394423)
        ·
          refine ⟨15586676872948324541091635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10391117915298883027394423 15586676872948324541091635)
          ·
            refine ⟨23380015309422486811637453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15586676872948324541091635 23380015309422486811637453)
            ·
              refine ⟨8767505741033432554364045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23380015309422486811637453 8767505741033432554364045)
              ·
                refine ⟨3287814652887537207886517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767505741033432554364045 3287814652887537207886517)
                ·
                  refine ⟨308232623708206613239361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3287814652887537207886517 308232623708206613239361)
                  ·
                    rfl

theorem cell21_1350632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_1350632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350632 prefixEnd_1350632 := by exact prefixLift 1350632
  have htrace : WordTrace (prefixWord ++ tailWord_1350632) baseStart_1350632 baseEnd_1350632 := by
    simpa [prefixWord, tailWord_1350632, baseEnd_1350632] using wordTrace_append hprefix tailTrace_1350632
  have hstable : (prefixWord ++ tailWord_1350632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350632).length < 2 ^ (prefixWord ++ tailWord_1350632).sum := by decide
  have hdescent : baseEnd_1350632 < baseStart_1350632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350666 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_1350666 : Nat := 118140960795 + 1350666 * 2 ^ 59
def prefixEnd_1350666 : Nat := 4983230072969 + 3 ^ 40 * 1350666 * 2
def baseEnd_1350666 : Nat := 308240382971430109672625

theorem tailTrace_1350666 : CollatzResearch.WordTrace tailWord_1350666 prefixEnd_1350666 308240382971430109672625 := by
  unfold tailWord_1350666
  simp only [CollatzResearch.WordTrace]
  refine ⟨12315709031193808058225963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32841890749850154821935901 12315709031193808058225963)
  ·
    refine ⟨18473563546790712087338945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12315709031193808058225963 18473563546790712087338945)
    ·
      refine ⟨13855172660093034065504209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18473563546790712087338945 13855172660093034065504209)
      ·
        refine ⟨10391379495069775549128157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13855172660093034065504209 10391379495069775549128157)
        ·
          refine ⟨3896767310651165830923059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10391379495069775549128157 3896767310651165830923059)
          ·
            refine ⟨5845150965976748746384589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896767310651165830923059 5845150965976748746384589)
            ·
              refine ⟨2191931612241280779894221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5845150965976748746384589 2191931612241280779894221)
              ·
                refine ⟨821974354590480292460333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2191931612241280779894221 821974354590480292460333)
                ·
                  refine ⟨308240382971430109672625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 821974354590480292460333 308240382971430109672625)
                  ·
                    rfl

theorem cell21_1350666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_1350666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350666 prefixEnd_1350666 := by exact prefixLift 1350666
  have htrace : WordTrace (prefixWord ++ tailWord_1350666) baseStart_1350666 baseEnd_1350666 := by
    simpa [prefixWord, tailWord_1350666, baseEnd_1350666] using wordTrace_append hprefix tailTrace_1350666
  have hstable : (prefixWord ++ tailWord_1350666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350666).length < 2 ^ (prefixWord ++ tailWord_1350666).sum := by decide
  have hdescent : baseEnd_1350666 < baseStart_1350666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350677 : List Nat := [1, 3, 2, 1, 4, 1, 9]
def baseStart_1350677 : Nat := 118140960795 + 1350677 * 2 ^ 59
def prefixEnd_1350677 : Nat := 4983230072969 + 3 ^ 40 * 1350677 * 2
def baseEnd_1350677 : Nat := 34249210369032948332141

theorem tailTrace_1350677 : CollatzResearch.WordTrace tailWord_1350677 prefixEnd_1350677 34249210369032948332141 := by
  unfold tailWord_1350677
  simp only [CollatzResearch.WordTrace]
  refine ⟨49263237327735381111554285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32842158218490254074369523 49263237327735381111554285)
  ·
    refine ⟨18473713997900767916832857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49263237327735381111554285 18473713997900767916832857)
    ·
      refine ⟨13855285498425575937624643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18473713997900767916832857 13855285498425575937624643)
      ·
        refine ⟨20782928247638363906436965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13855285498425575937624643 20782928247638363906436965)
        ·
          refine ⟨3896799046432193232456931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20782928247638363906436965 3896799046432193232456931)
          ·
            refine ⟨5845198569648289848685397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3896799046432193232456931 5845198569648289848685397)
            ·
              refine ⟨34249210369032948332141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5845198569648289848685397 34249210369032948332141)
              ·
                rfl

theorem cell21_1350677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 9].length) (baseStart_1350677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350677 prefixEnd_1350677 := by exact prefixLift 1350677
  have htrace : WordTrace (prefixWord ++ tailWord_1350677) baseStart_1350677 baseEnd_1350677 := by
    simpa [prefixWord, tailWord_1350677, baseEnd_1350677] using wordTrace_append hprefix tailTrace_1350677
  have hstable : (prefixWord ++ tailWord_1350677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350677).length < 2 ^ (prefixWord ++ tailWord_1350677).sum := by decide
  have hdescent : baseEnd_1350677 < baseStart_1350677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350753 : List Nat := [1, 2, 3, 1, 1, 2, 5, 6]
def baseStart_1350753 : Nat := 118140960795 + 1350753 * 2 ^ 59
def prefixEnd_1350753 : Nat := 4983230072969 + 3 ^ 40 * 1350753 * 2
def baseEnd_1350753 : Nat := 102753412518912430574149

theorem tailTrace_1350753 : CollatzResearch.WordTrace tailWord_1350753 prefixEnd_1350753 102753412518912430574149 := by
  unfold tailWord_1350753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266009275460046091320913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32844006183640030727547275 49266009275460046091320913)
  ·
    refine ⟨36949506956595034568490685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49266009275460046091320913 36949506956595034568490685)
    ·
      refine ⟨13856065108723137963184007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36949506956595034568490685 13856065108723137963184007)
      ·
        refine ⟨20784097663084706944776011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13856065108723137963184007 20784097663084706944776011)
        ·
          refine ⟨31176146494627060417164017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20784097663084706944776011 31176146494627060417164017)
          ·
            refine ⟨23382109870970295312873013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31176146494627060417164017 23382109870970295312873013)
            ·
              refine ⟨2192072800403465185581845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23382109870970295312873013 2192072800403465185581845)
              ·
                refine ⟨102753412518912430574149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2192072800403465185581845 102753412518912430574149)
                ·
                  rfl

theorem cell21_1350753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 6].length) (baseStart_1350753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350753 prefixEnd_1350753 := by exact prefixLift 1350753
  have htrace : WordTrace (prefixWord ++ tailWord_1350753) baseStart_1350753 baseEnd_1350753 := by
    simpa [prefixWord, tailWord_1350753, baseEnd_1350753] using wordTrace_append hprefix tailTrace_1350753
  have hstable : (prefixWord ++ tailWord_1350753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350753).length < 2 ^ (prefixWord ++ tailWord_1350753).sum := by decide
  have hdescent : baseEnd_1350753 < baseStart_1350753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350770 : List Nat := [3, 2, 1, 2, 2, 1, 5, 5]
def baseStart_1350770 : Nat := 118140960795 + 1350770 * 2 ^ 59
def prefixEnd_1350770 : Nat := 4983230072969 + 3 ^ 40 * 1350770 * 2
def baseEnd_1350770 : Nat := 102754705729449679979693

theorem tailTrace_1350770 : CollatzResearch.WordTrace tailWord_1350770 prefixEnd_1350770 102754705729449679979693 := by
  unfold tailWord_1350770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316657329099614498672441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32844419544265638663126509 12316657329099614498672441)
  ·
    refine ⟨9237492996824710874004331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12316657329099614498672441 9237492996824710874004331)
    ·
      refine ⟨13856239495237066311006497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9237492996824710874004331 13856239495237066311006497)
      ·
        refine ⟨10392179621427799733254873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13856239495237066311006497 10392179621427799733254873)
        ·
          refine ⟨7794134716070849799941155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10392179621427799733254873 7794134716070849799941155)
          ·
            refine ⟨11691202074106274699911733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794134716070849799941155 11691202074106274699911733)
            ·
              refine ⟨1096050194447463253116725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11691202074106274699911733 1096050194447463253116725)
              ·
                refine ⟨102754705729449679979693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1096050194447463253116725 102754705729449679979693)
                ·
                  rfl

theorem cell21_1350770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_1350770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350770 prefixEnd_1350770 := by exact prefixLift 1350770
  have htrace : WordTrace (prefixWord ++ tailWord_1350770) baseStart_1350770 baseEnd_1350770 := by
    simpa [prefixWord, tailWord_1350770, baseEnd_1350770] using wordTrace_append hprefix tailTrace_1350770
  have hstable : (prefixWord ++ tailWord_1350770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350770).length < 2 ^ (prefixWord ++ tailWord_1350770).sum := by decide
  have hdescent : baseEnd_1350770 < baseStart_1350770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350846 : List Nat := [4, 2, 1, 1, 3, 3, 7]
def baseStart_1350846 : Nat := 118140960795 + 1350846 * 2 ^ 59
def prefixEnd_1350846 : Nat := 4983230072969 + 3 ^ 40 * 1350846 * 2
def baseEnd_1350846 : Nat := 34253495713754421852473

theorem tailTrace_1350846 : CollatzResearch.WordTrace tailWord_1350846 prefixEnd_1350846 34253495713754421852473 := by
  unfold tailWord_1350846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158675158015390371807049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32846267509415415316304261 6158675158015390371807049)
  ·
    refine ⟨4619006368511542778855287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6158675158015390371807049 4619006368511542778855287)
    ·
      refine ⟨6928509552767314168282931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619006368511542778855287 6928509552767314168282931)
      ·
        refine ⟨10392764329150971252424397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6928509552767314168282931 10392764329150971252424397)
        ·
          refine ⟨3897286623431614219659149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10392764329150971252424397 3897286623431614219659149)
          ·
            refine ⟨1461482483786855332372181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3897286623431614219659149 1461482483786855332372181)
            ·
              refine ⟨34253495713754421852473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1461482483786855332372181 34253495713754421852473)
              ·
                rfl

theorem cell21_1350846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 7].length) (baseStart_1350846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350846 prefixEnd_1350846 := by exact prefixLift 1350846
  have htrace : WordTrace (prefixWord ++ tailWord_1350846) baseStart_1350846 baseEnd_1350846 := by
    simpa [prefixWord, tailWord_1350846, baseEnd_1350846] using wordTrace_append hprefix tailTrace_1350846
  have hstable : (prefixWord ++ tailWord_1350846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350846).length < 2 ^ (prefixWord ++ tailWord_1350846).sum := by decide
  have hdescent : baseEnd_1350846 < baseStart_1350846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350908 : List Nat := [2, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1350908 : Nat := 118140960795 + 1350908 * 2 ^ 59
def prefixEnd_1350908 : Nat := 4983230072969 + 3 ^ 40 * 1350908 * 2
def baseEnd_1350908 : Nat := 308295610668491466638797

theorem tailTrace_1350908 : CollatzResearch.WordTrace tailWord_1350908 prefixEnd_1350908 308295610668491466638797 := by
  unfold tailWord_1350908
  simp only [CollatzResearch.WordTrace]
  refine ⟨24635831294949253781606689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32847775059932338375475585 24635831294949253781606689)
  ·
    refine ⟨18476873471211940336205017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24635831294949253781606689 18476873471211940336205017)
    ·
      refine ⟨13857655103408955252153763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18476873471211940336205017 13857655103408955252153763)
      ·
        refine ⟨20786482655113432878230645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13857655103408955252153763 20786482655113432878230645)
        ·
          refine ⟨1948732748916884332334123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20786482655113432878230645 1948732748916884332334123)
          ·
            refine ⟨2923099123375326498501185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948732748916884332334123 2923099123375326498501185)
            ·
              refine ⟨2192324342531494873875889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2923099123375326498501185 2192324342531494873875889)
              ·
                refine ⟨1644243256898621155406917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2192324342531494873875889 1644243256898621155406917)
                ·
                  refine ⟨308295610668491466638797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644243256898621155406917 308295610668491466638797)
                  ·
                    rfl

theorem cell21_1350908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1350908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350908 prefixEnd_1350908 := by exact prefixLift 1350908
  have htrace : WordTrace (prefixWord ++ tailWord_1350908) baseStart_1350908 baseEnd_1350908 := by
    simpa [prefixWord, tailWord_1350908, baseEnd_1350908] using wordTrace_append hprefix tailTrace_1350908
  have hstable : (prefixWord ++ tailWord_1350908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350908).length < 2 ^ (prefixWord ++ tailWord_1350908).sum := by decide
  have hdescent : baseEnd_1350908 < baseStart_1350908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350936 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1350936 : Nat := 118140960795 + 1350936 * 2 ^ 59
def prefixEnd_1350936 : Nat := 4983230072969 + 3 ^ 40 * 1350936 * 2
def baseEnd_1350936 : Nat := 308302000649969640172073

theorem tailTrace_1350936 : CollatzResearch.WordTrace tailWord_1350936 prefixEnd_1350936 308302000649969640172073 := by
  unfold tailWord_1350936
  simp only [CollatzResearch.WordTrace]
  refine ⟨24636341916898534172616331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32848455889198045563488441 24636341916898534172616331)
  ·
    refine ⟨36954512875347801258924497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24636341916898534172616331 36954512875347801258924497)
    ·
      refine ⟨27715884656510850944193373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36954512875347801258924497 27715884656510850944193373)
      ·
        refine ⟨10393456746191569104072515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27715884656510850944193373 10393456746191569104072515)
        ·
          refine ⟨15590185119287353656108773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10393456746191569104072515 15590185119287353656108773)
          ·
            refine ⟨2923159709866378810520395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15590185119287353656108773 2923159709866378810520395)
            ·
              refine ⟨4384739564799568215780593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923159709866378810520395 4384739564799568215780593)
              ·
                refine ⟨3288554673599676161835445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384739564799568215780593 3288554673599676161835445)
                ·
                  refine ⟨308302000649969640172073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3288554673599676161835445 308302000649969640172073)
                  ·
                    rfl

theorem cell21_1350936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1350936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350936 prefixEnd_1350936 := by exact prefixLift 1350936
  have htrace : WordTrace (prefixWord ++ tailWord_1350936) baseStart_1350936 baseEnd_1350936 := by
    simpa [prefixWord, tailWord_1350936, baseEnd_1350936] using wordTrace_append hprefix tailTrace_1350936
  have hstable : (prefixWord ++ tailWord_1350936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350936).length < 2 ^ (prefixWord ++ tailWord_1350936).sum := by decide
  have hdescent : baseEnd_1350936 < baseStart_1350936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350995 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 5]
def baseStart_1350995 : Nat := 118140960795 + 1350995 * 2 ^ 59
def prefixEnd_1350995 : Nat := 4983230072969 + 3 ^ 40 * 1350995 * 2
def baseEnd_1350995 : Nat := 308315465253798648688619

theorem tailTrace_1350995 : CollatzResearch.WordTrace tailWord_1350995 prefixEnd_1350995 308315465253798648688619 := by
  unfold tailWord_1350995
  simp only [CollatzResearch.WordTrace]
  refine ⟨49274835740583321421630439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32849890493722214281086959 49274835740583321421630439)
  ·
    refine ⟨73912253610874982132445659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49274835740583321421630439 73912253610874982132445659)
    ·
      refine ⟨110868380416312473198668489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73912253610874982132445659 110868380416312473198668489)
      ·
        refine ⟨83151285312234354899001367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110868380416312473198668489 83151285312234354899001367)
        ·
          refine ⟨124726927968351532348502051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83151285312234354899001367 124726927968351532348502051)
          ·
            refine ⟨187090391952527298522753077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124726927968351532348502051 187090391952527298522753077)
            ·
              refine ⟨17539724245549434236508101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 187090391952527298522753077 17539724245549434236508101)
              ·
                refine ⟨3288698296040518919345269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17539724245549434236508101 3288698296040518919345269)
                ·
                  refine ⟨308315465253798648688619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3288698296040518919345269 308315465253798648688619)
                  ·
                    rfl

theorem cell21_1350995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 5].length) (baseStart_1350995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1350995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1350995 prefixEnd_1350995 := by exact prefixLift 1350995
  have htrace : WordTrace (prefixWord ++ tailWord_1350995) baseStart_1350995 baseEnd_1350995 := by
    simpa [prefixWord, tailWord_1350995, baseEnd_1350995] using wordTrace_append hprefix tailTrace_1350995
  have hstable : (prefixWord ++ tailWord_1350995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350995).length < 2 ^ (prefixWord ++ tailWord_1350995).sum := by decide
  have hdescent : baseEnd_1350995 < baseStart_1350995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351026 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_1351026 : Nat := 118140960795 + 1351026 * 2 ^ 59
def prefixEnd_1351026 : Nat := 4983230072969 + 3 ^ 40 * 1351026 * 2
def baseEnd_1351026 : Nat := 308322539876149483671889

theorem tailTrace_1351026 : CollatzResearch.WordTrace tailWord_1351026 prefixEnd_1351026 308322539876149483671889 := by
  unfold tailWord_1351026
  simp only [CollatzResearch.WordTrace]
  refine ⟨12318991600867753429002233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32850644268980675810672621 12318991600867753429002233)
  ·
    refine ⟨9239243700650815071751675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12318991600867753429002233 9239243700650815071751675)
    ·
      refine ⟨13858865550976222607627513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9239243700650815071751675 13858865550976222607627513)
      ·
        refine ⟨10394149163232166955720635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13858865550976222607627513 10394149163232166955720635)
        ·
          refine ⟨15591223744848250433580953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10394149163232166955720635 15591223744848250433580953)
          ·
            refine ⟨11693417808636187825185715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15591223744848250433580953 11693417808636187825185715)
            ·
              refine ⟨17540126712954281737778573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11693417808636187825185715 17540126712954281737778573)
              ·
                refine ⟨6577547517357855651666965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17540126712954281737778573 6577547517357855651666965)
                ·
                  refine ⟨308322539876149483671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6577547517357855651666965 308322539876149483671889)
                  ·
                    rfl

theorem cell21_1351026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_1351026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351026 prefixEnd_1351026 := by exact prefixLift 1351026
  have htrace : WordTrace (prefixWord ++ tailWord_1351026) baseStart_1351026 baseEnd_1351026 := by
    simpa [prefixWord, tailWord_1351026, baseEnd_1351026] using wordTrace_append hprefix tailTrace_1351026
  have hstable : (prefixWord ++ tailWord_1351026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351026).length < 2 ^ (prefixWord ++ tailWord_1351026).sum := by decide
  have hdescent : baseEnd_1351026 < baseStart_1351026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351043 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 4]
def baseStart_1351043 : Nat := 118140960795 + 1351043 * 2 ^ 59
def prefixEnd_1351043 : Nat := 4983230072969 + 3 ^ 40 * 1351043 * 2
def baseEnd_1351043 : Nat := 308326419507761231888521

theorem tailTrace_1351043 : CollatzResearch.WordTrace tailWord_1351043 prefixEnd_1351043 308326419507761231888521 := by
  unfold tailWord_1351043
  simp only [CollatzResearch.WordTrace]
  refine ⟨49276586444409425619377783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32851057629606283746251855 49276586444409425619377783)
  ·
    refine ⟨73914879666614138429066675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49276586444409425619377783 73914879666614138429066675)
    ·
      refine ⟨110872319499921207643600013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73914879666614138429066675 110872319499921207643600013)
      ·
        refine ⟨41577119812470452866350005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110872319499921207643600013 41577119812470452866350005)
        ·
          refine ⟨3897854982419104956220313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41577119812470452866350005 3897854982419104956220313)
          ·
            refine ⟨2923391236814328717165235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897854982419104956220313 2923391236814328717165235)
            ·
              refine ⟨4385086855221493075747853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923391236814328717165235 4385086855221493075747853)
              ·
                refine ⟨1644407570708059903405445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385086855221493075747853 1644407570708059903405445)
                ·
                  refine ⟨308326419507761231888521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1644407570708059903405445 308326419507761231888521)
                  ·
                    rfl

theorem cell21_1351043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 4].length) (baseStart_1351043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351043 prefixEnd_1351043 := by exact prefixLift 1351043
  have htrace : WordTrace (prefixWord ++ tailWord_1351043) baseStart_1351043 baseEnd_1351043 := by
    simpa [prefixWord, tailWord_1351043, baseEnd_1351043] using wordTrace_append hprefix tailTrace_1351043
  have hstable : (prefixWord ++ tailWord_1351043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351043).length < 2 ^ (prefixWord ++ tailWord_1351043).sum := by decide
  have hdescent : baseEnd_1351043 < baseStart_1351043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351080 : List Nat := [2, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_1351080 : Nat := 118140960795 + 1351080 * 2 ^ 59
def prefixEnd_1351080 : Nat := 4983230072969 + 3 ^ 40 * 1351080 * 2
def baseEnd_1351080 : Nat := 308334863411857389771779

theorem tailTrace_1351080 : CollatzResearch.WordTrace tailWord_1351080 prefixEnd_1351080 308334863411857389771779 := by
  unfold tailWord_1351080
  simp only [CollatzResearch.WordTrace]
  refine ⟨24638967972637690469237347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32851957296850253958983129 24638967972637690469237347)
  ·
    refine ⟨36958451958956535703856021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24638967972637690469237347 36958451958956535703856021)
    ·
      refine ⟨1732427435576087611118251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36958451958956535703856021 1732427435576087611118251)
      ·
        refine ⟨2598641153364131416677377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732427435576087611118251 2598641153364131416677377)
        ·
          refine ⟨1948980865023098562508033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598641153364131416677377 1948980865023098562508033)
          ·
            refine ⟨1461735648767323921881025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1948980865023098562508033 1461735648767323921881025)
            ·
              refine ⟨1096301736575492941410769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1461735648767323921881025 1096301736575492941410769)
              ·
                refine ⟨822226302431619706058077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096301736575492941410769 822226302431619706058077)
                ·
                  refine ⟨308334863411857389771779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822226302431619706058077 308334863411857389771779)
                  ·
                    rfl

theorem cell21_1351080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_1351080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351080 prefixEnd_1351080 := by exact prefixLift 1351080
  have htrace : WordTrace (prefixWord ++ tailWord_1351080) baseStart_1351080 baseEnd_1351080 := by
    simpa [prefixWord, tailWord_1351080, baseEnd_1351080] using wordTrace_append hprefix tailTrace_1351080
  have hstable : (prefixWord ++ tailWord_1351080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351080).length < 2 ^ (prefixWord ++ tailWord_1351080).sum := by decide
  have hdescent : baseEnd_1351080 < baseStart_1351080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351102 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1351102 : Nat := 118140960795 + 1351102 * 2 ^ 59
def prefixEnd_1351102 : Nat := 4983230072969 + 3 ^ 40 * 1351102 * 2
def baseEnd_1351102 : Nat := 308339884111590240405067

theorem tailTrace_1351102 : CollatzResearch.WordTrace tailWord_1351102 prefixEnd_1351102 308339884111590240405067 := by
  unfold tailWord_1351102
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159842293899459836971945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32852492234130452463850373 6159842293899459836971945)
  ·
    refine ⟨4619881720424594877728959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6159842293899459836971945 4619881720424594877728959)
    ·
      refine ⟨6929822580636892316593439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4619881720424594877728959 6929822580636892316593439)
      ·
        refine ⟨10394733870955338474890159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929822580636892316593439 10394733870955338474890159)
        ·
          refine ⟨15592100806433007712335239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10394733870955338474890159 15592100806433007712335239)
          ·
            refine ⟨23388151209649511568502859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15592100806433007712335239 23388151209649511568502859)
            ·
              refine ⟨35082226814474267352754289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23388151209649511568502859 35082226814474267352754289)
              ·
                refine ⟨26311670110855700514565717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35082226814474267352754289 26311670110855700514565717)
                ·
                  refine ⟨308339884111590240405067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26311670110855700514565717 308339884111590240405067)
                  ·
                    rfl

theorem cell21_1351102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1351102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351102 prefixEnd_1351102 := by exact prefixLift 1351102
  have htrace : WordTrace (prefixWord ++ tailWord_1351102) baseStart_1351102 baseEnd_1351102 := by
    simpa [prefixWord, tailWord_1351102, baseEnd_1351102] using wordTrace_append hprefix tailTrace_1351102
  have hstable : (prefixWord ++ tailWord_1351102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351102).length < 2 ^ (prefixWord ++ tailWord_1351102).sum := by decide
  have hdescent : baseEnd_1351102 < baseStart_1351102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351133 : List Nat := [1, 4, 3, 1, 1, 3, 8]
def baseStart_1351133 : Nat := 118140960795 + 1351133 * 2 ^ 59
def prefixEnd_1351133 : Nat := 4983230072969 + 3 ^ 40 * 1351133 * 2
def baseEnd_1351133 : Nat := 34260773192660119487593

theorem tailTrace_1351133 : CollatzResearch.WordTrace tailWord_1351133 prefixEnd_1351133 34260773192660119487593 := by
  unfold tailWord_1351133
  simp only [CollatzResearch.WordTrace]
  refine ⟨49279869014083370990154053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32853246009388913993436035 49279869014083370990154053)
  ·
    refine ⟨9239975440140632060653885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49279869014083370990154053 9239975440140632060653885)
    ·
      refine ⟨3464990790052737022745207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9239975440140632060653885 3464990790052737022745207)
      ·
        refine ⟨5197486185079105534117811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464990790052737022745207 5197486185079105534117811)
        ·
          refine ⟨7796229277618658301176717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197486185079105534117811 7796229277618658301176717)
          ·
            refine ⟨2923585979106996862941269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7796229277618658301176717 2923585979106996862941269)
            ·
              refine ⟨34260773192660119487593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2923585979106996862941269 34260773192660119487593)
              ·
                rfl

theorem cell21_1351133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 8].length) (baseStart_1351133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351133 prefixEnd_1351133 := by exact prefixLift 1351133
  have htrace : WordTrace (prefixWord ++ tailWord_1351133) baseStart_1351133 baseEnd_1351133 := by
    simpa [prefixWord, tailWord_1351133, baseEnd_1351133] using wordTrace_append hprefix tailTrace_1351133
  have hstable : (prefixWord ++ tailWord_1351133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351133).length < 2 ^ (prefixWord ++ tailWord_1351133).sum := by decide
  have hdescent : baseEnd_1351133 < baseStart_1351133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351178 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_1351178 : Nat := 118140960795 + 1351178 * 2 ^ 59
def prefixEnd_1351178 : Nat := 4983230072969 + 3 ^ 40 * 1351178 * 2
def baseEnd_1351178 : Nat := 308357228347030997138245

theorem tailTrace_1351178 : CollatzResearch.WordTrace tailWord_1351178 prefixEnd_1351178 308357228347030997138245 := by
  unfold tailWord_1351178
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320377574730085918885547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32854340199280229117028125 12320377574730085918885547)
  ·
    refine ⟨18480566362095128878328321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12320377574730085918885547 18480566362095128878328321)
    ·
      refine ⟨13860424771571346658746241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18480566362095128878328321 13860424771571346658746241)
      ·
        refine ⟨10395318578678509994059681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13860424771571346658746241 10395318578678509994059681)
        ·
          refine ⟨7796488934008882495544761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395318578678509994059681 7796488934008882495544761)
          ·
            refine ⟨5847366700506661871658571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7796488934008882495544761 5847366700506661871658571)
            ·
              refine ⟨8771050050759992807487857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847366700506661871658571 8771050050759992807487857)
              ·
                refine ⟨6578287538069994605615893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8771050050759992807487857 6578287538069994605615893)
                ·
                  refine ⟨308357228347030997138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6578287538069994605615893 308357228347030997138245)
                  ·
                    rfl

theorem cell21_1351178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_1351178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351178 prefixEnd_1351178 := by exact prefixLift 1351178
  have htrace : WordTrace (prefixWord ++ tailWord_1351178) baseStart_1351178 baseEnd_1351178 := by
    simpa [prefixWord, tailWord_1351178, baseEnd_1351178] using wordTrace_append hprefix tailTrace_1351178
  have hstable : (prefixWord ++ tailWord_1351178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351178).length < 2 ^ (prefixWord ++ tailWord_1351178).sum := by decide
  have hdescent : baseEnd_1351178 < baseStart_1351178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351468 : List Nat := [2, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1351468 : Nat := 118140960795 + 1351468 * 2 ^ 59
def prefixEnd_1351468 : Nat := 4983230072969 + 3 ^ 40 * 1351468 * 2
def baseEnd_1351468 : Nat := 308423410298054937304319

theorem tailTrace_1351468 : CollatzResearch.WordTrace tailWord_1351468 prefixEnd_1351468 308423410298054937304319 := by
  unfold tailWord_1351468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646043733934861601799529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32861391645246482135732705 24646043733934861601799529)
  ·
    refine ⟨18484532800451146201349647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24646043733934861601799529 18484532800451146201349647)
    ·
      refine ⟨27726799200676719302024471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18484532800451146201349647 27726799200676719302024471)
      ·
        refine ⟨41590198801015078953036707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27726799200676719302024471 41590198801015078953036707)
        ·
          refine ⟨62385298201522618429555061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41590198801015078953036707 62385298201522618429555061)
          ·
            refine ⟨5848621706392745477770787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62385298201522618429555061 5848621706392745477770787)
            ·
              refine ⟨8772932559589118216656181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848621706392745477770787 8772932559589118216656181)
              ·
                refine ⟨822462427461479832811517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8772932559589118216656181 822462427461479832811517)
                ·
                  refine ⟨308423410298054937304319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822462427461479832811517 308423410298054937304319)
                  ·
                    rfl

theorem cell21_1351468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1351468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351468 prefixEnd_1351468 := by exact prefixLift 1351468
  have htrace : WordTrace (prefixWord ++ tailWord_1351468) baseStart_1351468 baseEnd_1351468 := by
    simpa [prefixWord, tailWord_1351468, baseEnd_1351468] using wordTrace_append hprefix tailTrace_1351468
  have hstable : (prefixWord ++ tailWord_1351468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351468).length < 2 ^ (prefixWord ++ tailWord_1351468).sum := by decide
  have hdescent : baseEnd_1351468 < baseStart_1351468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351482 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_1351482 : Nat := 118140960795 + 1351482 * 2 ^ 59
def prefixEnd_1351482 : Nat := 4983230072969 + 3 ^ 40 * 1351482 * 2
def baseEnd_1351482 : Nat := 308426605288794024070957

theorem tailTrace_1351482 : CollatzResearch.WordTrace tailWord_1351482 prefixEnd_1351482 308426605288794024070957 := by
  unfold tailWord_1351482
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323149522454750898652175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32861732059879335729739133 12323149522454750898652175)
  ·
    refine ⟨18484724283682126347978263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323149522454750898652175 18484724283682126347978263)
    ·
      refine ⟨27727086425523189521967395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18484724283682126347978263 27727086425523189521967395)
      ·
        refine ⟨41590629638284784282951093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27727086425523189521967395 41590629638284784282951093)
        ·
          refine ⟨3899121528589198526526665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41590629638284784282951093 3899121528589198526526665)
          ·
            refine ⟨2924341146441898894894999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899121528589198526526665 2924341146441898894894999)
            ·
              refine ⟨4386511719662848342342499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924341146441898894894999 4386511719662848342342499)
              ·
                refine ⟨6579767579494272513513749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386511719662848342342499 6579767579494272513513749)
                ·
                  refine ⟨308426605288794024070957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6579767579494272513513749 308426605288794024070957)
                  ·
                    rfl

theorem cell21_1351482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_1351482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351482 prefixEnd_1351482 := by exact prefixLift 1351482
  have htrace : WordTrace (prefixWord ++ tailWord_1351482) baseStart_1351482 baseEnd_1351482 := by
    simpa [prefixWord, tailWord_1351482, baseEnd_1351482] using wordTrace_append hprefix tailTrace_1351482
  have hstable : (prefixWord ++ tailWord_1351482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351482).length < 2 ^ (prefixWord ++ tailWord_1351482).sum := by decide
  have hdescent : baseEnd_1351482 < baseStart_1351482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351485 : List Nat := [1, 4, 1, 4, 1, 1, 2, 4, 3]
def baseStart_1351485 : Nat := 118140960795 + 1351485 * 2 ^ 59
def prefixEnd_1351485 : Nat := 4983230072969 + 3 ^ 40 * 1351485 * 2
def baseEnd_1351485 : Nat := 308427289929666685520951

theorem tailTrace_1351485 : CollatzResearch.WordTrace tailWord_1351485 prefixEnd_1351485 308427289929666685520951 := by
  unfold tailWord_1351485
  simp only [CollatzResearch.WordTrace]
  refine ⟨49292707508808135106967909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32861805005872090071311939 49292707508808135106967909)
  ·
    refine ⟨9242382657901525332556483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49292707508808135106967909 9242382657901525332556483)
    ·
      refine ⟨13863573986852287998834725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9242382657901525332556483 13863573986852287998834725)
      ·
        refine ⟨2599420122534803999781511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13863573986852287998834725 2599420122534803999781511)
        ·
          refine ⟨3899130183802205999672267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599420122534803999781511 3899130183802205999672267)
          ·
            refine ⟨5848695275703308999508401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899130183802205999672267 5848695275703308999508401)
            ·
              refine ⟨4386521456777481749631301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5848695275703308999508401 4386521456777481749631301)
              ·
                refine ⟨822472773145777828055869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4386521456777481749631301 822472773145777828055869)
                ·
                  refine ⟨308427289929666685520951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822472773145777828055869 308427289929666685520951)
                  ·
                    rfl

theorem cell21_1351485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_1351485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351485 prefixEnd_1351485 := by exact prefixLift 1351485
  have htrace : WordTrace (prefixWord ++ tailWord_1351485) baseStart_1351485 baseEnd_1351485 := by
    simpa [prefixWord, tailWord_1351485, baseEnd_1351485] using wordTrace_append hprefix tailTrace_1351485
  have hstable : (prefixWord ++ tailWord_1351485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351485).length < 2 ^ (prefixWord ++ tailWord_1351485).sum := by decide
  have hdescent : baseEnd_1351485 < baseStart_1351485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351530 : List Nat := [3, 1, 3, 4, 1, 2, 7]
def baseStart_1351530 : Nat := 118140960795 + 1351530 * 2 ^ 59
def prefixEnd_1351530 : Nat := 4983230072969 + 3 ^ 40 * 1351530 * 2
def baseEnd_1351530 : Nat := 34270839949195178585651

theorem tailTrace_1351530 : CollatzResearch.WordTrace tailWord_1351530 prefixEnd_1351530 34270839949195178585651 := by
  unfold tailWord_1351530
  simp only [CollatzResearch.WordTrace]
  refine ⟨12323587198411276948089011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32862899195763405194904029 12323587198411276948089011)
  ·
    refine ⟨18485380797616915422133517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12323587198411276948089011 18485380797616915422133517)
    ·
      refine ⟨6932017799106343283300069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18485380797616915422133517 6932017799106343283300069)
      ·
        refine ⟨1299753337332439365618763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6932017799106343283300069 1299753337332439365618763)
        ·
          refine ⟨1949630005998659048428145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299753337332439365618763 1949630005998659048428145)
          ·
            refine ⟨1462222504498994286321109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949630005998659048428145 1462222504498994286321109)
            ·
              refine ⟨34270839949195178585651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1462222504498994286321109 34270839949195178585651)
              ·
                rfl

theorem cell21_1351530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 7].length) (baseStart_1351530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351530 prefixEnd_1351530 := by exact prefixLift 1351530
  have htrace : WordTrace (prefixWord ++ tailWord_1351530) baseStart_1351530 baseEnd_1351530 := by
    simpa [prefixWord, tailWord_1351530, baseEnd_1351530] using wordTrace_append hprefix tailTrace_1351530
  have hstable : (prefixWord ++ tailWord_1351530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351530).length < 2 ^ (prefixWord ++ tailWord_1351530).sum := by decide
  have hdescent : baseEnd_1351530 < baseStart_1351530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351637 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 3]
def baseStart_1351637 : Nat := 118140960795 + 1351637 * 2 ^ 59
def prefixEnd_1351637 : Nat := 4983230072969 + 3 ^ 40 * 1351637 * 2
def baseEnd_1351637 : Nat := 308461978400548198987307

theorem tailTrace_1351637 : CollatzResearch.WordTrace tailWord_1351637 prefixEnd_1351637 308461978400548198987307 := by
  unfold tailWord_1351637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49298251404257465066501165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32865500936171643377667443 49298251404257465066501165)
  ·
    refine ⟨18486844276596549399937937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49298251404257465066501165 18486844276596549399937937)
    ·
      refine ⟨13865133207447412049953453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18486844276596549399937937 13865133207447412049953453)
      ·
        refine ⟨5199424952792779518732545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13865133207447412049953453 5199424952792779518732545)
        ·
          refine ⟨3899568714594584639049409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5199424952792779518732545 3899568714594584639049409)
          ·
            refine ⟨2924676535945938479287057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899568714594584639049409 2924676535945938479287057)
            ·
              refine ⟨2193507401959453859465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924676535945938479287057 2193507401959453859465293)
              ·
                refine ⟨822565275734795197299485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2193507401959453859465293 822565275734795197299485)
                ·
                  refine ⟨308461978400548198987307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822565275734795197299485 308461978400548198987307)
                  ·
                    rfl

theorem cell21_1351637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 3].length) (baseStart_1351637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351637 prefixEnd_1351637 := by exact prefixLift 1351637
  have htrace : WordTrace (prefixWord ++ tailWord_1351637) baseStart_1351637 baseEnd_1351637 := by
    simpa [prefixWord, tailWord_1351637, baseEnd_1351637] using wordTrace_append hprefix tailTrace_1351637
  have hstable : (prefixWord ++ tailWord_1351637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351637).length < 2 ^ (prefixWord ++ tailWord_1351637).sum := by decide
  have hdescent : baseEnd_1351637 < baseStart_1351637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351651 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 4]
def baseStart_1351651 : Nat := 118140960795 + 1351651 * 2 ^ 59
def prefixEnd_1351651 : Nat := 4983230072969 + 3 ^ 40 * 1351651 * 2
def baseEnd_1351651 : Nat := 308465173391287285753945

theorem tailTrace_1351651 : CollatzResearch.WordTrace tailWord_1351651 prefixEnd_1351651 308465173391287285753945 := by
  unfold tailWord_1351651
  simp only [CollatzResearch.WordTrace]
  refine ⟨49298762026206745457510807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32865841350804496971673871 49298762026206745457510807)
  ·
    refine ⟨73948143039310118186266211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49298762026206745457510807 73948143039310118186266211)
    ·
      refine ⟨110922214558965177279399317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73948143039310118186266211 110922214558965177279399317)
      ·
        refine ⟨5199478807451492684971843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110922214558965177279399317 5199478807451492684971843)
        ·
          refine ⟨7799218211177239027457765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5199478807451492684971843 7799218211177239027457765)
          ·
            refine ⟨1462353414595732317648331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7799218211177239027457765 1462353414595732317648331)
            ·
              refine ⟨2193530121893598476472497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462353414595732317648331 2193530121893598476472497)
              ·
                refine ⟨1645147591420198857354373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193530121893598476472497 1645147591420198857354373)
                ·
                  refine ⟨308465173391287285753945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645147591420198857354373 308465173391287285753945)
                  ·
                    rfl

theorem cell21_1351651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 4].length) (baseStart_1351651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351651 prefixEnd_1351651 := by exact prefixLift 1351651
  have htrace : WordTrace (prefixWord ++ tailWord_1351651) baseStart_1351651 baseEnd_1351651 := by
    simpa [prefixWord, tailWord_1351651, baseEnd_1351651] using wordTrace_append hprefix tailTrace_1351651
  have hstable : (prefixWord ++ tailWord_1351651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351651).length < 2 ^ (prefixWord ++ tailWord_1351651).sum := by decide
  have hdescent : baseEnd_1351651 < baseStart_1351651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351713 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 5]
def baseStart_1351713 : Nat := 118140960795 + 1351713 * 2 ^ 59
def prefixEnd_1351713 : Nat := 4983230072969 + 3 ^ 40 * 1351713 * 2
def baseEnd_1351713 : Nat := 308479322635988955720485

theorem tailTrace_1351713 : CollatzResearch.WordTrace tailWord_1351713 prefixEnd_1351713 308479322635988955720485 := by
  unfold tailWord_1351713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49301023351982130046267793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32867348901321420030845195 49301023351982130046267793)
  ·
    refine ⟨36975767513986597534700845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49301023351982130046267793 36975767513986597534700845)
    ·
      refine ⟨13865912817744974075512817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36975767513986597534700845 13865912817744974075512817)
      ·
        refine ⟨10399434613308730556634613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13865912817744974075512817 10399434613308730556634613)
        ·
          refine ⟨974946994997693489684495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10399434613308730556634613 974946994997693489684495)
          ·
            refine ⟨1462420492496540234526743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974946994997693489684495 1462420492496540234526743)
            ·
              refine ⟨2193630738744810351790115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462420492496540234526743 2193630738744810351790115)
              ·
                refine ⟨3290446108117215527685173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193630738744810351790115 3290446108117215527685173)
                ·
                  refine ⟨308479322635988955720485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3290446108117215527685173 308479322635988955720485)
                  ·
                    rfl

theorem cell21_1351713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 5].length) (baseStart_1351713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351713 prefixEnd_1351713 := by exact prefixLift 1351713
  have htrace : WordTrace (prefixWord ++ tailWord_1351713) baseStart_1351713 baseEnd_1351713 := by
    simpa [prefixWord, tailWord_1351713, baseEnd_1351713] using wordTrace_append hprefix tailTrace_1351713
  have hstable : (prefixWord ++ tailWord_1351713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351713).length < 2 ^ (prefixWord ++ tailWord_1351713).sum := by decide
  have hdescent : baseEnd_1351713 < baseStart_1351713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351738 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_1351738 : Nat := 118140960795 + 1351738 * 2 ^ 59
def prefixEnd_1351738 : Nat := 4983230072969 + 3 ^ 40 * 1351738 * 2
def baseEnd_1351738 : Nat := 308485027976594467803767

theorem tailTrace_1351738 : CollatzResearch.WordTrace tailWord_1351738 prefixEnd_1351738 308485027976594467803767 := by
  unfold tailWord_1351738
  simp only [CollatzResearch.WordTrace]
  refine ⟨12325483794222889828981967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32867956784594372877285245 12325483794222889828981967)
  ·
    refine ⟨18488225691334334743472951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12325483794222889828981967 18488225691334334743472951)
    ·
      refine ⟨27732338537001502115209427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18488225691334334743472951 27732338537001502115209427)
      ·
        refine ⟨41598507805502253172814141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27732338537001502115209427 41598507805502253172814141)
        ·
          refine ⟨15599440427063344939805303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41598507805502253172814141 15599440427063344939805303)
          ·
            refine ⟨23399160640595017409707955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15599440427063344939805303 23399160640595017409707955)
            ·
              refine ⟨35098740960892526114561933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23399160640595017409707955 35098740960892526114561933)
              ·
                refine ⟨13162027860334697292960725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35098740960892526114561933 13162027860334697292960725)
                ·
                  refine ⟨308485027976594467803767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13162027860334697292960725 308485027976594467803767)
                  ·
                    rfl

theorem cell21_1351738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_1351738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351738 prefixEnd_1351738 := by exact prefixLift 1351738
  have htrace : WordTrace (prefixWord ++ tailWord_1351738) baseStart_1351738 baseEnd_1351738 := by
    simpa [prefixWord, tailWord_1351738, baseEnd_1351738] using wordTrace_append hprefix tailTrace_1351738
  have hstable : (prefixWord ++ tailWord_1351738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351738).length < 2 ^ (prefixWord ++ tailWord_1351738).sum := by decide
  have hdescent : baseEnd_1351738 < baseStart_1351738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351876 : List Nat := [2, 3, 3, 1, 2, 1, 9]
def baseStart_1351876 : Nat := 118140960795 + 1351876 * 2 ^ 59
def prefixEnd_1351876 : Nat := 4983230072969 + 3 ^ 40 * 1351876 * 2
def baseEnd_1351876 : Nat := 34279613495192988278165

theorem tailTrace_1351876 : CollatzResearch.WordTrace tailWord_1351876 prefixEnd_1351876 34279613495192988278165 := by
  unfold tailWord_1351876
  simp only [CollatzResearch.WordTrace]
  refine ⟨24653484225195804442225741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32871312300261072589634321 24653484225195804442225741)
  ·
    refine ⟨9245056584448426665834653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24653484225195804442225741 9245056584448426665834653)
    ·
      refine ⟨3466896219168159999687995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9245056584448426665834653 3466896219168159999687995)
      ·
        refine ⟨5200344328752239999531993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466896219168159999687995 5200344328752239999531993)
        ·
          refine ⟨3900258246564179999648995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5200344328752239999531993 3900258246564179999648995)
          ·
            refine ⟨5850387369846269999473493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900258246564179999648995 5850387369846269999473493)
            ·
              refine ⟨34279613495192988278165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5850387369846269999473493 34279613495192988278165)
              ·
                rfl

theorem cell21_1351876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 9].length) (baseStart_1351876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351876 prefixEnd_1351876 := by exact prefixLift 1351876
  have htrace : WordTrace (prefixWord ++ tailWord_1351876) baseStart_1351876 baseEnd_1351876 := by
    simpa [prefixWord, tailWord_1351876, baseEnd_1351876] using wordTrace_append hprefix tailTrace_1351876
  have hstable : (prefixWord ++ tailWord_1351876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351876).length < 2 ^ (prefixWord ++ tailWord_1351876).sum := by decide
  have hdescent : baseEnd_1351876 < baseStart_1351876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351893 : List Nat := [1, 3, 2, 4, 2, 1, 2, 6]
def baseStart_1351893 : Nat := 118140960795 + 1351893 * 2 ^ 59
def prefixEnd_1351893 : Nat := 4983230072969 + 3 ^ 40 * 1351893 * 2
def baseEnd_1351893 : Nat := 102840133696116214240039

theorem tailTrace_1351893 : CollatzResearch.WordTrace tailWord_1351893 prefixEnd_1351893 102840133696116214240039 := by
  unfold tailWord_1351893
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307588491330020787820333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32871725660886680525213555 49307588491330020787820333)
  ·
    refine ⟨18490345684248757795432625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49307588491330020787820333 18490345684248757795432625)
    ·
      refine ⟨13867759263186568346574469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18490345684248757795432625 13867759263186568346574469)
      ·
        refine ⟨2600204861847481564982713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13867759263186568346574469 2600204861847481564982713)
        ·
          refine ⟨1950153646385611173737035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2600204861847481564982713 1950153646385611173737035)
          ·
            refine ⟨2925230469578416760605553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950153646385611173737035 2925230469578416760605553)
            ·
              refine ⟨2193922852183812570454165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925230469578416760605553 2193922852183812570454165)
              ·
                refine ⟨102840133696116214240039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2193922852183812570454165 102840133696116214240039)
                ·
                  rfl

theorem cell21_1351893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 6].length) (baseStart_1351893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351893 prefixEnd_1351893 := by exact prefixLift 1351893
  have htrace : WordTrace (prefixWord ++ tailWord_1351893) baseStart_1351893 baseEnd_1351893 := by
    simpa [prefixWord, tailWord_1351893, baseEnd_1351893] using wordTrace_append hprefix tailTrace_1351893
  have hstable : (prefixWord ++ tailWord_1351893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351893).length < 2 ^ (prefixWord ++ tailWord_1351893).sum := by decide
  have hdescent : baseEnd_1351893 < baseStart_1351893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351975 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 3]
def baseStart_1351975 : Nat := 118140960795 + 1351975 * 2 ^ 59
def prefixEnd_1351975 : Nat := 4983230072969 + 3 ^ 40 * 1351975 * 2
def baseEnd_1351975 : Nat := 308539114605534722353283

theorem tailTrace_1351975 : CollatzResearch.WordTrace tailWord_1351975 prefixEnd_1351975 308539114605534722353283 := by
  unfold tailWord_1351975
  simp only [CollatzResearch.WordTrace]
  refine ⟨49310579277032948792305379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32873719518021965861536919 49310579277032948792305379)
  ·
    refine ⟨73965868915549423188458069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49310579277032948792305379 73965868915549423188458069)
    ·
      refine ⟨866787526354094802989743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 73965868915549423188458069 866787526354094802989743)
      ·
        refine ⟨1300181289531142204484615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866787526354094802989743 1300181289531142204484615)
        ·
          refine ⟨1950271934296713306726923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300181289531142204484615 1950271934296713306726923)
          ·
            refine ⟨2925407901445069960090385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950271934296713306726923 2925407901445069960090385)
            ·
              refine ⟨2194055926083802470067789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925407901445069960090385 2194055926083802470067789)
              ·
                refine ⟨822770972281425926275421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2194055926083802470067789 822770972281425926275421)
                ·
                  refine ⟨308539114605534722353283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822770972281425926275421 308539114605534722353283)
                  ·
                    rfl

theorem cell21_1351975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 3].length) (baseStart_1351975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351975 prefixEnd_1351975 := by exact prefixLift 1351975
  have htrace : WordTrace (prefixWord ++ tailWord_1351975) baseStart_1351975 baseEnd_1351975 := by
    simpa [prefixWord, tailWord_1351975, baseEnd_1351975] using wordTrace_append hprefix tailTrace_1351975
  have hstable : (prefixWord ++ tailWord_1351975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351975).length < 2 ^ (prefixWord ++ tailWord_1351975).sum := by decide
  have hdescent : baseEnd_1351975 < baseStart_1351975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351983 : List Nat := [1, 1, 2, 1, 2, 1, 5, 5, 3]
def baseStart_1351983 : Nat := 118140960795 + 1351983 * 2 ^ 59
def prefixEnd_1351983 : Nat := 4983230072969 + 3 ^ 40 * 1351983 * 2
def baseEnd_1351983 : Nat := 308540940314528486219933

theorem tailTrace_1351983 : CollatzResearch.WordTrace tailWord_1351983 prefixEnd_1351983 308540940314528486219933 := by
  unfold tailWord_1351983
  simp only [CollatzResearch.WordTrace]
  refine ⟨49310871061003966158596603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32873914040669310772397735 49310871061003966158596603)
  ·
    refine ⟨73966306591505949237894905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49310871061003966158596603 73966306591505949237894905)
    ·
      refine ⟨55474729943629461928421179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73966306591505949237894905 55474729943629461928421179)
      ·
        refine ⟨83212094915444192892631769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55474729943629461928421179 83212094915444192892631769)
        ·
          refine ⟨62409071186583144669473827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83212094915444192892631769 62409071186583144669473827)
          ·
            refine ⟨93613606779874717004210741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62409071186583144669473827 93613606779874717004210741)
            ·
              refine ⟨8776275635613254719144757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93613606779874717004210741 8776275635613254719144757)
              ·
                refine ⟨822775840838742629919821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8776275635613254719144757 822775840838742629919821)
                ·
                  refine ⟨308540940314528486219933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 822775840838742629919821 308540940314528486219933)
                  ·
                    rfl

theorem cell21_1351983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 3].length) (baseStart_1351983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1351983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1351983 prefixEnd_1351983 := by exact prefixLift 1351983
  have htrace : WordTrace (prefixWord ++ tailWord_1351983) baseStart_1351983 baseEnd_1351983 := by
    simpa [prefixWord, tailWord_1351983, baseEnd_1351983] using wordTrace_append hprefix tailTrace_1351983
  have hstable : (prefixWord ++ tailWord_1351983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351983).length < 2 ^ (prefixWord ++ tailWord_1351983).sum := by decide
  have hdescent : baseEnd_1351983 < baseStart_1351983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352059 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 5]
def baseStart_1352059 : Nat := 118140960795 + 1352059 * 2 ^ 59
def prefixEnd_1352059 : Nat := 4983230072969 + 3 ^ 40 * 1352059 * 2
def baseEnd_1352059 : Nat := 308558284549969242953111

theorem tailTrace_1352059 : CollatzResearch.WordTrace tailWord_1352059 prefixEnd_1352059 308558284549969242953111 := by
  unfold tailWord_1352059
  simp only [CollatzResearch.WordTrace]
  refine ⟨49313643008728631138363231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32875762005819087425575487 49313643008728631138363231)
  ·
    refine ⟨73970464513092946707544847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49313643008728631138363231 73970464513092946707544847)
    ·
      refine ⟨110955696769639420061317271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73970464513092946707544847 110955696769639420061317271)
      ·
        refine ⟨166433545154459130091975907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110955696769639420061317271 166433545154459130091975907)
        ·
          refine ⟨249650317731688695137963861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166433545154459130091975907 249650317731688695137963861)
          ·
            refine ⟨1462794830459113448074007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 249650317731688695137963861 1462794830459113448074007)
            ·
              refine ⟨2194192245688670172111011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462794830459113448074007 2194192245688670172111011)
              ·
                refine ⟨3291288368533005258166517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194192245688670172111011 3291288368533005258166517)
                ·
                  refine ⟨308558284549969242953111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3291288368533005258166517 308558284549969242953111)
                  ·
                    rfl

theorem cell21_1352059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 5].length) (baseStart_1352059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352059 prefixEnd_1352059 := by exact prefixLift 1352059
  have htrace : WordTrace (prefixWord ++ tailWord_1352059) baseStart_1352059 baseEnd_1352059 := by
    simpa [prefixWord, tailWord_1352059, baseEnd_1352059] using wordTrace_append hprefix tailTrace_1352059
  have hstable : (prefixWord ++ tailWord_1352059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352059).length < 2 ^ (prefixWord ++ tailWord_1352059).sum := by decide
  have hdescent : baseEnd_1352059 < baseStart_1352059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352087 : List Nat := [1, 1, 3, 3, 1, 1, 4, 7]
def baseStart_1352087 : Nat := 118140960795 + 1352087 * 2 ^ 59
def prefixEnd_1352087 : Nat := 4983230072969 + 3 ^ 40 * 1352087 * 2
def baseEnd_1352087 : Nat := 102854891510482472162129

theorem tailTrace_1352087 : CollatzResearch.WordTrace tailWord_1352087 prefixEnd_1352087 102854891510482472162129 := by
  unfold tailWord_1352087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49314664252627191920382515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32876442835084794613588343 49314664252627191920382515)
  ·
    refine ⟨73971996378940787880573773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49314664252627191920382515 73971996378940787880573773)
    ·
      refine ⟨27739498642102795455215165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73971996378940787880573773 27739498642102795455215165)
      ·
        refine ⟨10402311990788548295705687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27739498642102795455215165 10402311990788548295705687)
        ·
          refine ⟨15603467986182822443558531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10402311990788548295705687 15603467986182822443558531)
          ·
            refine ⟨23405201979274233665337797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15603467986182822443558531 23405201979274233665337797)
            ·
              refine ⟨4388475371113918812250837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23405201979274233665337797 4388475371113918812250837)
              ·
                refine ⟨102854891510482472162129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4388475371113918812250837 102854891510482472162129)
                ·
                  rfl

theorem cell21_1352087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 7].length) (baseStart_1352087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352087 prefixEnd_1352087 := by exact prefixLift 1352087
  have htrace : WordTrace (prefixWord ++ tailWord_1352087) baseStart_1352087 baseEnd_1352087 := by
    simpa [prefixWord, tailWord_1352087, baseEnd_1352087] using wordTrace_append hprefix tailTrace_1352087
  have hstable : (prefixWord ++ tailWord_1352087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352087).length < 2 ^ (prefixWord ++ tailWord_1352087).sum := by decide
  have hdescent : baseEnd_1352087 < baseStart_1352087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352104 : List Nat := [2, 1, 6, 1, 1, 10]
def baseStart_1352104 : Nat := 118140960795 + 1352104 * 2 ^ 59
def prefixEnd_1352104 : Nat := 4983230072969 + 3 ^ 40 * 1352104 * 2
def baseEnd_1352104 : Nat := 11428464969002191285297

theorem tailTrace_1352104 : CollatzResearch.WordTrace tailWord_1352104 prefixEnd_1352104 11428464969002191285297 := by
  unfold tailWord_1352104
  simp only [CollatzResearch.WordTrace]
  refine ⟨24657642146782801911875683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32876856195710402549167577 24657642146782801911875683)
  ·
    refine ⟨36986463220174202867813525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24657642146782801911875683 36986463220174202867813525)
    ·
      refine ⟨1733740463445665759428759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36986463220174202867813525 1733740463445665759428759)
      ·
        refine ⟨2600610695168498639143139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733740463445665759428759 2600610695168498639143139)
        ·
          refine ⟨3900916042752747958714709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600610695168498639143139 3900916042752747958714709)
          ·
            refine ⟨11428464969002191285297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3900916042752747958714709 11428464969002191285297)
            ·
              rfl

theorem cell21_1352104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 10].length) (baseStart_1352104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352104 prefixEnd_1352104 := by exact prefixLift 1352104
  have htrace : WordTrace (prefixWord ++ tailWord_1352104) baseStart_1352104 baseEnd_1352104 := by
    simpa [prefixWord, tailWord_1352104, baseEnd_1352104] using wordTrace_append hprefix tailTrace_1352104
  have hstable : (prefixWord ++ tailWord_1352104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352104).length < 2 ^ (prefixWord ++ tailWord_1352104).sum := by decide
  have hdescent : baseEnd_1352104 < baseStart_1352104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352225 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 4]
def baseStart_1352225 : Nat := 118140960795 + 1352225 * 2 ^ 59
def prefixEnd_1352225 : Nat := 4983230072969 + 3 ^ 40 * 1352225 * 2
def baseEnd_1352225 : Nat := 308596168011589843186105

theorem tailTrace_1352225 : CollatzResearch.WordTrace tailWord_1352225 prefixEnd_1352225 308596168011589843186105 := by
  unfold tailWord_1352225
  simp only [CollatzResearch.WordTrace]
  refine ⟨49319697526127241488906129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32879798350751494325937419 49319697526127241488906129)
  ·
    refine ⟨36989773144595431116679597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49319697526127241488906129 36989773144595431116679597)
    ·
      refine ⟨13871164929223286668754849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36989773144595431116679597 13871164929223286668754849)
      ·
        refine ⟨10403373696917465001566137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13871164929223286668754849 10403373696917465001566137)
        ·
          refine ⟨7802530272688098751174603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10403373696917465001566137 7802530272688098751174603)
          ·
            refine ⟨11703795409032148126761905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7802530272688098751174603 11703795409032148126761905)
            ·
              refine ⟨8777846556774111095071429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11703795409032148126761905 8777846556774111095071429)
              ·
                refine ⟨1645846229395145830325893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8777846556774111095071429 1645846229395145830325893)
                ·
                  refine ⟨308596168011589843186105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645846229395145830325893 308596168011589843186105)
                  ·
                    rfl

theorem cell21_1352225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 4].length) (baseStart_1352225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352225 prefixEnd_1352225 := by exact prefixLift 1352225
  have htrace : WordTrace (prefixWord ++ tailWord_1352225) baseStart_1352225 baseEnd_1352225 := by
    simpa [prefixWord, tailWord_1352225, baseEnd_1352225] using wordTrace_append hprefix tailTrace_1352225
  have hstable : (prefixWord ++ tailWord_1352225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352225).length < 2 ^ (prefixWord ++ tailWord_1352225).sum := by decide
  have hdescent : baseEnd_1352225 < baseStart_1352225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352242 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_1352242 : Nat := 118140960795 + 1352242 * 2 ^ 59
def prefixEnd_1352242 : Nat := 4983230072969 + 3 ^ 40 * 1352242 * 2
def baseEnd_1352242 : Nat := 308600047643201591402737

theorem tailTrace_1352242 : CollatzResearch.WordTrace tailWord_1352242 prefixEnd_1352242 308600047643201591402737 := by
  unfold tailWord_1352242
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330079391766413348068745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32880211711377102261516653 12330079391766413348068745)
  ·
    refine ⟨9247559543824810011051559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12330079391766413348068745 9247559543824810011051559)
    ·
      refine ⟨13871339315737215016577339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9247559543824810011051559 13871339315737215016577339)
      ·
        refine ⟨20807008973605822524866009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13871339315737215016577339 20807008973605822524866009)
        ·
          refine ⟨15605256730204366893649507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20807008973605822524866009 15605256730204366893649507)
          ·
            refine ⟨23407885095306550340474261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15605256730204366893649507 23407885095306550340474261)
            ·
              refine ⟨1097244613842494547209731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23407885095306550340474261 1097244613842494547209731)
              ·
                refine ⟨1645866920763741820814597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097244613842494547209731 1645866920763741820814597)
                ·
                  refine ⟨308600047643201591402737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1645866920763741820814597 308600047643201591402737)
                  ·
                    rfl

theorem cell21_1352242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_1352242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352242 prefixEnd_1352242 := by exact prefixLift 1352242
  have htrace : WordTrace (prefixWord ++ tailWord_1352242) baseStart_1352242 baseEnd_1352242 := by
    simpa [prefixWord, tailWord_1352242, baseEnd_1352242] using wordTrace_append hprefix tailTrace_1352242
  have hstable : (prefixWord ++ tailWord_1352242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352242).length < 2 ^ (prefixWord ++ tailWord_1352242).sum := by decide
  have hdescent : baseEnd_1352242 < baseStart_1352242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352290 : List Nat := [3, 3, 2, 3, 1, 2, 1, 6]
def baseStart_1352290 : Nat := 118140960795 + 1352290 * 2 ^ 59
def prefixEnd_1352290 : Nat := 4983230072969 + 3 ^ 40 * 1352290 * 2
def baseEnd_1352290 : Nat := 102870333965721391534213

theorem tailTrace_1352290 : CollatzResearch.WordTrace tailWord_1352290 prefixEnd_1352290 102870333965721391534213 := by
  unfold tailWord_1352290
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330517067722939397505581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32881378847261171726681549 12330517067722939397505581)
  ·
    refine ⟨4623943900396102274064593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12330517067722939397505581 4623943900396102274064593)
    ·
      refine ⟨3467957925297076705548445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623943900396102274064593 3467957925297076705548445)
      ·
        refine ⟨1300484221986403764580667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3467957925297076705548445 1300484221986403764580667)
        ·
          refine ⟨1950726332979605646871001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300484221986403764580667 1950726332979605646871001)
          ·
            refine ⟨1463044749734704235153251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950726332979605646871001 1463044749734704235153251)
            ·
              refine ⟨2194567124602056352729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463044749734704235153251 2194567124602056352729877)
              ·
                refine ⟨102870333965721391534213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194567124602056352729877 102870333965721391534213)
                ·
                  rfl

theorem cell21_1352290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_1352290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352290 prefixEnd_1352290 := by exact prefixLift 1352290
  have htrace : WordTrace (prefixWord ++ tailWord_1352290) baseStart_1352290 baseEnd_1352290 := by
    simpa [prefixWord, tailWord_1352290, baseEnd_1352290] using wordTrace_append hprefix tailTrace_1352290
  have hstable : (prefixWord ++ tailWord_1352290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352290).length < 2 ^ (prefixWord ++ tailWord_1352290).sum := by decide
  have hdescent : baseEnd_1352290 < baseStart_1352290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352329 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 9]
def baseStart_1352329 : Nat := 118140960795 + 1352329 * 2 ^ 59
def prefixEnd_1352329 : Nat := 4983230072969 + 3 ^ 40 * 1352329 * 2
def baseEnd_1352329 : Nat := 308619902228508773452559

theorem tailTrace_1352329 : CollatzResearch.WordTrace tailWord_1352329 prefixEnd_1352329 308619902228508773452559 := by
  unfold tailWord_1352329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49323490717750467250692041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32882327145166978167128027 49323490717750467250692041)
  ·
    refine ⟨36992618038312850438019031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49323490717750467250692041 36992618038312850438019031)
    ·
      refine ⟨55488927057469275657028547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36992618038312850438019031 55488927057469275657028547)
      ·
        refine ⟨83233390586203913485542821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55488927057469275657028547 83233390586203913485542821)
        ·
          refine ⟨15606260734913233778539279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83233390586203913485542821 15606260734913233778539279)
          ·
            refine ⟨23409391102369850667808919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15606260734913233778539279 23409391102369850667808919)
            ·
              refine ⟨35114086653554776001713379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23409391102369850667808919 35114086653554776001713379)
              ·
                refine ⟨52671129980332164002570069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35114086653554776001713379 52671129980332164002570069)
                ·
                  refine ⟨308619902228508773452559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52671129980332164002570069 308619902228508773452559)
                  ·
                    rfl

theorem cell21_1352329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_1352329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352329 prefixEnd_1352329 := by exact prefixLift 1352329
  have htrace : WordTrace (prefixWord ++ tailWord_1352329) baseStart_1352329 baseEnd_1352329 := by
    simpa [prefixWord, tailWord_1352329, baseEnd_1352329] using wordTrace_append hprefix tailTrace_1352329
  have hstable : (prefixWord ++ tailWord_1352329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352329).length < 2 ^ (prefixWord ++ tailWord_1352329).sum := by decide
  have hdescent : baseEnd_1352329 < baseStart_1352329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352366 : List Nat := [4, 1, 4, 1, 1, 3, 2, 5]
def baseStart_1352366 : Nat := 118140960795 + 1352366 * 2 ^ 59
def prefixEnd_1352366 : Nat := 4983230072969 + 3 ^ 40 * 1352366 * 2
def baseEnd_1352366 : Nat := 102876115377534977111939

theorem tailTrace_1352366 : CollatzResearch.WordTrace tailWord_1352366 prefixEnd_1352366 102876115377534977111939 := by
  unfold tailWord_1352366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165605027327052821223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32883226812410948379859301 6165605027327052821223619)
  ·
    refine ⟨9248407540990579231835429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165605027327052821223619 9248407540990579231835429)
    ·
      refine ⟨1734076413935733605969143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9248407540990579231835429 1734076413935733605969143)
      ·
        refine ⟨2601114620903600408953715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734076413935733605969143 2601114620903600408953715)
        ·
          refine ⟨3901671931355400613430573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601114620903600408953715 3901671931355400613430573)
          ·
            refine ⟨1463126974258275230036465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3901671931355400613430573 1463126974258275230036465)
            ·
              refine ⟨1097345230693706422527349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463126974258275230036465 1097345230693706422527349)
              ·
                refine ⟨102876115377534977111939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1097345230693706422527349 102876115377534977111939)
                ·
                  rfl

theorem cell21_1352366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_1352366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352366 prefixEnd_1352366 := by exact prefixLift 1352366
  have htrace : WordTrace (prefixWord ++ tailWord_1352366) baseStart_1352366 baseEnd_1352366 := by
    simpa [prefixWord, tailWord_1352366, baseEnd_1352366] using wordTrace_append hprefix tailTrace_1352366
  have hstable : (prefixWord ++ tailWord_1352366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352366).length < 2 ^ (prefixWord ++ tailWord_1352366).sum := by decide
  have hdescent : baseEnd_1352366 < baseStart_1352366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352397 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 5]
def baseStart_1352397 : Nat := 118140960795 + 1352397 * 2 ^ 59
def prefixEnd_1352397 : Nat := 4983230072969 + 3 ^ 40 * 1352397 * 2
def baseEnd_1352397 : Nat := 308635420754955766319087

theorem tailTrace_1352397 : CollatzResearch.WordTrace tailWord_1352397 prefixEnd_1352397 308635420754955766319087 := by
  unfold tailWord_1352397
  simp only [CollatzResearch.WordTrace]
  refine ⟨49325970881504114864167445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32883980587669409909444963 49325970881504114864167445)
  ·
    refine ⟨2312154885070505384257849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49325970881504114864167445 2312154885070505384257849)
    ·
      refine ⟨1734116163802879038193387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2312154885070505384257849 1734116163802879038193387)
      ·
        refine ⟨2601174245704318557290081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734116163802879038193387 2601174245704318557290081)
        ·
          refine ⟨1950880684278238917967561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2601174245704318557290081 1950880684278238917967561)
          ·
            refine ⟨1463160513208679188475671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950880684278238917967561 1463160513208679188475671)
            ·
              refine ⟨2194740769813018782713507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463160513208679188475671 2194740769813018782713507)
              ·
                refine ⟨3292111154719528174070261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194740769813018782713507 3292111154719528174070261)
                ·
                  refine ⟨308635420754955766319087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3292111154719528174070261 308635420754955766319087)
                  ·
                    rfl

theorem cell21_1352397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_1352397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352397 prefixEnd_1352397 := by exact prefixLift 1352397
  have htrace : WordTrace (prefixWord ++ tailWord_1352397) baseStart_1352397 baseEnd_1352397 := by
    simpa [prefixWord, tailWord_1352397, baseEnd_1352397] using wordTrace_append hprefix tailTrace_1352397
  have hstable : (prefixWord ++ tailWord_1352397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352397).length < 2 ^ (prefixWord ++ tailWord_1352397).sum := by decide
  have hdescent : baseEnd_1352397 < baseStart_1352397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352456 : List Nat := [2, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_1352456 : Nat := 118140960795 + 1352456 * 2 ^ 59
def prefixEnd_1352456 : Nat := 4983230072969 + 3 ^ 40 * 1352456 * 2
def baseEnd_1352456 : Nat := 308648885358784774835633

theorem tailTrace_1352456 : CollatzResearch.WordTrace tailWord_1352456 prefixEnd_1352456 308648885358784774835633 := by
  unfold tailWord_1352456
  simp only [CollatzResearch.WordTrace]
  refine ⟨24664061394145183970282611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32885415192193578627043481 24664061394145183970282611)
  ·
    refine ⟨36996092091217775955423917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24664061394145183970282611 36996092091217775955423917)
    ·
      refine ⟨13873534534206665983283969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36996092091217775955423917 13873534534206665983283969)
      ·
        refine ⟨10405150900654999487462977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13873534534206665983283969 10405150900654999487462977)
        ·
          refine ⟨7803863175491249615597233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10405150900654999487462977 7803863175491249615597233)
          ·
            refine ⟨5852897381618437211697925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7803863175491249615597233 5852897381618437211697925)
            ·
              refine ⟨1097418259053456977193361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5852897381618437211697925 1097418259053456977193361)
              ·
                refine ⟨823063694290092732895021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097418259053456977193361 823063694290092732895021)
                ·
                  refine ⟨308648885358784774835633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823063694290092732895021 308648885358784774835633)
                  ·
                    rfl

theorem cell21_1352456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_1352456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352456 prefixEnd_1352456 := by exact prefixLift 1352456
  have htrace : WordTrace (prefixWord ++ tailWord_1352456) baseStart_1352456 baseEnd_1352456 := by
    simpa [prefixWord, tailWord_1352456, baseEnd_1352456] using wordTrace_append hprefix tailTrace_1352456
  have hstable : (prefixWord ++ tailWord_1352456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352456).length < 2 ^ (prefixWord ++ tailWord_1352456).sum := by decide
  have hdescent : baseEnd_1352456 < baseStart_1352456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352625 : List Nat := [1, 2, 2, 4, 3, 2, 2, 2, 3]
def baseStart_1352625 : Nat := 118140960795 + 1352625 * 2 ^ 59
def prefixEnd_1352625 : Nat := 4983230072969 + 3 ^ 40 * 1352625 * 2
def baseEnd_1352625 : Nat := 308687453461278036518621

theorem tailTrace_1352625 : CollatzResearch.WordTrace tailWord_1352625 prefixEnd_1352625 308687453461278036518621 := by
  unfold tailWord_1352625
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334286724678109803467329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32889524483118739868978219 49334286724678109803467329)
  ·
    refine ⟨37000715043508582352600497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49334286724678109803467329 37000715043508582352600497)
    ·
      refine ⟨27750536282631436764450373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37000715043508582352600497 27750536282631436764450373)
      ·
        refine ⟨5203225552993394393334445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27750536282631436764450373 5203225552993394393334445)
        ·
          refine ⟨1951209582372522897500417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5203225552993394393334445 1951209582372522897500417)
          ·
            refine ⟨1463407186779392173125313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951209582372522897500417 1463407186779392173125313)
            ·
              refine ⟨1097555390084544129843985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463407186779392173125313 1097555390084544129843985)
              ·
                refine ⟨823166542563408097382989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097555390084544129843985 823166542563408097382989)
                ·
                  refine ⟨308687453461278036518621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823166542563408097382989 308687453461278036518621)
                  ·
                    rfl

theorem cell21_1352625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_1352625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352625 prefixEnd_1352625 := by exact prefixLift 1352625
  have htrace : WordTrace (prefixWord ++ tailWord_1352625) baseStart_1352625 baseEnd_1352625 := by
    simpa [prefixWord, tailWord_1352625, baseEnd_1352625] using wordTrace_append hprefix tailTrace_1352625
  have hstable : (prefixWord ++ tailWord_1352625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352625).length < 2 ^ (prefixWord ++ tailWord_1352625).sum := by decide
  have hdescent : baseEnd_1352625 < baseStart_1352625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352709 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 5]
def baseStart_1352709 : Nat := 118140960795 + 1352709 * 2 ^ 59
def prefixEnd_1352709 : Nat := 4983230072969 + 3 ^ 40 * 1352709 * 2
def baseEnd_1352709 : Nat := 308706623405712557118449

theorem tailTrace_1352709 : CollatzResearch.WordTrace tailWord_1352709 prefixEnd_1352709 308706623405712557118449 := by
  unfold tailWord_1352709
  simp only [CollatzResearch.WordTrace]
  refine ⟨49337350456373792149525181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32891566970915861433016787 49337350456373792149525181)
  ·
    refine ⟨18501506421140172056071943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49337350456373792149525181 18501506421140172056071943)
    ·
      refine ⟨27752259631710258084107915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18501506421140172056071943 27752259631710258084107915)
      ·
        refine ⟨41628389447565387126161873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27752259631710258084107915 41628389447565387126161873)
        ·
          refine ⟨31221292085674040344621405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41628389447565387126161873 31221292085674040344621405)
          ·
            refine ⟨11707984532127765129233027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31221292085674040344621405 11707984532127765129233027)
            ·
              refine ⟨17561976798191647693849541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11707984532127765129233027 17561976798191647693849541)
              ·
                refine ⟨3292870649660933942596789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17561976798191647693849541 3292870649660933942596789)
                ·
                  refine ⟨308706623405712557118449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3292870649660933942596789 308706623405712557118449)
                  ·
                    rfl

theorem cell21_1352709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_1352709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352709 prefixEnd_1352709 := by exact prefixLift 1352709
  have htrace : WordTrace (prefixWord ++ tailWord_1352709) baseStart_1352709 baseEnd_1352709 := by
    simpa [prefixWord, tailWord_1352709, baseEnd_1352709] using wordTrace_append hprefix tailTrace_1352709
  have hstable : (prefixWord ++ tailWord_1352709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352709).length < 2 ^ (prefixWord ++ tailWord_1352709).sum := by decide
  have hdescent : baseEnd_1352709 < baseStart_1352709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352712 : List Nat := [2, 1, 3, 2, 1, 5, 2, 5]
def baseStart_1352712 : Nat := 118140960795 + 1352712 * 2 ^ 59
def prefixEnd_1352712 : Nat := 4983230072969 + 3 ^ 40 * 1352712 * 2
def baseEnd_1352712 : Nat := 102902436015528406189481

theorem tailTrace_1352712 : CollatzResearch.WordTrace tailWord_1352712 prefixEnd_1352712 102902436015528406189481 := by
  unfold tailWord_1352712
  simp only [CollatzResearch.WordTrace]
  refine ⟨24668729937681461830942195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32891639916908615774589593 24668729937681461830942195)
  ·
    refine ⟨37003094906522192746413293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24668729937681461830942195 37003094906522192746413293)
    ·
      refine ⟨13876160589945822279904985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37003094906522192746413293 13876160589945822279904985)
      ·
        refine ⟨10407120442459366709928739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13876160589945822279904985 10407120442459366709928739)
        ·
          refine ⟨15610680663689050064893109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10407120442459366709928739 15610680663689050064893109)
          ·
            refine ⟨1463501312220848443583729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15610680663689050064893109 1463501312220848443583729)
            ·
              refine ⟨1097625984165636332687797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463501312220848443583729 1097625984165636332687797)
              ·
                refine ⟨102902436015528406189481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1097625984165636332687797 102902436015528406189481)
                ·
                  rfl

theorem cell21_1352712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_1352712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352712 prefixEnd_1352712 := by exact prefixLift 1352712
  have htrace : WordTrace (prefixWord ++ tailWord_1352712) baseStart_1352712 baseEnd_1352712 := by
    simpa [prefixWord, tailWord_1352712, baseEnd_1352712] using wordTrace_append hprefix tailTrace_1352712
  have hstable : (prefixWord ++ tailWord_1352712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352712).length < 2 ^ (prefixWord ++ tailWord_1352712).sum := by decide
  have hdescent : baseEnd_1352712 < baseStart_1352712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352743 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 5]
def baseStart_1352743 : Nat := 118140960795 + 1352743 * 2 ^ 59
def prefixEnd_1352743 : Nat := 4983230072969 + 3 ^ 40 * 1352743 * 2
def baseEnd_1352743 : Nat := 308714382668936053551713

theorem tailTrace_1352743 : CollatzResearch.WordTrace tailWord_1352743 prefixEnd_1352743 308714382668936053551713 := by
  unfold tailWord_1352743
  simp only [CollatzResearch.WordTrace]
  refine ⟨49338590538250615956262883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32892393692167077304175255 49338590538250615956262883)
  ·
    refine ⟨74007885807375923934394325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49338590538250615956262883 74007885807375923934394325)
    ·
      refine ⟨1734559823610373217212367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74007885807375923934394325 1734559823610373217212367)
      ·
        refine ⟨2601839735415559825818551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734559823610373217212367 2601839735415559825818551)
        ·
          refine ⟨3902759603123339738727827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601839735415559825818551 3902759603123339738727827)
          ·
            refine ⟨5854139404685009608091741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902759603123339738727827 5854139404685009608091741)
            ·
              refine ⟨2195302276756878603034403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5854139404685009608091741 2195302276756878603034403)
              ·
                refine ⟨3292953415135317904551605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195302276756878603034403 3292953415135317904551605)
                ·
                  refine ⟨308714382668936053551713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3292953415135317904551605 308714382668936053551713)
                  ·
                    rfl

theorem cell21_1352743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 5].length) (baseStart_1352743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352743 prefixEnd_1352743 := by exact prefixLift 1352743
  have htrace : WordTrace (prefixWord ++ tailWord_1352743) baseStart_1352743 baseEnd_1352743 := by
    simpa [prefixWord, tailWord_1352743, baseEnd_1352743] using wordTrace_append hprefix tailTrace_1352743
  have hstable : (prefixWord ++ tailWord_1352743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352743).length < 2 ^ (prefixWord ++ tailWord_1352743).sum := by decide
  have hdescent : baseEnd_1352743 < baseStart_1352743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352816 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_1352816 : Nat := 118140960795 + 1352816 * 2 ^ 59
def prefixEnd_1352816 : Nat := 4983230072969 + 3 ^ 40 * 1352816 * 2
def baseEnd_1352816 : Nat := 308731042263504148834897

theorem tailTrace_1352816 : CollatzResearch.WordTrace tailWord_1352816 prefixEnd_1352816 308731042263504148834897 := by
  unfold tailWord_1352816
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670626533493074711835151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32894168711324099615780201 24670626533493074711835151)
  ·
    refine ⟨37005939800239612067752727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24670626533493074711835151 37005939800239612067752727)
    ·
      refine ⟨55508909700359418101629091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37005939800239612067752727 55508909700359418101629091)
      ·
        refine ⟨83263364550539127152443637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55508909700359418101629091 83263364550539127152443637)
        ·
          refine ⟨7805940426613043170541591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83263364550539127152443637 7805940426613043170541591)
          ·
            refine ⟨11708910639919564755812387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805940426613043170541591 11708910639919564755812387)
            ·
              refine ⟨17563365959879347133718581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708910639919564755812387 17563365959879347133718581)
              ·
                refine ⟨1646565558738688793786117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17563365959879347133718581 1646565558738688793786117)
                ·
                  refine ⟨308731042263504148834897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1646565558738688793786117 308731042263504148834897)
                  ·
                    rfl

theorem cell21_1352816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_1352816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352816 prefixEnd_1352816 := by exact prefixLift 1352816
  have htrace : WordTrace (prefixWord ++ tailWord_1352816) baseStart_1352816 baseEnd_1352816 := by
    simpa [prefixWord, tailWord_1352816, baseEnd_1352816] using wordTrace_append hprefix tailTrace_1352816
  have hstable : (prefixWord ++ tailWord_1352816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352816).length < 2 ^ (prefixWord ++ tailWord_1352816).sum := by decide
  have hdescent : baseEnd_1352816 < baseStart_1352816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352850 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1352850 : Nat := 118140960795 + 1352850 * 2 ^ 59
def prefixEnd_1352850 : Nat := 4983230072969 + 3 ^ 40 * 1352850 * 2
def baseEnd_1352850 : Nat := 308738801526727645268161

theorem tailTrace_1352850 : CollatzResearch.WordTrace tailWord_1352850 prefixEnd_1352850 308738801526727645268161 := by
  unfold tailWord_1352850
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335623287215743307602001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32894995432575315486938669 12335623287215743307602001)
  ·
    refine ⟨9251717465411807480701501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12335623287215743307602001 9251717465411807480701501)
    ·
      refine ⟨3469394049529427805263063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9251717465411807480701501 3469394049529427805263063)
      ·
        refine ⟨5204091074294141707894595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3469394049529427805263063 5204091074294141707894595)
        ·
          refine ⟨7806136611441212561841893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204091074294141707894595 7806136611441212561841893)
          ·
            refine ⟨1463650614645227355345355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7806136611441212561841893 1463650614645227355345355)
            ·
              refine ⟨2195475921967841033018033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463650614645227355345355 2195475921967841033018033)
              ·
                refine ⟨1646606941475880774763525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195475921967841033018033 1646606941475880774763525)
                ·
                  refine ⟨308738801526727645268161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1646606941475880774763525 308738801526727645268161)
                  ·
                    rfl

theorem cell21_1352850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1352850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352850 prefixEnd_1352850 := by exact prefixLift 1352850
  have htrace : WordTrace (prefixWord ++ tailWord_1352850) baseStart_1352850 baseEnd_1352850 := by
    simpa [prefixWord, tailWord_1352850, baseEnd_1352850] using wordTrace_append hprefix tailTrace_1352850
  have hstable : (prefixWord ++ tailWord_1352850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352850).length < 2 ^ (prefixWord ++ tailWord_1352850).sum := by decide
  have hdescent : baseEnd_1352850 < baseStart_1352850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352892 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1352892 : Nat := 118140960795 + 1352892 * 2 ^ 59
def prefixEnd_1352892 : Nat := 4983230072969 + 3 ^ 40 * 1352892 * 2
def baseEnd_1352892 : Nat := 308748386498944905568075

theorem tailTrace_1352892 : CollatzResearch.WordTrace tailWord_1352892 prefixEnd_1352892 308748386498944905568075 := by
  unfold tailWord_1352892
  simp only [CollatzResearch.WordTrace]
  refine ⟨24672012507355407201718465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32896016676473876268957953 24672012507355407201718465)
  ·
    refine ⟨18504009380516555401288849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24672012507355407201718465 18504009380516555401288849)
    ·
      refine ⟨13878007035387416550966637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18504009380516555401288849 13878007035387416550966637)
      ·
        refine ⟨5204252638270281206612489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13878007035387416550966637 5204252638270281206612489)
        ·
          refine ⟨3903189478702710904959367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5204252638270281206612489 3903189478702710904959367)
          ·
            refine ⟨5854784218054066357439051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903189478702710904959367 5854784218054066357439051)
            ·
              refine ⟨8782176327081099536158577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854784218054066357439051 8782176327081099536158577)
              ·
                refine ⟨6586632245310824652118933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8782176327081099536158577 6586632245310824652118933)
                ·
                  refine ⟨308748386498944905568075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6586632245310824652118933 308748386498944905568075)
                  ·
                    rfl

theorem cell21_1352892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1352892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352892 prefixEnd_1352892 := by exact prefixLift 1352892
  have htrace : WordTrace (prefixWord ++ tailWord_1352892) baseStart_1352892 baseEnd_1352892 := by
    simpa [prefixWord, tailWord_1352892, baseEnd_1352892] using wordTrace_append hprefix tailTrace_1352892
  have hstable : (prefixWord ++ tailWord_1352892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352892).length < 2 ^ (prefixWord ++ tailWord_1352892).sum := by decide
  have hdescent : baseEnd_1352892 < baseStart_1352892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352898 : List Nat := [3, 5, 1, 1, 3, 1, 7]
def baseStart_1352898 : Nat := 118140960795 + 1352898 * 2 ^ 59
def prefixEnd_1352898 : Nat := 4983230072969 + 3 ^ 40 * 1352898 * 2
def baseEnd_1352898 : Nat := 34305528420076692052007

theorem tailTrace_1352898 : CollatzResearch.WordTrace tailWord_1352898 prefixEnd_1352898 34305528420076692052007 := by
  unfold tailWord_1352898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336060963172269357038837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32896162568459384952103565 12336060963172269357038837)
  ·
    refine ⟨1156505715297400252222391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12336060963172269357038837 1156505715297400252222391)
    ·
      refine ⟨1734758572946100378333587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156505715297400252222391 1734758572946100378333587)
      ·
        refine ⟨2602137859419150567500381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734758572946100378333587 2602137859419150567500381)
        ·
          refine ⟨975801697282181462812643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602137859419150567500381 975801697282181462812643)
          ·
            refine ⟨1463702545923272194218965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975801697282181462812643 1463702545923272194218965)
            ·
              refine ⟨34305528420076692052007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1463702545923272194218965 34305528420076692052007)
              ·
                rfl

theorem cell21_1352898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 7].length) (baseStart_1352898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352898 prefixEnd_1352898 := by exact prefixLift 1352898
  have htrace : WordTrace (prefixWord ++ tailWord_1352898) baseStart_1352898 baseEnd_1352898 := by
    simpa [prefixWord, tailWord_1352898, baseEnd_1352898] using wordTrace_append hprefix tailTrace_1352898
  have hstable : (prefixWord ++ tailWord_1352898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352898).length < 2 ^ (prefixWord ++ tailWord_1352898).sum := by decide
  have hdescent : baseEnd_1352898 < baseStart_1352898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352906 : List Nat := [3, 1, 2, 1, 3, 2, 9]
def baseStart_1352906 : Nat := 118140960795 + 1352906 * 2 ^ 59
def prefixEnd_1352906 : Nat := 4983230072969 + 3 ^ 40 * 1352906 * 2
def baseEnd_1352906 : Nat := 34305731276631554703857

theorem tailTrace_1352906 : CollatzResearch.WordTrace tailWord_1352906 prefixEnd_1352906 34305731276631554703857 := by
  unfold tailWord_1352906
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336133909165023698611643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32896357091106729862964381 12336133909165023698611643)
  ·
    refine ⟨18504200863747535547917465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336133909165023698611643 18504200863747535547917465)
    ·
      refine ⟨13878150647810651660938099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18504200863747535547917465 13878150647810651660938099)
      ·
        refine ⟨20817225971715977491407149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13878150647810651660938099 20817225971715977491407149)
        ·
          refine ⟨7806459739393491559277681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20817225971715977491407149 7806459739393491559277681)
          ·
            refine ⟨5854844804545118669458261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7806459739393491559277681 5854844804545118669458261)
            ·
              refine ⟨34305731276631554703857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5854844804545118669458261 34305731276631554703857)
              ·
                rfl

theorem cell21_1352906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 9].length) (baseStart_1352906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352906 prefixEnd_1352906 := by exact prefixLift 1352906
  have htrace : WordTrace (prefixWord ++ tailWord_1352906) baseStart_1352906 baseEnd_1352906 := by
    simpa [prefixWord, tailWord_1352906, baseEnd_1352906] using wordTrace_append hprefix tailTrace_1352906
  have hstable : (prefixWord ++ tailWord_1352906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352906).length < 2 ^ (prefixWord ++ tailWord_1352906).sum := by decide
  have hdescent : baseEnd_1352906 < baseStart_1352906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352954 : List Nat := [3, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_1352954 : Nat := 118140960795 + 1352954 * 2 ^ 59
def prefixEnd_1352954 : Nat := 4983230072969 + 3 ^ 40 * 1352954 * 2
def baseEnd_1352954 : Nat := 308762535743646575534615

theorem tailTrace_1352954 : CollatzResearch.WordTrace tailWord_1352954 prefixEnd_1352954 308762535743646575534615 := by
  unfold tailWord_1352954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336571585121549748048479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32897524226990799328129277 12336571585121549748048479)
  ·
    refine ⟨18504857377682324622072719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336571585121549748048479 18504857377682324622072719)
    ·
      refine ⟨27757286066523486933109079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18504857377682324622072719 27757286066523486933109079)
      ·
        refine ⟨41635929099785230399663619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27757286066523486933109079 41635929099785230399663619)
        ·
          refine ⟨62453893649677845599495429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41635929099785230399663619 62453893649677845599495429)
          ·
            refine ⟨11710105059314596049905393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62453893649677845599495429 11710105059314596049905393)
            ·
              refine ⟨8782578794485947037429045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11710105059314596049905393 8782578794485947037429045)
              ·
                refine ⟨823366761983057534758973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8782578794485947037429045 823366761983057534758973)
                ·
                  refine ⟨308762535743646575534615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823366761983057534758973 308762535743646575534615)
                  ·
                    rfl

theorem cell21_1352954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_1352954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352954 prefixEnd_1352954 := by exact prefixLift 1352954
  have htrace : WordTrace (prefixWord ++ tailWord_1352954) baseStart_1352954 baseEnd_1352954 := by
    simpa [prefixWord, tailWord_1352954, baseEnd_1352954] using wordTrace_append hprefix tailTrace_1352954
  have hstable : (prefixWord ++ tailWord_1352954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352954).length < 2 ^ (prefixWord ++ tailWord_1352954).sum := by decide
  have hdescent : baseEnd_1352954 < baseStart_1352954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352971 : List Nat := [1, 1, 1, 1, 5, 3, 4, 2, 3]
def baseStart_1352971 : Nat := 118140960795 + 1352971 * 2 ^ 59
def prefixEnd_1352971 : Nat := 4983230072969 + 3 ^ 40 * 1352971 * 2
def baseEnd_1352971 : Nat := 308766415375258323751247

theorem tailTrace_1352971 : CollatzResearch.WordTrace tailWord_1352971 prefixEnd_1352971 308766415375258323751247 := by
  unfold tailWord_1352971
  simp only [CollatzResearch.WordTrace]
  refine ⟨49346906381424610895562767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32897937587616407263708511 49346906381424610895562767)
  ·
    refine ⟨74020359572136916343344151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49346906381424610895562767 74020359572136916343344151)
    ·
      refine ⟨111030539358205374515016227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74020359572136916343344151 111030539358205374515016227)
      ·
        refine ⟨166545809037308061772524341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111030539358205374515016227 166545809037308061772524341)
        ·
          refine ⟨15613669597247630791174157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166545809037308061772524341 15613669597247630791174157)
          ·
            refine ⟨5855126098967861546690309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15613669597247630791174157 5855126098967861546690309)
            ·
              refine ⟨1097836143556474040004433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5855126098967861546690309 1097836143556474040004433)
              ·
                refine ⟨823377107667355530003325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1097836143556474040004433 823377107667355530003325)
                ·
                  refine ⟨308766415375258323751247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823377107667355530003325 308766415375258323751247)
                  ·
                    rfl

theorem cell21_1352971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 2, 3].length) (baseStart_1352971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1352971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1352971 prefixEnd_1352971 := by exact prefixLift 1352971
  have htrace : WordTrace (prefixWord ++ tailWord_1352971) baseStart_1352971 baseEnd_1352971 := by
    simpa [prefixWord, tailWord_1352971, baseEnd_1352971] using wordTrace_append hprefix tailTrace_1352971
  have hstable : (prefixWord ++ tailWord_1352971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352971).length < 2 ^ (prefixWord ++ tailWord_1352971).sum := by decide
  have hdescent : baseEnd_1352971 < baseStart_1352971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353064 : List Nat := [2, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_1353064 : Nat := 118140960795 + 1353064 * 2 ^ 59
def prefixEnd_1353064 : Nat := 4983230072969 + 3 ^ 40 * 1353064 * 2
def baseEnd_1353064 : Nat := 308787639242310828701057

theorem tailTrace_1353064 : CollatzResearch.WordTrace tailWord_1353064 prefixEnd_1353064 308787639242310828701057 := by
  unfold tailWord_1353064
  simp only [CollatzResearch.WordTrace]
  refine ⟨24675149185043843889349123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32900198913391791852465497 24675149185043843889349123)
  ·
    refine ⟨37012723777565765834023685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24675149185043843889349123 37012723777565765834023685)
    ·
      refine ⟨6939885708293581093879441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37012723777565765834023685 6939885708293581093879441)
      ·
        refine ⟨5204914281220185820409581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939885708293581093879441 5204914281220185820409581)
        ·
          refine ⟨1951842855457569682653593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5204914281220185820409581 1951842855457569682653593)
          ·
            refine ⟨1463882141593177261990195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951842855457569682653593 1463882141593177261990195)
            ·
              refine ⟨2195823212389765892985293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463882141593177261990195 2195823212389765892985293)
              ·
                refine ⟨823433704646162209869485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195823212389765892985293 823433704646162209869485)
                ·
                  refine ⟨308787639242310828701057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823433704646162209869485 308787639242310828701057)
                  ·
                    rfl

theorem cell21_1353064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_1353064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353064 prefixEnd_1353064 := by exact prefixLift 1353064
  have htrace : WordTrace (prefixWord ++ tailWord_1353064) baseStart_1353064 baseEnd_1353064 := by
    simpa [prefixWord, tailWord_1353064, baseEnd_1353064] using wordTrace_append hprefix tailTrace_1353064
  have hstable : (prefixWord ++ tailWord_1353064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353064).length < 2 ^ (prefixWord ++ tailWord_1353064).sum := by decide
  have hdescent : baseEnd_1353064 < baseStart_1353064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353213 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1353213 : Nat := 118140960795 + 1353213 * 2 ^ 59
def prefixEnd_1353213 : Nat := 4983230072969 + 3 ^ 40 * 1353213 * 2
def baseEnd_1353213 : Nat := 308821643072319680717419

theorem tailTrace_1353213 : CollatzResearch.WordTrace tailWord_1353213 prefixEnd_1353213 308821643072319680717419 := by
  unfold tailWord_1353213
  simp only [CollatzResearch.WordTrace]
  refine ⟨49355732846547886225872293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32903821897698590817248195 49355732846547886225872293)
  ·
    refine ⟨9254199908727728667351055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49355732846547886225872293 9254199908727728667351055)
    ·
      refine ⟨13881299863091593001026583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254199908727728667351055 13881299863091593001026583)
      ·
        refine ⟨20821949794637389501539875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13881299863091593001026583 20821949794637389501539875)
        ·
          refine ⟨31232924691956084252309813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20821949794637389501539875 31232924691956084252309813)
          ·
            refine ⟨2928086689870882898654045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31232924691956084252309813 2928086689870882898654045)
            ·
              refine ⟨1098032508701581086995267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2928086689870882898654045 1098032508701581086995267)
              ·
                refine ⟨1647048763052371630492901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098032508701581086995267 1647048763052371630492901)
                ·
                  refine ⟨308821643072319680717419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647048763052371630492901 308821643072319680717419)
                  ·
                    rfl

theorem cell21_1353213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1353213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353213 prefixEnd_1353213 := by exact prefixLift 1353213
  have htrace : WordTrace (prefixWord ++ tailWord_1353213) baseStart_1353213 baseEnd_1353213 := by
    simpa [prefixWord, tailWord_1353213, baseEnd_1353213] using wordTrace_append hprefix tailTrace_1353213
  have hstable : (prefixWord ++ tailWord_1353213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353213).length < 2 ^ (prefixWord ++ tailWord_1353213).sum := by decide
  have hdescent : baseEnd_1353213 < baseStart_1353213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353272 : List Nat := [2, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_1353272 : Nat := 118140960795 + 1353272 * 2 ^ 59
def prefixEnd_1353272 : Nat := 4983230072969 + 3 ^ 40 * 1353272 * 2
def baseEnd_1353272 : Nat := 308835107676148689233965

theorem tailTrace_1353272 : CollatzResearch.WordTrace tailWord_1353272 prefixEnd_1353272 308835107676148689233965 := by
  unfold tailWord_1353272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24678942376667069651135035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32905256502222759534846713 24678942376667069651135035)
  ·
    refine ⟨37018413565000604476702553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24678942376667069651135035 37018413565000604476702553)
    ·
      refine ⟨27763810173750453357526915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37018413565000604476702553 27763810173750453357526915)
      ·
        refine ⟨41645715260625680036290373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27763810173750453357526915 41645715260625680036290373)
        ·
          refine ⟨7808571611367315006804445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41645715260625680036290373 7808571611367315006804445)
          ·
            refine ⟨2928214354262743127551667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7808571611367315006804445 2928214354262743127551667)
            ·
              refine ⟨4392321531394114691327501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928214354262743127551667 4392321531394114691327501)
              ·
                refine ⟨1647120574272793009247813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4392321531394114691327501 1647120574272793009247813)
                ·
                  refine ⟨308835107676148689233965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647120574272793009247813 308835107676148689233965)
                  ·
                    rfl

theorem cell21_1353272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_1353272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353272 prefixEnd_1353272 := by exact prefixLift 1353272
  have htrace : WordTrace (prefixWord ++ tailWord_1353272) baseStart_1353272 baseEnd_1353272 := by
    simpa [prefixWord, tailWord_1353272, baseEnd_1353272] using wordTrace_append hprefix tailTrace_1353272
  have hstable : (prefixWord ++ tailWord_1353272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353272).length < 2 ^ (prefixWord ++ tailWord_1353272).sum := by decide
  have hdescent : baseEnd_1353272 < baseStart_1353272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353334 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_1353334 : Nat := 118140960795 + 1353334 * 2 ^ 59
def prefixEnd_1353334 : Nat := 4983230072969 + 3 ^ 40 * 1353334 * 2
def baseEnd_1353334 : Nat := 308849256920850359200505

theorem tailTrace_1353334 : CollatzResearch.WordTrace tailWord_1353334 prefixEnd_1353334 308849256920850359200505 := by
  unfold tailWord_1353334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085009129944345243189191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32906764052739682594018037 3085009129944345243189191)
  ·
    refine ⟨4627513694916517864783787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085009129944345243189191 4627513694916517864783787)
    ·
      refine ⟨6941270542374776797175681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627513694916517864783787 6941270542374776797175681)
      ·
        refine ⟨5205952906781082597881761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6941270542374776797175681 5205952906781082597881761)
        ·
          refine ⟨3904464680085811948411321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5205952906781082597881761 3904464680085811948411321)
          ·
            refine ⟨2928348510064358961308491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3904464680085811948411321 2928348510064358961308491)
            ·
              refine ⟨4392522765096538441962737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928348510064358961308491 4392522765096538441962737)
              ·
                refine ⟨3294392073822403831472053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4392522765096538441962737 3294392073822403831472053)
                ·
                  refine ⟨308849256920850359200505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294392073822403831472053 308849256920850359200505)
                  ·
                    rfl

theorem cell21_1353334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_1353334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353334 prefixEnd_1353334 := by exact prefixLift 1353334
  have htrace : WordTrace (prefixWord ++ tailWord_1353334) baseStart_1353334 baseEnd_1353334 := by
    simpa [prefixWord, tailWord_1353334, baseEnd_1353334] using wordTrace_append hprefix tailTrace_1353334
  have hstable : (prefixWord ++ tailWord_1353334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353334).length < 2 ^ (prefixWord ++ tailWord_1353334).sum := by decide
  have hdescent : baseEnd_1353334 < baseStart_1353334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353452 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_1353452 : Nat := 118140960795 + 1353452 * 2 ^ 59
def prefixEnd_1353452 : Nat := 4983230072969 + 3 ^ 40 * 1353452 * 2
def baseEnd_1353452 : Nat := 308876186128508376233597

theorem tailTrace_1353452 : CollatzResearch.WordTrace tailWord_1353452 prefixEnd_1353452 308876186128508376233597 := by
  unfold tailWord_1353452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24682224946341015021911305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32909633261788020029215073 24682224946341015021911305)
  ·
    refine ⟨18511668709755761266433479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24682224946341015021911305 18511668709755761266433479)
    ·
      refine ⟨27767503064633641899650219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18511668709755761266433479 27767503064633641899650219)
      ·
        refine ⟨41651254596950462849475329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27767503064633641899650219 41651254596950462849475329)
        ·
          refine ⟨31238440947712847137106497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41651254596950462849475329 31238440947712847137106497)
          ·
            refine ⟨23428830710784635352829873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31238440947712847137106497 23428830710784635352829873)
            ·
              refine ⟨17571623033088476514622405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23428830710784635352829873 17571623033088476514622405)
              ·
                refine ⟨3294679318704089346491701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17571623033088476514622405 3294679318704089346491701)
                ·
                  refine ⟨308876186128508376233597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3294679318704089346491701 308876186128508376233597)
                  ·
                    rfl

theorem cell21_1353452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_1353452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353452 prefixEnd_1353452 := by exact prefixLift 1353452
  have htrace : WordTrace (prefixWord ++ tailWord_1353452) baseStart_1353452 baseEnd_1353452 := by
    simpa [prefixWord, tailWord_1353452, baseEnd_1353452] using wordTrace_append hprefix tailTrace_1353452
  have hstable : (prefixWord ++ tailWord_1353452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353452).length < 2 ^ (prefixWord ++ tailWord_1353452).sum := by decide
  have hdescent : baseEnd_1353452 < baseStart_1353452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353483 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 4]
def baseStart_1353483 : Nat := 118140960795 + 1353483 * 2 ^ 59
def prefixEnd_1353483 : Nat := 4983230072969 + 3 ^ 40 * 1353483 * 2
def baseEnd_1353483 : Nat := 308883260750859211216867

theorem tailTrace_1353483 : CollatzResearch.WordTrace tailWord_1353483 prefixEnd_1353483 308883260750859211216867 := by
  unfold tailWord_1353483
  simp only [CollatzResearch.WordTrace]
  refine ⟨49365580555569722338201103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32910387037046481558800735 49365580555569722338201103)
  ·
    refine ⟨74048370833354583507301655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49365580555569722338201103 74048370833354583507301655)
    ·
      refine ⟨111072556250031875260952483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74048370833354583507301655 111072556250031875260952483)
      ·
        refine ⟨166608834375047812891428725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111072556250031875260952483 166608834375047812891428725)
        ·
          refine ⟨15619578222660732458571443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 166608834375047812891428725 15619578222660732458571443)
          ·
            refine ⟨23429367333991098687857165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15619578222660732458571443 23429367333991098687857165)
            ·
              refine ⟨8786012750246662007946437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23429367333991098687857165 8786012750246662007946437)
              ·
                refine ⟨1647377390671249126489957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8786012750246662007946437 1647377390671249126489957)
                ·
                  refine ⟨308883260750859211216867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647377390671249126489957 308883260750859211216867)
                  ·
                    rfl

theorem cell21_1353483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 4].length) (baseStart_1353483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353483 prefixEnd_1353483 := by exact prefixLift 1353483
  have htrace : WordTrace (prefixWord ++ tailWord_1353483) baseStart_1353483 baseEnd_1353483 := by
    simpa [prefixWord, tailWord_1353483, baseEnd_1353483] using wordTrace_append hprefix tailTrace_1353483
  have hstable : (prefixWord ++ tailWord_1353483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353483).length < 2 ^ (prefixWord ++ tailWord_1353483).sum := by decide
  have hdescent : baseEnd_1353483 < baseStart_1353483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353545 : List Nat := [1, 2, 1, 1, 2, 4, 1, 6, 3]
def baseStart_1353545 : Nat := 118140960795 + 1353545 * 2 ^ 59
def prefixEnd_1353545 : Nat := 4983230072969 + 3 ^ 40 * 1353545 * 2
def baseEnd_1353545 : Nat := 308897409995560881183407

theorem tailTrace_1353545 : CollatzResearch.WordTrace tailWord_1353545 prefixEnd_1353545 308897409995560881183407 := by
  unfold tailWord_1353545
  simp only [CollatzResearch.WordTrace]
  refine ⟨49367841881345106926958089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32911894587563404617972059 49367841881345106926958089)
  ·
    refine ⟨37025881411008830195218567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49367841881345106926958089 37025881411008830195218567)
    ·
      refine ⟨55538822116513245292827851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37025881411008830195218567 55538822116513245292827851)
      ·
        refine ⟨83308233174769867939241777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55538822116513245292827851 83308233174769867939241777)
        ·
          refine ⟨62481174881077400954431333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83308233174769867939241777 62481174881077400954431333)
          ·
            refine ⟨11715220290202012678955875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62481174881077400954431333 11715220290202012678955875)
            ·
              refine ⟨17572830435303019018433813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11715220290202012678955875 17572830435303019018433813)
              ·
                refine ⟨823726426654829016489085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17572830435303019018433813 823726426654829016489085)
                ·
                  refine ⟨308897409995560881183407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823726426654829016489085 308897409995560881183407)
                  ·
                    rfl

theorem cell21_1353545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 6, 3].length) (baseStart_1353545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353545 prefixEnd_1353545 := by exact prefixLift 1353545
  have htrace : WordTrace (prefixWord ++ tailWord_1353545) baseStart_1353545 baseEnd_1353545 := by
    simpa [prefixWord, tailWord_1353545, baseEnd_1353545] using wordTrace_append hprefix tailTrace_1353545
  have hstable : (prefixWord ++ tailWord_1353545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353545).length < 2 ^ (prefixWord ++ tailWord_1353545).sum := by decide
  have hdescent : baseEnd_1353545 < baseStart_1353545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353610 : List Nat := [3, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_1353610 : Nat := 118140960795 + 1353610 * 2 ^ 59
def prefixEnd_1353610 : Nat := 4983230072969 + 3 ^ 40 * 1353610 * 2
def baseEnd_1353610 : Nat := 308912243881135212599941

theorem tailTrace_1353610 : CollatzResearch.WordTrace tailWord_1353610 prefixEnd_1353610 308912243881135212599941 := by
  unfold tailWord_1353610
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342553156527405757018571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32913475084073082018716189 12342553156527405757018571)
  ·
    refine ⟨18513829734791108635527857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12342553156527405757018571 18513829734791108635527857)
    ·
      refine ⟨13885372301093331476645893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18513829734791108635527857 13885372301093331476645893)
      ·
        refine ⟨2603507306454999651871105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13885372301093331476645893 2603507306454999651871105)
        ·
          refine ⟨1952630479841249738903329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2603507306454999651871105 1952630479841249738903329)
          ·
            refine ⟨1464472859880937304177497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1952630479841249738903329 1464472859880937304177497)
            ·
              refine ⟨1098354644910702978133123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464472859880937304177497 1098354644910702978133123)
              ·
                refine ⟨1647531967366054467199685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098354644910702978133123 1647531967366054467199685)
                ·
                  refine ⟨308912243881135212599941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647531967366054467199685 308912243881135212599941)
                  ·
                    rfl

theorem cell21_1353610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_1353610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353610 prefixEnd_1353610 := by exact prefixLift 1353610
  have htrace : WordTrace (prefixWord ++ tailWord_1353610) baseStart_1353610 baseEnd_1353610 := by
    simpa [prefixWord, tailWord_1353610, baseEnd_1353610] using wordTrace_append hprefix tailTrace_1353610
  have hstable : (prefixWord ++ tailWord_1353610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353610).length < 2 ^ (prefixWord ++ tailWord_1353610).sum := by decide
  have hdescent : baseEnd_1353610 < baseStart_1353610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353649 : List Nat := [1, 2, 2, 4, 2, 10]
def baseStart_1353649 : Nat := 118140960795 + 1353649 * 2 ^ 59
def prefixEnd_1353649 : Nat := 4983230072969 + 3 ^ 40 * 1353649 * 2
def baseEnd_1353649 : Nat := 11441523859721474498143

theorem tailTrace_1353649 : CollatzResearch.WordTrace tailWord_1353649 prefixEnd_1353649 11441523859721474498143 := by
  unfold tailWord_1353649
  simp only [CollatzResearch.WordTrace]
  refine ⟨49371635072968332688744001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32914423381978888459162667 49371635072968332688744001)
  ·
    refine ⟨37028726304726249516558001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49371635072968332688744001 37028726304726249516558001)
    ·
      refine ⟨27771544728544687137418501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37028726304726249516558001 27771544728544687137418501)
      ·
        refine ⟨5207164636602128838265969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27771544728544687137418501 5207164636602128838265969)
        ·
          refine ⟨3905373477451596628699477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5207164636602128838265969 3905373477451596628699477)
          ·
            refine ⟨11441523859721474498143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3905373477451596628699477 11441523859721474498143)
            ·
              rfl

theorem cell21_1353649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 10].length) (baseStart_1353649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353649 prefixEnd_1353649 := by exact prefixLift 1353649
  have htrace : WordTrace (prefixWord ++ tailWord_1353649) baseStart_1353649 baseEnd_1353649 := by
    simpa [prefixWord, tailWord_1353649, baseEnd_1353649] using wordTrace_append hprefix tailTrace_1353649
  have hstable : (prefixWord ++ tailWord_1353649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353649).length < 2 ^ (prefixWord ++ tailWord_1353649).sum := by decide
  have hdescent : baseEnd_1353649 < baseStart_1353649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353697 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 3]
def baseStart_1353697 : Nat := 118140960795 + 1353697 * 2 ^ 59
def prefixEnd_1353697 : Nat := 4983230072969 + 3 ^ 40 * 1353697 * 2
def baseEnd_1353697 : Nat := 308932098466442394649763

theorem tailTrace_1353697 : CollatzResearch.WordTrace tailWord_1353697 prefixEnd_1353697 308932098466442394649763 := by
  unfold tailWord_1353697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49373385776794436886491345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32915590517862957924327563 49373385776794436886491345)
  ·
    refine ⟨37030039332595827664868509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49373385776794436886491345 37030039332595827664868509)
    ·
      refine ⟨13886264749723435374325691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37030039332595827664868509 13886264749723435374325691)
      ·
        refine ⟨20829397124585153061488537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13886264749723435374325691 20829397124585153061488537)
        ·
          refine ⟨15622047843438864796116403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20829397124585153061488537 15622047843438864796116403)
          ·
            refine ⟨23433071765158297194174605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15622047843438864796116403 23433071765158297194174605)
            ·
              refine ⟨8787401911934361447815477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23433071765158297194174605 8787401911934361447815477)
              ·
                refine ⟨823818929243846385732701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8787401911934361447815477 823818929243846385732701)
                ·
                  refine ⟨308932098466442394649763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823818929243846385732701 308932098466442394649763)
                  ·
                    rfl

theorem cell21_1353697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_1353697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353697 prefixEnd_1353697 := by exact prefixLift 1353697
  have htrace : WordTrace (prefixWord ++ tailWord_1353697) baseStart_1353697 baseEnd_1353697 := by
    simpa [prefixWord, tailWord_1353697, baseEnd_1353697] using wordTrace_append hprefix tailTrace_1353697
  have hstable : (prefixWord ++ tailWord_1353697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353697).length < 2 ^ (prefixWord ++ tailWord_1353697).sum := by decide
  have hdescent : baseEnd_1353697 < baseStart_1353697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353821 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1353821 : Nat := 118140960795 + 1353821 * 2 ^ 59
def prefixEnd_1353821 : Nat := 4983230072969 + 3 ^ 40 * 1353821 * 2
def baseEnd_1353821 : Nat := 308960396955845734582843

theorem tailTrace_1353821 : CollatzResearch.WordTrace tailWord_1353821 prefixEnd_1353821 308960396955845734582843 := by
  unfold tailWord_1353821
  simp only [CollatzResearch.WordTrace]
  refine ⟨49377908428345206064005317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32918605618896804042670211 49377908428345206064005317)
  ·
    refine ⟨9258357830314726137000997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49377908428345206064005317 9258357830314726137000997)
    ·
      refine ⟨1735942093184011150687687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9258357830314726137000997 1735942093184011150687687)
      ·
        refine ⟨2603913139776016726031531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735942093184011150687687 2603913139776016726031531)
        ·
          refine ⟨3905869709664025089047297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603913139776016726031531 3905869709664025089047297)
          ·
            refine ⟨2929402282248018816785473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3905869709664025089047297 2929402282248018816785473)
            ·
              refine ⟨2197051711686014112589105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929402282248018816785473 2197051711686014112589105)
              ·
                refine ⟨1647788783764510584441829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197051711686014112589105 1647788783764510584441829)
                ·
                  refine ⟨308960396955845734582843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1647788783764510584441829 308960396955845734582843)
                  ·
                    rfl

theorem cell21_1353821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1353821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353821 prefixEnd_1353821 := by exact prefixLift 1353821
  have htrace : WordTrace (prefixWord ++ tailWord_1353821) baseStart_1353821 baseEnd_1353821 := by
    simpa [prefixWord, tailWord_1353821, baseEnd_1353821] using wordTrace_append hprefix tailTrace_1353821
  have hstable : (prefixWord ++ tailWord_1353821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353821).length < 2 ^ (prefixWord ++ tailWord_1353821).sum := by decide
  have hdescent : baseEnd_1353821 < baseStart_1353821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353866 : List Nat := [3, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_1353866 : Nat := 118140960795 + 1353866 * 2 ^ 59
def prefixEnd_1353866 : Nat := 4983230072969 + 3 ^ 40 * 1353866 * 2
def baseEnd_1353866 : Nat := 308970666568935656332751

theorem tailTrace_1353866 : CollatzResearch.WordTrace tailWord_1353866 prefixEnd_1353866 308970666568935656332751 := by
  unfold tailWord_1353866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344887428295544687348363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32919699808788119166262301 12344887428295544687348363)
  ·
    refine ⟨18517331142443317031022545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344887428295544687348363 18517331142443317031022545)
    ·
      refine ⟨13887998356832487773266909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18517331142443317031022545 13887998356832487773266909)
      ·
        refine ⟨5207999383812182914975091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13887998356832487773266909 5207999383812182914975091)
        ·
          refine ⟨7811999075718274372462637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5207999383812182914975091 7811999075718274372462637)
          ·
            refine ⟨2929499653394352889673489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7811999075718274372462637 2929499653394352889673489)
            ·
              refine ⟨2197124740045764667255117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929499653394352889673489 2197124740045764667255117)
              ·
                refine ⟨823921777517161750220669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197124740045764667255117 823921777517161750220669)
                ·
                  refine ⟨308970666568935656332751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823921777517161750220669 308970666568935656332751)
                  ·
                    rfl

theorem cell21_1353866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_1353866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353866 prefixEnd_1353866 := by exact prefixLift 1353866
  have htrace : WordTrace (prefixWord ++ tailWord_1353866) baseStart_1353866 baseEnd_1353866 := by
    simpa [prefixWord, tailWord_1353866, baseEnd_1353866] using wordTrace_append hprefix tailTrace_1353866
  have hstable : (prefixWord ++ tailWord_1353866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353866).length < 2 ^ (prefixWord ++ tailWord_1353866).sum := by decide
  have hdescent : baseEnd_1353866 < baseStart_1353866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353925 : List Nat := [1, 3, 1, 1, 1, 1, 7, 3, 3]
def baseStart_1353925 : Nat := 118140960795 + 1353925 * 2 ^ 59
def prefixEnd_1353925 : Nat := 4983230072969 + 3 ^ 40 * 1353925 * 2
def baseEnd_1353925 : Nat := 308984131172764664849297

theorem tailTrace_1353925 : CollatzResearch.WordTrace tailWord_1353925 prefixEnd_1353925 308984131172764664849297 := by
  unfold tailWord_1353925
  simp only [CollatzResearch.WordTrace]
  refine ⟨49381701619968431825791229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32921134413312287883860819 49381701619968431825791229)
  ·
    refine ⟨18518138107488161934671711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49381701619968431825791229 18518138107488161934671711)
    ·
      refine ⟨27777207161232242902007567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18518138107488161934671711 27777207161232242902007567)
      ·
        refine ⟨41665810741848364353011351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27777207161232242902007567 41665810741848364353011351)
        ·
          refine ⟨62498716112772546529517027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41665810741848364353011351 62498716112772546529517027)
          ·
            refine ⟨93748074169158819794275541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62498716112772546529517027 93748074169158819794275541)
            ·
              refine ⟨2197220488339659838928333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93748074169158819794275541 2197220488339659838928333)
              ·
                refine ⟨823957683127372439598125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197220488339659838928333 823957683127372439598125)
                ·
                  refine ⟨308984131172764664849297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 823957683127372439598125 308984131172764664849297)
                  ·
                    rfl

theorem cell21_1353925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 3, 3].length) (baseStart_1353925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353925 prefixEnd_1353925 := by exact prefixLift 1353925
  have htrace : WordTrace (prefixWord ++ tailWord_1353925) baseStart_1353925 baseEnd_1353925 := by
    simpa [prefixWord, tailWord_1353925, baseEnd_1353925] using wordTrace_append hprefix tailTrace_1353925
  have hstable : (prefixWord ++ tailWord_1353925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353925).length < 2 ^ (prefixWord ++ tailWord_1353925).sum := by decide
  have hdescent : baseEnd_1353925 < baseStart_1353925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353942 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1353942 : Nat := 118140960795 + 1353942 * 2 ^ 59
def prefixEnd_1353942 : Nat := 4983230072969 + 3 ^ 40 * 1353942 * 2
def baseEnd_1353942 : Nat := 308988010804376413065929

theorem tailTrace_1353942 : CollatzResearch.WordTrace tailWord_1353942 prefixEnd_1353942 308988010804376413065929 := by
  unfold tailWord_1353942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086395103806677733072505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32921547773937895819440053 3086395103806677733072505)
  ·
    refine ⟨2314796327855008299804379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3086395103806677733072505 2314796327855008299804379)
    ·
      refine ⟨3472194491782512449706569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314796327855008299804379 3472194491782512449706569)
      ·
        refine ⟨2604145868836884337279927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3472194491782512449706569 2604145868836884337279927)
        ·
          refine ⟨3906218803255326505919891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604145868836884337279927 3906218803255326505919891)
          ·
            refine ⟨5859328204882989758879837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906218803255326505919891 5859328204882989758879837)
            ·
              refine ⟨2197248076831121159579939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5859328204882989758879837 2197248076831121159579939)
              ·
                refine ⟨3295872115246681739369909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197248076831121159579939 3295872115246681739369909)
                ·
                  refine ⟨308988010804376413065929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3295872115246681739369909 308988010804376413065929)
                  ·
                    rfl

theorem cell21_1353942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1353942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353942 prefixEnd_1353942 := by exact prefixLift 1353942
  have htrace : WordTrace (prefixWord ++ tailWord_1353942) baseStart_1353942 baseEnd_1353942 := by
    simpa [prefixWord, tailWord_1353942, baseEnd_1353942] using wordTrace_append hprefix tailTrace_1353942
  have hstable : (prefixWord ++ tailWord_1353942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353942).length < 2 ^ (prefixWord ++ tailWord_1353942).sum := by decide
  have hdescent : baseEnd_1353942 < baseStart_1353942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353953 : List Nat := [1, 2, 3, 1, 3, 1, 4, 6]
def baseStart_1353953 : Nat := 118140960795 + 1353953 * 2 ^ 59
def prefixEnd_1353953 : Nat := 4983230072969 + 3 ^ 40 * 1353953 * 2
def baseEnd_1353953 : Nat := 102996840384747612794191

theorem tailTrace_1353953 : CollatzResearch.WordTrace tailWord_1353953 prefixEnd_1353953 102996840384747612794191 := by
  unfold tailWord_1353953
  simp only [CollatzResearch.WordTrace]
  refine ⟨49382722863866992607810513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32921815242577995071873675 49382722863866992607810513)
  ·
    refine ⟨37037042147900244455857885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49382722863866992607810513 37037042147900244455857885)
    ·
      refine ⟨13888890805462591670946707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37037042147900244455857885 13888890805462591670946707)
      ·
        refine ⟨20833336208193887506420061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13888890805462591670946707 20833336208193887506420061)
        ·
          refine ⟨7812501078072707814907523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20833336208193887506420061 7812501078072707814907523)
          ·
            refine ⟨11718751617109061722361285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7812501078072707814907523 11718751617109061722361285)
            ·
              refine ⟨2197265928207949072942741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11718751617109061722361285 2197265928207949072942741)
              ·
                refine ⟨102996840384747612794191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2197265928207949072942741 102996840384747612794191)
                ·
                  rfl

theorem cell21_1353953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 6].length) (baseStart_1353953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1353953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1353953 prefixEnd_1353953 := by exact prefixLift 1353953
  have htrace : WordTrace (prefixWord ++ tailWord_1353953) baseStart_1353953 baseEnd_1353953 := by
    simpa [prefixWord, tailWord_1353953, baseEnd_1353953] using wordTrace_append hprefix tailTrace_1353953
  have hstable : (prefixWord ++ tailWord_1353953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353953).length < 2 ^ (prefixWord ++ tailWord_1353953).sum := by decide
  have hdescent : baseEnd_1353953 < baseStart_1353953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354001 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 3]
def baseStart_1354001 : Nat := 118140960795 + 1354001 * 2 ^ 59
def prefixEnd_1354001 : Nat := 4983230072969 + 3 ^ 40 * 1354001 * 2
def baseEnd_1354001 : Nat := 309001475408205421582475

theorem tailTrace_1354001 : CollatzResearch.WordTrace tailWord_1354001 prefixEnd_1354001 309001475408205421582475 := by
  unfold tailWord_1354001
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384473567693096805557857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32922982378462064537038571 49384473567693096805557857)
  ·
    refine ⟨37038355175769822604168393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49384473567693096805557857 37038355175769822604168393)
    ·
      refine ⟨27778766381827366953126295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37038355175769822604168393 27778766381827366953126295)
      ·
        refine ⟨41668149572741050429689443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27778766381827366953126295 41668149572741050429689443)
        ·
          refine ⟨62502224359111575644534165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41668149572741050429689443 62502224359111575644534165)
          ·
            refine ⟨2929791766833355108337539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62502224359111575644534165 2929791766833355108337539)
            ·
              refine ⟨4394687650250032662506309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929791766833355108337539 4394687650250032662506309)
              ·
                refine ⟨824003934421881124219933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4394687650250032662506309 824003934421881124219933)
                ·
                  refine ⟨309001475408205421582475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824003934421881124219933 309001475408205421582475)
                  ·
                    rfl

theorem cell21_1354001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 3].length) (baseStart_1354001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354001 prefixEnd_1354001 := by exact prefixLift 1354001
  have htrace : WordTrace (prefixWord ++ tailWord_1354001) baseStart_1354001 baseEnd_1354001 := by
    simpa [prefixWord, tailWord_1354001, baseEnd_1354001] using wordTrace_append hprefix tailTrace_1354001
  have hstable : (prefixWord ++ tailWord_1354001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354001).length < 2 ^ (prefixWord ++ tailWord_1354001).sum := by decide
  have hdescent : baseEnd_1354001 < baseStart_1354001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354015 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 4]
def baseStart_1354015 : Nat := 118140960795 + 1354015 * 2 ^ 59
def prefixEnd_1354015 : Nat := 4983230072969 + 3 ^ 40 * 1354015 * 2
def baseEnd_1354015 : Nat := 309004670398944508349113

theorem tailTrace_1354015 : CollatzResearch.WordTrace tailWord_1354015 prefixEnd_1354015 309004670398944508349113 := by
  unfold tailWord_1354015
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384984189642377196567499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32923322793094918131044999 49384984189642377196567499)
  ·
    refine ⟨74077476284463565794851249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49384984189642377196567499 74077476284463565794851249)
    ·
      refine ⟨55558107213347674346138437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74077476284463565794851249 55558107213347674346138437)
      ·
        refine ⟨10417145102502688939900957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55558107213347674346138437 10417145102502688939900957)
        ·
          refine ⟨3906429413438508352462859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10417145102502688939900957 3906429413438508352462859)
          ·
            refine ⟨5859644120157762528694289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906429413438508352462859 5859644120157762528694289)
            ·
              refine ⟨4394733090118321896520717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5859644120157762528694289 4394733090118321896520717)
              ·
                refine ⟨1648024908794370711195269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4394733090118321896520717 1648024908794370711195269)
                ·
                  refine ⟨309004670398944508349113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648024908794370711195269 309004670398944508349113)
                  ·
                    rfl

theorem cell21_1354015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 4].length) (baseStart_1354015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354015 prefixEnd_1354015 := by exact prefixLift 1354015
  have htrace : WordTrace (prefixWord ++ tailWord_1354015) baseStart_1354015 baseEnd_1354015 := by
    simpa [prefixWord, tailWord_1354015, baseEnd_1354015] using wordTrace_append hprefix tailTrace_1354015
  have hstable : (prefixWord ++ tailWord_1354015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354015).length < 2 ^ (prefixWord ++ tailWord_1354015).sum := by decide
  have hdescent : baseEnd_1354015 < baseStart_1354015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354049 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 4]
def baseStart_1354049 : Nat := 118140960795 + 1354049 * 2 ^ 59
def prefixEnd_1354049 : Nat := 4983230072969 + 3 ^ 40 * 1354049 * 2
def baseEnd_1354049 : Nat := 309012429662168004782377

theorem tailTrace_1354049 : CollatzResearch.WordTrace tailWord_1354049 prefixEnd_1354049 309012429662168004782377 := by
  unfold tailWord_1354049
  simp only [CollatzResearch.WordTrace]
  refine ⟨49386224271519201003305201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32924149514346134002203467 49386224271519201003305201)
  ·
    refine ⟨37039668203639400752478901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49386224271519201003305201 37039668203639400752478901)
    ·
      refine ⟨3472468894091193820544897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37039668203639400752478901 3472468894091193820544897)
      ·
        refine ⟨2604351670568395365408673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3472468894091193820544897 2604351670568395365408673)
        ·
          refine ⟨1953263752926296524056505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604351670568395365408673 1953263752926296524056505)
          ·
            refine ⟨1464947814694722393042379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953263752926296524056505 1464947814694722393042379)
            ·
              refine ⟨2197421722042083589563569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464947814694722393042379 2197421722042083589563569)
              ·
                refine ⟨1648066291531562692172677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197421722042083589563569 1648066291531562692172677)
                ·
                  refine ⟨309012429662168004782377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648066291531562692172677 309012429662168004782377)
                  ·
                    rfl

theorem cell21_1354049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_1354049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354049 prefixEnd_1354049 := by exact prefixLift 1354049
  have htrace : WordTrace (prefixWord ++ tailWord_1354049) baseStart_1354049 baseEnd_1354049 := by
    simpa [prefixWord, tailWord_1354049, baseEnd_1354049] using wordTrace_append hprefix tailTrace_1354049
  have hstable : (prefixWord ++ tailWord_1354049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354049).length < 2 ^ (prefixWord ++ tailWord_1354049).sum := by decide
  have hdescent : baseEnd_1354049 < baseStart_1354049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354060 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1354060 : Nat := 118140960795 + 1354060 * 2 ^ 59
def prefixEnd_1354060 : Nat := 4983230072969 + 3 ^ 40 * 1354060 * 2
def baseEnd_1354060 : Nat := 309014940012034430099021

theorem tailTrace_1354060 : CollatzResearch.WordTrace tailWord_1354060 prefixEnd_1354060 309014940012034430099021 := by
  unfold tailWord_1354060
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693312737239674940977817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32924416982986233254637089 24693312737239674940977817)
  ·
    refine ⟨18519984552929756205733363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24693312737239674940977817 18519984552929756205733363)
    ·
      refine ⟨27779976829394634308600045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18519984552929756205733363 27779976829394634308600045)
      ·
        refine ⟨10417491311022987865725017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27779976829394634308600045 10417491311022987865725017)
        ·
          refine ⟨7813118483267240899293763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10417491311022987865725017 7813118483267240899293763)
          ·
            refine ⟨11719677724900861348940645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813118483267240899293763 11719677724900861348940645)
            ·
              refine ⟨2197439573418911502926371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11719677724900861348940645 2197439573418911502926371)
              ·
                refine ⟨3296159360128367254389557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197439573418911502926371 3296159360128367254389557)
                ·
                  refine ⟨309014940012034430099021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3296159360128367254389557 309014940012034430099021)
                  ·
                    rfl

theorem cell21_1354060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1354060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354060 prefixEnd_1354060 := by exact prefixLift 1354060
  have htrace : WordTrace (prefixWord ++ tailWord_1354060) baseStart_1354060 baseEnd_1354060 := by
    simpa [prefixWord, tailWord_1354060, baseEnd_1354060] using wordTrace_append hprefix tailTrace_1354060
  have hstable : (prefixWord ++ tailWord_1354060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354060).length < 2 ^ (prefixWord ++ tailWord_1354060).sum := by decide
  have hdescent : baseEnd_1354060 < baseStart_1354060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354167 : List Nat := [1, 1, 3, 1, 3, 4, 2, 2, 4]
def baseStart_1354167 : Nat := 118140960795 + 1354167 * 2 ^ 59
def prefixEnd_1354167 : Nat := 4983230072969 + 3 ^ 40 * 1354167 * 2
def baseEnd_1354167 : Nat := 309039358869826021815469

theorem tailTrace_1354167 : CollatzResearch.WordTrace tailWord_1354167 prefixEnd_1354167 309039358869826021815469 := by
  unfold tailWord_1354167
  simp only [CollatzResearch.WordTrace]
  refine ⟨49390528085091707156100755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32927018723394471437400503 49390528085091707156100755)
  ·
    refine ⟨74085792127637560734151133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49390528085091707156100755 74085792127637560734151133)
    ·
      refine ⟨27782172047864085275306675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74085792127637560734151133 27782172047864085275306675)
      ·
        refine ⟨41673258071796127912960013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27782172047864085275306675 41673258071796127912960013)
        ·
          refine ⟨15627471776923547967360005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41673258071796127912960013 15627471776923547967360005)
          ·
            refine ⟨2930150958173165243880001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15627471776923547967360005 2930150958173165243880001)
            ·
              refine ⟨2197613218629873932910001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2930150958173165243880001 2197613218629873932910001)
              ·
                refine ⟨1648209913972405449682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197613218629873932910001 1648209913972405449682501)
                ·
                  refine ⟨309039358869826021815469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648209913972405449682501 309039358869826021815469)
                  ·
                    rfl

theorem cell21_1354167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 4].length) (baseStart_1354167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354167 prefixEnd_1354167 := by exact prefixLift 1354167
  have htrace : WordTrace (prefixWord ++ tailWord_1354167) baseStart_1354167 baseEnd_1354167 := by
    simpa [prefixWord, tailWord_1354167, baseEnd_1354167] using wordTrace_append hprefix tailTrace_1354167
  have hstable : (prefixWord ++ tailWord_1354167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354167).length < 2 ^ (prefixWord ++ tailWord_1354167).sum := by decide
  have hdescent : baseEnd_1354167 < baseStart_1354167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354243 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 4]
def baseStart_1354243 : Nat := 118140960795 + 1354243 * 2 ^ 59
def prefixEnd_1354243 : Nat := 4983230072969 + 3 ^ 40 * 1354243 * 2
def baseEnd_1354243 : Nat := 309056703105266778548647

theorem tailTrace_1354243 : CollatzResearch.WordTrace tailWord_1354243 prefixEnd_1354243 309056703105266778548647 := by
  unfold tailWord_1354243
  simp only [CollatzResearch.WordTrace]
  refine ⟨49393300032816372135867383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32928866688544248090578255 49393300032816372135867383)
  ·
    refine ⟨74089950049224558203801075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49393300032816372135867383 74089950049224558203801075)
    ·
      refine ⟨111134925073836837305701613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74089950049224558203801075 111134925073836837305701613)
      ·
        refine ⟨41675596902688813989638105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111134925073836837305701613 41675596902688813989638105)
        ·
          refine ⟨31256697677016610492228579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41675596902688813989638105 31256697677016610492228579)
          ·
            refine ⟨46885046515524915738342869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31256697677016610492228579 46885046515524915738342869)
            ·
              refine ⟨1098868277707615212617411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46885046515524915738342869 1098868277707615212617411)
              ·
                refine ⟨1648302416561422818926117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098868277707615212617411 1648302416561422818926117)
                ·
                  refine ⟨309056703105266778548647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648302416561422818926117 309056703105266778548647)
                  ·
                    rfl

theorem cell21_1354243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 4].length) (baseStart_1354243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354243 prefixEnd_1354243 := by exact prefixLift 1354243
  have htrace : WordTrace (prefixWord ++ tailWord_1354243) baseStart_1354243 baseEnd_1354243 := by
    simpa [prefixWord, tailWord_1354243, baseEnd_1354243] using wordTrace_append hprefix tailTrace_1354243
  have hstable : (prefixWord ++ tailWord_1354243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354243).length < 2 ^ (prefixWord ++ tailWord_1354243).sum := by decide
  have hdescent : baseEnd_1354243 < baseStart_1354243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354263 : List Nat := [1, 1, 3, 6, 1, 2, 1, 3, 3]
def baseStart_1354263 : Nat := 118140960795 + 1354263 * 2 ^ 59
def prefixEnd_1354263 : Nat := 4983230072969 + 3 ^ 40 * 1354263 * 2
def baseEnd_1354263 : Nat := 309061267377751188215273

theorem tailTrace_1354263 : CollatzResearch.WordTrace tailWord_1354263 prefixEnd_1354263 309061267377751188215273 := by
  unfold tailWord_1354263
  simp only [CollatzResearch.WordTrace]
  refine ⟨49394029492743915551595443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32929352995162610367730295 49394029492743915551595443)
  ·
    refine ⟨74091044239115873327393165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49394029492743915551595443 74091044239115873327393165)
    ·
      refine ⟨27784141589668452497772437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74091044239115873327393165 27784141589668452497772437)
      ·
        refine ⟨1302381637015708710833083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27784141589668452497772437 1302381637015708710833083)
        ·
          refine ⟨1953572455523563066249625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302381637015708710833083 1953572455523563066249625)
          ·
            refine ⟨1465179341642672299687219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953572455523563066249625 1465179341642672299687219)
            ·
              refine ⟨2197769012464008449530829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465179341642672299687219 2197769012464008449530829)
              ·
                refine ⟨824163379674003168574061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2197769012464008449530829 824163379674003168574061)
                ·
                  refine ⟨309061267377751188215273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824163379674003168574061 309061267377751188215273)
                  ·
                    rfl

theorem cell21_1354263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 3].length) (baseStart_1354263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354263 prefixEnd_1354263 := by exact prefixLift 1354263
  have htrace : WordTrace (prefixWord ++ tailWord_1354263) baseStart_1354263 baseEnd_1354263 := by
    simpa [prefixWord, tailWord_1354263, baseEnd_1354263] using wordTrace_append hprefix tailTrace_1354263
  have hstable : (prefixWord ++ tailWord_1354263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354263).length < 2 ^ (prefixWord ++ tailWord_1354263).sum := by decide
  have hdescent : baseEnd_1354263 < baseStart_1354263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354288 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_1354288 : Nat := 118140960795 + 1354288 * 2 ^ 59
def prefixEnd_1354288 : Nat := 4983230072969 + 3 ^ 40 * 1354288 * 2
def baseEnd_1354288 : Nat := 309066972718356700298555

theorem tailTrace_1354288 : CollatzResearch.WordTrace tailWord_1354288 prefixEnd_1354288 309066972718356700298555 := by
  unfold tailWord_1354288
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697470658826672410627759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32929960878435563214170345 24697470658826672410627759)
  ·
    refine ⟨37046205988240008615941639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24697470658826672410627759 37046205988240008615941639)
    ·
      refine ⟨55569308982360012923912459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37046205988240008615941639 55569308982360012923912459)
      ·
        refine ⟨83353963473540019385868689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55569308982360012923912459 83353963473540019385868689)
        ·
          refine ⟨62515472605155014539401517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83353963473540019385868689 62515472605155014539401517)
          ·
            refine ⟨23443302226933130452275569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62515472605155014539401517 23443302226933130452275569)
            ·
              refine ⟨17582476670199847839206677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23443302226933130452275569 17582476670199847839206677)
              ·
                refine ⟨824178593915617867462813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17582476670199847839206677 824178593915617867462813)
                ·
                  refine ⟨309066972718356700298555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824178593915617867462813 309066972718356700298555)
                  ·
                    rfl

theorem cell21_1354288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_1354288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354288 prefixEnd_1354288 := by exact prefixLift 1354288
  have htrace : WordTrace (prefixWord ++ tailWord_1354288) baseStart_1354288 baseEnd_1354288 := by
    simpa [prefixWord, tailWord_1354288, baseEnd_1354288] using wordTrace_append hprefix tailTrace_1354288
  have hstable : (prefixWord ++ tailWord_1354288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354288).length < 2 ^ (prefixWord ++ tailWord_1354288).sum := by decide
  have hdescent : baseEnd_1354288 < baseStart_1354288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354316 : List Nat := [2, 2, 1, 3, 1, 2, 1, 9]
def baseStart_1354316 : Nat := 118140960795 + 1354316 * 2 ^ 59
def prefixEnd_1354316 : Nat := 4983230072969 + 3 ^ 40 * 1354316 * 2
def baseEnd_1354316 : Nat := 103024454233278291277277

theorem tailTrace_1354316 : CollatzResearch.WordTrace tailWord_1354316 prefixEnd_1354316 103024454233278291277277 := by
  unfold tailWord_1354316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697981280775952801637401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32930641707701270402183201 24697981280775952801637401)
  ·
    refine ⟨18523485960581964601228051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24697981280775952801637401 18523485960581964601228051)
    ·
      refine ⟨27785228940872946901842077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18523485960581964601228051 27785228940872946901842077)
      ·
        refine ⟨10419460852827355088190779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27785228940872946901842077 10419460852827355088190779)
        ·
          refine ⟨15629191279241032632286169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10419460852827355088190779 15629191279241032632286169)
          ·
            refine ⟨11721893459430774474214627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15629191279241032632286169 11721893459430774474214627)
            ·
              refine ⟨17582840189146161711321941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11721893459430774474214627 17582840189146161711321941)
              ·
                refine ⟨103024454233278291277277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17582840189146161711321941 103024454233278291277277)
                ·
                  rfl

theorem cell21_1354316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_1354316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354316 prefixEnd_1354316 := by exact prefixLift 1354316
  have htrace : WordTrace (prefixWord ++ tailWord_1354316) baseStart_1354316 baseEnd_1354316 := by
    simpa [prefixWord, tailWord_1354316, baseEnd_1354316] using wordTrace_append hprefix tailTrace_1354316
  have hstable : (prefixWord ++ tailWord_1354316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354316).length < 2 ^ (prefixWord ++ tailWord_1354316).sum := by decide
  have hdescent : baseEnd_1354316 < baseStart_1354316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354350 : List Nat := [4, 1, 2, 2, 2, 3, 1, 6]
def baseStart_1354350 : Nat := 118140960795 + 1354350 * 2 ^ 59
def prefixEnd_1354350 : Nat := 4983230072969 + 3 ^ 40 * 1354350 * 2
def baseEnd_1354350 : Nat := 103027040654352790088365

theorem tailTrace_1354350 : CollatzResearch.WordTrace tailWord_1354350 prefixEnd_1354350 103027040654352790088365 := by
  unfold tailWord_1354350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174650330428591176251563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32931468428952486273341669 6174650330428591176251563)
  ·
    refine ⟨9261975495642886764377345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174650330428591176251563 9261975495642886764377345)
    ·
      refine ⟨6946481621732165073283009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9261975495642886764377345 6946481621732165073283009)
      ·
        refine ⟨5209861216299123804962257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6946481621732165073283009 5209861216299123804962257)
        ·
          refine ⟨3907395912224342853721693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5209861216299123804962257 3907395912224342853721693)
          ·
            refine ⟨1465273467084128570145635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3907395912224342853721693 1465273467084128570145635)
            ·
              refine ⟨2197910200626192855218453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465273467084128570145635 2197910200626192855218453)
              ·
                refine ⟨103027040654352790088365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2197910200626192855218453 103027040654352790088365)
                ·
                  rfl

theorem cell21_1354350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_1354350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354350 prefixEnd_1354350 := by exact prefixLift 1354350
  have htrace : WordTrace (prefixWord ++ tailWord_1354350) baseStart_1354350 baseEnd_1354350 := by
    simpa [prefixWord, tailWord_1354350, baseEnd_1354350] using wordTrace_append hprefix tailTrace_1354350
  have hstable : (prefixWord ++ tailWord_1354350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354350).length < 2 ^ (prefixWord ++ tailWord_1354350).sum := by decide
  have hdescent : baseEnd_1354350 < baseStart_1354350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354392 : List Nat := [2, 1, 2, 4, 1, 1, 10]
def baseStart_1354392 : Nat := 118140960795 + 1354392 * 2 ^ 59
def prefixEnd_1354392 : Nat := 4983230072969 + 3 ^ 40 * 1354392 * 2
def baseEnd_1354392 : Nat := 34343411881697292285001

theorem tailTrace_1354392 : CollatzResearch.WordTrace tailWord_1354392 prefixEnd_1354392 34343411881697292285001 := by
  unfold tailWord_1354392
  simp only [CollatzResearch.WordTrace]
  refine ⟨24699367254638285291520715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32932489672851047055360953 24699367254638285291520715)
  ·
    refine ⟨37049050881957427937281073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24699367254638285291520715 37049050881957427937281073)
    ·
      refine ⟨27786788161468070952960805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37049050881957427937281073 27786788161468070952960805)
      ·
        refine ⟨5210022780275263303680151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27786788161468070952960805 5210022780275263303680151)
        ·
          refine ⟨7815034170412894955520227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5210022780275263303680151 7815034170412894955520227)
          ·
            refine ⟨11722551255619342433280341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7815034170412894955520227 11722551255619342433280341)
            ·
              refine ⟨34343411881697292285001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11722551255619342433280341 34343411881697292285001)
              ·
                rfl

theorem cell21_1354392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 10].length) (baseStart_1354392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354392 prefixEnd_1354392 := by exact prefixLift 1354392
  have htrace : WordTrace (prefixWord ++ tailWord_1354392) baseStart_1354392 baseEnd_1354392 := by
    simpa [prefixWord, tailWord_1354392, baseEnd_1354392] using wordTrace_append hprefix tailTrace_1354392
  have hstable : (prefixWord ++ tailWord_1354392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354392).length < 2 ^ (prefixWord ++ tailWord_1354392).sum := by decide
  have hdescent : baseEnd_1354392 < baseStart_1354392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354457 : List Nat := [1, 2, 1, 2, 3, 2, 5, 2, 3]
def baseStart_1354457 : Nat := 118140960795 + 1354457 * 2 ^ 59
def prefixEnd_1354457 : Nat := 4983230072969 + 3 ^ 40 * 1354457 * 2
def baseEnd_1354457 : Nat := 309105540820849961981543

theorem tailTrace_1354457 : CollatzResearch.WordTrace tailWord_1354457 prefixEnd_1354457 309105540820849961981543 := by
  unfold tailWord_1354457
  simp only [CollatzResearch.WordTrace]
  refine ⟨49401105254041086684157625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32934070169360724456105083 49401105254041086684157625)
  ·
    refine ⟨37050828940530815013118219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49401105254041086684157625 37050828940530815013118219)
    ·
      refine ⟨55576243410796222519677329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37050828940530815013118219 55576243410796222519677329)
      ·
        refine ⟨41682182558097166889757997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55576243410796222519677329 41682182558097166889757997)
        ·
          refine ⟨15630818459286437583659249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41682182558097166889757997 15630818459286437583659249)
          ·
            refine ⟨11723113844464828187744437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15630818459286437583659249 11723113844464828187744437)
            ·
              refine ⟨1099041922918577642601041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11723113844464828187744437 1099041922918577642601041)
              ·
                refine ⟨824281442188933231950781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099041922918577642601041 824281442188933231950781)
                ·
                  refine ⟨309105540820849961981543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824281442188933231950781 309105540820849961981543)
                  ·
                    rfl

theorem cell21_1354457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 2, 3].length) (baseStart_1354457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354457 prefixEnd_1354457 := by exact prefixLift 1354457
  have htrace : WordTrace (prefixWord ++ tailWord_1354457) baseStart_1354457 baseEnd_1354457 := by
    simpa [prefixWord, tailWord_1354457, baseEnd_1354457] using wordTrace_append hprefix tailTrace_1354457
  have hstable : (prefixWord ++ tailWord_1354457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354457).length < 2 ^ (prefixWord ++ tailWord_1354457).sum := by decide
  have hdescent : baseEnd_1354457 < baseStart_1354457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354468 : List Nat := [2, 3, 1, 1, 1, 4, 1, 8]
def baseStart_1354468 : Nat := 118140960795 + 1354468 * 2 ^ 59
def prefixEnd_1354468 : Nat := 4983230072969 + 3 ^ 40 * 1354468 * 2
def baseEnd_1354468 : Nat := 103036017056905462432729

theorem tailTrace_1354468 : CollatzResearch.WordTrace tailWord_1354468 prefixEnd_1354468 103036017056905462432729 := by
  unfold tailWord_1354468
  simp only [CollatzResearch.WordTrace]
  refine ⟨24700753228500617781404029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32934337638000823708538705 24700753228500617781404029)
  ·
    refine ⟨9262782460687731668026511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24700753228500617781404029 9262782460687731668026511)
    ·
      refine ⟨13894173691031597502039767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9262782460687731668026511 13894173691031597502039767)
      ·
        refine ⟨20841260536547396253059651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13894173691031597502039767 20841260536547396253059651)
        ·
          refine ⟨31261890804821094379589477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20841260536547396253059651 31261890804821094379589477)
          ·
            refine ⟨5861604525903955196173027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31261890804821094379589477 5861604525903955196173027)
            ·
              refine ⟨8792406788855932794259541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5861604525903955196173027 8792406788855932794259541)
              ·
                refine ⟨103036017056905462432729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8792406788855932794259541 103036017056905462432729)
                ·
                  rfl

theorem cell21_1354468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_1354468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354468 prefixEnd_1354468 := by exact prefixLift 1354468
  have htrace : WordTrace (prefixWord ++ tailWord_1354468) baseStart_1354468 baseEnd_1354468 := by
    simpa [prefixWord, tailWord_1354468, baseEnd_1354468] using wordTrace_append hprefix tailTrace_1354468
  have hstable : (prefixWord ++ tailWord_1354468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354468).length < 2 ^ (prefixWord ++ tailWord_1354468).sum := by decide
  have hdescent : baseEnd_1354468 < baseStart_1354468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354513 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 6]
def baseStart_1354513 : Nat := 118140960795 + 1354513 * 2 ^ 59
def prefixEnd_1354513 : Nat := 4983230072969 + 3 ^ 40 * 1354513 * 2
def baseEnd_1354513 : Nat := 309118320783806309048095

theorem tailTrace_1354513 : CollatzResearch.WordTrace tailWord_1354513 prefixEnd_1354513 309118320783806309048095 := by
  unfold tailWord_1354513
  simp only [CollatzResearch.WordTrace]
  refine ⟨49403147741838208248196193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32935431827892138832130795 49403147741838208248196193)
  ·
    refine ⟨37052360806378656186147145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49403147741838208248196193 37052360806378656186147145)
    ·
      refine ⟨27789270604783992139610359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37052360806378656186147145 27789270604783992139610359)
      ·
        refine ⟨41683905907175988209415539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27789270604783992139610359 41683905907175988209415539)
        ·
          refine ⟨62525858860763982314123309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41683905907175988209415539 62525858860763982314123309)
          ·
            refine ⟨23447197072786493367796241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62525858860763982314123309 23447197072786493367796241)
            ·
              refine ⟨17585397804589870025847181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23447197072786493367796241 17585397804589870025847181)
              ·
                refine ⟨6594524176721201259692693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17585397804589870025847181 6594524176721201259692693)
                ·
                  refine ⟨309118320783806309048095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6594524176721201259692693 309118320783806309048095)
                  ·
                    rfl

theorem cell21_1354513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 6].length) (baseStart_1354513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354513 prefixEnd_1354513 := by exact prefixLift 1354513
  have htrace : WordTrace (prefixWord ++ tailWord_1354513) baseStart_1354513 baseEnd_1354513 := by
    simpa [prefixWord, tailWord_1354513, baseEnd_1354513] using wordTrace_append hprefix tailTrace_1354513
  have hstable : (prefixWord ++ tailWord_1354513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354513).length < 2 ^ (prefixWord ++ tailWord_1354513).sum := by decide
  have hdescent : baseEnd_1354513 < baseStart_1354513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354564 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1354564 : Nat := 118140960795 + 1354564 * 2 ^ 59
def prefixEnd_1354564 : Nat := 4983230072969 + 3 ^ 40 * 1354564 * 2
def baseEnd_1354564 : Nat := 309129959678641553697991

theorem tailTrace_1354564 : CollatzResearch.WordTrace tailWord_1354564 prefixEnd_1354564 309129959678641553697991 := by
  unfold tailWord_1354564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24702503932326721979151373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32936671909768962638868497 24702503932326721979151373)
  ·
    refine ⟨9263438974622520742181765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24702503932326721979151373 9263438974622520742181765)
    ·
      refine ⟨1736894807741722639159081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9263438974622520742181765 1736894807741722639159081)
      ·
        refine ⟨1302671105806291979369311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1736894807741722639159081 1302671105806291979369311)
        ·
          refine ⟨1954006658709437969053967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302671105806291979369311 1954006658709437969053967)
          ·
            refine ⟨2931009988064156953580951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954006658709437969053967 2931009988064156953580951)
            ·
              refine ⟨4396514982096235430371427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931009988064156953580951 4396514982096235430371427)
              ·
                refine ⟨6594772473144353145557141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4396514982096235430371427 6594772473144353145557141)
                ·
                  refine ⟨309129959678641553697991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6594772473144353145557141 309129959678641553697991)
                  ·
                    rfl

theorem cell21_1354564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1354564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354564 prefixEnd_1354564 := by exact prefixLift 1354564
  have htrace : WordTrace (prefixWord ++ tailWord_1354564) baseStart_1354564 baseEnd_1354564 := by
    simpa [prefixWord, tailWord_1354564, baseEnd_1354564] using wordTrace_append hprefix tailTrace_1354564
  have hstable : (prefixWord ++ tailWord_1354564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354564).length < 2 ^ (prefixWord ++ tailWord_1354564).sum := by decide
  have hdescent : baseEnd_1354564 < baseStart_1354564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354609 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 3]
def baseStart_1354609 : Nat := 118140960795 + 1354609 * 2 ^ 59
def prefixEnd_1354609 : Nat := 4983230072969 + 3 ^ 40 * 1354609 * 2
def baseEnd_1354609 : Nat := 309140229291731475447899

theorem tailTrace_1354609 : CollatzResearch.WordTrace tailWord_1354609 prefixEnd_1354609 309140229291731475447899 := by
  unfold tailWord_1354609
  simp only [CollatzResearch.WordTrace]
  refine ⟨49406649149490416643690881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32937766099660277762460587 49406649149490416643690881)
  ·
    refine ⟨37054986862117812482768161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49406649149490416643690881 37054986862117812482768161)
    ·
      refine ⟨27791240146588359362076121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37054986862117812482768161 27791240146588359362076121)
      ·
        refine ⟨20843430109941269521557091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27791240146588359362076121 20843430109941269521557091)
        ·
          refine ⟨31265145164911904282335637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20843430109941269521557091 31265145164911904282335637)
          ·
            refine ⟨1465553679605245513234483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31265145164911904282335637 1465553679605245513234483)
            ·
              refine ⟨2198330519407868269851725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1465553679605245513234483 2198330519407868269851725)
              ·
                refine ⟨824373944777950601194397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2198330519407868269851725 824373944777950601194397)
                ·
                  refine ⟨309140229291731475447899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824373944777950601194397 309140229291731475447899)
                  ·
                    rfl

theorem cell21_1354609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 3].length) (baseStart_1354609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354609 prefixEnd_1354609 := by exact prefixLift 1354609
  have htrace : WordTrace (prefixWord ++ tailWord_1354609) baseStart_1354609 baseEnd_1354609 := by
    simpa [prefixWord, tailWord_1354609, baseEnd_1354609] using wordTrace_append hprefix tailTrace_1354609
  have hstable : (prefixWord ++ tailWord_1354609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354609).length < 2 ^ (prefixWord ++ tailWord_1354609).sum := by decide
  have hdescent : baseEnd_1354609 < baseStart_1354609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354682 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_1354682 : Nat := 118140960795 + 1354682 * 2 ^ 59
def prefixEnd_1354682 : Nat := 4983230072969 + 3 ^ 40 * 1354682 * 2
def baseEnd_1354682 : Nat := 309156888886299570731083

theorem tailTrace_1354682 : CollatzResearch.WordTrace tailWord_1354682 prefixEnd_1354682 309156888886299570731083 := by
  unfold tailWord_1354682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12352327919556487527774575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32939541118817300074065533 12352327919556487527774575)
  ·
    refine ⟨18528491879334731291661863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12352327919556487527774575 18528491879334731291661863)
    ·
      refine ⟨27792737819002096937492795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18528491879334731291661863 27792737819002096937492795)
      ·
        refine ⟨41689106728503145406239193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27792737819002096937492795 41689106728503145406239193)
        ·
          refine ⟨31266830046377359054679395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41689106728503145406239193 31266830046377359054679395)
          ·
            refine ⟨46900245069566038582019093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31266830046377359054679395 46900245069566038582019093)
            ·
              refine ⟨2198448987635908058532145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46900245069566038582019093 2198448987635908058532145)
              ·
                refine ⟨1648836740726931043899109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2198448987635908058532145 1648836740726931043899109)
                ·
                  refine ⟨309156888886299570731083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1648836740726931043899109 309156888886299570731083)
                  ·
                    rfl

theorem cell21_1354682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_1354682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354682 prefixEnd_1354682 := by exact prefixLift 1354682
  have htrace : WordTrace (prefixWord ++ tailWord_1354682) baseStart_1354682 baseEnd_1354682 := by
    simpa [prefixWord, tailWord_1354682, baseEnd_1354682] using wordTrace_append hprefix tailTrace_1354682
  have hstable : (prefixWord ++ tailWord_1354682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354682).length < 2 ^ (prefixWord ++ tailWord_1354682).sum := by decide
  have hdescent : baseEnd_1354682 < baseStart_1354682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354685 : List Nat := [1, 4, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1354685 : Nat := 118140960795 + 1354685 * 2 ^ 59
def prefixEnd_1354685 : Nat := 4983230072969 + 3 ^ 40 * 1354685 * 2
def baseEnd_1354685 : Nat := 309157573527172232181077

theorem tailTrace_1354685 : CollatzResearch.WordTrace tailWord_1354685 prefixEnd_1354685 309157573527172232181077 := by
  unfold tailWord_1354685
  simp only [CollatzResearch.WordTrace]
  refine ⟨49409421097215081623457509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32939614064810054415638339 49409421097215081623457509)
  ·
    refine ⟨9264266455727827804398283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49409421097215081623457509 9264266455727827804398283)
    ·
      refine ⟨13896399683591741706597425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9264266455727827804398283 13896399683591741706597425)
      ·
        refine ⟨10422299762693806279948069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13896399683591741706597425 10422299762693806279948069)
        ·
          refine ⟨1954181205505088677490263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10422299762693806279948069 1954181205505088677490263)
          ·
            refine ⟨2931271808257633016235395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954181205505088677490263 2931271808257633016235395)
            ·
              refine ⟨4396907712386449524353093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931271808257633016235395 4396907712386449524353093)
              ·
                refine ⟨824420196072459285816205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4396907712386449524353093 824420196072459285816205)
                ·
                  refine ⟨309157573527172232181077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824420196072459285816205 309157573527172232181077)
                  ·
                    rfl

theorem cell21_1354685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1354685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354685 prefixEnd_1354685 := by exact prefixLift 1354685
  have htrace : WordTrace (prefixWord ++ tailWord_1354685) baseStart_1354685 baseEnd_1354685 := by
    simpa [prefixWord, tailWord_1354685, baseEnd_1354685] using wordTrace_append hprefix tailTrace_1354685
  have hstable : (prefixWord ++ tailWord_1354685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354685).length < 2 ^ (prefixWord ++ tailWord_1354685).sum := by decide
  have hdescent : baseEnd_1354685 < baseStart_1354685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354713 : List Nat := [1, 2, 1, 2, 5, 2, 3, 5]
def baseStart_1354713 : Nat := 118140960795 + 1354713 * 2 ^ 59
def prefixEnd_1354713 : Nat := 4983230072969 + 3 ^ 40 * 1354713 * 2
def baseEnd_1354713 : Nat := 103054654502883468571451

theorem tailTrace_1354713 : CollatzResearch.WordTrace tailWord_1354713 prefixEnd_1354713 103054654502883468571451 := by
  unfold tailWord_1354713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49410442341113642405476793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32940294894075761603651195 49410442341113642405476793)
  ·
    refine ⟨37057831755835231804107595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49410442341113642405476793 37057831755835231804107595)
    ·
      refine ⟨55586747633752847706161393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37057831755835231804107595 55586747633752847706161393)
      ·
        refine ⟨41690060725314635779621045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55586747633752847706161393 41690060725314635779621045)
        ·
          refine ⟨3908443192998247104339473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41690060725314635779621045 3908443192998247104339473)
          ·
            refine ⟨2931332394748685328254605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3908443192998247104339473 2931332394748685328254605)
            ·
              refine ⟨1099249648030756998095477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2931332394748685328254605 1099249648030756998095477)
              ·
                refine ⟨103054654502883468571451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1099249648030756998095477 103054654502883468571451)
                ·
                  rfl

theorem cell21_1354713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 5].length) (baseStart_1354713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354713 prefixEnd_1354713 := by exact prefixLift 1354713
  have htrace : WordTrace (prefixWord ++ tailWord_1354713) baseStart_1354713 baseEnd_1354713 := by
    simpa [prefixWord, tailWord_1354713, baseEnd_1354713] using wordTrace_append hprefix tailTrace_1354713
  have hstable : (prefixWord ++ tailWord_1354713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354713).length < 2 ^ (prefixWord ++ tailWord_1354713).sum := by decide
  have hdescent : baseEnd_1354713 < baseStart_1354713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354955 : List Nat := [1, 1, 1, 1, 3, 2, 2, 7, 3]
def baseStart_1354955 : Nat := 118140960795 + 1354955 * 2 ^ 59
def prefixEnd_1354955 : Nat := 4983230072969 + 3 ^ 40 * 1354955 * 2
def baseEnd_1354955 : Nat := 309219191205711762680525

theorem tailTrace_1354955 : CollatzResearch.WordTrace tailWord_1354955 prefixEnd_1354955 309219191205711762680525 := by
  unfold tailWord_1354955
  simp only [CollatzResearch.WordTrace]
  refine ⟨49419268806236917735786319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32946179204157945157190879 49419268806236917735786319)
  ·
    refine ⟨74128903209355376603679479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49419268806236917735786319 74128903209355376603679479)
    ·
      refine ⟨111193354814033064905519219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74128903209355376603679479 111193354814033064905519219)
      ·
        refine ⟨166790032221049597358278829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111193354814033064905519219 166790032221049597358278829)
        ·
          refine ⟨62546262082893599009354561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166790032221049597358278829 62546262082893599009354561)
          ·
            refine ⟨46909696562170199257015921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62546262082893599009354561 46909696562170199257015921)
            ·
              refine ⟨35182272421627649442761941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46909696562170199257015921 35182272421627649442761941)
              ·
                refine ⟨824584509881898033814733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 35182272421627649442761941 824584509881898033814733)
                ·
                  refine ⟨309219191205711762680525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824584509881898033814733 309219191205711762680525)
                  ·
                    rfl

theorem cell21_1354955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 7, 3].length) (baseStart_1354955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354955 prefixEnd_1354955 := by exact prefixLift 1354955
  have htrace : WordTrace (prefixWord ++ tailWord_1354955) baseStart_1354955 baseEnd_1354955 := by
    simpa [prefixWord, tailWord_1354955, baseEnd_1354955] using wordTrace_append hprefix tailTrace_1354955
  have hstable : (prefixWord ++ tailWord_1354955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354955).length < 2 ^ (prefixWord ++ tailWord_1354955).sum := by decide
  have hdescent : baseEnd_1354955 < baseStart_1354955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354969 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 4]
def baseStart_1354969 : Nat := 118140960795 + 1354969 * 2 ^ 59
def prefixEnd_1354969 : Nat := 4983230072969 + 3 ^ 40 * 1354969 * 2
def baseEnd_1354969 : Nat := 309222386196450849447163

theorem tailTrace_1354969 : CollatzResearch.WordTrace tailWord_1354969 prefixEnd_1354969 309222386196450849447163 := by
  unfold tailWord_1354969
  simp only [CollatzResearch.WordTrace]
  refine ⟨49419779428186198126795961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32946519618790798751197307 49419779428186198126795961)
  ·
    refine ⟨37064834571139648595096971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49419779428186198126795961 37064834571139648595096971)
    ·
      refine ⟨55597251856709472892645457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37064834571139648595096971 55597251856709472892645457)
      ·
        refine ⟨41697938892532104669484093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55597251856709472892645457 41697938892532104669484093)
        ·
          refine ⟨15636727084699539251056535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41697938892532104669484093 15636727084699539251056535)
          ·
            refine ⟨23455090627049308876584803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15636727084699539251056535 23455090627049308876584803)
            ·
              refine ⟨35182635940573963314877205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23455090627049308876584803 35182635940573963314877205)
              ·
                refine ⟨1649186059714404530384869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35182635940573963314877205 1649186059714404530384869)
                ·
                  refine ⟨309222386196450849447163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649186059714404530384869 309222386196450849447163)
                  ·
                    rfl

theorem cell21_1354969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_1354969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354969 prefixEnd_1354969 := by exact prefixLift 1354969
  have htrace : WordTrace (prefixWord ++ tailWord_1354969) baseStart_1354969 baseEnd_1354969 := by
    simpa [prefixWord, tailWord_1354969, baseEnd_1354969] using wordTrace_append hprefix tailTrace_1354969
  have hstable : (prefixWord ++ tailWord_1354969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354969).length < 2 ^ (prefixWord ++ tailWord_1354969).sum := by decide
  have hdescent : baseEnd_1354969 < baseStart_1354969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354986 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_1354986 : Nat := 118140960795 + 1354986 * 2 ^ 59
def prefixEnd_1354986 : Nat := 4983230072969 + 3 ^ 40 * 1354986 * 2
def baseEnd_1354986 : Nat := 309226265828062597663795

theorem tailTrace_1354986 : CollatzResearch.WordTrace tailWord_1354986 prefixEnd_1354986 309226265828062597663795 := by
  unfold tailWord_1354986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12355099867281152507541203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32946932979416406686776541 12355099867281152507541203)
  ·
    refine ⟨18532649800921728761311805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12355099867281152507541203 18532649800921728761311805)
    ·
      refine ⟨6949743675345648285491927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18532649800921728761311805 6949743675345648285491927)
      ·
        refine ⟨10424615513018472428237891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6949743675345648285491927 10424615513018472428237891)
        ·
          refine ⟨15636923269527708642356837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10424615513018472428237891 15636923269527708642356837)
          ·
            refine ⟨2931923113036445370441907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15636923269527708642356837 2931923113036445370441907)
            ·
              refine ⟨4397884669554668055662861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2931923113036445370441907 4397884669554668055662861)
              ·
                refine ⟨1649206751083000520873573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4397884669554668055662861 1649206751083000520873573)
                ·
                  refine ⟨309226265828062597663795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649206751083000520873573 309226265828062597663795)
                  ·
                    rfl

theorem cell21_1354986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_1354986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1354986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1354986 prefixEnd_1354986 := by exact prefixLift 1354986
  have htrace : WordTrace (prefixWord ++ tailWord_1354986) baseStart_1354986 baseEnd_1354986 := by
    simpa [prefixWord, tailWord_1354986, baseEnd_1354986] using wordTrace_append hprefix tailTrace_1354986
  have hstable : (prefixWord ++ tailWord_1354986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354986).length < 2 ^ (prefixWord ++ tailWord_1354986).sum := by decide
  have hdescent : baseEnd_1354986 < baseStart_1354986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355065 : List Nat := [1, 2, 1, 6, 2, 1, 2, 3, 3]
def baseStart_1355065 : Nat := 118140960795 + 1355065 * 2 ^ 59
def prefixEnd_1355065 : Nat := 4983230072969 + 3 ^ 40 * 1355065 * 2
def baseEnd_1355065 : Nat := 309244294704376015846967

theorem tailTrace_1355065 : CollatzResearch.WordTrace tailWord_1355065 prefixEnd_1355065 309244294704376015846967 := by
  unfold tailWord_1355065
  simp only [CollatzResearch.WordTrace]
  refine ⟨49423280835838406522290649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32948853890558937681527099 49423280835838406522290649)
  ·
    refine ⟨37067460626878804891717987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49423280835838406522290649 37067460626878804891717987)
    ·
      refine ⟨55601190940318207337576981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37067460626878804891717987 55601190940318207337576981)
      ·
        refine ⟨2606305825327415968948921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55601190940318207337576981 2606305825327415968948921)
        ·
          refine ⟨1954729368995561976711691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2606305825327415968948921 1954729368995561976711691)
          ·
            refine ⟨2932094053493342965067537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1954729368995561976711691 2932094053493342965067537)
            ·
              refine ⟨2199070540120007223800653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932094053493342965067537 2199070540120007223800653)
              ·
                refine ⟨824651452545002708925245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199070540120007223800653 824651452545002708925245)
                ·
                  refine ⟨309244294704376015846967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824651452545002708925245 309244294704376015846967)
                  ·
                    rfl

theorem cell21_1355065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_1355065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355065 prefixEnd_1355065 := by exact prefixLift 1355065
  have htrace : WordTrace (prefixWord ++ tailWord_1355065) baseStart_1355065 baseEnd_1355065 := by
    simpa [prefixWord, tailWord_1355065, baseEnd_1355065] using wordTrace_append hprefix tailTrace_1355065
  have hstable : (prefixWord ++ tailWord_1355065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355065).length < 2 ^ (prefixWord ++ tailWord_1355065).sum := by decide
  have hdescent : baseEnd_1355065 < baseStart_1355065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355180 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_1355180 : Nat := 118140960795 + 1355180 * 2 ^ 59
def prefixEnd_1355180 : Nat := 4983230072969 + 3 ^ 40 * 1355180 * 2
def baseEnd_1355180 : Nat := 309270539271161371430065

theorem tailTrace_1355180 : CollatzResearch.WordTrace tailWord_1355180 prefixEnd_1355180 309270539271161371430065 := by
  unfold tailWord_1355180
  simp only [CollatzResearch.WordTrace]
  refine ⟨24713737615210890581363497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32951650153614520775151329 24713737615210890581363497)
  ·
    refine ⟨18535303211408167936022623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24713737615210890581363497 18535303211408167936022623)
    ·
      refine ⟨27802954817112251904033935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18535303211408167936022623 27802954817112251904033935)
      ·
        refine ⟨41704432225668377856050903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27802954817112251904033935 41704432225668377856050903)
        ·
          refine ⟨62556648338502566784076355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41704432225668377856050903 62556648338502566784076355)
          ·
            refine ⟨93834972507753850176114533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62556648338502566784076355 93834972507753850176114533)
            ·
              refine ⟨17594057345203846908021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93834972507753850176114533 17594057345203846908021475)
              ·
                refine ⟨26391086017805770362032213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17594057345203846908021475 26391086017805770362032213)
                ·
                  refine ⟨309270539271161371430065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26391086017805770362032213 309270539271161371430065)
                  ·
                    rfl

theorem cell21_1355180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_1355180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355180 prefixEnd_1355180 := by exact prefixLift 1355180
  have htrace : WordTrace (prefixWord ++ tailWord_1355180) baseStart_1355180 baseEnd_1355180 := by
    simpa [prefixWord, tailWord_1355180, baseEnd_1355180] using wordTrace_append hprefix tailTrace_1355180
  have hstable : (prefixWord ++ tailWord_1355180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355180).length < 2 ^ (prefixWord ++ tailWord_1355180).sum := by decide
  have hdescent : baseEnd_1355180 < baseStart_1355180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355200 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_1355200 : Nat := 118140960795 + 1355200 * 2 ^ 59
def prefixEnd_1355200 : Nat := 4983230072969 + 3 ^ 40 * 1355200 * 2
def baseEnd_1355200 : Nat := 309275103543645781096691

theorem tailTrace_1355200 : CollatzResearch.WordTrace tailWord_1355200 prefixEnd_1355200 309275103543645781096691 := by
  unfold tailWord_1355200
  simp only [CollatzResearch.WordTrace]
  refine ⟨24714102345174662289227527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32952136460232883052303369 24714102345174662289227527)
  ·
    refine ⟨37071153517761993433841291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24714102345174662289227527 37071153517761993433841291)
    ·
      refine ⟨55606730276642990150761937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37071153517761993433841291 55606730276642990150761937)
      ·
        refine ⟨41705047707482242613071453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55606730276642990150761937 41705047707482242613071453)
        ·
          refine ⟨15639392890305840979901795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41705047707482242613071453 15639392890305840979901795)
          ·
            refine ⟨23459089335458761469852693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15639392890305840979901795 23459089335458761469852693)
            ·
              refine ⟨1099644812599629443899345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23459089335458761469852693 1099644812599629443899345)
              ·
                refine ⟨824733609449722082924509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099644812599629443899345 824733609449722082924509)
                ·
                  refine ⟨309275103543645781096691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824733609449722082924509 309275103543645781096691)
                  ·
                    rfl

theorem cell21_1355200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_1355200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355200 prefixEnd_1355200 := by exact prefixLift 1355200
  have htrace : WordTrace (prefixWord ++ tailWord_1355200) baseStart_1355200 baseEnd_1355200 := by
    simpa [prefixWord, tailWord_1355200, baseEnd_1355200] using wordTrace_append hprefix tailTrace_1355200
  have hstable : (prefixWord ++ tailWord_1355200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355200).length < 2 ^ (prefixWord ++ tailWord_1355200).sum := by decide
  have hdescent : baseEnd_1355200 < baseStart_1355200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355211 : List Nat := [1, 1, 1, 1, 3, 3, 5, 6]
def baseStart_1355211 : Nat := 118140960795 + 1355211 * 2 ^ 59
def prefixEnd_1355211 : Nat := 4983230072969 + 3 ^ 40 * 1355211 * 2
def baseEnd_1355211 : Nat := 103092537964504068804445

theorem tailTrace_1355211 : CollatzResearch.WordTrace tailWord_1355211 prefixEnd_1355211 103092537964504068804445 := by
  unfold tailWord_1355211
  simp only [CollatzResearch.WordTrace]
  refine ⟨49428605893309473457105487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32952403928872982304736991 49428605893309473457105487)
  ·
    refine ⟨74142908839964210185658231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49428605893309473457105487 74142908839964210185658231)
    ·
      refine ⟨111214363259946315278487347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74142908839964210185658231 111214363259946315278487347)
      ·
        refine ⟨166821544889919472917731021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111214363259946315278487347 166821544889919472917731021)
        ·
          refine ⟨62558079333719802344149133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166821544889919472917731021 62558079333719802344149133)
          ·
            refine ⟨23459279750144925879055925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62558079333719802344149133 23459279750144925879055925)
            ·
              refine ⟨2199307476576086801161493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23459279750144925879055925 2199307476576086801161493)
              ·
                refine ⟨103092537964504068804445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199307476576086801161493 103092537964504068804445)
                ·
                  rfl

theorem cell21_1355211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 6].length) (baseStart_1355211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355211 prefixEnd_1355211 := by exact prefixLift 1355211
  have htrace : WordTrace (prefixWord ++ tailWord_1355211) baseStart_1355211 baseEnd_1355211 := by
    simpa [prefixWord, tailWord_1355211, baseEnd_1355211] using wordTrace_append hprefix tailTrace_1355211
  have hstable : (prefixWord ++ tailWord_1355211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355211).length < 2 ^ (prefixWord ++ tailWord_1355211).sum := by decide
  have hdescent : baseEnd_1355211 < baseStart_1355211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355324 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_1355324 : Nat := 118140960795 + 1355324 * 2 ^ 59
def prefixEnd_1355324 : Nat := 4983230072969 + 3 ^ 40 * 1355324 * 2
def baseEnd_1355324 : Nat := 309303402033049121029771

theorem tailTrace_1355324 : CollatzResearch.WordTrace tailWord_1355324 prefixEnd_1355324 309303402033049121029771 := by
  unfold tailWord_1355324
  simp only [CollatzResearch.WordTrace]
  refine ⟨24716363670950046877984513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32955151561266729170646017 24716363670950046877984513)
  ·
    refine ⟨18537272753212535158488385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24716363670950046877984513 18537272753212535158488385)
    ·
      refine ⟨13902954564909401368866289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18537272753212535158488385 13902954564909401368866289)
      ·
        refine ⟨10427215923682051026649717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13902954564909401368866289 10427215923682051026649717)
        ·
          refine ⟨977551492845192283748411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10427215923682051026649717 977551492845192283748411)
          ·
            refine ⟨1466327239267788425622617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977551492845192283748411 1466327239267788425622617)
            ·
              refine ⟨1099745429450841319216963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466327239267788425622617 1099745429450841319216963)
              ·
                refine ⟨1649618144176261978825445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1099745429450841319216963 1649618144176261978825445)
                ·
                  refine ⟨309303402033049121029771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649618144176261978825445 309303402033049121029771)
                  ·
                    rfl

theorem cell21_1355324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_1355324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355324 prefixEnd_1355324 := by exact prefixLift 1355324
  have htrace : WordTrace (prefixWord ++ tailWord_1355324) baseStart_1355324 baseEnd_1355324 := by
    simpa [prefixWord, tailWord_1355324, baseEnd_1355324] using wordTrace_append hprefix tailTrace_1355324
  have hstable : (prefixWord ++ tailWord_1355324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355324).length < 2 ^ (prefixWord ++ tailWord_1355324).sum := by decide
  have hdescent : baseEnd_1355324 < baseStart_1355324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355377 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 9]
def baseStart_1355377 : Nat := 118140960795 + 1355377 * 2 ^ 59
def prefixEnd_1355377 : Nat := 4983230072969 + 3 ^ 40 * 1355377 * 2
def baseEnd_1355377 : Nat := 309315497355132806646329

theorem tailTrace_1355377 : CollatzResearch.WordTrace tailWord_1355377 prefixEnd_1355377 309315497355132806646329 := by
  unfold tailWord_1355377
  simp only [CollatzResearch.WordTrace]
  refine ⟨49434660410708083807648385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32956440273805389205098923 49434660410708083807648385)
  ·
    refine ⟨37075995308031062855736289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49434660410708083807648385 37075995308031062855736289)
    ·
      refine ⟨27806996481023297141802217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37075995308031062855736289 27806996481023297141802217)
      ·
        refine ⟨20855247360767472856351663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27806996481023297141802217 20855247360767472856351663)
        ·
          refine ⟨31282871041151209284527495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20855247360767472856351663 31282871041151209284527495)
          ·
            refine ⟨46924306561726813926791243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31282871041151209284527495 46924306561726813926791243)
            ·
              refine ⟨70386459842590220890186865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46924306561726813926791243 70386459842590220890186865)
              ·
                refine ⟨52789844881942665667640149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70386459842590220890186865 52789844881942665667640149)
                ·
                  refine ⟨309315497355132806646329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52789844881942665667640149 309315497355132806646329)
                  ·
                    rfl

theorem cell21_1355377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_1355377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355377 prefixEnd_1355377 := by exact prefixLift 1355377
  have htrace : WordTrace (prefixWord ++ tailWord_1355377) baseStart_1355377 baseEnd_1355377 := by
    simpa [prefixWord, tailWord_1355377, baseEnd_1355377] using wordTrace_append hprefix tailTrace_1355377
  have hstable : (prefixWord ++ tailWord_1355377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355377).length < 2 ^ (prefixWord ++ tailWord_1355377).sum := by decide
  have hdescent : baseEnd_1355377 < baseStart_1355377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355425 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 6]
def baseStart_1355425 : Nat := 118140960795 + 1355425 * 2 ^ 59
def prefixEnd_1355425 : Nat := 4983230072969 + 3 ^ 40 * 1355425 * 2
def baseEnd_1355425 : Nat := 309326451609095389846231

theorem tailTrace_1355425 : CollatzResearch.WordTrace tailWord_1355425 prefixEnd_1355425 309326451609095389846231 := by
  unfold tailWord_1355425
  simp only [CollatzResearch.WordTrace]
  refine ⟨49436411114534188005395729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32957607409689458670263819 49436411114534188005395729)
  ·
    refine ⟨37077308335900641004046797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49436411114534188005395729 37077308335900641004046797)
    ·
      refine ⟨13903990625962740376517549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37077308335900641004046797 13903990625962740376517549)
      ·
        refine ⟨5213996484736027641194081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13903990625962740376517549 5213996484736027641194081)
        ·
          refine ⟨3910497363552020730895561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213996484736027641194081 3910497363552020730895561)
          ·
            refine ⟨2932873022664015548171671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910497363552020730895561 2932873022664015548171671)
            ·
              refine ⟨4399309533996023322257507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932873022664015548171671 4399309533996023322257507)
              ·
                refine ⟨6598964300994034983386261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399309533996023322257507 6598964300994034983386261)
                ·
                  refine ⟨309326451609095389846231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6598964300994034983386261 309326451609095389846231)
                  ·
                    rfl

theorem cell21_1355425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_1355425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355425 prefixEnd_1355425 := by exact prefixLift 1355425
  have htrace : WordTrace (prefixWord ++ tailWord_1355425) baseStart_1355425 baseEnd_1355425 := by
    simpa [prefixWord, tailWord_1355425, baseEnd_1355425] using wordTrace_append hprefix tailTrace_1355425
  have hstable : (prefixWord ++ tailWord_1355425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355425).length < 2 ^ (prefixWord ++ tailWord_1355425).sum := by decide
  have hdescent : baseEnd_1355425 < baseStart_1355425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355462 : List Nat := [6, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1355462 : Nat := 118140960795 + 1355462 * 2 ^ 59
def prefixEnd_1355462 : Nat := 4983230072969 + 3 ^ 40 * 1355462 * 2
def baseEnd_1355462 : Nat := 309334895513191547729489

theorem tailTrace_1355462 : CollatzResearch.WordTrace tailWord_1355462 prefixEnd_1355462 309334895513191547729489 := by
  unfold tailWord_1355462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544930019231254478890395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32958507076933428882995093 1544930019231254478890395)
  ·
    refine ⟨2317395028846881718335593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544930019231254478890395 2317395028846881718335593)
    ·
      refine ⟨1738046271635161288751695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317395028846881718335593 1738046271635161288751695)
      ·
        refine ⟨2607069407452741933127543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738046271635161288751695 2607069407452741933127543)
        ·
          refine ⟨3910604111179112899691315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607069407452741933127543 3910604111179112899691315)
          ·
            refine ⟨5865906166768669349536973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910604111179112899691315 5865906166768669349536973)
            ·
              refine ⟨2199714812538251006076365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5865906166768669349536973 2199714812538251006076365)
              ·
                refine ⟨824893054701844127278637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2199714812538251006076365 824893054701844127278637)
                ·
                  refine ⟨309334895513191547729489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824893054701844127278637 309334895513191547729489)
                  ·
                    rfl

theorem cell21_1355462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1355462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355462 prefixEnd_1355462 := by exact prefixLift 1355462
  have htrace : WordTrace (prefixWord ++ tailWord_1355462) baseStart_1355462 baseEnd_1355462 := by
    simpa [prefixWord, tailWord_1355462, baseEnd_1355462] using wordTrace_append hprefix tailTrace_1355462
  have hstable : (prefixWord ++ tailWord_1355462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355462).length < 2 ^ (prefixWord ++ tailWord_1355462).sum := by decide
  have hdescent : baseEnd_1355462 < baseStart_1355462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355538 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_1355538 : Nat := 118140960795 + 1355538 * 2 ^ 59
def prefixEnd_1355538 : Nat := 4983230072969 + 3 ^ 40 * 1355538 * 2
def baseEnd_1355538 : Nat := 309352239748632304462667

theorem tailTrace_1355538 : CollatzResearch.WordTrace tailWord_1355538 prefixEnd_1355538 309352239748632304462667 := by
  unfold tailWord_1355538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12360133140781202076064817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32960355042083205536172845 12360133140781202076064817)
  ·
    refine ⟨9270099855585901557048613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12360133140781202076064817 9270099855585901557048613)
    ·
      refine ⟨1738143722922356541946615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9270099855585901557048613 1738143722922356541946615)
      ·
        refine ⟨2607215584383534812919923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1738143722922356541946615 2607215584383534812919923)
        ·
          refine ⟨3910823376575302219379885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607215584383534812919923 3910823376575302219379885)
          ·
            refine ⟨1466558766215738332267457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3910823376575302219379885 1466558766215738332267457)
            ·
              refine ⟨1099919074661803749200593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466558766215738332267457 1099919074661803749200593)
              ·
                refine ⟨824939305996352811900445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1099919074661803749200593 824939305996352811900445)
                ·
                  refine ⟨309352239748632304462667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 824939305996352811900445 309352239748632304462667)
                  ·
                    rfl

theorem cell21_1355538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_1355538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355538 prefixEnd_1355538 := by exact prefixLift 1355538
  have htrace : WordTrace (prefixWord ++ tailWord_1355538) baseStart_1355538 baseEnd_1355538 := by
    simpa [prefixWord, tailWord_1355538, baseEnd_1355538] using wordTrace_append hprefix tailTrace_1355538
  have hstable : (prefixWord ++ tailWord_1355538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355538).length < 2 ^ (prefixWord ++ tailWord_1355538).sum := by decide
  have hdescent : baseEnd_1355538 < baseStart_1355538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355656 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_1355656 : Nat := 118140960795 + 1355656 * 2 ^ 59
def prefixEnd_1355656 : Nat := 4983230072969 + 3 ^ 40 * 1355656 * 2
def baseEnd_1355656 : Nat := 309379168956290321495759

theorem tailTrace_1355656 : CollatzResearch.WordTrace tailWord_1355656 prefixEnd_1355656 309379168956290321495759 := by
  unfold tailWord_1355656
  simp only [CollatzResearch.WordTrace]
  refine ⟨24722418188348657228527411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32963224251131542971369881 24722418188348657228527411)
  ·
    refine ⟨37083627282522985842791117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24722418188348657228527411 37083627282522985842791117)
    ·
      refine ⟨13906360230946119691046669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37083627282522985842791117 13906360230946119691046669)
      ·
        refine ⟨5214885086604794884142501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13906360230946119691046669 5214885086604794884142501)
        ·
          refine ⟨977790953738399040776719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5214885086604794884142501 977790953738399040776719)
          ·
            refine ⟨1466686430607598561165079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977790953738399040776719 1466686430607598561165079)
            ·
              refine ⟨2200029645911397841747619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466686430607598561165079 2200029645911397841747619)
              ·
                refine ⟨3300044468867096762621429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200029645911397841747619 3300044468867096762621429)
                ·
                  refine ⟨309379168956290321495759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300044468867096762621429 309379168956290321495759)
                  ·
                    rfl

theorem cell21_1355656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_1355656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355656 prefixEnd_1355656 := by exact prefixLift 1355656
  have htrace : WordTrace (prefixWord ++ tailWord_1355656) baseStart_1355656 baseEnd_1355656 := by
    simpa [prefixWord, tailWord_1355656, baseEnd_1355656] using wordTrace_append hprefix tailTrace_1355656
  have hstable : (prefixWord ++ tailWord_1355656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355656).length < 2 ^ (prefixWord ++ tailWord_1355656).sum := by decide
  have hdescent : baseEnd_1355656 < baseStart_1355656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355884 : List Nat := [2, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1355884 : Nat := 118140960795 + 1355884 * 2 ^ 59
def prefixEnd_1355884 : Nat := 4983230072969 + 3 ^ 40 * 1355884 * 2
def baseEnd_1355884 : Nat := 309431201662612591695293

theorem tailTrace_1355884 : CollatzResearch.WordTrace tailWord_1355884 prefixEnd_1355884 309431201662612591695293 := by
  unfold tailWord_1355884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726576109935654698177353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32968768146580872930903137 24726576109935654698177353)
  ·
    refine ⟨18544932082451741023633015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24726576109935654698177353 18544932082451741023633015)
    ·
      refine ⟨27817398123677611535449523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18544932082451741023633015 27817398123677611535449523)
      ·
        refine ⟨41726097185516417303174285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817398123677611535449523 41726097185516417303174285)
        ·
          refine ⟨15647286444568656488690357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41726097185516417303174285 15647286444568656488690357)
          ·
            refine ⟨1466933104178311545814721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15647286444568656488690357 1466933104178311545814721)
            ·
              refine ⟨1100199828133733659361041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1466933104178311545814721 1100199828133733659361041)
              ·
                refine ⟨825149871100300244520781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100199828133733659361041 825149871100300244520781)
                ·
                  refine ⟨309431201662612591695293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825149871100300244520781 309431201662612591695293)
                  ·
                    rfl

theorem cell21_1355884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1355884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355884 prefixEnd_1355884 := by exact prefixLift 1355884
  have htrace : WordTrace (prefixWord ++ tailWord_1355884) baseStart_1355884 baseEnd_1355884 := by
    simpa [prefixWord, tailWord_1355884, baseEnd_1355884] using wordTrace_append hprefix tailTrace_1355884
  have hstable : (prefixWord ++ tailWord_1355884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355884).length < 2 ^ (prefixWord ++ tailWord_1355884).sum := by decide
  have hdescent : baseEnd_1355884 < baseStart_1355884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355895 : List Nat := [1, 1, 3, 1, 1, 7, 1, 6]
def baseStart_1355895 : Nat := 118140960795 + 1355895 * 2 ^ 59
def prefixEnd_1355895 : Nat := 4983230072969 + 3 ^ 40 * 1355895 * 2
def baseEnd_1355895 : Nat := 103144570670826339003979

theorem tailTrace_1355895 : CollatzResearch.WordTrace tailWord_1355895 prefixEnd_1355895 103144570670826339003979 := by
  unfold tailWord_1355895
  simp only [CollatzResearch.WordTrace]
  refine ⟨49453553422831458275005139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32969035615220972183336759 49453553422831458275005139)
  ·
    refine ⟨74180330134247187412507709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49453553422831458275005139 74180330134247187412507709)
    ·
      refine ⟨27817623800342695279690391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74180330134247187412507709 27817623800342695279690391)
      ·
        refine ⟨41726435700514042919535587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817623800342695279690391 41726435700514042919535587)
        ·
          refine ⟨62589653550771064379303381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41726435700514042919535587 62589653550771064379303381)
          ·
            refine ⟨1466945005096196821389923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62589653550771064379303381 1466945005096196821389923)
            ·
              refine ⟨2200417507644295232084885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466945005096196821389923 2200417507644295232084885)
              ·
                refine ⟨103144570670826339003979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2200417507644295232084885 103144570670826339003979)
                ·
                  rfl

theorem cell21_1355895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 6].length) (baseStart_1355895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355895 prefixEnd_1355895 := by exact prefixLift 1355895
  have htrace : WordTrace (prefixWord ++ tailWord_1355895) baseStart_1355895 baseEnd_1355895 := by
    simpa [prefixWord, tailWord_1355895, baseEnd_1355895] using wordTrace_append hprefix tailTrace_1355895
  have hstable : (prefixWord ++ tailWord_1355895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355895).length < 2 ^ (prefixWord ++ tailWord_1355895).sum := by decide
  have hdescent : baseEnd_1355895 < baseStart_1355895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355909 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 7]
def baseStart_1355909 : Nat := 118140960795 + 1355909 * 2 ^ 59
def prefixEnd_1355909 : Nat := 4983230072969 + 3 ^ 40 * 1355909 * 2
def baseEnd_1355909 : Nat := 309436907003218103778575

theorem tailTrace_1355909 : CollatzResearch.WordTrace tailWord_1355909 prefixEnd_1355909 309436907003218103778575 := by
  unfold tailWord_1355909
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454064044780738666014781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32969376029853825777343187 49454064044780738666014781)
  ·
    refine ⟨18545274016792776999755543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49454064044780738666014781 18545274016792776999755543)
    ·
      refine ⟨27817911025189165499633315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18545274016792776999755543 27817911025189165499633315)
      ·
        refine ⟨41726866537783748249449973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817911025189165499633315 41726866537783748249449973)
        ·
          refine ⟨3911893737917226398385935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41726866537783748249449973 3911893737917226398385935)
          ·
            refine ⟨5867840606875839597578903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3911893737917226398385935 5867840606875839597578903)
            ·
              refine ⟨8801760910313759396368355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5867840606875839597578903 8801760910313759396368355)
              ·
                refine ⟨13202641365470639094552533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801760910313759396368355 13202641365470639094552533)
                ·
                  refine ⟨309436907003218103778575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13202641365470639094552533 309436907003218103778575)
                  ·
                    rfl

theorem cell21_1355909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_1355909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355909 prefixEnd_1355909 := by exact prefixLift 1355909
  have htrace : WordTrace (prefixWord ++ tailWord_1355909) baseStart_1355909 baseEnd_1355909 := by
    simpa [prefixWord, tailWord_1355909, baseEnd_1355909] using wordTrace_append hprefix tailTrace_1355909
  have hstable : (prefixWord ++ tailWord_1355909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355909).length < 2 ^ (prefixWord ++ tailWord_1355909).sum := by decide
  have hdescent : baseEnd_1355909 < baseStart_1355909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355912 : List Nat := [2, 1, 3, 4, 1, 2, 3, 5]
def baseStart_1355912 : Nat := 118140960795 + 1355912 * 2 ^ 59
def prefixEnd_1355912 : Nat := 4983230072969 + 3 ^ 40 * 1355912 * 2
def baseEnd_1355912 : Nat := 103145863881363588409523

theorem tailTrace_1355912 : CollatzResearch.WordTrace tailWord_1355912 prefixEnd_1355912 103145863881363588409523 := by
  unfold tailWord_1355912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24727086731884935089186995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32969448975846580118915993 24727086731884935089186995)
  ·
    refine ⟨37090630097827402633780493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24727086731884935089186995 37090630097827402633780493)
    ·
      refine ⟨13908986286685275987667685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37090630097827402633780493 13908986286685275987667685)
      ·
        refine ⟨2607934928753489247687691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13908986286685275987667685 2607934928753489247687691)
        ·
          refine ⟨3911902393130233871531537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607934928753489247687691 3911902393130233871531537)
          ·
            refine ⟨2933926794847675403648653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911902393130233871531537 2933926794847675403648653)
            ·
              refine ⟨1100222548067878276368245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2933926794847675403648653 1100222548067878276368245)
              ·
                refine ⟨103145863881363588409523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100222548067878276368245 103145863881363588409523)
                ·
                  rfl

theorem cell21_1355912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_1355912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355912 prefixEnd_1355912 := by exact prefixLift 1355912
  have htrace : WordTrace (prefixWord ++ tailWord_1355912) baseStart_1355912 baseEnd_1355912 := by
    simpa [prefixWord, tailWord_1355912, baseEnd_1355912] using wordTrace_append hprefix tailTrace_1355912
  have hstable : (prefixWord ++ tailWord_1355912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355912).length < 2 ^ (prefixWord ++ tailWord_1355912).sum := by decide
  have hdescent : baseEnd_1355912 < baseStart_1355912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355923 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 6]
def baseStart_1355923 : Nat := 118140960795 + 1355923 * 2 ^ 59
def prefixEnd_1355923 : Nat := 4983230072969 + 3 ^ 40 * 1355923 * 2
def baseEnd_1355923 : Nat := 309440101993957190545213

theorem tailTrace_1355923 : CollatzResearch.WordTrace tailWord_1355923 prefixEnd_1355923 309440101993957190545213 := by
  unfold tailWord_1355923
  simp only [CollatzResearch.WordTrace]
  refine ⟨49454574666730019057024423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32969716444486679371349615 49454574666730019057024423)
  ·
    refine ⟨74181862000095028585536635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49454574666730019057024423 74181862000095028585536635)
    ·
      refine ⟨111272793000142542878304953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74181862000095028585536635 111272793000142542878304953)
      ·
        refine ⟨83454594750106907158728715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111272793000142542878304953 83454594750106907158728715)
        ·
          refine ⟨125181892125160360738093073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83454594750106907158728715 125181892125160360738093073)
          ·
            refine ⟨93886419093870270553569805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125181892125160360738093073 93886419093870270553569805)
            ·
              refine ⟨35207407160201351457588677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93886419093870270553569805 35207407160201351457588677)
              ·
                refine ⟨6601388842537753398297877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35207407160201351457588677 6601388842537753398297877)
                ·
                  refine ⟨309440101993957190545213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6601388842537753398297877 309440101993957190545213)
                  ·
                    rfl

theorem cell21_1355923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 6].length) (baseStart_1355923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355923 prefixEnd_1355923 := by exact prefixLift 1355923
  have htrace : WordTrace (prefixWord ++ tailWord_1355923) baseStart_1355923 baseEnd_1355923 := by
    simpa [prefixWord, tailWord_1355923, baseEnd_1355923] using wordTrace_append hprefix tailTrace_1355923
  have hstable : (prefixWord ++ tailWord_1355923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355923).length < 2 ^ (prefixWord ++ tailWord_1355923).sum := by decide
  have hdescent : baseEnd_1355923 < baseStart_1355923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355943 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 5]
def baseStart_1355943 : Nat := 118140960795 + 1355943 * 2 ^ 59
def prefixEnd_1355943 : Nat := 4983230072969 + 3 ^ 40 * 1355943 * 2
def baseEnd_1355943 : Nat := 309444666266441600211839

theorem tailTrace_1355943 : CollatzResearch.WordTrace tailWord_1355943 prefixEnd_1355943 309444666266441600211839 := by
  unfold tailWord_1355943
  simp only [CollatzResearch.WordTrace]
  refine ⟨49455304126657562472752483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32970202751105041648501655 49455304126657562472752483)
  ·
    refine ⟨74182956189986343709128725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49455304126657562472752483 74182956189986343709128725)
    ·
      refine ⟨3477326071405609861365409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74182956189986343709128725 3477326071405609861365409)
      ·
        refine ⟨2607994553554207396024057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3477326071405609861365409 2607994553554207396024057)
        ·
          refine ⟨1955995915165655547018043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607994553554207396024057 1955995915165655547018043)
          ·
            refine ⟨2933993872748483320527065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955995915165655547018043 2933993872748483320527065)
            ·
              refine ⟨2200495404561362490395299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2933993872748483320527065 2200495404561362490395299)
              ·
                refine ⟨3300743106842043735592949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200495404561362490395299 3300743106842043735592949)
                ·
                  refine ⟨309444666266441600211839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300743106842043735592949 309444666266441600211839)
                  ·
                    rfl

theorem cell21_1355943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 5].length) (baseStart_1355943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355943 prefixEnd_1355943 := by exact prefixLift 1355943
  have htrace : WordTrace (prefixWord ++ tailWord_1355943) baseStart_1355943 baseEnd_1355943 := by
    simpa [prefixWord, tailWord_1355943, baseEnd_1355943] using wordTrace_append hprefix tailTrace_1355943
  have hstable : (prefixWord ++ tailWord_1355943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355943).length < 2 ^ (prefixWord ++ tailWord_1355943).sum := by decide
  have hdescent : baseEnd_1355943 < baseStart_1355943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1355954 : List Nat := [3, 2, 1, 1, 1, 3, 2, 8]
def baseStart_1355954 : Nat := 118140960795 + 1355954 * 2 ^ 59
def prefixEnd_1355954 : Nat := 4983230072969 + 3 ^ 40 * 1355954 * 2
def baseEnd_1355954 : Nat := 103149058872102675176161

theorem tailTrace_1355954 : CollatzResearch.WordTrace tailWord_1355954 prefixEnd_1355954 103149058872102675176161 := by
  unfold tailWord_1355954
  simp only [CollatzResearch.WordTrace]
  refine ⟨12363926332404427837850729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32970470219745140900935277 12363926332404427837850729)
  ·
    refine ⟨9272944749303320878388047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12363926332404427837850729 9272944749303320878388047)
    ·
      refine ⟨13909417123954981317582071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9272944749303320878388047 13909417123954981317582071)
      ·
        refine ⟨20864125685932471976373107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13909417123954981317582071 20864125685932471976373107)
        ·
          refine ⟨31296188528898707964559661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20864125685932471976373107 31296188528898707964559661)
          ·
            refine ⟨11736070698337015486709873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31296188528898707964559661 11736070698337015486709873)
            ·
              refine ⟨8802053023752761615032405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11736070698337015486709873 8802053023752761615032405)
              ·
                refine ⟨103149058872102675176161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8802053023752761615032405 103149058872102675176161)
                ·
                  rfl

theorem cell21_1355954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_1355954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1355954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1355954 prefixEnd_1355954 := by exact prefixLift 1355954
  have htrace : WordTrace (prefixWord ++ tailWord_1355954) baseStart_1355954 baseEnd_1355954 := by
    simpa [prefixWord, tailWord_1355954, baseEnd_1355954] using wordTrace_append hprefix tailTrace_1355954
  have hstable : (prefixWord ++ tailWord_1355954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1355954).length < 2 ^ (prefixWord ++ tailWord_1355954).sum := by decide
  have hdescent : baseEnd_1355954 < baseStart_1355954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1355954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356140 : List Nat := [2, 2, 1, 1, 6, 2, 2, 5]
def baseStart_1356140 : Nat := 118140960795 + 1356140 * 2 ^ 59
def prefixEnd_1356140 : Nat := 4983230072969 + 3 ^ 40 * 1356140 * 2
def baseEnd_1356140 : Nat := 103163208116804345142701

theorem tailTrace_1356140 : CollatzResearch.WordTrace tailWord_1356140 prefixEnd_1356140 103163208116804345142701 := by
  unfold tailWord_1356140
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731244653471932558836937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32974992871295910078449249 24731244653471932558836937)
  ·
    refine ⟨18548433490103949419127703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24731244653471932558836937 18548433490103949419127703)
    ·
      refine ⟨27822650235155924128691555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18548433490103949419127703 27822650235155924128691555)
      ·
        refine ⟨41733975352733886193037333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27822650235155924128691555 41733975352733886193037333)
        ·
          refine ⟨1956280094659400915298625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41733975352733886193037333 1956280094659400915298625)
          ·
            refine ⟨1467210070994550686473969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956280094659400915298625 1467210070994550686473969)
            ·
              refine ⟨1100407553245913014855477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467210070994550686473969 1100407553245913014855477)
              ·
                refine ⟨103163208116804345142701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100407553245913014855477 103163208116804345142701)
                ·
                  rfl

theorem cell21_1356140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_1356140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356140 prefixEnd_1356140 := by exact prefixLift 1356140
  have htrace : WordTrace (prefixWord ++ tailWord_1356140) baseStart_1356140 baseEnd_1356140 := by
    simpa [prefixWord, tailWord_1356140, baseEnd_1356140] using wordTrace_append hprefix tailTrace_1356140
  have hstable : (prefixWord ++ tailWord_1356140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356140).length < 2 ^ (prefixWord ++ tailWord_1356140).sum := by decide
  have hdescent : baseEnd_1356140 < baseStart_1356140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356168 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_1356168 : Nat := 118140960795 + 1356168 * 2 ^ 59
def prefixEnd_1356168 : Nat := 4983230072969 + 3 ^ 40 * 1356168 * 2
def baseEnd_1356168 : Nat := 309496014331891208961379

theorem tailTrace_1356168 : CollatzResearch.WordTrace tailWord_1356168 prefixEnd_1356168 309496014331891208961379 := by
  unfold tailWord_1356168
  simp only [CollatzResearch.WordTrace]
  refine ⟨24731755275421212949846579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32975673700561617266462105 24731755275421212949846579)
  ·
    refine ⟨37097632913131819424769869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24731755275421212949846579 37097632913131819424769869)
    ·
      refine ⟨13911612342424432284288701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37097632913131819424769869 13911612342424432284288701)
      ·
        refine ⟨5216854628409162106608263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13911612342424432284288701 5216854628409162106608263)
        ·
          refine ⟨7825281942613743159912395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216854628409162106608263 7825281942613743159912395)
          ·
            refine ⟨11737922913920614739868593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7825281942613743159912395 11737922913920614739868593)
            ·
              refine ⟨8803442185440461054901445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11737922913920614739868593 8803442185440461054901445)
              ·
                refine ⟨1650645409770086447794021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8803442185440461054901445 1650645409770086447794021)
                ·
                  refine ⟨309496014331891208961379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650645409770086447794021 309496014331891208961379)
                  ·
                    rfl

theorem cell21_1356168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_1356168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356168 prefixEnd_1356168 := by exact prefixLift 1356168
  have htrace : WordTrace (prefixWord ++ tailWord_1356168) baseStart_1356168 baseEnd_1356168 := by
    simpa [prefixWord, tailWord_1356168, baseEnd_1356168] using wordTrace_append hprefix tailTrace_1356168
  have hstable : (prefixWord ++ tailWord_1356168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356168).length < 2 ^ (prefixWord ++ tailWord_1356168).sum := by decide
  have hdescent : baseEnd_1356168 < baseStart_1356168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356171 : List Nat := [1, 1, 1, 1, 4, 5, 3, 2, 3]
def baseStart_1356171 : Nat := 118140960795 + 1356171 * 2 ^ 59
def prefixEnd_1356171 : Nat := 4983230072969 + 3 ^ 40 * 1356171 * 2
def baseEnd_1356171 : Nat := 309496698972763870411373

theorem tailTrace_1356171 : CollatzResearch.WordTrace tailWord_1356171 prefixEnd_1356171 309496698972763870411373 := by
  unfold tailWord_1356171
  simp only [CollatzResearch.WordTrace]
  refine ⟨49463619969831557412052367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32975746646554371608034911 49463619969831557412052367)
  ·
    refine ⟨74195429954747336118078551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49463619969831557412052367 74195429954747336118078551)
    ·
      refine ⟨111293144932121004177117827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74195429954747336118078551 111293144932121004177117827)
      ·
        refine ⟨166939717398181506265676741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111293144932121004177117827 166939717398181506265676741)
        ·
          refine ⟨31301197012159032424814389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166939717398181506265676741 31301197012159032424814389)
          ·
            refine ⟨2934487219889909289826349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31301197012159032424814389 2934487219889909289826349)
            ·
              refine ⟨1100432707458715983684881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2934487219889909289826349 1100432707458715983684881)
              ·
                refine ⟨825324530594036987763661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100432707458715983684881 825324530594036987763661)
                ·
                  refine ⟨309496698972763870411373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825324530594036987763661 309496698972763870411373)
                  ·
                    rfl

theorem cell21_1356171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 3].length) (baseStart_1356171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356171 prefixEnd_1356171 := by exact prefixLift 1356171
  have htrace : WordTrace (prefixWord ++ tailWord_1356171) baseStart_1356171 baseEnd_1356171 := by
    simpa [prefixWord, tailWord_1356171, baseEnd_1356171] using wordTrace_append hprefix tailTrace_1356171
  have hstable : (prefixWord ++ tailWord_1356171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356171).length < 2 ^ (prefixWord ++ tailWord_1356171).sum := by decide
  have hdescent : baseEnd_1356171 < baseStart_1356171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356272 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_1356272 : Nat := 118140960795 + 1356272 * 2 ^ 59
def prefixEnd_1356272 : Nat := 4983230072969 + 3 ^ 40 * 1356272 * 2
def baseEnd_1356272 : Nat := 309519748548810139227833

theorem tailTrace_1356272 : CollatzResearch.WordTrace tailWord_1356272 prefixEnd_1356272 309519748548810139227833 := by
  unfold tailWord_1356272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733651871232825830739535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32978202494977101107652713 24733651871232825830739535)
  ·
    refine ⟨37100477806849238746109303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24733651871232825830739535 37100477806849238746109303)
    ·
      refine ⟨55650716710273858119163955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37100477806849238746109303 55650716710273858119163955)
      ·
        refine ⟨83476075065410787178745933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55650716710273858119163955 83476075065410787178745933)
        ·
          refine ⟨31303528149529045192029725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83476075065410787178745933 31303528149529045192029725)
          ·
            refine ⟨11738823056073391947011147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31303528149529045192029725 11738823056073391947011147)
            ·
              refine ⟨17608234584110087920516721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11738823056073391947011147 17608234584110087920516721)
              ·
                refine ⟨13206175938082565940387541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17608234584110087920516721 13206175938082565940387541)
                ·
                  refine ⟨309519748548810139227833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13206175938082565940387541 309519748548810139227833)
                  ·
                    rfl

theorem cell21_1356272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_1356272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356272 prefixEnd_1356272 := by exact prefixLift 1356272
  have htrace : WordTrace (prefixWord ++ tailWord_1356272) baseStart_1356272 baseEnd_1356272 := by
    simpa [prefixWord, tailWord_1356272, baseEnd_1356272] using wordTrace_append hprefix tailTrace_1356272
  have hstable : (prefixWord ++ tailWord_1356272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356272).length < 2 ^ (prefixWord ++ tailWord_1356272).sum := by decide
  have hdescent : baseEnd_1356272 < baseStart_1356272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356289 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 5]
def baseStart_1356289 : Nat := 118140960795 + 1356289 * 2 ^ 59
def prefixEnd_1356289 : Nat := 4983230072969 + 3 ^ 40 * 1356289 * 2
def baseEnd_1356289 : Nat := 309523628180421887444465

theorem tailTrace_1356289 : CollatzResearch.WordTrace tailWord_1356289 prefixEnd_1356289 309523628180421887444465 := by
  unfold tailWord_1356289
  simp only [CollatzResearch.WordTrace]
  refine ⟨49467923783404063564847921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32978615855602709043231947 49467923783404063564847921)
  ·
    refine ⟨37100942837553047673635941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49467923783404063564847921 37100942837553047673635941)
    ·
      refine ⟨6956426782041196438806739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37100942837553047673635941 6956426782041196438806739)
      ·
        refine ⟨10434640173061794658210109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956426782041196438806739 10434640173061794658210109)
        ·
          refine ⟨3912990064898172996828791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10434640173061794658210109 3912990064898172996828791)
          ·
            refine ⟨5869485097347259495243187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912990064898172996828791 5869485097347259495243187)
            ·
              refine ⟨8804227646020889242864781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869485097347259495243187 8804227646020889242864781)
              ·
                refine ⟨3301585367257833466074293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8804227646020889242864781 3301585367257833466074293)
                ·
                  refine ⟨309523628180421887444465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301585367257833466074293 309523628180421887444465)
                  ·
                    rfl

theorem cell21_1356289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_1356289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356289 prefixEnd_1356289 := by exact prefixLift 1356289
  have htrace : WordTrace (prefixWord ++ tailWord_1356289) baseStart_1356289 baseEnd_1356289 := by
    simpa [prefixWord, tailWord_1356289, baseEnd_1356289] using wordTrace_append hprefix tailTrace_1356289
  have hstable : (prefixWord ++ tailWord_1356289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356289).length < 2 ^ (prefixWord ++ tailWord_1356289).sum := by decide
  have hdescent : baseEnd_1356289 < baseStart_1356289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356323 : List Nat := [1, 1, 1, 4, 4, 3, 1, 3, 3]
def baseStart_1356323 : Nat := 118140960795 + 1356323 * 2 ^ 59
def prefixEnd_1356323 : Nat := 4983230072969 + 3 ^ 40 * 1356323 * 2
def baseEnd_1356323 : Nat := 309531387443645383877729

theorem tailTrace_1356323 : CollatzResearch.WordTrace tailWord_1356323 prefixEnd_1356323 309531387443645383877729 := by
  unfold tailWord_1356323
  simp only [CollatzResearch.WordTrace]
  refine ⟨49469163865280887371585623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32979442576853924914390415 49469163865280887371585623)
  ·
    refine ⟨74203745797921331057378435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49469163865280887371585623 74203745797921331057378435)
    ·
      refine ⟨111305618696881996586067653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74203745797921331057378435 111305618696881996586067653)
      ·
        refine ⟨20869803505665374359887685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111305618696881996586067653 20869803505665374359887685)
        ·
          refine ⟨3913088157312257692478941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20869803505665374359887685 3913088157312257692478941)
          ·
            refine ⟨1467408058992096634679603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3913088157312257692478941 1467408058992096634679603)
            ·
              refine ⟨2201112088488144952019405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467408058992096634679603 2201112088488144952019405)
              ·
                refine ⟨825417033183054357007277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2201112088488144952019405 825417033183054357007277)
                ·
                  refine ⟨309531387443645383877729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 825417033183054357007277 309531387443645383877729)
                  ·
                    rfl

theorem cell21_1356323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3, 3].length) (baseStart_1356323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356323 prefixEnd_1356323 := by exact prefixLift 1356323
  have htrace : WordTrace (prefixWord ++ tailWord_1356323) baseStart_1356323 baseEnd_1356323 := by
    simpa [prefixWord, tailWord_1356323, baseEnd_1356323] using wordTrace_append hprefix tailTrace_1356323
  have hstable : (prefixWord ++ tailWord_1356323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356323).length < 2 ^ (prefixWord ++ tailWord_1356323).sum := by decide
  have hdescent : baseEnd_1356323 < baseStart_1356323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356340 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1356340 : Nat := 118140960795 + 1356340 * 2 ^ 59
def prefixEnd_1356340 : Nat := 4983230072969 + 3 ^ 40 * 1356340 * 2
def baseEnd_1356340 : Nat := 309535267075257132094361

theorem tailTrace_1356340 : CollatzResearch.WordTrace tailWord_1356340 prefixEnd_1356340 309535267075257132094361 := by
  unfold tailWord_1356340
  simp only [CollatzResearch.WordTrace]
  refine ⟨24734891953109649637477237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32979855937479532849969649 24734891953109649637477237)
  ·
    refine ⟨2318896120604029653513491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24734891953109649637477237 2318896120604029653513491)
    ·
      refine ⟨3478344180906044480270237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318896120604029653513491 3478344180906044480270237)
      ·
        refine ⟨1304379067839766680101339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3478344180906044480270237 1304379067839766680101339)
        ·
          refine ⟨1956568601759650020152009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304379067839766680101339 1956568601759650020152009)
          ·
            refine ⟨1467426451319737515114007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956568601759650020152009 1467426451319737515114007)
            ·
              refine ⟨2201139676979606272671011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467426451319737515114007 2201139676979606272671011)
              ·
                refine ⟨3301709515469409409006517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201139676979606272671011 3301709515469409409006517)
                ·
                  refine ⟨309535267075257132094361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301709515469409409006517 309535267075257132094361)
                  ·
                    rfl

theorem cell21_1356340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1356340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356340 prefixEnd_1356340 := by exact prefixLift 1356340
  have htrace : WordTrace (prefixWord ++ tailWord_1356340) baseStart_1356340 baseEnd_1356340 := by
    simpa [prefixWord, tailWord_1356340, baseEnd_1356340] using wordTrace_append hprefix tailTrace_1356340
  have hstable : (prefixWord ++ tailWord_1356340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356340).length < 2 ^ (prefixWord ++ tailWord_1356340).sum := by decide
  have hdescent : baseEnd_1356340 < baseStart_1356340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356517 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 5]
def baseStart_1356517 : Nat := 118140960795 + 1356517 * 2 ^ 59
def prefixEnd_1356517 : Nat := 4983230072969 + 3 ^ 40 * 1356517 * 2
def baseEnd_1356517 : Nat := 309575660886744157643999

theorem tailTrace_1356517 : CollatzResearch.WordTrace tailWord_1356517 prefixEnd_1356517 309575660886744157643999 := by
  unfold tailWord_1356517
  simp only [CollatzResearch.WordTrace]
  refine ⟨49476239626578058504147805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32984159751052039002765203 49476239626578058504147805)
  ·
    refine ⟨18553589859966771939055427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49476239626578058504147805 18553589859966771939055427)
    ·
      refine ⟨27830384789950157908583141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18553589859966771939055427 27830384789950157908583141)
      ·
        refine ⟨5218197148115654607859339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27830384789950157908583141 5218197148115654607859339)
        ·
          refine ⟨7827295722173481911789009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218197148115654607859339 7827295722173481911789009)
          ·
            refine ⟨5870471791630111433841757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7827295722173481911789009 5870471791630111433841757)
            ·
              refine ⟨2201426921861291787690659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5870471791630111433841757 2201426921861291787690659)
              ·
                refine ⟨3302140382791937681535989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201426921861291787690659 3302140382791937681535989)
                ·
                  refine ⟨309575660886744157643999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3302140382791937681535989 309575660886744157643999)
                  ·
                    rfl

theorem cell21_1356517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_1356517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356517 prefixEnd_1356517 := by exact prefixLift 1356517
  have htrace : WordTrace (prefixWord ++ tailWord_1356517) baseStart_1356517 baseEnd_1356517 := by
    simpa [prefixWord, tailWord_1356517, baseEnd_1356517] using wordTrace_append hprefix tailTrace_1356517
  have hstable : (prefixWord ++ tailWord_1356517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356517).length < 2 ^ (prefixWord ++ tailWord_1356517).sum := by decide
  have hdescent : baseEnd_1356517 < baseStart_1356517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356562 : List Nat := [3, 2, 4, 1, 11]
def baseStart_1356562 : Nat := 118140960795 + 1356562 * 2 ^ 59
def prefixEnd_1356562 : Nat := 4983230072969 + 3 ^ 40 * 1356562 * 2
def baseEnd_1356562 : Nat := 3822048524689309622147

theorem tailTrace_1356562 : CollatzResearch.WordTrace tailWord_1356562 prefixEnd_1356562 3822048524689309622147 := by
  unfold tailWord_1356562
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369470227853757797383985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32985253940943354126357293 12369470227853757797383985)
  ·
    refine ⟨9277102670890318348037989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12369470227853757797383985 9277102670890318348037989)
    ·
      refine ⟨1739456750791934690257123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9277102670890318348037989 1739456750791934690257123)
      ·
        refine ⟨2609185126187902035385685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739456750791934690257123 2609185126187902035385685)
        ·
          refine ⟨3822048524689309622147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2609185126187902035385685 3822048524689309622147)
          ·
            rfl

theorem cell21_1356562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 11].length) (baseStart_1356562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356562 prefixEnd_1356562 := by exact prefixLift 1356562
  have htrace : WordTrace (prefixWord ++ tailWord_1356562) baseStart_1356562 baseEnd_1356562 := by
    simpa [prefixWord, tailWord_1356562, baseEnd_1356562] using wordTrace_append hprefix tailTrace_1356562
  have hstable : (prefixWord ++ tailWord_1356562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356562).length < 2 ^ (prefixWord ++ tailWord_1356562).sum := by decide
  have hdescent : baseEnd_1356562 < baseStart_1356562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356596 : List Nat := [2, 5, 1, 1, 3, 1, 3, 5]
def baseStart_1356596 : Nat := 118140960795 + 1356596 * 2 ^ 59
def prefixEnd_1356596 : Nat := 4983230072969 + 3 ^ 40 * 1356596 * 2
def baseEnd_1356596 : Nat := 103197896587685858609057

theorem tailTrace_1356596 : CollatzResearch.WordTrace tailWord_1356596 prefixEnd_1356596 103197896587685858609057 := by
  unfold tailWord_1356596
  simp only [CollatzResearch.WordTrace]
  refine ⟨24739560496645927498136821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32986080662194569997515761 24739560496645927498136821)
  ·
    refine ⟨2319333796560555702950327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24739560496645927498136821 2319333796560555702950327)
    ·
      refine ⟨3479000694840833554425491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319333796560555702950327 3479000694840833554425491)
      ·
        refine ⟨5218501042261250331638237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479000694840833554425491 5218501042261250331638237)
        ·
          refine ⟨1956937890847968874364339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5218501042261250331638237 1956937890847968874364339)
          ·
            refine ⟨2935406836271953311546509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956937890847968874364339 2935406836271953311546509)
            ·
              refine ⟨1100777563601982491829941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2935406836271953311546509 1100777563601982491829941)
              ·
                refine ⟨103197896587685858609057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100777563601982491829941 103197896587685858609057)
                ·
                  rfl

theorem cell21_1356596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_1356596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356596 prefixEnd_1356596 := by exact prefixLift 1356596
  have htrace : WordTrace (prefixWord ++ tailWord_1356596) baseStart_1356596 baseEnd_1356596 := by
    simpa [prefixWord, tailWord_1356596, baseEnd_1356596] using wordTrace_append hprefix tailTrace_1356596
  have hstable : (prefixWord ++ tailWord_1356596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356596).length < 2 ^ (prefixWord ++ tailWord_1356596).sum := by decide
  have hdescent : baseEnd_1356596 < baseStart_1356596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356652 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1356652 : Nat := 118140960795 + 1356652 * 2 ^ 59
def prefixEnd_1356652 : Nat := 4983230072969 + 3 ^ 40 * 1356652 * 2
def baseEnd_1356652 : Nat := 309606469726013922893723

theorem tailTrace_1356652 : CollatzResearch.WordTrace tailWord_1356652 prefixEnd_1356652 309606469726013922893723 := by
  unfold tailWord_1356652
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740581740544488280156105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32987442320725984373541473 24740581740544488280156105)
  ·
    refine ⟨18555436305408366210117079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24740581740544488280156105 18555436305408366210117079)
    ·
      refine ⟨27833154458112549315175619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18555436305408366210117079 27833154458112549315175619)
      ·
        refine ⟨41749731687168823972763429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27833154458112549315175619 41749731687168823972763429)
        ·
          refine ⟨7828074691344154494893143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41749731687168823972763429 7828074691344154494893143)
          ·
            refine ⟨11742112037016231742339715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7828074691344154494893143 11742112037016231742339715)
            ·
              refine ⟨17613168055524347613509573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742112037016231742339715 17613168055524347613509573)
              ·
                refine ⟨3302469010410815177533045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17613168055524347613509573 3302469010410815177533045)
                ·
                  refine ⟨309606469726013922893723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3302469010410815177533045 309606469726013922893723)
                  ·
                    rfl

theorem cell21_1356652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1356652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356652 prefixEnd_1356652 := by exact prefixLift 1356652
  have htrace : WordTrace (prefixWord ++ tailWord_1356652) baseStart_1356652 baseEnd_1356652 := by
    simpa [prefixWord, tailWord_1356652, baseEnd_1356652] using wordTrace_append hprefix tailTrace_1356652
  have hstable : (prefixWord ++ tailWord_1356652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356652).length < 2 ^ (prefixWord ++ tailWord_1356652).sum := by decide
  have hdescent : baseEnd_1356652 < baseStart_1356652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356790 : List Nat := [5, 1, 1, 1, 3, 2, 8]
def baseStart_1356790 : Nat := 118140960795 + 1356790 * 2 ^ 59
def prefixEnd_1356790 : Nat := 4983230072969 + 3 ^ 40 * 1356790 * 2
def baseEnd_1356790 : Nat := 34404218134017372177049

theorem tailTrace_1356790 : CollatzResearch.WordTrace tailWord_1356790 prefixEnd_1356790 34404218134017372177049 := by
  unfold tailWord_1356790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092887297161814133052239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32990797836392684085890549 3092887297161814133052239)
  ·
    refine ⟨4639330945742721199578359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092887297161814133052239 4639330945742721199578359)
    ·
      refine ⟨6958996418614081799367539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639330945742721199578359 6958996418614081799367539)
      ·
        refine ⟨10438494627921122699051309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958996418614081799367539 10438494627921122699051309)
        ·
          refine ⟨3914435485470421012144241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10438494627921122699051309 3914435485470421012144241)
          ·
            refine ⟨2935826614102815759108181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3914435485470421012144241 2935826614102815759108181)
            ·
              refine ⟨34404218134017372177049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2935826614102815759108181 34404218134017372177049)
              ·
                rfl

theorem cell21_1356790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 8].length) (baseStart_1356790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356790 prefixEnd_1356790 := by exact prefixLift 1356790
  have htrace : WordTrace (prefixWord ++ tailWord_1356790) baseStart_1356790 baseEnd_1356790 := by
    simpa [prefixWord, tailWord_1356790, baseEnd_1356790] using wordTrace_append hprefix tailTrace_1356790
  have hstable : (prefixWord ++ tailWord_1356790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356790).length < 2 ^ (prefixWord ++ tailWord_1356790).sum := by decide
  have hdescent : baseEnd_1356790 < baseStart_1356790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356852 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1356852 : Nat := 118140960795 + 1356852 * 2 ^ 59
def prefixEnd_1356852 : Nat := 4983230072969 + 3 ^ 40 * 1356852 * 2
def baseEnd_1356852 : Nat := 309652112450858019559981

theorem tailTrace_1356852 : CollatzResearch.WordTrace tailWord_1356852 prefixEnd_1356852 309652112450858019559981 := by
  unfold tailWord_1356852
  simp only [CollatzResearch.WordTrace]
  refine ⟨24744229040182205358796405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32992305386909607145061873 24744229040182205358796405)
  ·
    refine ⟨2319771472517081752387163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24744229040182205358796405 2319771472517081752387163)
    ·
      refine ⟨3479657208775622628580745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319771472517081752387163 3479657208775622628580745)
      ·
        refine ⟨2609742906581716971435559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479657208775622628580745 2609742906581716971435559)
        ·
          refine ⟨3914614359872575457153339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609742906581716971435559 3914614359872575457153339)
          ·
            refine ⟨5871921539808863185730009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914614359872575457153339 5871921539808863185730009)
            ·
              refine ⟨4403941154856647389297507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871921539808863185730009 4403941154856647389297507)
              ·
                refine ⟨6605911732284971083946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403941154856647389297507 6605911732284971083946261)
                ·
                  refine ⟨309652112450858019559981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6605911732284971083946261 309652112450858019559981)
                  ·
                    rfl

theorem cell21_1356852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1356852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356852 prefixEnd_1356852 := by exact prefixLift 1356852
  have htrace : WordTrace (prefixWord ++ tailWord_1356852) baseStart_1356852 baseEnd_1356852 := by
    simpa [prefixWord, tailWord_1356852, baseEnd_1356852] using wordTrace_append hprefix tailTrace_1356852
  have hstable : (prefixWord ++ tailWord_1356852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356852).length < 2 ^ (prefixWord ++ tailWord_1356852).sum := by decide
  have hdescent : baseEnd_1356852 < baseStart_1356852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356911 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 4]
def baseStart_1356911 : Nat := 118140960795 + 1356911 * 2 ^ 59
def prefixEnd_1356911 : Nat := 4983230072969 + 3 ^ 40 * 1356911 * 2
def baseEnd_1356911 : Nat := 309665577054687028076527

theorem tailTrace_1356911 : CollatzResearch.WordTrace tailWord_1356911 prefixEnd_1356911 309665577054687028076527 := by
  unfold tailWord_1356911
  simp only [CollatzResearch.WordTrace]
  refine ⟨49490609987150663793990587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32993739991433775862660391 49490609987150663793990587)
  ·
    refine ⟨74235914980725995690985881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49490609987150663793990587 74235914980725995690985881)
    ·
      refine ⟨55676936235544496768239411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74235914980725995690985881 55676936235544496768239411)
      ·
        refine ⟨83515404353316745152359117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55676936235544496768239411 83515404353316745152359117)
        ·
          refine ⟨31318276632493779432134669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83515404353316745152359117 31318276632493779432134669)
          ·
            refine ⟨11744353737185167287050501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31318276632493779432134669 11744353737185167287050501)
            ·
              refine ⟨2202066325722218866321969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11744353737185167287050501 2202066325722218866321969)
              ·
                refine ⟨1651549744291664149741477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202066325722218866321969 1651549744291664149741477)
                ·
                  refine ⟨309665577054687028076527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651549744291664149741477 309665577054687028076527)
                  ·
                    rfl

theorem cell21_1356911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 4].length) (baseStart_1356911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356911 prefixEnd_1356911 := by exact prefixLift 1356911
  have htrace : WordTrace (prefixWord ++ tailWord_1356911) baseStart_1356911 baseEnd_1356911 := by
    simpa [prefixWord, tailWord_1356911, baseEnd_1356911] using wordTrace_append hprefix tailTrace_1356911
  have hstable : (prefixWord ++ tailWord_1356911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356911).length < 2 ^ (prefixWord ++ tailWord_1356911).sum := by decide
  have hdescent : baseEnd_1356911 < baseStart_1356911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1356962 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_1356962 : Nat := 118140960795 + 1356962 * 2 ^ 59
def prefixEnd_1356962 : Nat := 4983230072969 + 3 ^ 40 * 1356962 * 2
def baseEnd_1356962 : Nat := 309677215949522272726423

theorem tailTrace_1356962 : CollatzResearch.WordTrace tailWord_1356962 prefixEnd_1356962 309677215949522272726423 := by
  unfold tailWord_1356962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12373117527491474876024285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32994980073310599669398093 12373117527491474876024285)
  ·
    refine ⟨4639919072809303078509107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12373117527491474876024285 4639919072809303078509107)
    ·
      refine ⟨6959878609213954617763661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4639919072809303078509107 6959878609213954617763661)
      ·
        refine ⟨2609954478455232981661373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6959878609213954617763661 2609954478455232981661373)
        ·
          refine ⟨978732929420712368123015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2609954478455232981661373 978732929420712368123015)
          ·
            refine ⟨1468099394131068552184523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978732929420712368123015 1468099394131068552184523)
            ·
              refine ⟨2202149091196602828276785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468099394131068552184523 2202149091196602828276785)
              ·
                refine ⟨1651611818397452121207589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202149091196602828276785 1651611818397452121207589)
                ·
                  refine ⟨309677215949522272726423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651611818397452121207589 309677215949522272726423)
                  ·
                    rfl

theorem cell21_1356962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_1356962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1356962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1356962 prefixEnd_1356962 := by exact prefixLift 1356962
  have htrace : WordTrace (prefixWord ++ tailWord_1356962) baseStart_1356962 baseEnd_1356962 := by
    simpa [prefixWord, tailWord_1356962, baseEnd_1356962] using wordTrace_append hprefix tailTrace_1356962
  have hstable : (prefixWord ++ tailWord_1356962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1356962).length < 2 ^ (prefixWord ++ tailWord_1356962).sum := by decide
  have hdescent : baseEnd_1356962 < baseStart_1356962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1356962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357015 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 7]
def baseStart_1357015 : Nat := 118140960795 + 1357015 * 2 ^ 59
def prefixEnd_1357015 : Nat := 4983230072969 + 3 ^ 40 * 1357015 * 2
def baseEnd_1357015 : Nat := 309689311271605958342981

theorem tailTrace_1357015 : CollatzResearch.WordTrace tailWord_1357015 prefixEnd_1357015 309689311271605958342981 := by
  unfold tailWord_1357015
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494403178773889555776499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32996268785849259703850999 49494403178773889555776499)
  ·
    refine ⟨74241604768160834333664749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49494403178773889555776499 74241604768160834333664749)
    ·
      refine ⟨27840601788060312875124281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74241604768160834333664749 27840601788060312875124281)
      ·
        refine ⟨20880451341045234656343211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27840601788060312875124281 20880451341045234656343211)
        ·
          refine ⟨31320677011567851984514817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20880451341045234656343211 31320677011567851984514817)
          ·
            refine ⟨23490507758675888988386113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31320677011567851984514817 23490507758675888988386113)
            ·
              refine ⟨17617880819006916741289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23490507758675888988386113 17617880819006916741289585)
              ·
                refine ⟨13213410614255187555967189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17617880819006916741289585 13213410614255187555967189)
                ·
                  refine ⟨309689311271605958342981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13213410614255187555967189 309689311271605958342981)
                  ·
                    rfl

theorem cell21_1357015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 7].length) (baseStart_1357015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357015 prefixEnd_1357015 := by exact prefixLift 1357015
  have htrace : WordTrace (prefixWord ++ tailWord_1357015) baseStart_1357015 baseEnd_1357015 := by
    simpa [prefixWord, tailWord_1357015, baseEnd_1357015] using wordTrace_append hprefix tailTrace_1357015
  have hstable : (prefixWord ++ tailWord_1357015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357015).length < 2 ^ (prefixWord ++ tailWord_1357015).sum := by decide
  have hdescent : baseEnd_1357015 < baseStart_1357015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357136 : List Nat := [2, 1, 1, 1, 1, 5, 10]
def baseStart_1357136 : Nat := 118140960795 + 1357136 * 2 ^ 59
def prefixEnd_1357136 : Nat := 4983230072969 + 3 ^ 40 * 1357136 * 2
def baseEnd_1357136 : Nat := 34412991680015181869563

theorem tailTrace_1357136 : CollatzResearch.WordTrace tailWord_1357136 prefixEnd_1357136 34412991680015181869563 := by
  unfold tailWord_1357136
  simp only [CollatzResearch.WordTrace]
  refine ⟨24749408205667763610465631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32999210940890351480620841 24749408205667763610465631)
  ·
    refine ⟨37124112308501645415698447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24749408205667763610465631 37124112308501645415698447)
    ·
      refine ⟨55686168462752468123547671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37124112308501645415698447 55686168462752468123547671)
      ·
        refine ⟨83529252694128702185321507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55686168462752468123547671 83529252694128702185321507)
        ·
          refine ⟨125293879041193053277982261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83529252694128702185321507 125293879041193053277982261)
          ·
            refine ⟨11746301160111848744810837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125293879041193053277982261 11746301160111848744810837)
            ·
              refine ⟨34412991680015181869563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11746301160111848744810837 34412991680015181869563)
              ·
                rfl

theorem cell21_1357136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 10].length) (baseStart_1357136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357136 prefixEnd_1357136 := by exact prefixLift 1357136
  have htrace : WordTrace (prefixWord ++ tailWord_1357136) baseStart_1357136 baseEnd_1357136 := by
    simpa [prefixWord, tailWord_1357136, baseEnd_1357136] using wordTrace_append hprefix tailTrace_1357136
  have hstable : (prefixWord ++ tailWord_1357136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357136).length < 2 ^ (prefixWord ++ tailWord_1357136).sum := by decide
  have hdescent : baseEnd_1357136 < baseStart_1357136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357156 : List Nat := [2, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1357156 : Nat := 118140960795 + 1357156 * 2 ^ 59
def prefixEnd_1357156 : Nat := 4983230072969 + 3 ^ 40 * 1357156 * 2
def baseEnd_1357156 : Nat := 309721489392621046492693

theorem tailTrace_1357156 : CollatzResearch.WordTrace tailWord_1357156 prefixEnd_1357156 309721489392621046492693 := by
  unfold tailWord_1357156
  simp only [CollatzResearch.WordTrace]
  refine ⟨24749772935631535318329661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32999697247508713757772881 24749772935631535318329661)
  ·
    refine ⟨9281164850861825744373623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24749772935631535318329661 9281164850861825744373623)
    ·
      refine ⟨13921747276292738616560435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9281164850861825744373623 13921747276292738616560435)
      ·
        refine ⟨20882620914439107924840653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921747276292738616560435 20882620914439107924840653)
        ·
          refine ⟨7830982842914665471815245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20882620914439107924840653 7830982842914665471815245)
          ·
            refine ⟨2936618566092999551930717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7830982842914665471815245 2936618566092999551930717)
            ·
              refine ⟨1101231962284874831974019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2936618566092999551930717 1101231962284874831974019)
              ·
                refine ⟨1651847943427312247961029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101231962284874831974019 1651847943427312247961029)
                ·
                  refine ⟨309721489392621046492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651847943427312247961029 309721489392621046492693)
                  ·
                    rfl

theorem cell21_1357156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1357156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357156 prefixEnd_1357156 := by exact prefixLift 1357156
  have htrace : WordTrace (prefixWord ++ tailWord_1357156) baseStart_1357156 baseEnd_1357156 := by
    simpa [prefixWord, tailWord_1357156, baseEnd_1357156] using wordTrace_append hprefix tailTrace_1357156
  have hstable : (prefixWord ++ tailWord_1357156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357156).length < 2 ^ (prefixWord ++ tailWord_1357156).sum := by decide
  have hdescent : baseEnd_1357156 < baseStart_1357156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357167 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 5]
def baseStart_1357167 : Nat := 118140960795 + 1357167 * 2 ^ 59
def prefixEnd_1357167 : Nat := 4983230072969 + 3 ^ 40 * 1357167 * 2
def baseEnd_1357167 : Nat := 309723999742487471809337

theorem tailTrace_1357167 : CollatzResearch.WordTrace tailWord_1357167 prefixEnd_1357167 309723999742487471809337 := by
  unfold tailWord_1357167
  simp only [CollatzResearch.WordTrace]
  refine ⟨49499947074223219515309755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32999964716148813010206503 49499947074223219515309755)
  ·
    refine ⟨74249920611334829272964633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49499947074223219515309755 74249920611334829272964633)
    ·
      refine ⟨55687440458501121954723475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74249920611334829272964633 55687440458501121954723475)
      ·
        refine ⟨83531160687751682932085213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55687440458501121954723475 83531160687751682932085213)
        ·
          refine ⟨31324185257906881099531955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83531160687751682932085213 31324185257906881099531955)
          ·
            refine ⟨46986277886860321649297933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31324185257906881099531955 46986277886860321649297933)
            ·
              refine ⟨17619854207572620618486725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46986277886860321649297933 17619854207572620618486725)
              ·
                refine ⟨3303722663919866365966261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17619854207572620618486725 3303722663919866365966261)
                ·
                  refine ⟨309723999742487471809337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3303722663919866365966261 309723999742487471809337)
                  ·
                    rfl

theorem cell21_1357167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 5].length) (baseStart_1357167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357167 prefixEnd_1357167 := by exact prefixLift 1357167
  have htrace : WordTrace (prefixWord ++ tailWord_1357167) baseStart_1357167 baseEnd_1357167 := by
    simpa [prefixWord, tailWord_1357167, baseEnd_1357167] using wordTrace_append hprefix tailTrace_1357167
  have hstable : (prefixWord ++ tailWord_1357167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357167).length < 2 ^ (prefixWord ++ tailWord_1357167).sum := by decide
  have hdescent : baseEnd_1357167 < baseStart_1357167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357215 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 4]
def baseStart_1357215 : Nat := 118140960795 + 1357215 * 2 ^ 59
def prefixEnd_1357215 : Nat := 4983230072969 + 3 ^ 40 * 1357215 * 2
def baseEnd_1357215 : Nat := 309734953996450055009239

theorem tailTrace_1357215 : CollatzResearch.WordTrace tailWord_1357215 prefixEnd_1357215 309734953996450055009239 := by
  unfold tailWord_1357215
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501697778049323713057099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33001131852032882475371399 49501697778049323713057099)
  ·
    refine ⟨74252546667073985569585649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49501697778049323713057099 74252546667073985569585649)
    ·
      refine ⟨55689410000305489177189237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74252546667073985569585649 55689410000305489177189237)
      ·
        refine ⟨5220882187528639610361491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55689410000305489177189237 5220882187528639610361491)
        ·
          refine ⟨7831323281292959415542237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220882187528639610361491 7831323281292959415542237)
          ·
            refine ⟨2936746230484859780828339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7831323281292959415542237 2936746230484859780828339)
            ·
              refine ⟨4405119345727289671242509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936746230484859780828339 4405119345727289671242509)
              ·
                refine ⟨1651919754647733626715941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405119345727289671242509 1651919754647733626715941)
                ·
                  refine ⟨309734953996450055009239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651919754647733626715941 309734953996450055009239)
                  ·
                    rfl

theorem cell21_1357215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 4].length) (baseStart_1357215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357215 prefixEnd_1357215 := by exact prefixLift 1357215
  have htrace : WordTrace (prefixWord ++ tailWord_1357215) baseStart_1357215 baseEnd_1357215 := by
    simpa [prefixWord, tailWord_1357215, baseEnd_1357215] using wordTrace_append hprefix tailTrace_1357215
  have hstable : (prefixWord ++ tailWord_1357215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357215).length < 2 ^ (prefixWord ++ tailWord_1357215).sum := by decide
  have hdescent : baseEnd_1357215 < baseStart_1357215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357474 : List Nat := [3, 3, 1, 4, 1, 1, 8]
def baseStart_1357474 : Nat := 118140960795 + 1357474 * 2 ^ 59
def prefixEnd_1357474 : Nat := 4983230072969 + 3 ^ 40 * 1357474 * 2
def baseEnd_1357474 : Nat := 34421562369458128910227

theorem tailTrace_1357474 : CollatzResearch.WordTrace tailWord_1357474 prefixEnd_1357474 34421562369458128910227 := by
  unfold tailWord_1357474
  simp only [CollatzResearch.WordTrace]
  refine ⟨12377786071027752736683869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33007429522740673964490317 12377786071027752736683869)
  ·
    refine ⟨4641669776635407276256451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12377786071027752736683869 4641669776635407276256451)
    ·
      refine ⟨6962504664953110914384677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641669776635407276256451 6962504664953110914384677)
      ·
        refine ⟨1305469624678708296447127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6962504664953110914384677 1305469624678708296447127)
        ·
          refine ⟨1958204437018062444670691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305469624678708296447127 1958204437018062444670691)
          ·
            refine ⟨2937306655527093667006037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958204437018062444670691 2937306655527093667006037)
            ·
              refine ⟨34421562369458128910227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2937306655527093667006037 34421562369458128910227)
              ·
                rfl

theorem cell21_1357474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 8].length) (baseStart_1357474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357474 prefixEnd_1357474 := by exact prefixLift 1357474
  have htrace : WordTrace (prefixWord ++ tailWord_1357474) baseStart_1357474 baseEnd_1357474 := by
    simpa [prefixWord, tailWord_1357474, baseEnd_1357474] using wordTrace_append hprefix tailTrace_1357474
  have hstable : (prefixWord ++ tailWord_1357474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357474).length < 2 ^ (prefixWord ++ tailWord_1357474).sum := by decide
  have hdescent : baseEnd_1357474 < baseStart_1357474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357488 : List Nat := [2, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_1357488 : Nat := 118140960795 + 1357488 * 2 ^ 59
def prefixEnd_1357488 : Nat := 4983230072969 + 3 ^ 40 * 1357488 * 2
def baseEnd_1357488 : Nat := 309797256315862246958681

theorem tailTrace_1357488 : CollatzResearch.WordTrace tailWord_1357488 prefixEnd_1357488 309797256315862246958681 := by
  unfold tailWord_1357488
  simp only [CollatzResearch.WordTrace]
  refine ⟨24755827453030145668872559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33007769937373527558496745 24755827453030145668872559)
  ·
    refine ⟨37133741179545218503308839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24755827453030145668872559 37133741179545218503308839)
    ·
      refine ⟨55700611769317827754963259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37133741179545218503308839 55700611769317827754963259)
      ·
        refine ⟨83550917653976741632444889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55700611769317827754963259 83550917653976741632444889)
        ·
          refine ⟨62663188240482556224333667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83550917653976741632444889 62663188240482556224333667)
          ·
            refine ⟨93994782360723834336500501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62663188240482556224333667 93994782360723834336500501)
            ·
              refine ⟨4406005423158929734523461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93994782360723834336500501 4406005423158929734523461)
              ·
                refine ⟨826126016842299325223149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4406005423158929734523461 826126016842299325223149)
                ·
                  refine ⟨309797256315862246958681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826126016842299325223149 309797256315862246958681)
                  ·
                    rfl

theorem cell21_1357488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_1357488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357488 prefixEnd_1357488 := by exact prefixLift 1357488
  have htrace : WordTrace (prefixWord ++ tailWord_1357488) baseStart_1357488 baseEnd_1357488 := by
    simpa [prefixWord, tailWord_1357488, baseEnd_1357488] using wordTrace_append hprefix tailTrace_1357488
  have hstable : (prefixWord ++ tailWord_1357488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357488).length < 2 ^ (prefixWord ++ tailWord_1357488).sum := by decide
  have hdescent : baseEnd_1357488 < baseStart_1357488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357522 : List Nat := [3, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_1357522 : Nat := 118140960795 + 1357522 * 2 ^ 59
def prefixEnd_1357522 : Nat := 4983230072969 + 3 ^ 40 * 1357522 * 2
def baseEnd_1357522 : Nat := 309805015579085743391945

theorem tailTrace_1357522 : CollatzResearch.WordTrace tailWord_1357522 prefixEnd_1357522 309805015579085743391945 := by
  unfold tailWord_1357522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378223746984278786120705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33008596658624743429655213 12378223746984278786120705)
  ·
    refine ⟨9283667810238209089590529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12378223746984278786120705 9283667810238209089590529)
    ·
      refine ⟨6962750857678656817192897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9283667810238209089590529 6962750857678656817192897)
      ·
        refine ⟨5222063143258992612894673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6962750857678656817192897 5222063143258992612894673)
        ·
          refine ⟨3916547357444244459671005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5222063143258992612894673 3916547357444244459671005)
          ·
            refine ⟨1468705259041591672376627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3916547357444244459671005 1468705259041591672376627)
            ·
              refine ⟨2203057888562387508564941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468705259041591672376627 2203057888562387508564941)
              ·
                refine ⟨826146708210895315711853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2203057888562387508564941 826146708210895315711853)
                ·
                  refine ⟨309805015579085743391945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826146708210895315711853 309805015579085743391945)
                  ·
                    rfl

theorem cell21_1357522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_1357522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357522 prefixEnd_1357522 := by exact prefixLift 1357522
  have htrace : WordTrace (prefixWord ++ tailWord_1357522) baseStart_1357522 baseEnd_1357522 := by
    simpa [prefixWord, tailWord_1357522, baseEnd_1357522] using wordTrace_append hprefix tailTrace_1357522
  have hstable : (prefixWord ++ tailWord_1357522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357522).length < 2 ^ (prefixWord ++ tailWord_1357522).sum := by decide
  have hdescent : baseEnd_1357522 < baseStart_1357522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357547 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 5]
def baseStart_1357547 : Nat := 118140960795 + 1357547 * 2 ^ 59
def prefixEnd_1357547 : Nat := 4983230072969 + 3 ^ 40 * 1357547 * 2
def baseEnd_1357547 : Nat := 309810720919691255475227

theorem tailTrace_1357547 : CollatzResearch.WordTrace tailWord_1357547 prefixEnd_1357547 309810720919691255475227 := by
  unfold tailWord_1357547
  simp only [CollatzResearch.WordTrace]
  refine ⟨49513806812846544414142895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33009204541897696276095263 49513806812846544414142895)
  ·
    refine ⟨74270710219269816621214343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49513806812846544414142895 74270710219269816621214343)
    ·
      refine ⟨111406065328904724931821515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74270710219269816621214343 111406065328904724931821515)
      ·
        refine ⟨167109097993357087397732273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111406065328904724931821515 167109097993357087397732273)
        ·
          refine ⟨125331823495017815548299205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167109097993357087397732273 125331823495017815548299205)
          ·
            refine ⟨23499716905315840415306101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125331823495017815548299205 23499716905315840415306101)
            ·
              refine ⟨2203098459873360038934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23499716905315840415306101 2203098459873360038934947)
              ·
                refine ⟨3304647689810040058402421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203098459873360038934947 3304647689810040058402421)
                ·
                  refine ⟨309810720919691255475227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304647689810040058402421 309810720919691255475227)
                  ·
                    rfl

theorem cell21_1357547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 5].length) (baseStart_1357547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357547 prefixEnd_1357547 := by exact prefixLift 1357547
  have htrace : WordTrace (prefixWord ++ tailWord_1357547) baseStart_1357547 baseEnd_1357547 := by
    simpa [prefixWord, tailWord_1357547, baseEnd_1357547] using wordTrace_append hprefix tailTrace_1357547
  have hstable : (prefixWord ++ tailWord_1357547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357547).length < 2 ^ (prefixWord ++ tailWord_1357547).sum := by decide
  have hdescent : baseEnd_1357547 < baseStart_1357547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357637 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 6]
def baseStart_1357637 : Nat := 118140960795 + 1357637 * 2 ^ 59
def prefixEnd_1357637 : Nat := 4983230072969 + 3 ^ 40 * 1357637 * 2
def baseEnd_1357637 : Nat := 309831260145871098975043

theorem tailTrace_1357637 : CollatzResearch.WordTrace tailWord_1357637 prefixEnd_1357637 309831260145871098975043 := by
  unfold tailWord_1357637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49517089382520489784919165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33011392921680326523279443 49517089382520489784919165)
  ·
    refine ⟨18568908518445183669344687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49517089382520489784919165 18568908518445183669344687)
    ·
      refine ⟨27853362777667775504017031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18568908518445183669344687 27853362777667775504017031)
      ·
        refine ⟨41780044166501663256025547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27853362777667775504017031 41780044166501663256025547)
        ·
          refine ⟨62670066249752494884038321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41780044166501663256025547 62670066249752494884038321)
          ·
            refine ⟨47002549687314371163028741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62670066249752494884038321 47002549687314371163028741)
            ·
              refine ⟨8812978066371444593067889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47002549687314371163028741 8812978066371444593067889)
              ·
                refine ⟨6609733549778583444800917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8812978066371444593067889 6609733549778583444800917)
                ·
                  refine ⟨309831260145871098975043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6609733549778583444800917 309831260145871098975043)
                  ·
                    rfl

theorem cell21_1357637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_1357637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357637 prefixEnd_1357637 := by exact prefixLift 1357637
  have htrace : WordTrace (prefixWord ++ tailWord_1357637) baseStart_1357637 baseEnd_1357637 := by
    simpa [prefixWord, tailWord_1357637, baseEnd_1357637] using wordTrace_append hprefix tailTrace_1357637
  have hstable : (prefixWord ++ tailWord_1357637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357637).length < 2 ^ (prefixWord ++ tailWord_1357637).sum := by decide
  have hdescent : baseEnd_1357637 < baseStart_1357637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357640 : List Nat := [2, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_1357640 : Nat := 118140960795 + 1357640 * 2 ^ 59
def prefixEnd_1357640 : Nat := 4983230072969 + 3 ^ 40 * 1357640 * 2
def baseEnd_1357640 : Nat := 309831944786743760425037

theorem tailTrace_1357640 : CollatzResearch.WordTrace tailWord_1357640 prefixEnd_1357640 309831944786743760425037 := by
  unfold tailWord_1357640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758599400754810648639187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33011465867673080864852249 24758599400754810648639187)
  ·
    refine ⟨37137899101132215972958781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24758599400754810648639187 37137899101132215972958781)
    ·
      refine ⟨13926712162924580989859543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37137899101132215972958781 13926712162924580989859543)
      ·
        refine ⟨20890068244386871484789315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13926712162924580989859543 20890068244386871484789315)
        ·
          refine ⟨31335102366580307227183973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890068244386871484789315 31335102366580307227183973)
          ·
            refine ⟨5875331693733807605096995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31335102366580307227183973 5875331693733807605096995)
            ·
              refine ⟨8812997540600711407645493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875331693733807605096995 8812997540600711407645493)
              ·
                refine ⟨826218519431316694466765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8812997540600711407645493 826218519431316694466765)
                ·
                  refine ⟨309831944786743760425037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826218519431316694466765 309831944786743760425037)
                  ·
                    rfl

theorem cell21_1357640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_1357640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357640 prefixEnd_1357640 := by exact prefixLift 1357640
  have htrace : WordTrace (prefixWord ++ tailWord_1357640) baseStart_1357640 baseEnd_1357640 := by
    simpa [prefixWord, tailWord_1357640, baseEnd_1357640] using wordTrace_append hprefix tailTrace_1357640
  have hstable : (prefixWord ++ tailWord_1357640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357640).length < 2 ^ (prefixWord ++ tailWord_1357640).sum := by decide
  have hdescent : baseEnd_1357640 < baseStart_1357640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357671 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 4]
def baseStart_1357671 : Nat := 118140960795 + 1357671 * 2 ^ 59
def prefixEnd_1357671 : Nat := 4983230072969 + 3 ^ 40 * 1357671 * 2
def baseEnd_1357671 : Nat := 309839019409094595408307

theorem tailTrace_1357671 : CollatzResearch.WordTrace tailWord_1357671 prefixEnd_1357671 309839019409094595408307 := by
  unfold tailWord_1357671
  simp only [CollatzResearch.WordTrace]
  refine ⟨49518329464397313591656867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33012219642931542394437911 49518329464397313591656867)
  ·
    refine ⟨74277494196595970387485301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49518329464397313591656867 74277494196595970387485301)
    ·
      refine ⟨6963515080930872223826747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74277494196595970387485301 6963515080930872223826747)
      ·
        refine ⟨10445272621396308335740121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963515080930872223826747 10445272621396308335740121)
        ·
          refine ⟨7833954466047231251805091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445272621396308335740121 7833954466047231251805091)
          ·
            refine ⟨11750931699070846877707637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833954466047231251805091 11750931699070846877707637)
            ·
              refine ⟨1101649846787891894785091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11750931699070846877707637 1101649846787891894785091)
              ·
                refine ⟨1652474770181837842177637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101649846787891894785091 1652474770181837842177637)
                ·
                  refine ⟨309839019409094595408307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652474770181837842177637 309839019409094595408307)
                  ·
                    rfl

theorem cell21_1357671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 4].length) (baseStart_1357671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357671 prefixEnd_1357671 := by exact prefixLift 1357671
  have htrace : WordTrace (prefixWord ++ tailWord_1357671) baseStart_1357671 baseEnd_1357671 := by
    simpa [prefixWord, tailWord_1357671, baseEnd_1357671] using wordTrace_append hprefix tailTrace_1357671
  have hstable : (prefixWord ++ tailWord_1357671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357671).length < 2 ^ (prefixWord ++ tailWord_1357671).sum := by decide
  have hdescent : baseEnd_1357671 < baseStart_1357671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357713 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 6]
def baseStart_1357713 : Nat := 118140960795 + 1357713 * 2 ^ 59
def prefixEnd_1357713 : Nat := 4983230072969 + 3 ^ 40 * 1357713 * 2
def baseEnd_1357713 : Nat := 309848604381311855708221

theorem tailTrace_1357713 : CollatzResearch.WordTrace tailWord_1357713 prefixEnd_1357713 309848604381311855708221 := by
  unfold tailWord_1357713
  simp only [CollatzResearch.WordTrace]
  refine ⟨49519861330245154764685793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33013240886830103176457195 49519861330245154764685793)
  ·
    refine ⟨37139895997683866073514345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49519861330245154764685793 37139895997683866073514345)
    ·
      refine ⟨27854921998262899555135759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37139895997683866073514345 27854921998262899555135759)
      ·
        refine ⟨41782382997394349332703639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27854921998262899555135759 41782382997394349332703639)
        ·
          refine ⟨62673574496091523999055459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41782382997394349332703639 62673574496091523999055459)
          ·
            refine ⟨94010361744137285998583189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62673574496091523999055459 94010361744137285998583189)
            ·
              refine ⟨4406735706756435281183587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94010361744137285998583189 4406735706756435281183587)
              ·
                refine ⟨6610103560134652921775381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406735706756435281183587 6610103560134652921775381)
                ·
                  refine ⟨309848604381311855708221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6610103560134652921775381 309848604381311855708221)
                  ·
                    rfl

theorem cell21_1357713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 6].length) (baseStart_1357713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357713 prefixEnd_1357713 := by exact prefixLift 1357713
  have htrace : WordTrace (prefixWord ++ tailWord_1357713) baseStart_1357713 baseEnd_1357713 := by
    simpa [prefixWord, tailWord_1357713, baseEnd_1357713] using wordTrace_append hprefix tailTrace_1357713
  have hstable : (prefixWord ++ tailWord_1357713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357713).length < 2 ^ (prefixWord ++ tailWord_1357713).sum := by decide
  have hdescent : baseEnd_1357713 < baseStart_1357713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357716 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1357716 : Nat := 118140960795 + 1357716 * 2 ^ 59
def prefixEnd_1357716 : Nat := 4983230072969 + 3 ^ 40 * 1357716 * 2
def baseEnd_1357716 : Nat := 309849289022184517158215

theorem tailTrace_1357716 : CollatzResearch.WordTrace tailWord_1357716 prefixEnd_1357716 309849289022184517158215 := by
  unfold tailWord_1357716
  simp only [CollatzResearch.WordTrace]
  refine ⟨24759985374617143138522501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33013313832822857518030001 24759985374617143138522501)
  ·
    refine ⟨4642497257740714338472969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24759985374617143138522501 4642497257740714338472969)
    ·
      refine ⟨3481872943305535753854727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4642497257740714338472969 3481872943305535753854727)
      ·
        refine ⟨5222809414958303630782091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481872943305535753854727 5222809414958303630782091)
        ·
          refine ⟨7834214122437455446173137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222809414958303630782091 7834214122437455446173137)
          ·
            refine ⟨5875660591828091584629853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7834214122437455446173137 5875660591828091584629853)
            ·
              refine ⟨2203372721935534344236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5875660591828091584629853 2203372721935534344236195)
              ·
                refine ⟨3305059082903301516354293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203372721935534344236195 3305059082903301516354293)
                ·
                  refine ⟨309849289022184517158215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3305059082903301516354293 309849289022184517158215)
                  ·
                    rfl

theorem cell21_1357716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1357716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357716 prefixEnd_1357716 := by exact prefixLift 1357716
  have htrace : WordTrace (prefixWord ++ tailWord_1357716) baseStart_1357716 baseEnd_1357716 := by
    simpa [prefixWord, tailWord_1357716, baseEnd_1357716] using wordTrace_append hprefix tailTrace_1357716
  have hstable : (prefixWord ++ tailWord_1357716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357716).length < 2 ^ (prefixWord ++ tailWord_1357716).sum := by decide
  have hdescent : baseEnd_1357716 < baseStart_1357716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357778 : List Nat := [3, 2, 2, 3, 2, 2, 1, 6]
def baseStart_1357778 : Nat := 118140960795 + 1357778 * 2 ^ 59
def prefixEnd_1357778 : Nat := 4983230072969 + 3 ^ 40 * 1357778 * 2
def baseEnd_1357778 : Nat := 103287812755628729041585

theorem tailTrace_1357778 : CollatzResearch.WordTrace tailWord_1357778 prefixEnd_1357778 103287812755628729041585 := by
  unfold tailWord_1357778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380558018752417716450497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33014821383339780577201325 12380558018752417716450497)
  ·
    refine ⟨9285418514064313287337873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12380558018752417716450497 9285418514064313287337873)
    ·
      refine ⟨6964063885548234965503405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285418514064313287337873 6964063885548234965503405)
      ·
        refine ⟨2611523957080588112063777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6964063885548234965503405 2611523957080588112063777)
        ·
          refine ⟨1958642967810441084047833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2611523957080588112063777 1958642967810441084047833)
          ·
            refine ⟨1468982225857830813035875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1958642967810441084047833 1468982225857830813035875)
            ·
              refine ⟨2203473338786746219553813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1468982225857830813035875 2203473338786746219553813)
              ·
                refine ⟨103287812755628729041585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203473338786746219553813 103287812755628729041585)
                ·
                  rfl

theorem cell21_1357778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_1357778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357778 prefixEnd_1357778 := by exact prefixLift 1357778
  have htrace : WordTrace (prefixWord ++ tailWord_1357778) baseStart_1357778 baseEnd_1357778 := by
    simpa [prefixWord, tailWord_1357778, baseEnd_1357778] using wordTrace_append hprefix tailTrace_1357778
  have hstable : (prefixWord ++ tailWord_1357778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357778).length < 2 ^ (prefixWord ++ tailWord_1357778).sum := by decide
  have hdescent : baseEnd_1357778 < baseStart_1357778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357803 : List Nat := [1, 1, 1, 1, 2, 3, 1, 11]
def baseStart_1357803 : Nat := 118140960795 + 1357803 * 2 ^ 59
def prefixEnd_1357803 : Nat := 4983230072969 + 3 ^ 40 * 1357803 * 2
def baseEnd_1357803 : Nat := 103289714535830566402679

theorem tailTrace_1357803 : CollatzResearch.WordTrace tailWord_1357803 prefixEnd_1357803 103289714535830566402679 := by
  unfold tailWord_1357803
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523143899919100135462063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33015429266612733423641375 49523143899919100135462063)
  ·
    refine ⟨74284715849878650203193095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49523143899919100135462063 74284715849878650203193095)
    ·
      refine ⟨111427073774817975304789643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74284715849878650203193095 111427073774817975304789643)
      ·
        refine ⟨167140610662226962957184465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111427073774817975304789643 167140610662226962957184465)
        ·
          refine ⟨125355457996670222217888349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167140610662226962957184465 125355457996670222217888349)
          ·
            refine ⟨47008296748751333331708131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125355457996670222217888349 47008296748751333331708131)
            ·
              refine ⟨70512445123126999997562197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47008296748751333331708131 70512445123126999997562197)
              ·
                refine ⟨103289714535830566402679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 70512445123126999997562197 103289714535830566402679)
                ·
                  rfl

theorem cell21_1357803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 11].length) (baseStart_1357803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357803 prefixEnd_1357803 := by exact prefixLift 1357803
  have htrace : WordTrace (prefixWord ++ tailWord_1357803) baseStart_1357803 baseEnd_1357803 := by
    simpa [prefixWord, tailWord_1357803, baseEnd_1357803] using wordTrace_append hprefix tailTrace_1357803
  have hstable : (prefixWord ++ tailWord_1357803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357803).length < 2 ^ (prefixWord ++ tailWord_1357803).sum := by decide
  have hdescent : baseEnd_1357803 < baseStart_1357803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357809 : List Nat := [1, 2, 2, 2, 5, 1, 2, 3, 3]
def baseStart_1357809 : Nat := 118140960795 + 1357809 * 2 ^ 59
def prefixEnd_1357809 : Nat := 4983230072969 + 3 ^ 40 * 1357809 * 2
def baseEnd_1357809 : Nat := 309870512889237022108025

theorem tailTrace_1357809 : CollatzResearch.WordTrace tailWord_1357809 prefixEnd_1357809 309870512889237022108025 := by
  unfold tailWord_1357809
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523362737897363160180481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33015575158598242106786987 49523362737897363160180481)
  ·
    refine ⟨37142522053423022370135361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49523362737897363160180481 37142522053423022370135361)
    ·
      refine ⟨27856891540067266777601521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37142522053423022370135361 27856891540067266777601521)
      ·
        refine ⟨20892668655050450083201141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27856891540067266777601521 20892668655050450083201141)
        ·
          refine ⟨1958687686410979695300107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20892668655050450083201141 1958687686410979695300107)
          ·
            refine ⟨2938031529616469542950161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958687686410979695300107 2938031529616469542950161)
            ·
              refine ⟨2203523647212352157212621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2938031529616469542950161 2203523647212352157212621)
              ·
                refine ⟨826321367704632058954733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2203523647212352157212621 826321367704632058954733)
                ·
                  refine ⟨309870512889237022108025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826321367704632058954733 309870512889237022108025)
                  ·
                    rfl

theorem cell21_1357809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_1357809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357809 prefixEnd_1357809 := by exact prefixLift 1357809
  have htrace : WordTrace (prefixWord ++ tailWord_1357809) baseStart_1357809 baseEnd_1357809 := by
    simpa [prefixWord, tailWord_1357809, baseEnd_1357809] using wordTrace_append hprefix tailTrace_1357809
  have hstable : (prefixWord ++ tailWord_1357809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357809).length < 2 ^ (prefixWord ++ tailWord_1357809).sum := by decide
  have hdescent : baseEnd_1357809 < baseStart_1357809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357879 : List Nat := [1, 1, 3, 1, 2, 2, 11]
def baseStart_1357879 : Nat := 118140960795 + 1357879 * 2 ^ 59
def prefixEnd_1357879 : Nat := 4983230072969 + 3 ^ 40 * 1357879 * 2
def baseEnd_1357879 : Nat := 34431831982548050660135

theorem tailTrace_1357879 : CollatzResearch.WordTrace tailWord_1357879 prefixEnd_1357879 34431831982548050660135 := by
  unfold tailWord_1357879
  simp only [CollatzResearch.WordTrace]
  refine ⟨49525915847643765115228691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33017277231762510076819127 49525915847643765115228691)
  ·
    refine ⟨74288873771465647672843037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49525915847643765115228691 74288873771465647672843037)
    ·
      refine ⟨27858327664299617877316139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74288873771465647672843037 27858327664299617877316139)
      ·
        refine ⟨41787491496449426815974209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27858327664299617877316139 41787491496449426815974209)
        ·
          refine ⟨31340618622337070111980657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41787491496449426815974209 31340618622337070111980657)
          ·
            refine ⟨23505463966752802583985493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31340618622337070111980657 23505463966752802583985493)
            ·
              refine ⟨34431831982548050660135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 23505463966752802583985493 34431831982548050660135)
              ·
                rfl

theorem cell21_1357879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_1357879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357879 prefixEnd_1357879 := by exact prefixLift 1357879
  have htrace : WordTrace (prefixWord ++ tailWord_1357879) baseStart_1357879 baseEnd_1357879 := by
    simpa [prefixWord, tailWord_1357879, baseEnd_1357879] using wordTrace_append hprefix tailTrace_1357879
  have hstable : (prefixWord ++ tailWord_1357879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357879).length < 2 ^ (prefixWord ++ tailWord_1357879).sum := by decide
  have hdescent : baseEnd_1357879 < baseStart_1357879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1357885 : List Nat := [1, 4, 1, 3, 1, 1, 5, 2, 3]
def baseStart_1357885 : Nat := 118140960795 + 1357885 * 2 ^ 59
def prefixEnd_1357885 : Nat := 4983230072969 + 3 ^ 40 * 1357885 * 2
def baseEnd_1357885 : Nat := 309887857124677778841203

theorem tailTrace_1357885 : CollatzResearch.WordTrace tailWord_1357885 prefixEnd_1357885 309887857124677778841203 := by
  unfold tailWord_1357885
  simp only [CollatzResearch.WordTrace]
  refine ⟨49526134685622028139947109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33017423123748018759964739 49526134685622028139947109)
  ·
    refine ⟨9286150253554130276240083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49526134685622028139947109 9286150253554130276240083)
    ·
      refine ⟨13929225380331195414360125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286150253554130276240083 13929225380331195414360125)
      ·
        refine ⟨5223459517624198280385047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13929225380331195414360125 5223459517624198280385047)
        ·
          refine ⟨7835189276436297420577571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223459517624198280385047 7835189276436297420577571)
          ·
            refine ⟨11752783914654446130866357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835189276436297420577571 11752783914654446130866357)
            ·
              refine ⟨1101823491998854324768721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11752783914654446130866357 1101823491998854324768721)
              ·
                refine ⟨826367618999140743576541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1101823491998854324768721 826367618999140743576541)
                ·
                  refine ⟨309887857124677778841203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826367618999140743576541 309887857124677778841203)
                  ·
                    rfl

theorem cell21_1357885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 2, 3].length) (baseStart_1357885 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1357885 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1357885 prefixEnd_1357885 := by exact prefixLift 1357885
  have htrace : WordTrace (prefixWord ++ tailWord_1357885) baseStart_1357885 baseEnd_1357885 := by
    simpa [prefixWord, tailWord_1357885, baseEnd_1357885] using wordTrace_append hprefix tailTrace_1357885
  have hstable : (prefixWord ++ tailWord_1357885).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1357885).length < 2 ^ (prefixWord ++ tailWord_1357885).sum := by decide
  have hdescent : baseEnd_1357885 < baseStart_1357885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1357885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358031 : List Nat := [1, 1, 2, 1, 1, 3, 5, 7]
def baseStart_1358031 : Nat := 118140960795 + 1358031 * 2 ^ 59
def prefixEnd_1358031 : Nat := 4983230072969 + 3 ^ 40 * 1358031 * 2
def baseEnd_1358031 : Nat := 103307058771271323135857

theorem tailTrace_1358031 : CollatzResearch.WordTrace tailWord_1358031 prefixEnd_1358031 103307058771271323135857 := by
  unfold tailWord_1358031
  simp only [CollatzResearch.WordTrace]
  refine ⟨49531459743093095074761947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33020973162062063383174631 49531459743093095074761947)
  ·
    refine ⟨74297189614639642612142921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49531459743093095074761947 74297189614639642612142921)
    ·
      refine ⟨55722892210979731959107191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74297189614639642612142921 55722892210979731959107191)
      ·
        refine ⟨83584338316469597938660787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55722892210979731959107191 83584338316469597938660787)
        ·
          refine ⟨125376507474704396907991181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83584338316469597938660787 125376507474704396907991181)
          ·
            refine ⟨47016190303014148840496693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125376507474704396907991181 47016190303014148840496693)
            ·
              refine ⟨4407767840907576453796565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47016190303014148840496693 4407767840907576453796565)
              ·
                refine ⟨103307058771271323135857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4407767840907576453796565 103307058771271323135857)
                ·
                  rfl

theorem cell21_1358031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 7].length) (baseStart_1358031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358031 prefixEnd_1358031 := by exact prefixLift 1358031
  have htrace : WordTrace (prefixWord ++ tailWord_1358031) baseStart_1358031 baseEnd_1358031 := by
    simpa [prefixWord, tailWord_1358031, baseEnd_1358031] using wordTrace_append hprefix tailTrace_1358031
  have hstable : (prefixWord ++ tailWord_1358031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358031).length < 2 ^ (prefixWord ++ tailWord_1358031).sum := by decide
  have hdescent : baseEnd_1358031 < baseStart_1358031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358138 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_1358138 : Nat := 118140960795 + 1358138 * 2 ^ 59
def prefixEnd_1358138 : Nat := 4983230072969 + 3 ^ 40 * 1358138 * 2
def baseEnd_1358138 : Nat := 309945595171605561124019

theorem tailTrace_1358138 : CollatzResearch.WordTrace tailWord_1358138 prefixEnd_1358138 309945595171605561124019 := by
  unfold tailWord_1358138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12383840588426363087226767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33023574902470301565938045 12383840588426363087226767)
  ·
    refine ⟨18575760882639544630840151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12383840588426363087226767 18575760882639544630840151)
    ·
      refine ⟨27863641323959316946260227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18575760882639544630840151 27863641323959316946260227)
      ·
        refine ⟨41795461985938975419390341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27863641323959316946260227 41795461985938975419390341)
        ·
          refine ⟨7836649122363557891135689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41795461985938975419390341 7836649122363557891135689)
          ·
            refine ⟨5877486841772668418351767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7836649122363557891135689 5877486841772668418351767)
            ·
              refine ⟨8816230262659002627527651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877486841772668418351767 8816230262659002627527651)
              ·
                refine ⟨13224345393988503941291477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8816230262659002627527651 13224345393988503941291477)
                ·
                  refine ⟨309945595171605561124019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13224345393988503941291477 309945595171605561124019)
                  ·
                    rfl

theorem cell21_1358138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_1358138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358138 prefixEnd_1358138 := by exact prefixLift 1358138
  have htrace : WordTrace (prefixWord ++ tailWord_1358138) baseStart_1358138 baseEnd_1358138 := by
    simpa [prefixWord, tailWord_1358138, baseEnd_1358138] using wordTrace_append hprefix tailTrace_1358138
  have hstable : (prefixWord ++ tailWord_1358138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358138).length < 2 ^ (prefixWord ++ tailWord_1358138).sum := by decide
  have hdescent : baseEnd_1358138 < baseStart_1358138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358231 : List Nat := [1, 1, 3, 3, 1, 1, 2, 6, 3]
def baseStart_1358231 : Nat := 118140960795 + 1358231 * 2 ^ 59
def prefixEnd_1358231 : Nat := 4983230072969 + 3 ^ 40 * 1358231 * 2
def baseEnd_1358231 : Nat := 309966819038658066073829

theorem tailTrace_1358231 : CollatzResearch.WordTrace tailWord_1358231 prefixEnd_1358231 309966819038658066073829 := by
  unfold tailWord_1358231
  simp only [CollatzResearch.WordTrace]
  refine ⟨49538754342368529232042547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33025836228245686154695031 49538754342368529232042547)
  ·
    refine ⟨74308131513552793848063821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49538754342368529232042547 74308131513552793848063821)
    ·
      refine ⟨27865549317582297693023933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74308131513552793848063821 27865549317582297693023933)
      ·
        refine ⟨10449580994093361634883975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27865549317582297693023933 10449580994093361634883975)
        ·
          refine ⟨15674371491140042452325963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449580994093361634883975 15674371491140042452325963)
          ·
            refine ⟨23511557236710063678488945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15674371491140042452325963 23511557236710063678488945)
            ·
              refine ⟨17633667927532547758866709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23511557236710063678488945 17633667927532547758866709)
              ·
                refine ⟨826578184103088176196877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17633667927532547758866709 826578184103088176196877)
                ·
                  refine ⟨309966819038658066073829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826578184103088176196877 309966819038658066073829)
                  ·
                    rfl

theorem cell21_1358231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 6, 3].length) (baseStart_1358231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358231 prefixEnd_1358231 := by exact prefixLift 1358231
  have htrace : WordTrace (prefixWord ++ tailWord_1358231) baseStart_1358231 baseEnd_1358231 := by
    simpa [prefixWord, tailWord_1358231, baseEnd_1358231] using wordTrace_append hprefix tailTrace_1358231
  have hstable : (prefixWord ++ tailWord_1358231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358231).length < 2 ^ (prefixWord ++ tailWord_1358231).sum := by decide
  have hdescent : baseEnd_1358231 < baseStart_1358231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358245 : List Nat := [1, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_1358245 : Nat := 118140960795 + 1358245 * 2 ^ 59
def prefixEnd_1358245 : Nat := 4983230072969 + 3 ^ 40 * 1358245 * 2
def baseEnd_1358245 : Nat := 309970014029397152840467

theorem tailTrace_1358245 : CollatzResearch.WordTrace tailWord_1358245 prefixEnd_1358245 309970014029397152840467 := by
  unfold tailWord_1358245
  simp only [CollatzResearch.WordTrace]
  refine ⟨49539264964317809623052189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33026176642878539748701459 49539264964317809623052189)
  ·
    refine ⟨18577224361619178608644571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49539264964317809623052189 18577224361619178608644571)
    ·
      refine ⟨27865836542428767912966857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18577224361619178608644571 27865836542428767912966857)
      ·
        refine ⟨20899377406821575934725143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27865836542428767912966857 20899377406821575934725143)
        ·
          refine ⟨31349066110232363902087715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20899377406821575934725143 31349066110232363902087715)
          ·
            refine ⟨47023599165348545853131573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31349066110232363902087715 47023599165348545853131573)
            ·
              refine ⟨4408462421751426173731085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47023599165348545853131573 4408462421751426173731085)
              ·
                refine ⟨1653173408156784815149157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4408462421751426173731085 1653173408156784815149157)
                ·
                  refine ⟨309970014029397152840467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653173408156784815149157 309970014029397152840467)
                  ·
                    rfl

theorem cell21_1358245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_1358245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358245 prefixEnd_1358245 := by exact prefixLift 1358245
  have htrace : WordTrace (prefixWord ++ tailWord_1358245) baseStart_1358245 baseEnd_1358245 := by
    simpa [prefixWord, tailWord_1358245, baseEnd_1358245] using wordTrace_append hprefix tailTrace_1358245
  have hstable : (prefixWord ++ tailWord_1358245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358245).length < 2 ^ (prefixWord ++ tailWord_1358245).sum := by decide
  have hdescent : baseEnd_1358245 < baseStart_1358245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358276 : List Nat := [2, 3, 3, 2, 2, 9]
def baseStart_1358276 : Nat := 118140960795 + 1358276 * 2 ^ 59
def prefixEnd_1358276 : Nat := 4983230072969 + 3 ^ 40 * 1358276 * 2
def baseEnd_1358276 : Nat := 11480632913027703252731

theorem tailTrace_1358276 : CollatzResearch.WordTrace tailWord_1358276 prefixEnd_1358276 11480632913027703252731 := by
  unfold tailWord_1358276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24770197813602750958715341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33026930418137001278287121 24770197813602750958715341)
  ·
    refine ⟨9288824180101031609518253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24770197813602750958715341 9288824180101031609518253)
    ·
      refine ⟨3483309067537886853569345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9288824180101031609518253 3483309067537886853569345)
      ·
        refine ⟨2612481800653415140177009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483309067537886853569345 2612481800653415140177009)
        ·
          refine ⟨1959361350490061355132757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2612481800653415140177009 1959361350490061355132757)
          ·
            refine ⟨11480632913027703252731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1959361350490061355132757 11480632913027703252731)
            ·
              rfl

theorem cell21_1358276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 9].length) (baseStart_1358276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358276 prefixEnd_1358276 := by exact prefixLift 1358276
  have htrace : WordTrace (prefixWord ++ tailWord_1358276) baseStart_1358276 baseEnd_1358276 := by
    simpa [prefixWord, tailWord_1358276, baseEnd_1358276] using wordTrace_append hprefix tailTrace_1358276
  have hstable : (prefixWord ++ tailWord_1358276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358276).length < 2 ^ (prefixWord ++ tailWord_1358276).sum := by decide
  have hdescent : baseEnd_1358276 < baseStart_1358276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358307 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 5]
def baseStart_1358307 : Nat := 118140960795 + 1358307 * 2 ^ 59
def prefixEnd_1358307 : Nat := 4983230072969 + 3 ^ 40 * 1358307 * 2
def baseEnd_1358307 : Nat := 309984163274098822807007

theorem tailTrace_1358307 : CollatzResearch.WordTrace tailWord_1358307 prefixEnd_1358307 309984163274098822807007 := by
  unfold tailWord_1358307
  simp only [CollatzResearch.WordTrace]
  refine ⟨49541526290093194211809175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33027684193395462807872783 49541526290093194211809175)
  ·
    refine ⟨74312289435139791317713763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49541526290093194211809175 74312289435139791317713763)
    ·
      refine ⟨111468434152709686976570645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74312289435139791317713763 111468434152709686976570645)
      ·
        refine ⟨5225082850908266577026749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111468434152709686976570645 5225082850908266577026749)
        ·
          refine ⟨1959406069090599966385031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5225082850908266577026749 1959406069090599966385031)
          ·
            refine ⟨2939109103635899949577547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959406069090599966385031 2939109103635899949577547)
            ·
              refine ⟨4408663655453849924366321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939109103635899949577547 4408663655453849924366321)
              ·
                refine ⟨3306497741590387443274741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408663655453849924366321 3306497741590387443274741)
                ·
                  refine ⟨309984163274098822807007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3306497741590387443274741 309984163274098822807007)
                  ·
                    rfl

theorem cell21_1358307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 5].length) (baseStart_1358307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358307 prefixEnd_1358307 := by exact prefixLift 1358307
  have htrace : WordTrace (prefixWord ++ tailWord_1358307) baseStart_1358307 baseEnd_1358307 := by
    simpa [prefixWord, tailWord_1358307, baseEnd_1358307] using wordTrace_append hprefix tailTrace_1358307
  have hstable : (prefixWord ++ tailWord_1358307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358307).length < 2 ^ (prefixWord ++ tailWord_1358307).sum := by decide
  have hdescent : baseEnd_1358307 < baseStart_1358307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358375 : List Nat := [1, 1, 7, 2, 2, 1, 1, 3, 3]
def baseStart_1358375 : Nat := 118140960795 + 1358375 * 2 ^ 59
def prefixEnd_1358375 : Nat := 4983230072969 + 3 ^ 40 * 1358375 * 2
def baseEnd_1358375 : Nat := 309999681800545815673535

theorem tailTrace_1358375 : CollatzResearch.WordTrace tailWord_1358375 prefixEnd_1358375 309999681800545815673535 := by
  unfold tailWord_1358375
  simp only [CollatzResearch.WordTrace]
  refine ⟨49544006453846841825284579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33029337635897894550189719 49544006453846841825284579)
  ·
    refine ⟨74316009680770262737926869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49544006453846841825284579 74316009680770262737926869)
    ·
      refine ⟨1741781476893053032920161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 74316009680770262737926869 1741781476893053032920161)
      ·
        refine ⟨1306336107669789774690121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741781476893053032920161 1306336107669789774690121)
        ·
          refine ⟨979752080752342331017591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1306336107669789774690121 979752080752342331017591)
          ·
            refine ⟨1469628121128513496526387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979752080752342331017591 1469628121128513496526387)
            ·
              refine ⟨2204442181692770244789581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469628121128513496526387 2204442181692770244789581)
              ·
                refine ⟨826665818134788841796093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204442181692770244789581 826665818134788841796093)
                ·
                  refine ⟨309999681800545815673535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826665818134788841796093 309999681800545815673535)
                  ·
                    rfl

theorem cell21_1358375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 3, 3].length) (baseStart_1358375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358375 prefixEnd_1358375 := by exact prefixLift 1358375
  have htrace : WordTrace (prefixWord ++ tailWord_1358375) baseStart_1358375 baseEnd_1358375 := by
    simpa [prefixWord, tailWord_1358375, baseEnd_1358375] using wordTrace_append hprefix tailTrace_1358375
  have hstable : (prefixWord ++ tailWord_1358375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358375).length < 2 ^ (prefixWord ++ tailWord_1358375).sum := by decide
  have hdescent : baseEnd_1358375 < baseStart_1358375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358397 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 6]
def baseStart_1358397 : Nat := 118140960795 + 1358397 * 2 ^ 59
def prefixEnd_1358397 : Nat := 4983230072969 + 3 ^ 40 * 1358397 * 2
def baseEnd_1358397 : Nat := 310004702500278666306823

theorem tailTrace_1358397 : CollatzResearch.WordTrace tailWord_1358397 prefixEnd_1358397 310004702500278666306823 := by
  unfold tailWord_1358397
  simp only [CollatzResearch.WordTrace]
  refine ⟨49544808859767139582585445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33029872573178093055056963 49544808859767139582585445)
  ·
    refine ⟨9289651661206338671734771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49544808859767139582585445 9289651661206338671734771)
    ·
      refine ⟨13934477491809508007602157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9289651661206338671734771 13934477491809508007602157)
      ·
        refine ⟨5225429059428565502850809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13934477491809508007602157 5225429059428565502850809)
        ·
          refine ⟨3919071794571424127138107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5225429059428565502850809 3919071794571424127138107)
          ·
            refine ⟨5878607691857136190707161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919071794571424127138107 5878607691857136190707161)
            ·
              refine ⟨4408955768892852143030371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5878607691857136190707161 4408955768892852143030371)
              ·
                refine ⟨6613433653339278214545557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408955768892852143030371 6613433653339278214545557)
                ·
                  refine ⟨310004702500278666306823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6613433653339278214545557 310004702500278666306823)
                  ·
                    rfl

theorem cell21_1358397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_1358397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358397 prefixEnd_1358397 := by exact prefixLift 1358397
  have htrace : WordTrace (prefixWord ++ tailWord_1358397) baseStart_1358397 baseEnd_1358397 := by
    simpa [prefixWord, tailWord_1358397, baseEnd_1358397] using wordTrace_append hprefix tailTrace_1358397
  have hstable : (prefixWord ++ tailWord_1358397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358397).length < 2 ^ (prefixWord ++ tailWord_1358397).sum := by decide
  have hdescent : baseEnd_1358397 < baseStart_1358397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358414 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_1358414 : Nat := 118140960795 + 1358414 * 2 ^ 59
def prefixEnd_1358414 : Nat := 4983230072969 + 3 ^ 40 * 1358414 * 2
def baseEnd_1358414 : Nat := 310008582131890414523455

theorem tailTrace_1358414 : CollatzResearch.WordTrace tailWord_1358414 prefixEnd_1358414 310008582131890414523455 := by
  unfold tailWord_1358414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193178612588193935744287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33030285933803700990636197 6193178612588193935744287)
  ·
    refine ⟨9289767918882290903616431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6193178612588193935744287 9289767918882290903616431)
    ·
      refine ⟨13934651878323436355424647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9289767918882290903616431 13934651878323436355424647)
      ·
        refine ⟨20901977817485154533136971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13934651878323436355424647 20901977817485154533136971)
        ·
          refine ⟨31352966726227731799705457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20901977817485154533136971 31352966726227731799705457)
          ·
            refine ⟨23514725044670798849779093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31352966726227731799705457 23514725044670798849779093)
            ·
              refine ⟨1102252736468943696083395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23514725044670798849779093 1102252736468943696083395)
              ·
                refine ⟨1653379104703415544125093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102252736468943696083395 1653379104703415544125093)
                ·
                  refine ⟨310008582131890414523455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653379104703415544125093 310008582131890414523455)
                  ·
                    rfl

theorem cell21_1358414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_1358414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358414 prefixEnd_1358414 := by exact prefixLift 1358414
  have htrace : WordTrace (prefixWord ++ tailWord_1358414) baseStart_1358414 baseEnd_1358414 := by
    simpa [prefixWord, tailWord_1358414, baseEnd_1358414] using wordTrace_append hprefix tailTrace_1358414
  have hstable : (prefixWord ++ tailWord_1358414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358414).length < 2 ^ (prefixWord ++ tailWord_1358414).sum := by decide
  have hdescent : baseEnd_1358414 < baseStart_1358414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358501 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 9]
def baseStart_1358501 : Nat := 118140960795 + 1358501 * 2 ^ 59
def prefixEnd_1358501 : Nat := 4983230072969 + 3 ^ 40 * 1358501 * 2
def baseEnd_1358501 : Nat := 310028436717197596573277

theorem tailTrace_1358501 : CollatzResearch.WordTrace tailWord_1358501 prefixEnd_1358501 310028436717197596573277 := by
  unfold tailWord_1358501
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548602051390365344371357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33032401367593576896247571 49548602051390365344371357)
  ·
    refine ⟨18580725769271387004139259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49548602051390365344371357 18580725769271387004139259)
    ·
      refine ⟨27871088653907080506208889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18580725769271387004139259 27871088653907080506208889)
      ·
        refine ⟨20903316490430310379656667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27871088653907080506208889 20903316490430310379656667)
        ·
          refine ⟨31354974735645465569485001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20903316490430310379656667 31354974735645465569485001)
          ·
            refine ⟨23516231051734099177113751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31354974735645465569485001 23516231051734099177113751)
            ·
              refine ⟨35274346577601148765670627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23516231051734099177113751 35274346577601148765670627)
              ·
                refine ⟨52911519866401723148505941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35274346577601148765670627 52911519866401723148505941)
                ·
                  refine ⟨310028436717197596573277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52911519866401723148505941 310028436717197596573277)
                  ·
                    rfl

theorem cell21_1358501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_1358501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358501 prefixEnd_1358501 := by exact prefixLift 1358501
  have htrace : WordTrace (prefixWord ++ tailWord_1358501) baseStart_1358501 baseEnd_1358501 := by
    simpa [prefixWord, tailWord_1358501, baseEnd_1358501] using wordTrace_append hprefix tailTrace_1358501
  have hstable : (prefixWord ++ tailWord_1358501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358501).length < 2 ^ (prefixWord ++ tailWord_1358501).sum := by decide
  have hdescent : baseEnd_1358501 < baseStart_1358501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358552 : List Nat := [2, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_1358552 : Nat := 118140960795 + 1358552 * 2 ^ 59
def prefixEnd_1358552 : Nat := 4983230072969 + 3 ^ 40 * 1358552 * 2
def baseEnd_1358552 : Nat := 310040075612032841223173

theorem tailTrace_1358552 : CollatzResearch.WordTrace tailWord_1358552 prefixEnd_1358552 310040075612032841223173 := by
  unfold tailWord_1358552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24775231087102800527238955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33033641449470400702985273 24775231087102800527238955)
  ·
    refine ⟨37162846630654200790858433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24775231087102800527238955 37162846630654200790858433)
    ·
      refine ⟨27872134972990650593143825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37162846630654200790858433 27872134972990650593143825)
      ·
        refine ⟨20904101229742987944857869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27872134972990650593143825 20904101229742987944857869)
        ·
          refine ⟨7839037961153620479321701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20904101229742987944857869 7839037961153620479321701)
          ·
            refine ⟨1469819617716303839872819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7839037961153620479321701 1469819617716303839872819)
            ·
              refine ⟨2204729426574455759809229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1469819617716303839872819 2204729426574455759809229)
              ·
                refine ⟨826773534965420909928461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204729426574455759809229 826773534965420909928461)
                ·
                  refine ⟨310040075612032841223173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826773534965420909928461 310040075612032841223173)
                  ·
                    rfl

theorem cell21_1358552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_1358552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358552 prefixEnd_1358552 := by exact prefixLift 1358552
  have htrace : WordTrace (prefixWord ++ tailWord_1358552) baseStart_1358552 baseEnd_1358552 := by
    simpa [prefixWord, tailWord_1358552, baseEnd_1358552] using wordTrace_append hprefix tailTrace_1358552
  have hstable : (prefixWord ++ tailWord_1358552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358552).length < 2 ^ (prefixWord ++ tailWord_1358552).sum := by decide
  have hdescent : baseEnd_1358552 < baseStart_1358552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358563 : List Nat := [1, 1, 1, 7, 1, 1, 9]
def baseStart_1358563 : Nat := 118140960795 + 1358563 * 2 ^ 59
def prefixEnd_1358563 : Nat := 4983230072969 + 3 ^ 40 * 1358563 * 2
def baseEnd_1358563 : Nat := 34449176217988807393313

theorem tailTrace_1358563 : CollatzResearch.WordTrace tailWord_1358563 prefixEnd_1358563 34449176217988807393313 := by
  unfold tailWord_1358563
  simp only [CollatzResearch.WordTrace]
  refine ⟨49550863377165749933128343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33033908918110499955418895 49550863377165749933128343)
  ·
    refine ⟨74326295065748624899692515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49550863377165749933128343 74326295065748624899692515)
    ·
      refine ⟨111489442598622937349538773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74326295065748624899692515 111489442598622937349538773)
      ·
        refine ⟨2613033810905225094129815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 111489442598622937349538773 2613033810905225094129815)
        ·
          refine ⟨3919550716357837641194723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613033810905225094129815 3919550716357837641194723)
          ·
            refine ⟨5879326074536756461792085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919550716357837641194723 5879326074536756461792085)
            ·
              refine ⟨34449176217988807393313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5879326074536756461792085 34449176217988807393313)
              ·
                rfl

theorem cell21_1358563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_1358563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358563 prefixEnd_1358563 := by exact prefixLift 1358563
  have htrace : WordTrace (prefixWord ++ tailWord_1358563) baseStart_1358563 baseEnd_1358563 := by
    simpa [prefixWord, tailWord_1358563, baseEnd_1358563] using wordTrace_append hprefix tailTrace_1358563
  have hstable : (prefixWord ++ tailWord_1358563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358563).length < 2 ^ (prefixWord ++ tailWord_1358563).sum := by decide
  have hdescent : baseEnd_1358563 < baseStart_1358563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358625 : List Nat := [1, 2, 3, 2, 1, 2, 4, 2, 4]
def baseStart_1358625 : Nat := 118140960795 + 1358625 * 2 ^ 59
def prefixEnd_1358625 : Nat := 4983230072969 + 3 ^ 40 * 1358625 * 2
def baseEnd_1358625 : Nat := 310056735206600936506357

theorem tailTrace_1358625 : CollatzResearch.WordTrace tailWord_1358625 prefixEnd_1358625 310056735206600936506357 := by
  unfold tailWord_1358625
  simp only [CollatzResearch.WordTrace]
  refine ⟨49553124702941134521885329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33035416468627423014590219 49553124702941134521885329)
  ·
    refine ⟨37164843527205850891413997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49553124702941134521885329 37164843527205850891413997)
    ·
      refine ⟨13936816322702194084280249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37164843527205850891413997 13936816322702194084280249)
      ·
        refine ⟨10452612242026645563210187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13936816322702194084280249 10452612242026645563210187)
        ·
          refine ⟨15678918363039968344815281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10452612242026645563210187 15678918363039968344815281)
          ·
            refine ⟨11759188772279976258611461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15678918363039968344815281 11759188772279976258611461)
            ·
              refine ⟨2204847894802495548489649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11759188772279976258611461 2204847894802495548489649)
              ·
                refine ⟨1653635921101871661367237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204847894802495548489649 1653635921101871661367237)
                ·
                  refine ⟨310056735206600936506357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653635921101871661367237 310056735206600936506357)
                  ·
                    rfl

theorem cell21_1358625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 4].length) (baseStart_1358625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358625 prefixEnd_1358625 := by exact prefixLift 1358625
  have htrace : WordTrace (prefixWord ++ tailWord_1358625) baseStart_1358625 baseEnd_1358625 := by
    simpa [prefixWord, tailWord_1358625, baseEnd_1358625] using wordTrace_append hprefix tailTrace_1358625
  have hstable : (prefixWord ++ tailWord_1358625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358625).length < 2 ^ (prefixWord ++ tailWord_1358625).sum := by decide
  have hdescent : baseEnd_1358625 < baseStart_1358625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358628 : List Nat := [2, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1358628 : Nat := 118140960795 + 1358628 * 2 ^ 59
def prefixEnd_1358628 : Nat := 4983230072969 + 3 ^ 40 * 1358628 * 2
def baseEnd_1358628 : Nat := 310057419847473597956351

theorem tailTrace_1358628 : CollatzResearch.WordTrace tailWord_1358628 prefixEnd_1358628 310057419847473597956351 := by
  unfold tailWord_1358628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24776617060965133017122269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33035489414620177356163025 24776617060965133017122269)
  ·
    refine ⟨9291231397861924881420851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24776617060965133017122269 9291231397861924881420851)
    ·
      refine ⟨13936847096792887322131277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9291231397861924881420851 13936847096792887322131277)
      ·
        refine ⟨5226317661297332745799229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13936847096792887322131277 5226317661297332745799229)
        ·
          refine ⟨1959869122986499779674711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5226317661297332745799229 1959869122986499779674711)
          ·
            refine ⟨2939803684479749669512067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959869122986499779674711 2939803684479749669512067)
            ·
              refine ⟨4409705526719624504268101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939803684479749669512067 4409705526719624504268101)
              ·
                refine ⟨826819786259929594550269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4409705526719624504268101 826819786259929594550269)
                ·
                  refine ⟨310057419847473597956351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826819786259929594550269 310057419847473597956351)
                  ·
                    rfl

theorem cell21_1358628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1358628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358628 prefixEnd_1358628 := by exact prefixLift 1358628
  have htrace : WordTrace (prefixWord ++ tailWord_1358628) baseStart_1358628 baseEnd_1358628 := by
    simpa [prefixWord, tailWord_1358628, baseEnd_1358628] using wordTrace_append hprefix tailTrace_1358628
  have hstable : (prefixWord ++ tailWord_1358628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358628).length < 2 ^ (prefixWord ++ tailWord_1358628).sum := by decide
  have hdescent : baseEnd_1358628 < baseStart_1358628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358662 : List Nat := [6, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1358662 : Nat := 118140960795 + 1358662 * 2 ^ 59
def prefixEnd_1358662 : Nat := 4983230072969 + 3 ^ 40 * 1358662 * 2
def baseEnd_1358662 : Nat := 310065179110697094389615

theorem tailTrace_1358662 : CollatzResearch.WordTrace tailWord_1358662 prefixEnd_1358662 310065179110697094389615 := by
  unfold tailWord_1358662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548577318868971557530695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33036316135871393227321493 1548577318868971557530695)
  ·
    refine ⟨2322865978303457336296043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548577318868971557530695 2322865978303457336296043)
    ·
      refine ⟨3484298967455186004444065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322865978303457336296043 3484298967455186004444065)
      ·
        refine ⟨2613224225591389503333049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3484298967455186004444065 2613224225591389503333049)
        ·
          refine ⟨1959918169193542127499787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613224225591389503333049 1959918169193542127499787)
          ·
            refine ⟨2939877253790313191249681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959918169193542127499787 2939877253790313191249681)
            ·
              refine ⟨2204907940342734893437261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939877253790313191249681 2204907940342734893437261)
              ·
                refine ⟨826840477628525585038973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2204907940342734893437261 826840477628525585038973)
                ·
                  refine ⟨310065179110697094389615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826840477628525585038973 310065179110697094389615)
                  ·
                    rfl

theorem cell21_1358662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1358662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358662 prefixEnd_1358662 := by exact prefixLift 1358662
  have htrace : WordTrace (prefixWord ++ tailWord_1358662) baseStart_1358662 baseEnd_1358662 := by
    simpa [prefixWord, tailWord_1358662, baseEnd_1358662] using wordTrace_append hprefix tailTrace_1358662
  have hstable : (prefixWord ++ tailWord_1358662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358662).length < 2 ^ (prefixWord ++ tailWord_1358662).sum := by decide
  have hdescent : baseEnd_1358662 < baseStart_1358662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358715 : List Nat := [1, 1, 1, 1, 1, 5, 6, 5]
def baseStart_1358715 : Nat := 118140960795 + 1358715 * 2 ^ 59
def prefixEnd_1358715 : Nat := 4983230072969 + 3 ^ 40 * 1358715 * 2
def baseEnd_1358715 : Nat := 103359091477593593335391

theorem tailTrace_1358715 : CollatzResearch.WordTrace tailWord_1358715 prefixEnd_1358715 103359091477593593335391 := by
  unfold tailWord_1358715
  simp only [CollatzResearch.WordTrace]
  refine ⟨49556407272615079892661599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33037604848410053261774399 49556407272615079892661599)
  ·
    refine ⟨74334610908922619838992399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49556407272615079892661599 74334610908922619838992399)
    ·
      refine ⟨111501916363383929758488599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74334610908922619838992399 111501916363383929758488599)
      ·
        refine ⟨167252874545075894637732899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111501916363383929758488599 167252874545075894637732899)
        ·
          refine ⟨250879311817613841956599349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167252874545075894637732899 250879311817613841956599349)
          ·
            refine ⟨23519935482901297683431189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250879311817613841956599349 23519935482901297683431189)
            ·
              refine ⟨1102496975760998328910837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23519935482901297683431189 1102496975760998328910837)
              ·
                refine ⟨103359091477593593335391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102496975760998328910837 103359091477593593335391)
                ·
                  rfl

theorem cell21_1358715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 5].length) (baseStart_1358715 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358715 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358715 prefixEnd_1358715 := by exact prefixLift 1358715
  have htrace : WordTrace (prefixWord ++ tailWord_1358715) baseStart_1358715 baseEnd_1358715 := by
    simpa [prefixWord, tailWord_1358715, baseEnd_1358715] using wordTrace_append hprefix tailTrace_1358715
  have hstable : (prefixWord ++ tailWord_1358715).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358715).length < 2 ^ (prefixWord ++ tailWord_1358715).sum := by decide
  have hdescent : baseEnd_1358715 < baseStart_1358715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358884 : List Nat := [2, 3, 1, 4, 1, 1, 4, 5]
def baseStart_1358884 : Nat := 118140960795 + 1358884 * 2 ^ 59
def prefixEnd_1358884 : Nat := 4983230072969 + 3 ^ 40 * 1358884 * 2
def baseEnd_1358884 : Nat := 103371947511758013896387

theorem tailTrace_1358884 : CollatzResearch.WordTrace tailWord_1358884 prefixEnd_1358884 103371947511758013896387 := by
  unfold tailWord_1358884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781285604501410877781853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33041714139335214503709137 24781285604501410877781853)
  ·
    refine ⟨9292982101688029079168195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24781285604501410877781853 9292982101688029079168195)
    ·
      refine ⟨13939473152532043618752293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9292982101688029079168195 13939473152532043618752293)
      ·
        refine ⟨2613651216099758178516055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13939473152532043618752293 2613651216099758178516055)
        ·
          refine ⟨3920476824149637267774083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613651216099758178516055 3920476824149637267774083)
          ·
            refine ⟨5880715236224455901661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3920476824149637267774083 5880715236224455901661125)
            ·
              refine ⟨1102634106792085481561461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5880715236224455901661125 1102634106792085481561461)
              ·
                refine ⟨103371947511758013896387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1102634106792085481561461 103371947511758013896387)
                ·
                  rfl

theorem cell21_1358884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_1358884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358884 prefixEnd_1358884 := by exact prefixLift 1358884
  have htrace : WordTrace (prefixWord ++ tailWord_1358884) baseStart_1358884 baseEnd_1358884 := by
    simpa [prefixWord, tailWord_1358884, baseEnd_1358884] using wordTrace_append hprefix tailTrace_1358884
  have hstable : (prefixWord ++ tailWord_1358884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358884).length < 2 ^ (prefixWord ++ tailWord_1358884).sum := by decide
  have hdescent : baseEnd_1358884 < baseStart_1358884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358912 : List Nat := [2, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_1358912 : Nat := 118140960795 + 1358912 * 2 ^ 59
def prefixEnd_1358912 : Nat := 4983230072969 + 3 ^ 40 * 1358912 * 2
def baseEnd_1358912 : Nat := 310122232516752215222437

theorem tailTrace_1358912 : CollatzResearch.WordTrace tailWord_1358912 prefixEnd_1358912 310122232516752215222437 := by
  unfold tailWord_1358912
  simp only [CollatzResearch.WordTrace]
  refine ⟨24781796226450691268791495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33042394968600921691721993 24781796226450691268791495)
  ·
    refine ⟨37172694339676036903187243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24781796226450691268791495 37172694339676036903187243)
    ·
      refine ⟨55759041509514055354780865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37172694339676036903187243 55759041509514055354780865)
      ·
        refine ⟨41819281132135541516085649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55759041509514055354780865 41819281132135541516085649)
        ·
          refine ⟨31364460849101656137064237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41819281132135541516085649 31364460849101656137064237)
          ·
            refine ⟨11761672818413121051399089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31364460849101656137064237 11761672818413121051399089)
            ·
              refine ⟨8821254613809840788549317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11761672818413121051399089 8821254613809840788549317)
              ·
                refine ⟨1653985240089345147852997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8821254613809840788549317 1653985240089345147852997)
                ·
                  refine ⟨310122232516752215222437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653985240089345147852997 310122232516752215222437)
                  ·
                    rfl

theorem cell21_1358912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_1358912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358912 prefixEnd_1358912 := by exact prefixLift 1358912
  have htrace : WordTrace (prefixWord ++ tailWord_1358912) baseStart_1358912 baseEnd_1358912 := by
    simpa [prefixWord, tailWord_1358912, baseEnd_1358912] using wordTrace_append hprefix tailTrace_1358912
  have hstable : (prefixWord ++ tailWord_1358912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358912).length < 2 ^ (prefixWord ++ tailWord_1358912).sum := by decide
  have hdescent : baseEnd_1358912 < baseStart_1358912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358915 : List Nat := [1, 1, 1, 3, 1, 2, 7, 2, 3]
def baseStart_1358915 : Nat := 118140960795 + 1358915 * 2 ^ 59
def prefixEnd_1358915 : Nat := 4983230072969 + 3 ^ 40 * 1358915 * 2
def baseEnd_1358915 : Nat := 310122917157624876672431

theorem tailTrace_1358915 : CollatzResearch.WordTrace tailWord_1358915 prefixEnd_1358915 310122917157624876672431 := by
  unfold tailWord_1358915
  simp only [CollatzResearch.WordTrace]
  refine ⟨49563701871890514049942199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33042467914593676033294799 49563701871890514049942199)
  ·
    refine ⟨74345552807835771074913299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49563701871890514049942199 74345552807835771074913299)
    ·
      refine ⟨111518329211753656612369949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74345552807835771074913299 111518329211753656612369949)
      ·
        refine ⟨41819373454407621229638731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111518329211753656612369949 41819373454407621229638731)
        ·
          refine ⟨62729060181611431844458097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41819373454407621229638731 62729060181611431844458097)
          ·
            refine ⟨47046795136208573883343573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62729060181611431844458097 47046795136208573883343573)
            ·
              refine ⟨1102659261004888450390865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 47046795136208573883343573 1102659261004888450390865)
              ·
                refine ⟨826994445753666337793149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102659261004888450390865 826994445753666337793149)
                ·
                  refine ⟨310122917157624876672431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 826994445753666337793149 310122917157624876672431)
                  ·
                    rfl

theorem cell21_1358915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 2, 3].length) (baseStart_1358915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358915 prefixEnd_1358915 := by exact prefixLift 1358915
  have htrace : WordTrace (prefixWord ++ tailWord_1358915) baseStart_1358915 baseEnd_1358915 := by
    simpa [prefixWord, tailWord_1358915, baseEnd_1358915] using wordTrace_append hprefix tailTrace_1358915
  have hstable : (prefixWord ++ tailWord_1358915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358915).length < 2 ^ (prefixWord ++ tailWord_1358915).sum := by decide
  have hdescent : baseEnd_1358915 < baseStart_1358915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358929 : List Nat := [1, 2, 2, 1, 3, 1, 6, 1, 4]
def baseStart_1358929 : Nat := 118140960795 + 1358929 * 2 ^ 59
def prefixEnd_1358929 : Nat := 4983230072969 + 3 ^ 40 * 1358929 * 2
def baseEnd_1358929 : Nat := 310126112148363963439069

theorem tailTrace_1358929 : CollatzResearch.WordTrace tailWord_1358929 prefixEnd_1358929 310126112148363963439069 := by
  unfold tailWord_1358929
  simp only [CollatzResearch.WordTrace]
  refine ⟨49564212493839794440951841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33042808329226529627301227 49564212493839794440951841)
  ·
    refine ⟨37173159370379845830713881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49564212493839794440951841 37173159370379845830713881)
    ·
      refine ⟨27879869527784884373035411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37173159370379845830713881 27879869527784884373035411)
      ·
        refine ⟨41819804291677326559553117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27879869527784884373035411 41819804291677326559553117)
        ·
          refine ⟨15682426609378997459832419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41819804291677326559553117 15682426609378997459832419)
          ·
            refine ⟨23523639914068496189748629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15682426609378997459832419 23523639914068496189748629)
            ·
              refine ⟨1102670620971960758894467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23523639914068496189748629 1102670620971960758894467)
              ·
                refine ⟨1654005931457941138341701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1102670620971960758894467 1654005931457941138341701)
                ·
                  refine ⟨310126112148363963439069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654005931457941138341701 310126112148363963439069)
                  ·
                    rfl

theorem cell21_1358929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_1358929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358929 prefixEnd_1358929 := by exact prefixLift 1358929
  have htrace : WordTrace (prefixWord ++ tailWord_1358929) baseStart_1358929 baseEnd_1358929 := by
    simpa [prefixWord, tailWord_1358929, baseEnd_1358929] using wordTrace_append hprefix tailTrace_1358929
  have hstable : (prefixWord ++ tailWord_1358929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358929).length < 2 ^ (prefixWord ++ tailWord_1358929).sum := by decide
  have hdescent : baseEnd_1358929 < baseStart_1358929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1358971 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_1358971 : Nat := 118140960795 + 1358971 * 2 ^ 59
def prefixEnd_1358971 : Nat := 4983230072969 + 3 ^ 40 * 1358971 * 2
def baseEnd_1358971 : Nat := 310135697120581223738983

theorem tailTrace_1358971 : CollatzResearch.WordTrace tailWord_1358971 prefixEnd_1358971 310135697120581223738983 := by
  unfold tailWord_1358971
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565744359687635613980767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33043829573125090409320511 49565744359687635613980767)
  ·
    refine ⟨74348616539531453420971151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49565744359687635613980767 74348616539531453420971151)
    ·
      refine ⟨111522924809297180131456727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74348616539531453420971151 111522924809297180131456727)
      ·
        refine ⟨167284387213945770197185091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111522924809297180131456727 167284387213945770197185091)
        ·
          refine ⟨250926580820918655295777637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167284387213945770197185091 250926580820918655295777637)
          ·
            refine ⟨47048733903922247867958307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250926580820918655295777637 47048733903922247867958307)
            ·
              refine ⟨70573100855883371801937461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47048733903922247867958307 70573100855883371801937461)
              ·
                refine ⟨6616228205239066106431637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70573100855883371801937461 6616228205239066106431637)
                ·
                  refine ⟨310135697120581223738983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6616228205239066106431637 310135697120581223738983)
                  ·
                    rfl

theorem cell21_1358971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_1358971 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1358971 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1358971 prefixEnd_1358971 := by exact prefixLift 1358971
  have htrace : WordTrace (prefixWord ++ tailWord_1358971) baseStart_1358971 baseEnd_1358971 := by
    simpa [prefixWord, tailWord_1358971, baseEnd_1358971] using wordTrace_append hprefix tailTrace_1358971
  have hstable : (prefixWord ++ tailWord_1358971).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1358971).length < 2 ^ (prefixWord ++ tailWord_1358971).sum := by decide
  have hdescent : baseEnd_1358971 < baseStart_1358971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1358971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359033 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 5]
def baseStart_1359033 : Nat := 118140960795 + 1359033 * 2 ^ 59
def prefixEnd_1359033 : Nat := 4983230072969 + 3 ^ 40 * 1359033 * 2
def baseEnd_1359033 : Nat := 310149846365282893705523

theorem tailTrace_1359033 : CollatzResearch.WordTrace tailWord_1359033 prefixEnd_1359033 310149846365282893705523 := by
  unfold tailWord_1359033
  simp only [CollatzResearch.WordTrace]
  refine ⟨49568005685463020202737753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33045337123642013468491835 49568005685463020202737753)
  ·
    refine ⟨37176004264097265152053315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49568005685463020202737753 37176004264097265152053315)
    ·
      refine ⟨55764006396145897728079973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37176004264097265152053315 55764006396145897728079973)
      ·
        refine ⟨10455751199277355824014995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55764006396145897728079973 10455751199277355824014995)
        ·
          refine ⟨15683626798916033736022493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10455751199277355824014995 15683626798916033736022493)
          ·
            refine ⟨5881360049593512651008435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15683626798916033736022493 5881360049593512651008435)
            ·
              refine ⟨8822040074390268976512653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5881360049593512651008435 8822040074390268976512653)
              ·
                refine ⟨3308265027896350866192245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8822040074390268976512653 3308265027896350866192245)
                ·
                  refine ⟨310149846365282893705523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3308265027896350866192245 310149846365282893705523)
                  ·
                    rfl

theorem cell21_1359033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_1359033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359033 prefixEnd_1359033 := by exact prefixLift 1359033
  have htrace : WordTrace (prefixWord ++ tailWord_1359033) baseStart_1359033 baseEnd_1359033 := by
    simpa [prefixWord, tailWord_1359033, baseEnd_1359033] using wordTrace_append hprefix tailTrace_1359033
  have hstable : (prefixWord ++ tailWord_1359033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359033).length < 2 ^ (prefixWord ++ tailWord_1359033).sum := by decide
  have hdescent : baseEnd_1359033 < baseStart_1359033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359053 : List Nat := [1, 6, 2, 2, 1, 1, 1, 7]
def baseStart_1359053 : Nat := 118140960795 + 1359053 * 2 ^ 59
def prefixEnd_1359053 : Nat := 4983230072969 + 3 ^ 40 * 1359053 * 2
def baseEnd_1359053 : Nat := 103384803545922434457383

theorem tailTrace_1359053 : CollatzResearch.WordTrace tailWord_1359053 prefixEnd_1359053 103384803545922434457383 := by
  unfold tailWord_1359053
  simp only [CollatzResearch.WordTrace]
  refine ⟨49568735145390563618465813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33045823430260375745643875 49568735145390563618465813)
  ·
    refine ⟨2323534459940182669615585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49568735145390563618465813 2323534459940182669615585)
    ·
      refine ⟨1742650844955137002211689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2323534459940182669615585 1742650844955137002211689)
      ·
        refine ⟨1306988133716352751658767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1742650844955137002211689 1306988133716352751658767)
        ·
          refine ⟨1960482200574529127488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306988133716352751658767 1960482200574529127488151)
          ·
            refine ⟨2940723300861793691232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960482200574529127488151 2940723300861793691232227)
            ·
              refine ⟨4411084951292690536848341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940723300861793691232227 4411084951292690536848341)
              ·
                refine ⟨103384803545922434457383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4411084951292690536848341 103384803545922434457383)
                ·
                  rfl

theorem cell21_1359053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 7].length) (baseStart_1359053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359053 prefixEnd_1359053 := by exact prefixLift 1359053
  have htrace : WordTrace (prefixWord ++ tailWord_1359053) baseStart_1359053 baseEnd_1359053 := by
    simpa [prefixWord, tailWord_1359053, baseEnd_1359053] using wordTrace_append hprefix tailTrace_1359053
  have hstable : (prefixWord ++ tailWord_1359053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359053).length < 2 ^ (prefixWord ++ tailWord_1359053).sum := by decide
  have hdescent : baseEnd_1359053 < baseStart_1359053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359202 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1359202 : Nat := 118140960795 + 1359202 * 2 ^ 59
def prefixEnd_1359202 : Nat := 4983230072969 + 3 ^ 40 * 1359202 * 2
def baseEnd_1359202 : Nat := 310188414467776155388511

theorem tailTrace_1359202 : CollatzResearch.WordTrace tailWord_1359202 prefixEnd_1359202 310188414467776155388511 := by
  unfold tailWord_1359202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393542405462690516409965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33049446414567174710426573 12393542405462690516409965)
  ·
    refine ⟨4647578402048508943653737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12393542405462690516409965 4647578402048508943653737)
    ·
      refine ⟨3485683801536381707740303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4647578402048508943653737 3485683801536381707740303)
      ·
        refine ⟨5228525702304572561610455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485683801536381707740303 5228525702304572561610455)
        ·
          refine ⟨7842788553456858842415683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228525702304572561610455 7842788553456858842415683)
          ·
            refine ⟨11764182830185288263623525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842788553456858842415683 11764182830185288263623525)
            ·
              refine ⟨2205784280659741549429411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11764182830185288263623525 2205784280659741549429411)
              ·
                refine ⟨3308676420989612324144117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205784280659741549429411 3308676420989612324144117)
                ·
                  refine ⟨310188414467776155388511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3308676420989612324144117 310188414467776155388511)
                  ·
                    rfl

theorem cell21_1359202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1359202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359202 prefixEnd_1359202 := by exact prefixLift 1359202
  have htrace : WordTrace (prefixWord ++ tailWord_1359202) baseStart_1359202 baseEnd_1359202 := by
    simpa [prefixWord, tailWord_1359202, baseEnd_1359202] using wordTrace_append hprefix tailTrace_1359202
  have hstable : (prefixWord ++ tailWord_1359202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359202).length < 2 ^ (prefixWord ++ tailWord_1359202).sum := by decide
  have hdescent : baseEnd_1359202 < baseStart_1359202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359298 : List Nat := [3, 5, 2, 1, 2, 8]
def baseStart_1359298 : Nat := 118140960795 + 1359298 * 2 ^ 59
def prefixEnd_1359298 : Nat := 4983230072969 + 3 ^ 40 * 1359298 * 2
def baseEnd_1359298 : Nat := 11489271221322271177345

theorem tailTrace_1359298 : CollatzResearch.WordTrace tailWord_1359298 prefixEnd_1359298 11489271221322271177345 := by
  unfold tailWord_1359298
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394417757375742615283637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33051780686335313640756365 12394417757375742615283637)
  ·
    refine ⟨1161976664753975870182841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12394417757375742615283637 1161976664753975870182841)
    ·
      refine ⟨871482498565481902637131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1161976664753975870182841 871482498565481902637131)
      ·
        refine ⟨1307223747848222853955697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871482498565481902637131 1307223747848222853955697)
        ·
          refine ⟨980417810886167140466773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307223747848222853955697 980417810886167140466773)
          ·
            refine ⟨11489271221322271177345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 980417810886167140466773 11489271221322271177345)
            ·
              rfl

theorem cell21_1359298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 8].length) (baseStart_1359298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359298 prefixEnd_1359298 := by exact prefixLift 1359298
  have htrace : WordTrace (prefixWord ++ tailWord_1359298) baseStart_1359298 baseEnd_1359298 := by
    simpa [prefixWord, tailWord_1359298, baseEnd_1359298] using wordTrace_append hprefix tailTrace_1359298
  have hstable : (prefixWord ++ tailWord_1359298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359298).length < 2 ^ (prefixWord ++ tailWord_1359298).sum := by decide
  have hdescent : baseEnd_1359298 < baseStart_1359298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359354 : List Nat := [3, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_1359354 : Nat := 118140960795 + 1359354 * 2 ^ 59
def prefixEnd_1359354 : Nat := 4983230072969 + 3 ^ 40 * 1359354 * 2
def baseEnd_1359354 : Nat := 310223102938657668854867

theorem tailTrace_1359354 : CollatzResearch.WordTrace tailWord_1359354 prefixEnd_1359354 310223102938657668854867 := by
  unfold tailWord_1359354
  simp only [CollatzResearch.WordTrace]
  refine ⟨12394928379325023006293279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33053142344866728016782077 12394928379325023006293279)
  ·
    refine ⟨18592392568987534509439919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12394928379325023006293279 18592392568987534509439919)
    ·
      refine ⟨27888588853481301764159879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18592392568987534509439919 27888588853481301764159879)
      ·
        refine ⟨41832883280221952646239819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27888588853481301764159879 41832883280221952646239819)
        ·
          refine ⟨62749324920332928969359729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41832883280221952646239819 62749324920332928969359729)
          ·
            refine ⟨47061993690249696727019797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62749324920332928969359729 47061993690249696727019797)
            ·
              refine ⟨2206030954230454534079053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47061993690249696727019797 2206030954230454534079053)
              ·
                refine ⟨827261607836420450279645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2206030954230454534079053 827261607836420450279645)
                ·
                  refine ⟨310223102938657668854867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827261607836420450279645 310223102938657668854867)
                  ·
                    rfl

theorem cell21_1359354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_1359354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359354 prefixEnd_1359354 := by exact prefixLift 1359354
  have htrace : WordTrace (prefixWord ++ tailWord_1359354) baseStart_1359354 baseEnd_1359354 := by
    simpa [prefixWord, tailWord_1359354, baseEnd_1359354] using wordTrace_append hprefix tailTrace_1359354
  have hstable : (prefixWord ++ tailWord_1359354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359354).length < 2 ^ (prefixWord ++ tailWord_1359354).sum := by decide
  have hdescent : baseEnd_1359354 < baseStart_1359354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359368 : List Nat := [2, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_1359368 : Nat := 118140960795 + 1359368 * 2 ^ 59
def prefixEnd_1359368 : Nat := 4983230072969 + 3 ^ 40 * 1359368 * 2
def baseEnd_1359368 : Nat := 310226297929396755621505

theorem tailTrace_1359368 : CollatzResearch.WordTrace tailWord_1359368 prefixEnd_1359368 310226297929396755621505 := by
  unfold tailWord_1359368
  simp only [CollatzResearch.WordTrace]
  refine ⟨24790112069624686208091379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33053482759499581610788505 24790112069624686208091379)
  ·
    refine ⟨37185168104437029312137069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24790112069624686208091379 37185168104437029312137069)
    ·
      refine ⟨13944438039163885992051401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37185168104437029312137069 13944438039163885992051401)
      ·
        refine ⟨10458328529372914494038551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13944438039163885992051401 10458328529372914494038551)
        ·
          refine ⟨15687492794059371741057827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10458328529372914494038551 15687492794059371741057827)
          ·
            refine ⟨23531239191089057611586741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15687492794059371741057827 23531239191089057611586741)
            ·
              refine ⟨2206053674164599151086257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23531239191089057611586741 2206053674164599151086257)
              ·
                refine ⟨1654540255623449363314693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206053674164599151086257 1654540255623449363314693)
                ·
                  refine ⟨310226297929396755621505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654540255623449363314693 310226297929396755621505)
                  ·
                    rfl

theorem cell21_1359368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_1359368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359368 prefixEnd_1359368 := by exact prefixLift 1359368
  have htrace : WordTrace (prefixWord ++ tailWord_1359368) baseStart_1359368 baseEnd_1359368 := by
    simpa [prefixWord, tailWord_1359368, baseEnd_1359368] using wordTrace_append hprefix tailTrace_1359368
  have hstable : (prefixWord ++ tailWord_1359368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359368).length < 2 ^ (prefixWord ++ tailWord_1359368).sum := by decide
  have hdescent : baseEnd_1359368 < baseStart_1359368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359444 : List Nat := [2, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1359444 : Nat := 118140960795 + 1359444 * 2 ^ 59
def prefixEnd_1359444 : Nat := 4983230072969 + 3 ^ 40 * 1359444 * 2
def baseEnd_1359444 : Nat := 310243642164837512354683

theorem tailTrace_1359444 : CollatzResearch.WordTrace tailWord_1359444 prefixEnd_1359444 310243642164837512354683 := by
  unfold tailWord_1359444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791498043487018697974693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33055330724649358263966257 24791498043487018697974693)
  ·
    refine ⟨4648405883153816005870255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24791498043487018697974693 4648405883153816005870255)
    ·
      refine ⟨6972608824730724008805383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648405883153816005870255 6972608824730724008805383)
      ·
        refine ⟨10458913237096086013208075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972608824730724008805383 10458913237096086013208075)
        ·
          refine ⟨15688369855644129019812113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10458913237096086013208075 15688369855644129019812113)
          ·
            refine ⟨11766277391733096764859085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15688369855644129019812113 11766277391733096764859085)
            ·
              refine ⟨4412354021899911286822157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11766277391733096764859085 4412354021899911286822157)
              ·
                refine ⟨1654632758212466732558309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4412354021899911286822157 1654632758212466732558309)
                ·
                  refine ⟨310243642164837512354683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654632758212466732558309 310243642164837512354683)
                  ·
                    rfl

theorem cell21_1359444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1359444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359444 prefixEnd_1359444 := by exact prefixLift 1359444
  have htrace : WordTrace (prefixWord ++ tailWord_1359444) baseStart_1359444 baseEnd_1359444 := by
    simpa [prefixWord, tailWord_1359444, baseEnd_1359444] using wordTrace_append hprefix tailTrace_1359444
  have hstable : (prefixWord ++ tailWord_1359444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359444).length < 2 ^ (prefixWord ++ tailWord_1359444).sum := by decide
  have hdescent : baseEnd_1359444 < baseStart_1359444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359492 : List Nat := [2, 3, 2, 1, 5, 1, 1, 6]
def baseStart_1359492 : Nat := 118140960795 + 1359492 * 2 ^ 59
def prefixEnd_1359492 : Nat := 4983230072969 + 3 ^ 40 * 1359492 * 2
def baseEnd_1359492 : Nat := 103418198806266698518195

theorem tailTrace_1359492 : CollatzResearch.WordTrace tailWord_1359492 prefixEnd_1359492 103418198806266698518195 := by
  unfold tailWord_1359492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24792373395400070796848365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33056497860533427729131153 24792373395400070796848365)
  ·
    refine ⟨9297140023275026548818137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24792373395400070796848365 9297140023275026548818137)
    ·
      refine ⟨6972855017456269911613603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9297140023275026548818137 6972855017456269911613603)
      ·
        refine ⟨10459282526184404867420405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6972855017456269911613603 10459282526184404867420405)
        ·
          refine ⟨980557736829787956320663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10459282526184404867420405 980557736829787956320663)
          ·
            refine ⟨1470836605244681934480995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980557736829787956320663 1470836605244681934480995)
            ·
              refine ⟨2206254907867022901721493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470836605244681934480995 2206254907867022901721493)
              ·
                refine ⟨103418198806266698518195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2206254907867022901721493 103418198806266698518195)
                ·
                  rfl

theorem cell21_1359492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_1359492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359492 prefixEnd_1359492 := by exact prefixLift 1359492
  have htrace : WordTrace (prefixWord ++ tailWord_1359492) baseStart_1359492 baseEnd_1359492 := by
    simpa [prefixWord, tailWord_1359492, baseEnd_1359492] using wordTrace_append hprefix tailTrace_1359492
  have hstable : (prefixWord ++ tailWord_1359492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359492).length < 2 ^ (prefixWord ++ tailWord_1359492).sum := by decide
  have hdescent : baseEnd_1359492 < baseStart_1359492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359506 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_1359506 : Nat := 118140960795 + 1359506 * 2 ^ 59
def prefixEnd_1359506 : Nat := 4983230072969 + 3 ^ 40 * 1359506 * 2
def baseEnd_1359506 : Nat := 310257791409539182321223

theorem tailTrace_1359506 : CollatzResearch.WordTrace tailWord_1359506 prefixEnd_1359506 310257791409539182321223 := by
  unfold tailWord_1359506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12396314353187355496176593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33056838275166281323137581 12396314353187355496176593)
  ·
    refine ⟨9297235764890516622132445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12396314353187355496176593 9297235764890516622132445)
    ·
      refine ⟨3486463411833943733299667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9297235764890516622132445 3486463411833943733299667)
      ·
        refine ⟨5229695117750915599949501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3486463411833943733299667 5229695117750915599949501)
        ·
          refine ⟨1961135669156593349981063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5229695117750915599949501 1961135669156593349981063)
          ·
            refine ⟨2941703503734890024971595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961135669156593349981063 2941703503734890024971595)
            ·
              refine ⟨4412555255602335037457393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941703503734890024971595 4412555255602335037457393)
              ·
                refine ⟨3309416441701751278093045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412555255602335037457393 3309416441701751278093045)
                ·
                  refine ⟨310257791409539182321223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3309416441701751278093045 310257791409539182321223)
                  ·
                    rfl

theorem cell21_1359506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_1359506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359506 prefixEnd_1359506 := by exact prefixLift 1359506
  have htrace : WordTrace (prefixWord ++ tailWord_1359506) baseStart_1359506 baseEnd_1359506 := by
    simpa [prefixWord, tailWord_1359506, baseEnd_1359506] using wordTrace_append hprefix tailTrace_1359506
  have hstable : (prefixWord ++ tailWord_1359506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359506).length < 2 ^ (prefixWord ++ tailWord_1359506).sum := by decide
  have hdescent : baseEnd_1359506 < baseStart_1359506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359574 : List Nat := [5, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1359574 : Nat := 118140960795 + 1359574 * 2 ^ 59
def prefixEnd_1359574 : Nat := 4983230072969 + 3 ^ 40 * 1359574 * 2
def baseEnd_1359574 : Nat := 310273309935986175187751

theorem tailTrace_1359574 : CollatzResearch.WordTrace tailWord_1359574 prefixEnd_1359574 310273309935986175187751 := by
  unfold tailWord_1359574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099233598531441849886361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33058491717668713065454517 3099233598531441849886361)
  ·
    refine ⟨2324425198898581387414771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3099233598531441849886361 2324425198898581387414771)
    ·
      refine ⟨3486637798347872081122157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324425198898581387414771 3486637798347872081122157)
      ·
        refine ⟨1307489174380452030420809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3486637798347872081122157 1307489174380452030420809)
        ·
          refine ⟨980616880785339022815607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307489174380452030420809 980616880785339022815607)
          ·
            refine ⟨1470925321178008534223411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980616880785339022815607 1470925321178008534223411)
            ·
              refine ⟨2206387981767012801335117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470925321178008534223411 2206387981767012801335117)
              ·
                refine ⟨827395493162629800500669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2206387981767012801335117 827395493162629800500669)
                ·
                  refine ⟨310273309935986175187751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827395493162629800500669 310273309935986175187751)
                  ·
                    rfl

theorem cell21_1359574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1359574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359574 prefixEnd_1359574 := by exact prefixLift 1359574
  have htrace : WordTrace (prefixWord ++ tailWord_1359574) baseStart_1359574 baseEnd_1359574 := by
    simpa [prefixWord, tailWord_1359574, baseEnd_1359574] using wordTrace_append hprefix tailTrace_1359574
  have hstable : (prefixWord ++ tailWord_1359574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359574).length < 2 ^ (prefixWord ++ tailWord_1359574).sum := by decide
  have hdescent : baseEnd_1359574 < baseStart_1359574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359624 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_1359624 : Nat := 118140960795 + 1359624 * 2 ^ 59
def prefixEnd_1359624 : Nat := 4983230072969 + 3 ^ 40 * 1359624 * 2
def baseEnd_1359624 : Nat := 310284720617197199354315

theorem tailTrace_1359624 : CollatzResearch.WordTrace tailWord_1359624 prefixEnd_1359624 310284720617197199354315 := by
  unfold tailWord_1359624
  simp only [CollatzResearch.WordTrace]
  refine ⟨24794780613160964068750963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33059707484214618758334617 24794780613160964068750963)
  ·
    refine ⟨37192170919741446103126445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24794780613160964068750963 37192170919741446103126445)
    ·
      refine ⟨13947064094903042288672417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37192170919741446103126445 13947064094903042288672417)
      ·
        refine ⟨10460298071177281716504313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13947064094903042288672417 10460298071177281716504313)
        ·
          refine ⟨7845223553382961287378235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10460298071177281716504313 7845223553382961287378235)
          ·
            refine ⟨11767835330074441931067353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7845223553382961287378235 11767835330074441931067353)
            ·
              refine ⟨8825876497555831448300515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11767835330074441931067353 8825876497555831448300515)
              ·
                refine ⟨13238814746333747172450773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8825876497555831448300515 13238814746333747172450773)
                ·
                  refine ⟨310284720617197199354315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13238814746333747172450773 310284720617197199354315)
                  ·
                    rfl

theorem cell21_1359624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_1359624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359624 prefixEnd_1359624 := by exact prefixLift 1359624
  have htrace : WordTrace (prefixWord ++ tailWord_1359624) baseStart_1359624 baseEnd_1359624 := by
    simpa [prefixWord, tailWord_1359624, baseEnd_1359624] using wordTrace_append hprefix tailTrace_1359624
  have hstable : (prefixWord ++ tailWord_1359624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359624).length < 2 ^ (prefixWord ++ tailWord_1359624).sum := by decide
  have hdescent : baseEnd_1359624 < baseStart_1359624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359751 : List Nat := [1, 1, 4, 2, 4, 2, 1, 3, 3]
def baseStart_1359751 : Nat := 118140960795 + 1359751 * 2 ^ 59
def prefixEnd_1359751 : Nat := 4983230072969 + 3 ^ 40 * 1359751 * 2
def baseEnd_1359751 : Nat := 310313703747473200737389

theorem tailTrace_1359751 : CollatzResearch.WordTrace tailWord_1359751 prefixEnd_1359751 310313703747473200737389 := by
  unfold tailWord_1359751
  simp only [CollatzResearch.WordTrace]
  refine ⟨49594193296861828827375107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33062795531241219218250071 49594193296861828827375107)
  ·
    refine ⟨74391289945292743241062661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49594193296861828827375107 74391289945292743241062661)
    ·
      refine ⟨13948366864742389357699249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74391289945292743241062661 13948366864742389357699249)
      ·
        refine ⟨10461275148556792018274437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13948366864742389357699249 10461275148556792018274437)
        ·
          refine ⟨1961489090354398503426457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10461275148556792018274437 1961489090354398503426457)
          ·
            refine ⟨1471116817765798877569843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1961489090354398503426457 1471116817765798877569843)
            ·
              refine ⟨2206675226648698316354765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471116817765798877569843 2206675226648698316354765)
              ·
                refine ⟨827503209993261868633037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2206675226648698316354765 827503209993261868633037)
                ·
                  refine ⟨310313703747473200737389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827503209993261868633037 310313703747473200737389)
                  ·
                    rfl

theorem cell21_1359751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 3, 3].length) (baseStart_1359751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359751 prefixEnd_1359751 := by exact prefixLift 1359751
  have htrace : WordTrace (prefixWord ++ tailWord_1359751) baseStart_1359751 baseEnd_1359751 := by
    simpa [prefixWord, tailWord_1359751, baseEnd_1359751] using wordTrace_append hprefix tailTrace_1359751
  have hstable : (prefixWord ++ tailWord_1359751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359751).length < 2 ^ (prefixWord ++ tailWord_1359751).sum := by decide
  have hdescent : baseEnd_1359751 < baseStart_1359751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359762 : List Nat := [3, 2, 3, 2, 1, 1, 9]
def baseStart_1359762 : Nat := 118140960795 + 1359762 * 2 ^ 59
def prefixEnd_1359762 : Nat := 4983230072969 + 3 ^ 40 * 1359762 * 2
def baseEnd_1359762 : Nat := 34479579344148847339337

theorem tailTrace_1359762 : CollatzResearch.WordTrace tailWord_1359762 prefixEnd_1359762 34479579344148847339337 := by
  unfold tailWord_1359762
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398648624955494426506385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33063062999881318470683693 12398648624955494426506385)
  ·
    refine ⟨9298986468716620819879789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12398648624955494426506385 9298986468716620819879789)
    ·
      refine ⟨3487119925768732807454921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9298986468716620819879789 3487119925768732807454921)
      ·
        refine ⟨2615339944326549605591191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3487119925768732807454921 2615339944326549605591191)
        ·
          refine ⟨3923009916489824408386787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2615339944326549605591191 3923009916489824408386787)
          ·
            refine ⟨5884514874734736612580181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3923009916489824408386787 5884514874734736612580181)
            ·
              refine ⟨34479579344148847339337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5884514874734736612580181 34479579344148847339337)
              ·
                rfl

theorem cell21_1359762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 9].length) (baseStart_1359762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359762 prefixEnd_1359762 := by exact prefixLift 1359762
  have htrace : WordTrace (prefixWord ++ tailWord_1359762) baseStart_1359762 baseEnd_1359762 := by
    simpa [prefixWord, tailWord_1359762, baseEnd_1359762] using wordTrace_append hprefix tailTrace_1359762
  have hstable : (prefixWord ++ tailWord_1359762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359762).length < 2 ^ (prefixWord ++ tailWord_1359762).sum := by decide
  have hdescent : baseEnd_1359762 < baseStart_1359762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359768 : List Nat := [2, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_1359768 : Nat := 118140960795 + 1359768 * 2 ^ 59
def prefixEnd_1359768 : Nat := 4983230072969 + 3 ^ 40 * 1359768 * 2
def baseEnd_1359768 : Nat := 310317583379084948954021

theorem tailTrace_1359768 : CollatzResearch.WordTrace tailWord_1359768 prefixEnd_1359768 310317583379084948954021 := by
  unfold tailWord_1359768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24797406668900120365371979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33063208891866827153829305 24797406668900120365371979)
  ·
    refine ⟨37196110003350180548057969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24797406668900120365371979 37196110003350180548057969)
    ·
      refine ⟨27897082502512635411043477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37196110003350180548057969 27897082502512635411043477)
      ·
        refine ⟨1307675742305279784892663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27897082502512635411043477 1307675742305279784892663)
        ·
          refine ⟨1961513613457919677338995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307675742305279784892663 1961513613457919677338995)
          ·
            refine ⟨2942270420186879516008493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961513613457919677338995 2942270420186879516008493)
            ·
              refine ⟨1103351407570079818503185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2942270420186879516008493 1103351407570079818503185)
              ·
                refine ⟨827513555677559863877389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103351407570079818503185 827513555677559863877389)
                ·
                  refine ⟨310317583379084948954021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827513555677559863877389 310317583379084948954021)
                  ·
                    rfl

theorem cell21_1359768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_1359768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359768 prefixEnd_1359768 := by exact prefixLift 1359768
  have htrace : WordTrace (prefixWord ++ tailWord_1359768) baseStart_1359768 baseEnd_1359768 := by
    simpa [prefixWord, tailWord_1359768, baseEnd_1359768] using wordTrace_append hprefix tailTrace_1359768
  have hstable : (prefixWord ++ tailWord_1359768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359768).length < 2 ^ (prefixWord ++ tailWord_1359768).sum := by decide
  have hdescent : baseEnd_1359768 < baseStart_1359768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359869 : List Nat := [1, 4, 1, 1, 1, 2, 3, 5, 3]
def baseStart_1359869 : Nat := 118140960795 + 1359869 * 2 ^ 59
def prefixEnd_1359869 : Nat := 4983230072969 + 3 ^ 40 * 1359869 * 2
def baseEnd_1359869 : Nat := 310340632955131217770481

theorem tailTrace_1359869 : CollatzResearch.WordTrace tailWord_1359869 prefixEnd_1359869 310340632955131217770481 := by
  unfold tailWord_1359869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49598497110434334980170661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33065664740289556653447107 49598497110434334980170661)
  ·
    refine ⟨9299718208206437808781999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49598497110434334980170661 9299718208206437808781999)
    ·
      refine ⟨13949577312309656713172999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9299718208206437808781999 13949577312309656713172999)
      ·
        refine ⟨20924365968464485069759499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13949577312309656713172999 20924365968464485069759499)
        ·
          refine ⟨31386548952696727604639249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924365968464485069759499 31386548952696727604639249)
          ·
            refine ⟨23539911714522545703479437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31386548952696727604639249 23539911714522545703479437)
            ·
              refine ⟨8827466892945954638804789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23539911714522545703479437 8827466892945954638804789)
              ·
                refine ⟨827575021213683247387949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8827466892945954638804789 827575021213683247387949)
                ·
                  refine ⟨310340632955131217770481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827575021213683247387949 310340632955131217770481)
                  ·
                    rfl

theorem cell21_1359869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_1359869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359869 prefixEnd_1359869 := by exact prefixLift 1359869
  have htrace : WordTrace (prefixWord ++ tailWord_1359869) baseStart_1359869 baseEnd_1359869 := by
    simpa [prefixWord, tailWord_1359869, baseEnd_1359869] using wordTrace_append hprefix tailTrace_1359869
  have hstable : (prefixWord ++ tailWord_1359869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359869).length < 2 ^ (prefixWord ++ tailWord_1359869).sum := by decide
  have hdescent : baseEnd_1359869 < baseStart_1359869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359914 : List Nat := [3, 1, 4, 1, 2, 2, 1, 7]
def baseStart_1359914 : Nat := 118140960795 + 1359914 * 2 ^ 59
def prefixEnd_1359914 : Nat := 4983230072969 + 3 ^ 40 * 1359914 * 2
def baseEnd_1359914 : Nat := 103450300856073713173463

theorem tailTrace_1359914 : CollatzResearch.WordTrace tailWord_1359914 prefixEnd_1359914 103450300856073713173463 := by
  unfold tailWord_1359914
  simp only [CollatzResearch.WordTrace]
  refine ⟨12400034598817826916389699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33066758930180871777039197 12400034598817826916389699)
  ·
    refine ⟨18600051898226740374584549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12400034598817826916389699 18600051898226740374584549)
    ·
      refine ⟨3487509730917513820234603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18600051898226740374584549 3487509730917513820234603)
      ·
        refine ⟨5231264596376270730351905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3487509730917513820234603 5231264596376270730351905)
        ·
          refine ⟨3923448447282203047763929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5231264596376270730351905 3923448447282203047763929)
          ·
            refine ⟨2942586335461652285822947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3923448447282203047763929 2942586335461652285822947)
            ·
              refine ⟨4413879503192478428734421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942586335461652285822947 4413879503192478428734421)
              ·
                refine ⟨103450300856073713173463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4413879503192478428734421 103450300856073713173463)
                ·
                  rfl

theorem cell21_1359914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_1359914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359914 prefixEnd_1359914 := by exact prefixLift 1359914
  have htrace : WordTrace (prefixWord ++ tailWord_1359914) baseStart_1359914 baseEnd_1359914 := by
    simpa [prefixWord, tailWord_1359914, baseEnd_1359914] using wordTrace_append hprefix tailTrace_1359914
  have hstable : (prefixWord ++ tailWord_1359914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359914).length < 2 ^ (prefixWord ++ tailWord_1359914).sum := by decide
  have hdescent : baseEnd_1359914 < baseStart_1359914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1359973 : List Nat := [1, 3, 1, 3, 2, 2, 2, 7]
def baseStart_1359973 : Nat := 118140960795 + 1359973 * 2 ^ 59
def prefixEnd_1359973 : Nat := 4983230072969 + 3 ^ 40 * 1359973 * 2
def baseEnd_1359973 : Nat := 103454789057350049345645

theorem tailTrace_1359973 : CollatzResearch.WordTrace tailWord_1359973 prefixEnd_1359973 103454789057350049345645 := by
  unfold tailWord_1359973
  simp only [CollatzResearch.WordTrace]
  refine ⟨49602290302057560741956573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33068193534705040494637715 49602290302057560741956573)
  ·
    refine ⟨18600858863271585278233715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49602290302057560741956573 18600858863271585278233715)
    ·
      refine ⟨27901288294907377917350573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18600858863271585278233715 27901288294907377917350573)
      ·
        refine ⟨10462983110590266719006465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27901288294907377917350573 10462983110590266719006465)
        ·
          refine ⟨7847237332942700039254849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10462983110590266719006465 7847237332942700039254849)
          ·
            refine ⟨5885427999707025029441137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7847237332942700039254849 5885427999707025029441137)
            ·
              refine ⟨4414070999780268772080853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5885427999707025029441137 4414070999780268772080853)
              ·
                refine ⟨103454789057350049345645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4414070999780268772080853 103454789057350049345645)
                ·
                  rfl

theorem cell21_1359973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_1359973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1359973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1359973 prefixEnd_1359973 := by exact prefixLift 1359973
  have htrace : WordTrace (prefixWord ++ tailWord_1359973) baseStart_1359973 baseEnd_1359973 := by
    simpa [prefixWord, tailWord_1359973, baseEnd_1359973] using wordTrace_append hprefix tailTrace_1359973
  have hstable : (prefixWord ++ tailWord_1359973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1359973).length < 2 ^ (prefixWord ++ tailWord_1359973).sum := by decide
  have hdescent : baseEnd_1359973 < baseStart_1359973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1359973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360004 : List Nat := [2, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1360004 : Nat := 118140960795 + 1360004 * 2 ^ 59
def prefixEnd_1360004 : Nat := 4983230072969 + 3 ^ 40 * 1360004 * 2
def baseEnd_1360004 : Nat := 310371441794400983020205

theorem tailTrace_1360004 : CollatzResearch.WordTrace tailWord_1360004 prefixEnd_1360004 310371441794400983020205 := by
  unfold tailWord_1360004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24801710482472626518167533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33068947309963502024223377 24801710482472626518167533)
  ·
    refine ⟨9300641430927234944312825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24801710482472626518167533 9300641430927234944312825)
    ·
      refine ⟨6975481073195426208234619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9300641430927234944312825 6975481073195426208234619)
      ·
        refine ⟨10463221609793139312351929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6975481073195426208234619 10463221609793139312351929)
        ·
          refine ⟨7847416207344854484263947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10463221609793139312351929 7847416207344854484263947)
          ·
            refine ⟨11771124311017281726395921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7847416207344854484263947 11771124311017281726395921)
            ·
              refine ⟨8828343233262961294796941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11771124311017281726395921 8828343233262961294796941)
              ·
                refine ⟨3310628712473610485548853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8828343233262961294796941 3310628712473610485548853)
                ·
                  refine ⟨310371441794400983020205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3310628712473610485548853 310371441794400983020205)
                  ·
                    rfl

theorem cell21_1360004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1360004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360004 prefixEnd_1360004 := by exact prefixLift 1360004
  have htrace : WordTrace (prefixWord ++ tailWord_1360004) baseStart_1360004 baseEnd_1360004 := by
    simpa [prefixWord, tailWord_1360004, baseEnd_1360004] using wordTrace_append hprefix tailTrace_1360004
  have hstable : (prefixWord ++ tailWord_1360004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360004).length < 2 ^ (prefixWord ++ tailWord_1360004).sum := by decide
  have hdescent : baseEnd_1360004 < baseStart_1360004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360139 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 7]
def baseStart_1360139 : Nat := 118140960795 + 1360139 * 2 ^ 59
def prefixEnd_1360139 : Nat := 4983230072969 + 3 ^ 40 * 1360139 * 2
def baseEnd_1360139 : Nat := 310402250633670748269929

theorem tailTrace_1360139 : CollatzResearch.WordTrace tailWord_1360139 prefixEnd_1360139 310402250633670748269929 := by
  unfold tailWord_1360139
  simp only [CollatzResearch.WordTrace]
  refine ⟨49608344819456171092499471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33072229879637447394999647 49608344819456171092499471)
  ·
    refine ⟨74412517229184256638749207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49608344819456171092499471 74412517229184256638749207)
    ·
      refine ⟨111618775843776384958123811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74412517229184256638749207 111618775843776384958123811)
      ·
        refine ⟨167428163765664577437185717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111618775843776384958123811 167428163765664577437185717)
        ·
          refine ⟨15696390353031054134736161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167428163765664577437185717 15696390353031054134736161)
          ·
            refine ⟨11772292764773290601052121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15696390353031054134736161 11772292764773290601052121)
            ·
              refine ⟨8829219573579967950789091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11772292764773290601052121 8829219573579967950789091)
              ·
                refine ⟨13243829360369951926183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8829219573579967950789091 13243829360369951926183637)
                ·
                  refine ⟨310402250633670748269929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13243829360369951926183637 310402250633670748269929)
                  ·
                    rfl

theorem cell21_1360139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_1360139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360139 prefixEnd_1360139 := by exact prefixLift 1360139
  have htrace : WordTrace (prefixWord ++ tailWord_1360139) baseStart_1360139 baseEnd_1360139 := by
    simpa [prefixWord, tailWord_1360139, baseEnd_1360139] using wordTrace_append hprefix tailTrace_1360139
  have hstable : (prefixWord ++ tailWord_1360139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360139).length < 2 ^ (prefixWord ++ tailWord_1360139).sum := by decide
  have hdescent : baseEnd_1360139 < baseStart_1360139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360215 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 7]
def baseStart_1360215 : Nat := 118140960795 + 1360215 * 2 ^ 59
def prefixEnd_1360215 : Nat := 4983230072969 + 3 ^ 40 * 1360215 * 2
def baseEnd_1360215 : Nat := 310419594869111505003107

theorem tailTrace_1360215 : CollatzResearch.WordTrace tailWord_1360215 prefixEnd_1360215 310419594869111505003107 := by
  unfold tailWord_1360215
  simp only [CollatzResearch.WordTrace]
  refine ⟨49611116767180836072266099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33074077844787224048177399 49611116767180836072266099)
  ·
    refine ⟨74416675150771254108399149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49611116767180836072266099 74416675150771254108399149)
    ·
      refine ⟨27906253181539220290649681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74416675150771254108399149 27906253181539220290649681)
      ·
        refine ⟨20929689886154415217987261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27906253181539220290649681 20929689886154415217987261)
        ·
          refine ⟨7848633707307905706745223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20929689886154415217987261 7848633707307905706745223)
          ·
            refine ⟨11772950560961858560117835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848633707307905706745223 11772950560961858560117835)
            ·
              refine ⟨17659425841442787840176753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11772950560961858560117835 17659425841442787840176753)
              ·
                refine ⟨13244569381082090880132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17659425841442787840176753 13244569381082090880132565)
                ·
                  refine ⟨310419594869111505003107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13244569381082090880132565 310419594869111505003107)
                  ·
                    rfl

theorem cell21_1360215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_1360215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360215 prefixEnd_1360215 := by exact prefixLift 1360215
  have htrace : WordTrace (prefixWord ++ tailWord_1360215) baseStart_1360215 baseEnd_1360215 := by
    simpa [prefixWord, tailWord_1360215, baseEnd_1360215] using wordTrace_append hprefix tailTrace_1360215
  have hstable : (prefixWord ++ tailWord_1360215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360215).length < 2 ^ (prefixWord ++ tailWord_1360215).sum := by decide
  have hdescent : baseEnd_1360215 < baseStart_1360215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360232 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_1360232 : Nat := 118140960795 + 1360232 * 2 ^ 59
def prefixEnd_1360232 : Nat := 4983230072969 + 3 ^ 40 * 1360232 * 2
def baseEnd_1360232 : Nat := 310423474500723253219739

theorem tailTrace_1360232 : CollatzResearch.WordTrace tailWord_1360232 prefixEnd_1360232 310423474500723253219739 := by
  unfold tailWord_1360232
  simp only [CollatzResearch.WordTrace]
  refine ⟨24805868404059623987817475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33074491205412831983756633 24805868404059623987817475)
  ·
    refine ⟨37208802606089435981726213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24805868404059623987817475 37208802606089435981726213)
    ·
      refine ⟨6976650488641769246573665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37208802606089435981726213 6976650488641769246573665)
      ·
        refine ⟨5232487866481326934930249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6976650488641769246573665 5232487866481326934930249)
        ·
          refine ⟨3924365899860995201197687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5232487866481326934930249 3924365899860995201197687)
          ·
            refine ⟨5886548849791492801796531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924365899860995201197687 5886548849791492801796531)
            ·
              refine ⟨8829823274687239202694797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5886548849791492801796531 8829823274687239202694797)
              ·
                refine ⟨3311183728007714701010549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829823274687239202694797 3311183728007714701010549)
                ·
                  refine ⟨310423474500723253219739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311183728007714701010549 310423474500723253219739)
                  ·
                    rfl

theorem cell21_1360232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_1360232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360232 prefixEnd_1360232 := by exact prefixLift 1360232
  have htrace : WordTrace (prefixWord ++ tailWord_1360232) baseStart_1360232 baseEnd_1360232 := by
    simpa [prefixWord, tailWord_1360232, baseEnd_1360232] using wordTrace_append hprefix tailTrace_1360232
  have hstable : (prefixWord ++ tailWord_1360232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360232).length < 2 ^ (prefixWord ++ tailWord_1360232).sum := by decide
  have hdescent : baseEnd_1360232 < baseStart_1360232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360342 : List Nat := [5, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1360342 : Nat := 118140960795 + 1360342 * 2 ^ 59
def prefixEnd_1360342 : Nat := 4983230072969 + 3 ^ 40 * 1360342 * 2
def baseEnd_1360342 : Nat := 310448577999387506386181

theorem tailTrace_1360342 : CollatzResearch.WordTrace tailWord_1360342 prefixEnd_1360342 310448577999387506386181 := by
  unfold tailWord_1360342
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100984302357546047633705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33077165891813824508092853 3100984302357546047633705)
  ·
    refine ⟨2325738226768159535725279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3100984302357546047633705 2325738226768159535725279)
    ·
      refine ⟨3488607340152239303587919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325738226768159535725279 3488607340152239303587919)
      ·
        refine ⟨5232911010228358955381879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488607340152239303587919 5232911010228358955381879)
        ·
          refine ⟨7849366515342538433072819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232911010228358955381879 7849366515342538433072819)
          ·
            refine ⟨11774049773013807649609229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7849366515342538433072819 11774049773013807649609229)
            ·
              refine ⟨4415268664880177868603461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11774049773013807649609229 4415268664880177868603461)
              ·
                refine ⟨827862874665033350363149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4415268664880177868603461 827862874665033350363149)
                ·
                  refine ⟨310448577999387506386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 827862874665033350363149 310448577999387506386181)
                  ·
                    rfl

theorem cell21_1360342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1360342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360342 prefixEnd_1360342 := by exact prefixLift 1360342
  have htrace : WordTrace (prefixWord ++ tailWord_1360342) baseStart_1360342 baseEnd_1360342 := by
    simpa [prefixWord, tailWord_1360342, baseEnd_1360342] using wordTrace_append hprefix tailTrace_1360342
  have hstable : (prefixWord ++ tailWord_1360342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360342).length < 2 ^ (prefixWord ++ tailWord_1360342).sum := by decide
  have hdescent : baseEnd_1360342 < baseStart_1360342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360390 : List Nat := [6, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1360390 : Nat := 118140960795 + 1360390 * 2 ^ 59
def prefixEnd_1360390 : Nat := 4983230072969 + 3 ^ 40 * 1360390 * 2
def baseEnd_1360390 : Nat := 310459532253350089586083

theorem tailTrace_1360390 : CollatzResearch.WordTrace tailWord_1360390 prefixEnd_1360390 310459532253350089586083 := by
  unfold tailWord_1360390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1550546860673338779996457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 33078333027697893973257749 1550546860673338779996457)
  ·
    refine ⟨1162910145505004084997343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1550546860673338779996457 1162910145505004084997343)
    ·
      refine ⟨1744365218257506127496015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1162910145505004084997343 1744365218257506127496015)
      ·
        refine ⟨2616547827386259191244023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744365218257506127496015 2616547827386259191244023)
        ·
          refine ⟨3924821741079388786866035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2616547827386259191244023 3924821741079388786866035)
          ·
            refine ⟨5887232611619083180299053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924821741079388786866035 5887232611619083180299053)
            ·
              refine ⟨2207712229357156192612145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5887232611619083180299053 2207712229357156192612145)
              ·
                refine ⟨1655784172017867144459109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207712229357156192612145 1655784172017867144459109)
                ·
                  refine ⟨310459532253350089586083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655784172017867144459109 310459532253350089586083)
                  ·
                    rfl

theorem cell21_1360390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1360390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360390 prefixEnd_1360390 := by exact prefixLift 1360390
  have htrace : WordTrace (prefixWord ++ tailWord_1360390) baseStart_1360390 baseEnd_1360390 := by
    simpa [prefixWord, tailWord_1360390, baseEnd_1360390] using wordTrace_append hprefix tailTrace_1360390
  have hstable : (prefixWord ++ tailWord_1360390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360390).length < 2 ^ (prefixWord ++ tailWord_1360390).sum := by decide
  have hdescent : baseEnd_1360390 < baseStart_1360390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360452 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1360452 : Nat := 118140960795 + 1360452 * 2 ^ 59
def prefixEnd_1360452 : Nat := 4983230072969 + 3 ^ 40 * 1360452 * 2
def baseEnd_1360452 : Nat := 310473681498051759552623

theorem tailTrace_1360452 : CollatzResearch.WordTrace tailWord_1360452 prefixEnd_1360452 310473681498051759552623 := by
  unfold tailWord_1360452
  simp only [CollatzResearch.WordTrace]
  refine ⟨24809880433661112774321805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33079840578214817032429073 24809880433661112774321805)
  ·
    refine ⟨9303705162622917290370677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24809880433661112774321805 9303705162622917290370677)
    ·
      refine ⟨872222358995898495972251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9303705162622917290370677 872222358995898495972251)
      ·
        refine ⟨1308333538493847743958377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872222358995898495972251 1308333538493847743958377)
        ·
          refine ⟨981250153870385807968783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308333538493847743958377 981250153870385807968783)
          ·
            refine ⟨1471875230805578711953175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981250153870385807968783 1471875230805578711953175)
            ·
              refine ⟨2207812846208368067929763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471875230805578711953175 2207812846208368067929763)
              ·
                refine ⟨3311719269312552101894645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207812846208368067929763 3311719269312552101894645)
                ·
                  refine ⟨310473681498051759552623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311719269312552101894645 310473681498051759552623)
                  ·
                    rfl

theorem cell21_1360452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1360452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360452 prefixEnd_1360452 := by exact prefixLift 1360452
  have htrace : WordTrace (prefixWord ++ tailWord_1360452) baseStart_1360452 baseEnd_1360452 := by
    simpa [prefixWord, tailWord_1360452, baseEnd_1360452] using wordTrace_append hprefix tailTrace_1360452
  have hstable : (prefixWord ++ tailWord_1360452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360452).length < 2 ^ (prefixWord ++ tailWord_1360452).sum := by decide
  have hdescent : baseEnd_1360452 < baseStart_1360452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360519 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_1360519 : Nat := 118140960795 + 1360519 * 2 ^ 59
def prefixEnd_1360519 : Nat := 4983230072969 + 3 ^ 40 * 1360519 * 2
def baseEnd_1360519 : Nat := 310488971810874531935819

theorem tailTrace_1360519 : CollatzResearch.WordTrace tailWord_1360519 prefixEnd_1360519 310488971810874531935819 := by
  unfold tailWord_1360519
  simp only [CollatzResearch.WordTrace]
  refine ⟨49622204558079495991332611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33081469705386330660888407 49622204558079495991332611)
  ·
    refine ⟨74433306837119243986998917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49622204558079495991332611 74433306837119243986998917)
    ·
      refine ⟨13956245031959858247562297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74433306837119243986998917 13956245031959858247562297)
      ·
        refine ⟨10467183773969893685671723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13956245031959858247562297 10467183773969893685671723)
        ·
          refine ⟨15700775660954840528507585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10467183773969893685671723 15700775660954840528507585)
          ·
            refine ⟨11775581745716130396380689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15700775660954840528507585 11775581745716130396380689)
            ·
              refine ⟨8831686309287097797285517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11775581745716130396380689 8831686309287097797285517)
              ·
                refine ⟨3311882365982661673982069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8831686309287097797285517 3311882365982661673982069)
                ·
                  refine ⟨310488971810874531935819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3311882365982661673982069 310488971810874531935819)
                  ·
                    rfl

theorem cell21_1360519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_1360519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360519 prefixEnd_1360519 := by exact prefixLift 1360519
  have htrace : WordTrace (prefixWord ++ tailWord_1360519) baseStart_1360519 baseEnd_1360519 := by
    simpa [prefixWord, tailWord_1360519, baseEnd_1360519] using wordTrace_append hprefix tailTrace_1360519
  have hstable : (prefixWord ++ tailWord_1360519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360519).length < 2 ^ (prefixWord ++ tailWord_1360519).sum := by decide
  have hdescent : baseEnd_1360519 < baseStart_1360519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360522 : List Nat := [3, 1, 2, 3, 3, 2, 1, 6]
def baseStart_1360522 : Nat := 118140960795 + 1360522 * 2 ^ 59
def prefixEnd_1360522 : Nat := 4983230072969 + 3 ^ 40 * 1360522 * 2
def baseEnd_1360522 : Nat := 103496552150582397795271

theorem tailTrace_1360522 : CollatzResearch.WordTrace tailWord_1360522 prefixEnd_1360522 103496552150582397795271 := by
  unfold tailWord_1360522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12405578494267156875922955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33081542651379085002461213 12405578494267156875922955)
  ·
    refine ⟨18608367741400735313884433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12405578494267156875922955 18608367741400735313884433)
    ·
      refine ⟨13956275806050551485413325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18608367741400735313884433 13956275806050551485413325)
      ·
        refine ⟨5233603427268956807029997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13956275806050551485413325 5233603427268956807029997)
        ·
          refine ⟨1962601285225858802636249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5233603427268956807029997 1962601285225858802636249)
          ·
            refine ⟨1471950963919394101977187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1962601285225858802636249 1471950963919394101977187)
            ·
              refine ⟨2207926445879091152965781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471950963919394101977187 2207926445879091152965781)
              ·
                refine ⟨103496552150582397795271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2207926445879091152965781 103496552150582397795271)
                ·
                  rfl

theorem cell21_1360522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_1360522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360522 prefixEnd_1360522 := by exact prefixLift 1360522
  have htrace : WordTrace (prefixWord ++ tailWord_1360522) baseStart_1360522 baseEnd_1360522 := by
    simpa [prefixWord, tailWord_1360522, baseEnd_1360522] using wordTrace_append hprefix tailTrace_1360522
  have hstable : (prefixWord ++ tailWord_1360522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360522).length < 2 ^ (prefixWord ++ tailWord_1360522).sum := by decide
  have hdescent : baseEnd_1360522 < baseStart_1360522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360533 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 10]
def baseStart_1360533 : Nat := 118140960795 + 1360533 * 2 ^ 59
def prefixEnd_1360533 : Nat := 4983230072969 + 3 ^ 40 * 1360533 * 2
def baseEnd_1360533 : Nat := 310492166801613618702457

theorem tailTrace_1360533 : CollatzResearch.WordTrace tailWord_1360533 prefixEnd_1360533 310492166801613618702457 := by
  unfold tailWord_1360533
  simp only [CollatzResearch.WordTrace]
  refine ⟨49622715180028776382342253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33081810120019184254894835 49622715180028776382342253)
  ·
    refine ⟨18608518192510791143378345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49622715180028776382342253 18608518192510791143378345)
    ·
      refine ⟨13956388644383093357533759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18608518192510791143378345 13956388644383093357533759)
      ·
        refine ⟨20934582966574640036300639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13956388644383093357533759 20934582966574640036300639)
        ·
          refine ⟨31401874449861960054450959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20934582966574640036300639 31401874449861960054450959)
          ·
            refine ⟨47102811674792940081676439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31401874449861960054450959 47102811674792940081676439)
            ·
              refine ⟨70654217512189410122514659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47102811674792940081676439 70654217512189410122514659)
              ·
                refine ⟨105981326268284115183771989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70654217512189410122514659 105981326268284115183771989)
                ·
                  refine ⟨310492166801613618702457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105981326268284115183771989 310492166801613618702457)
                  ·
                    rfl

theorem cell21_1360533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_1360533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360533 prefixEnd_1360533 := by exact prefixLift 1360533
  have htrace : WordTrace (prefixWord ++ tailWord_1360533) baseStart_1360533 baseEnd_1360533 := by
    simpa [prefixWord, tailWord_1360533, baseEnd_1360533] using wordTrace_append hprefix tailTrace_1360533
  have hstable : (prefixWord ++ tailWord_1360533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360533).length < 2 ^ (prefixWord ++ tailWord_1360533).sum := by decide
  have hdescent : baseEnd_1360533 < baseStart_1360533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360626 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_1360626 : Nat := 118140960795 + 1360626 * 2 ^ 59
def prefixEnd_1360626 : Nat := 4983230072969 + 3 ^ 40 * 1360626 * 2
def baseEnd_1360626 : Nat := 310513390668666123652267

theorem tailTrace_1360626 : CollatzResearch.WordTrace tailWord_1360626 prefixEnd_1360626 310513390668666123652267 := by
  unfold tailWord_1360626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12406526792172963316369433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33084071445794568843651821 12406526792172963316369433)
  ·
    refine ⟨9304895094129722487277075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12406526792172963316369433 9304895094129722487277075)
    ·
      refine ⟨13957342641194583730915613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9304895094129722487277075 13957342641194583730915613)
      ·
        refine ⟨5234003490447968899093355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13957342641194583730915613 5234003490447968899093355)
        ·
          refine ⟨7851005235671953348640033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5234003490447968899093355 7851005235671953348640033)
          ·
            refine ⟨5888253926753965011480025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7851005235671953348640033 5888253926753965011480025)
            ·
              refine ⟨4416190445065473758610019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5888253926753965011480025 4416190445065473758610019)
              ·
                refine ⟨6624285667598210637915029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4416190445065473758610019 6624285667598210637915029)
                ·
                  refine ⟨310513390668666123652267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6624285667598210637915029 310513390668666123652267)
                  ·
                    rfl

theorem cell21_1360626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_1360626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360626 prefixEnd_1360626 := by exact prefixLift 1360626
  have htrace : WordTrace (prefixWord ++ tailWord_1360626) baseStart_1360626 baseEnd_1360626 := by
    simpa [prefixWord, tailWord_1360626, baseEnd_1360626] using wordTrace_append hprefix tailTrace_1360626
  have hstable : (prefixWord ++ tailWord_1360626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360626).length < 2 ^ (prefixWord ++ tailWord_1360626).sum := by decide
  have hdescent : baseEnd_1360626 < baseStart_1360626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360705 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_1360705 : Nat := 118140960795 + 1360705 * 2 ^ 59
def prefixEnd_1360705 : Nat := 4983230072969 + 3 ^ 40 * 1360705 * 2
def baseEnd_1360705 : Nat := 310531419544979541835439

theorem tailTrace_1360705 : CollatzResearch.WordTrace tailWord_1360705 prefixEnd_1360705 310531419544979541835439 := by
  unfold tailWord_1360705
  simp only [CollatzResearch.WordTrace]
  refine ⟨49628988535405649757603569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33085992356937099838402379 49628988535405649757603569)
  ·
    refine ⟨37221741401554237318202677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49628988535405649757603569 37221741401554237318202677)
    ·
      refine ⟨3489538256395709748581501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37221741401554237318202677 3489538256395709748581501)
      ·
        refine ⟨1308576846148391155718063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3489538256395709748581501 1308576846148391155718063)
        ·
          refine ⟨1962865269222586733577095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308576846148391155718063 1962865269222586733577095)
          ·
            refine ⟨2944297903833880100365643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962865269222586733577095 2944297903833880100365643)
            ·
              refine ⟨4416446855750820150548465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2944297903833880100365643 4416446855750820150548465)
              ·
                refine ⟨3312335141813115112911349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4416446855750820150548465 3312335141813115112911349)
                ·
                  refine ⟨310531419544979541835439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3312335141813115112911349 310531419544979541835439)
                  ·
                    rfl

theorem cell21_1360705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_1360705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360705 prefixEnd_1360705 := by exact prefixLift 1360705
  have htrace : WordTrace (prefixWord ++ tailWord_1360705) baseStart_1360705 baseEnd_1360705 := by
    simpa [prefixWord, tailWord_1360705, baseEnd_1360705] using wordTrace_append hprefix tailTrace_1360705
  have hstable : (prefixWord ++ tailWord_1360705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360705).length < 2 ^ (prefixWord ++ tailWord_1360705).sum := by decide
  have hdescent : baseEnd_1360705 < baseStart_1360705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360778 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_1360778 : Nat := 118140960795 + 1360778 * 2 ^ 59
def prefixEnd_1360778 : Nat := 4983230072969 + 3 ^ 40 * 1360778 * 2
def baseEnd_1360778 : Nat := 310548079139547637118623

theorem tailTrace_1360778 : CollatzResearch.WordTrace tailWord_1360778 prefixEnd_1360778 310548079139547637118623 := by
  unfold tailWord_1360778
  simp only [CollatzResearch.WordTrace]
  refine ⟨12407912766035295806252747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33087767376094122150007325 12407912766035295806252747)
  ·
    refine ⟨18611869149052943709379121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12407912766035295806252747 18611869149052943709379121)
    ·
      refine ⟨13958901861789707782034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18611869149052943709379121 13958901861789707782034341)
      ·
        refine ⟨2617294099085570209131439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13958901861789707782034341 2617294099085570209131439)
        ·
          refine ⟨3925941148628355313697159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2617294099085570209131439 3925941148628355313697159)
          ·
            refine ⟨5888911722942532970545739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3925941148628355313697159 5888911722942532970545739)
            ·
              refine ⟨8833367584413799455818609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5888911722942532970545739 8833367584413799455818609)
              ·
                refine ⟨6625025688310349591863957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8833367584413799455818609 6625025688310349591863957)
                ·
                  refine ⟨310548079139547637118623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6625025688310349591863957 310548079139547637118623)
                  ·
                    rfl

theorem cell21_1360778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_1360778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360778 prefixEnd_1360778 := by exact prefixLift 1360778
  have htrace : WordTrace (prefixWord ++ tailWord_1360778) baseStart_1360778 baseEnd_1360778 := by
    simpa [prefixWord, tailWord_1360778, baseEnd_1360778] using wordTrace_append hprefix tailTrace_1360778
  have hstable : (prefixWord ++ tailWord_1360778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360778).length < 2 ^ (prefixWord ++ tailWord_1360778).sum := by decide
  have hdescent : baseEnd_1360778 < baseStart_1360778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360857 : List Nat := [1, 2, 1, 2, 5, 1, 4, 2, 3]
def baseStart_1360857 : Nat := 118140960795 + 1360857 * 2 ^ 59
def prefixEnd_1360857 : Nat := 4983230072969 + 3 ^ 40 * 1360857 * 2
def baseEnd_1360857 : Nat := 310566108015861055301795

theorem tailTrace_1360857 : CollatzResearch.WordTrace tailWord_1360857 prefixEnd_1360857 310566108015861055301795 := by
  unfold tailWord_1360857
  simp only [CollatzResearch.WordTrace]
  refine ⟨49634532430854979717136825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33089688287236653144757883 49634532430854979717136825)
  ·
    refine ⟨37225899323141234787852619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49634532430854979717136825 37225899323141234787852619)
    ·
      refine ⟨55838848984711852181778929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37225899323141234787852619 55838848984711852181778929)
      ·
        refine ⟨41879136738533889136334197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55838848984711852181778929 41879136738533889136334197)
        ·
          refine ⟨3926169069237552106531331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41879136738533889136334197 3926169069237552106531331)
          ·
            refine ⟨5889253603856328159796997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3926169069237552106531331 5889253603856328159796997)
            ·
              refine ⟨1104235050723061529961937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5889253603856328159796997 1104235050723061529961937)
              ·
                refine ⟨828176288042296147471453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104235050723061529961937 828176288042296147471453)
                ·
                  refine ⟨310566108015861055301795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828176288042296147471453 310566108015861055301795)
                  ·
                    rfl

theorem cell21_1360857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 3].length) (baseStart_1360857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360857 prefixEnd_1360857 := by exact prefixLift 1360857
  have htrace : WordTrace (prefixWord ++ tailWord_1360857) baseStart_1360857 baseEnd_1360857 := by
    simpa [prefixWord, tailWord_1360857, baseEnd_1360857] using wordTrace_append hprefix tailTrace_1360857
  have hstable : (prefixWord ++ tailWord_1360857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360857).length < 2 ^ (prefixWord ++ tailWord_1360857).sum := by decide
  have hdescent : baseEnd_1360857 < baseStart_1360857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360950 : List Nat := [5, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1360950 : Nat := 118140960795 + 1360950 * 2 ^ 59
def prefixEnd_1360950 : Nat := 4983230072969 + 3 ^ 40 * 1360950 * 2
def baseEnd_1360950 : Nat := 310587331882913560251605

theorem tailTrace_1360950 : CollatzResearch.WordTrace tailWord_1360950 prefixEnd_1360950 310587331882913560251605 := by
  unfold tailWord_1360950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102370276219878537517019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33091949613012037733514869 3102370276219878537517019)
  ·
    refine ⟨4653555414329817806275529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102370276219878537517019 4653555414329817806275529)
    ·
      refine ⟨3490166560747363354706647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4653555414329817806275529 3490166560747363354706647)
      ·
        refine ⟨5235249841121045032059971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490166560747363354706647 5235249841121045032059971)
        ·
          refine ⟨7852874761681567548089957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5235249841121045032059971 7852874761681567548089957)
          ·
            refine ⟨1472414017815293915266867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7852874761681567548089957 1472414017815293915266867)
            ·
              refine ⟨2208621026722940872900301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1472414017815293915266867 2208621026722940872900301)
              ·
                refine ⟨828232885021102827337613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2208621026722940872900301 828232885021102827337613)
                ·
                  refine ⟨310587331882913560251605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828232885021102827337613 310587331882913560251605)
                  ·
                    rfl

theorem cell21_1360950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1360950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360950 prefixEnd_1360950 := by exact prefixLift 1360950
  have htrace : WordTrace (prefixWord ++ tailWord_1360950) baseStart_1360950 baseEnd_1360950 := by
    simpa [prefixWord, tailWord_1360950, baseEnd_1360950] using wordTrace_append hprefix tailTrace_1360950
  have hstable : (prefixWord ++ tailWord_1360950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360950).length < 2 ^ (prefixWord ++ tailWord_1360950).sum := by decide
  have hdescent : baseEnd_1360950 < baseStart_1360950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1360961 : List Nat := [1, 2, 5, 1, 3, 2, 7]
def baseStart_1360961 : Nat := 118140960795 + 1360961 * 2 ^ 59
def prefixEnd_1360961 : Nat := 4983230072969 + 3 ^ 40 * 1360961 * 2
def baseEnd_1360961 : Nat := 34509982470308887285361

theorem tailTrace_1360961 : CollatzResearch.WordTrace tailWord_1360961 prefixEnd_1360961 34509982470308887285361 := by
  unfold tailWord_1360961
  simp only [CollatzResearch.WordTrace]
  refine ⟨49638325622478205478922737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33092217081652136985948491 49638325622478205478922737)
  ·
    refine ⟨37228744216858654109192053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49638325622478205478922737 37228744216858654109192053)
    ·
      refine ⟨3490194770330498822736755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37228744216858654109192053 3490194770330498822736755)
      ·
        refine ⟨5235292155495748234105133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490194770330498822736755 5235292155495748234105133)
        ·
          refine ⟨1963234558310905587789425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5235292155495748234105133 1963234558310905587789425)
          ·
            refine ⟨1472425918733179190842069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1963234558310905587789425 1472425918733179190842069)
            ·
              refine ⟨34509982470308887285361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1472425918733179190842069 34509982470308887285361)
              ·
                rfl

theorem cell21_1360961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 7].length) (baseStart_1360961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1360961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1360961 prefixEnd_1360961 := by exact prefixLift 1360961
  have htrace : WordTrace (prefixWord ++ tailWord_1360961) baseStart_1360961 baseEnd_1360961 := by
    simpa [prefixWord, tailWord_1360961, baseEnd_1360961] using wordTrace_append hprefix tailTrace_1360961
  have hstable : (prefixWord ++ tailWord_1360961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1360961).length < 2 ^ (prefixWord ++ tailWord_1360961).sum := by decide
  have hdescent : baseEnd_1360961 < baseStart_1360961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1360961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361054 : List Nat := [4, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1361054 : Nat := 118140960795 + 1361054 * 2 ^ 59
def prefixEnd_1361054 : Nat := 4983230072969 + 3 ^ 40 * 1361054 * 2
def baseEnd_1361054 : Nat := 103537022033277496839353

theorem tailTrace_1361054 : CollatzResearch.WordTrace tailWord_1361054 prefixEnd_1361054 103537022033277496839353 := by
  unfold tailWord_1361054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6205214701392660295257277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33094478407427521574705477 6205214701392660295257277)
  ·
    refine ⟨2326955513022247610721479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6205214701392660295257277 2326955513022247610721479)
    ·
      refine ⟨3490433269533371416082219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326955513022247610721479 3490433269533371416082219)
      ·
        refine ⟨5235649904300057124123329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3490433269533371416082219 5235649904300057124123329)
        ·
          refine ⟨3926737428225042843092497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5235649904300057124123329 3926737428225042843092497)
          ·
            refine ⟨2945053071168782132319373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3926737428225042843092497 2945053071168782132319373)
            ·
              refine ⟨1104394901688293299619765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2945053071168782132319373 1104394901688293299619765)
              ·
                refine ⟨103537022033277496839353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104394901688293299619765 103537022033277496839353)
                ·
                  rfl

theorem cell21_1361054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1361054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361054 prefixEnd_1361054 := by exact prefixLift 1361054
  have htrace : WordTrace (prefixWord ++ tailWord_1361054) baseStart_1361054 baseEnd_1361054 := by
    simpa [prefixWord, tailWord_1361054, baseEnd_1361054] using wordTrace_append hprefix tailTrace_1361054
  have hstable : (prefixWord ++ tailWord_1361054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361054).length < 2 ^ (prefixWord ++ tailWord_1361054).sum := by decide
  have hdescent : baseEnd_1361054 < baseStart_1361054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361079 : List Nat := [1, 1, 3, 1, 4, 1, 10]
def baseStart_1361079 : Nat := 118140960795 + 1361079 * 2 ^ 59
def prefixEnd_1361079 : Nat := 4983230072969 + 3 ^ 40 * 1361079 * 2
def baseEnd_1361079 : Nat := 34512974604493111400149

theorem tailTrace_1361079 : CollatzResearch.WordTrace tailWord_1361079 prefixEnd_1361079 34512974604493111400149 := by
  unfold tailWord_1361079
  simp only [CollatzResearch.WordTrace]
  refine ⟨49642629436050711631718291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33095086290700474421145527 49642629436050711631718291)
  ·
    refine ⟨74463944154076067447577437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49642629436050711631718291 74463944154076067447577437)
    ·
      refine ⟨27923979057778525292841539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74463944154076067447577437 27923979057778525292841539)
      ·
        refine ⟨41885968586667787939262309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27923979057778525292841539 41885968586667787939262309)
        ·
          refine ⟨7853619110000210238611683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41885968586667787939262309 7853619110000210238611683)
          ·
            refine ⟨11780428665000315357917525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7853619110000210238611683 11780428665000315357917525)
            ·
              refine ⟨34512974604493111400149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11780428665000315357917525 34512974604493111400149)
              ·
                rfl

theorem cell21_1361079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_1361079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361079 prefixEnd_1361079 := by exact prefixLift 1361079
  have htrace : WordTrace (prefixWord ++ tailWord_1361079) baseStart_1361079 baseEnd_1361079 := by
    simpa [prefixWord, tailWord_1361079, baseEnd_1361079] using wordTrace_append hprefix tailTrace_1361079
  have hstable : (prefixWord ++ tailWord_1361079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361079).length < 2 ^ (prefixWord ++ tailWord_1361079).sum := by decide
  have hdescent : baseEnd_1361079 < baseStart_1361079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361155 : List Nat := [1, 1, 1, 3, 2, 4, 1, 8]
def baseStart_1361155 : Nat := 118140960795 + 1361155 * 2 ^ 59
def prefixEnd_1361155 : Nat := 4983230072969 + 3 ^ 40 * 1361155 * 2
def baseEnd_1361155 : Nat := 103544705225292919778173

theorem tailTrace_1361155 : CollatzResearch.WordTrace tailWord_1361155 prefixEnd_1361155 103544705225292919778173 := by
  unfold tailWord_1361155
  simp only [CollatzResearch.WordTrace]
  refine ⟨49645401383775376611484919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33096934255850251074323279 49645401383775376611484919)
  ·
    refine ⟨74468102075663064917227379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49645401383775376611484919 74468102075663064917227379)
    ·
      refine ⟨111702153113494597375841069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74468102075663064917227379 111702153113494597375841069)
      ·
        refine ⟨41888307417560474015940401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111702153113494597375841069 41888307417560474015940401)
        ·
          refine ⟨31416230563170355511955301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41888307417560474015940401 31416230563170355511955301)
          ·
            refine ⟨5890543230594441658491619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31416230563170355511955301 5890543230594441658491619)
            ·
              refine ⟨8835814845891662487737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5890543230594441658491619 8835814845891662487737429)
              ·
                refine ⟨103544705225292919778173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8835814845891662487737429 103544705225292919778173)
                ·
                  rfl

theorem cell21_1361155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_1361155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361155 prefixEnd_1361155 := by exact prefixLift 1361155
  have htrace : WordTrace (prefixWord ++ tailWord_1361155) baseStart_1361155 baseEnd_1361155 := by
    simpa [prefixWord, tailWord_1361155, baseEnd_1361155] using wordTrace_append hprefix tailTrace_1361155
  have hstable : (prefixWord ++ tailWord_1361155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361155).length < 2 ^ (prefixWord ++ tailWord_1361155).sum := by decide
  have hdescent : baseEnd_1361155 < baseStart_1361155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361220 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1361220 : Nat := 118140960795 + 1361220 * 2 ^ 59
def prefixEnd_1361220 : Nat := 4983230072969 + 3 ^ 40 * 1361220 * 2
def baseEnd_1361220 : Nat := 310648949561453090751053

theorem tailTrace_1361220 : CollatzResearch.WordTrace tailWord_1361220 prefixEnd_1361220 310648949561453090751053 := by
  unfold tailWord_1361220
  simp only [CollatzResearch.WordTrace]
  refine ⟨24823886064269946356300557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33098514752359928475067409 24823886064269946356300557)
  ·
    refine ⟨9308957274101229883612709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24823886064269946356300557 9308957274101229883612709)
    ·
      refine ⟨1745429488893980603177383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9308957274101229883612709 1745429488893980603177383)
      ·
        refine ⟨2618144233340970904766075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745429488893980603177383 2618144233340970904766075)
        ·
          refine ⟨3927216350011456357149113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618144233340970904766075 3927216350011456357149113)
          ·
            refine ⟨2945412262508592267861835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3927216350011456357149113 2945412262508592267861835)
            ·
              refine ⟨4418118393762888401792753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945412262508592267861835 4418118393762888401792753)
              ·
                refine ⟨3313588795322166301344565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4418118393762888401792753 3313588795322166301344565)
                ·
                  refine ⟨310648949561453090751053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3313588795322166301344565 310648949561453090751053)
                  ·
                    rfl

theorem cell21_1361220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1361220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361220 prefixEnd_1361220 := by exact prefixLift 1361220
  have htrace : WordTrace (prefixWord ++ tailWord_1361220) baseStart_1361220 baseEnd_1361220 := by
    simpa [prefixWord, tailWord_1361220, baseEnd_1361220] using wordTrace_append hprefix tailTrace_1361220
  have hstable : (prefixWord ++ tailWord_1361220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361220).length < 2 ^ (prefixWord ++ tailWord_1361220).sum := by decide
  have hdescent : baseEnd_1361220 < baseStart_1361220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361282 : List Nat := [3, 4, 2, 1, 1, 1, 4, 5]
def baseStart_1361282 : Nat := 118140960795 + 1361282 * 2 ^ 59
def prefixEnd_1361282 : Nat := 4983230072969 + 3 ^ 40 * 1361282 * 2
def baseEnd_1361282 : Nat := 103554366268718253572531

theorem tailTrace_1361282 : CollatzResearch.WordTrace tailWord_1361282 prefixEnd_1361282 103554366268718253572531 := by
  unfold tailWord_1361282
  simp only [CollatzResearch.WordTrace]
  refine ⟨12412508363578819325339525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33100022302876851534238733 12412508363578819325339525)
  ·
    refine ⟨2327345318171028623501161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12412508363578819325339525 2327345318171028623501161)
    ·
      refine ⟨1745508988628271467625871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2327345318171028623501161 1745508988628271467625871)
      ·
        refine ⟨2618263482942407201438807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745508988628271467625871 2618263482942407201438807)
        ·
          refine ⟨3927395224413610802158211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2618263482942407201438807 3927395224413610802158211)
          ·
            refine ⟨5891092836620416203237317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927395224413610802158211 5891092836620416203237317)
            ·
              refine ⟨1104579906866328038106997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5891092836620416203237317 1104579906866328038106997)
              ·
                refine ⟨103554366268718253572531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104579906866328038106997 103554366268718253572531)
                ·
                  rfl

theorem cell21_1361282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_1361282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361282 prefixEnd_1361282 := by exact prefixLift 1361282
  have htrace : WordTrace (prefixWord ++ tailWord_1361282) baseStart_1361282 baseEnd_1361282 := by
    simpa [prefixWord, tailWord_1361282, baseEnd_1361282] using wordTrace_append hprefix tailTrace_1361282
  have hstable : (prefixWord ++ tailWord_1361282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361282).length < 2 ^ (prefixWord ++ tailWord_1361282).sum := by decide
  have hdescent : baseEnd_1361282 < baseStart_1361282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361369 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 4]
def baseStart_1361369 : Nat := 118140960795 + 1361369 * 2 ^ 59
def prefixEnd_1361369 : Nat := 4983230072969 + 3 ^ 40 * 1361369 * 2
def baseEnd_1361369 : Nat := 310682953391461942767415

theorem tailTrace_1361369 : CollatzResearch.WordTrace tailWord_1361369 prefixEnd_1361369 310682953391461942767415 := by
  unfold tailWord_1361369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49653206605000091159775161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33102137736666727439850107 49653206605000091159775161)
  ·
    refine ⟨37239904953750068369831371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49653206605000091159775161 37239904953750068369831371)
    ·
      refine ⟨55859857430625102554747057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37239904953750068369831371 55859857430625102554747057)
      ·
        refine ⟨41894893072968826916060293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55859857430625102554747057 41894893072968826916060293)
        ·
          refine ⟨7855292451181655046761305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41894893072968826916060293 7855292451181655046761305)
          ·
            refine ⟨5891469338386241285070979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7855292451181655046761305 5891469338386241285070979)
            ·
              refine ⟨8837204007579361927606469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5891469338386241285070979 8837204007579361927606469)
              ·
                refine ⟨1656975751421130361426213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8837204007579361927606469 1656975751421130361426213)
                ·
                  refine ⟨310682953391461942767415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1656975751421130361426213 310682953391461942767415)
                  ·
                    rfl

theorem cell21_1361369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_1361369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361369 prefixEnd_1361369 := by exact prefixLift 1361369
  have htrace : WordTrace (prefixWord ++ tailWord_1361369) baseStart_1361369 baseEnd_1361369 := by
    simpa [prefixWord, tailWord_1361369, baseEnd_1361369] using wordTrace_append hprefix tailTrace_1361369
  have hstable : (prefixWord ++ tailWord_1361369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361369).length < 2 ^ (prefixWord ++ tailWord_1361369).sum := by decide
  have hdescent : baseEnd_1361369 < baseStart_1361369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361400 : List Nat := [2, 1, 2, 1, 1, 6, 3, 5]
def baseStart_1361400 : Nat := 118140960795 + 1361400 * 2 ^ 59
def prefixEnd_1361400 : Nat := 4983230072969 + 3 ^ 40 * 1361400 * 2
def baseEnd_1361400 : Nat := 103563342671270925916895

theorem tailTrace_1361400 : CollatzResearch.WordTrace tailWord_1361400 prefixEnd_1361400 103563342671270925916895 := by
  unfold tailWord_1361400
  simp only [CollatzResearch.WordTrace]
  refine ⟨24827168633943891727076827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33102891511925188969435769 24827168633943891727076827)
  ·
    refine ⟨37240752950915837590615241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24827168633943891727076827 37240752950915837590615241)
    ·
      refine ⟨27930564713186878192961431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37240752950915837590615241 27930564713186878192961431)
      ·
        refine ⟨41895847069780317289442147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27930564713186878192961431 41895847069780317289442147)
        ·
          refine ⟨62843770604670475934163221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41895847069780317289442147 62843770604670475934163221)
          ·
            refine ⟨2945801747093928559413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62843770604670475934163221 2945801747093928559413901)
            ·
              refine ⟨1104675655160223209780213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2945801747093928559413901 1104675655160223209780213)
              ·
                refine ⟨103563342671270925916895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1104675655160223209780213 103563342671270925916895)
                ·
                  rfl

theorem cell21_1361400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_1361400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361400 prefixEnd_1361400 := by exact prefixLift 1361400
  have htrace : WordTrace (prefixWord ++ tailWord_1361400) baseStart_1361400 baseEnd_1361400 := by
    simpa [prefixWord, tailWord_1361400, baseEnd_1361400] using wordTrace_append hprefix tailTrace_1361400
  have hstable : (prefixWord ++ tailWord_1361400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361400).length < 2 ^ (prefixWord ++ tailWord_1361400).sum := by decide
  have hdescent : baseEnd_1361400 < baseStart_1361400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361406 : List Nat := [4, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_1361406 : Nat := 118140960795 + 1361406 * 2 ^ 59
def prefixEnd_1361406 : Nat := 4983230072969 + 3 ^ 40 * 1361406 * 2
def baseEnd_1361406 : Nat := 310691397295558100650673

theorem tailTrace_1361406 : CollatzResearch.WordTrace tailWord_1361406 prefixEnd_1361406 310691397295558100650673 := by
  unfold tailWord_1361406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6206819513233255809859009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33103037403910697652581381 6206819513233255809859009)
  ·
    refine ⟨4655114634924941857394257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6206819513233255809859009 4655114634924941857394257)
    ·
      refine ⟨3491335976193706393045693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4655114634924941857394257 3491335976193706393045693)
      ·
        refine ⟨1309250991072639897392135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3491335976193706393045693 1309250991072639897392135)
        ·
          refine ⟨1963876486608959846088203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309250991072639897392135 1963876486608959846088203)
          ·
            refine ⟨2945814729913439769132305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963876486608959846088203 2945814729913439769132305)
            ·
              refine ⟨2209361047435079826849229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2945814729913439769132305 2209361047435079826849229)
              ·
                refine ⟨828510392788154935068461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209361047435079826849229 828510392788154935068461)
                ·
                  refine ⟨310691397295558100650673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828510392788154935068461 310691397295558100650673)
                  ·
                    rfl

theorem cell21_1361406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_1361406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361406 prefixEnd_1361406 := by exact prefixLift 1361406
  have htrace : WordTrace (prefixWord ++ tailWord_1361406) baseStart_1361406 baseEnd_1361406 := by
    simpa [prefixWord, tailWord_1361406, baseEnd_1361406] using wordTrace_append hprefix tailTrace_1361406
  have hstable : (prefixWord ++ tailWord_1361406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361406).length < 2 ^ (prefixWord ++ tailWord_1361406).sum := by decide
  have hdescent : baseEnd_1361406 < baseStart_1361406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361459 : List Nat := [1, 1, 1, 2, 4, 4, 1, 7]
def baseStart_1361459 : Nat := 118140960795 + 1361459 * 2 ^ 59
def prefixEnd_1361459 : Nat := 4983230072969 + 3 ^ 40 * 1361459 * 2
def baseEnd_1361459 : Nat := 103567830872547262089077

theorem tailTrace_1361459 : CollatzResearch.WordTrace tailWord_1361459 prefixEnd_1361459 103567830872547262089077 := by
  unfold tailWord_1361459
  simp only [CollatzResearch.WordTrace]
  refine ⟨49656489174674036530551431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33104326116449357687034287 49656489174674036530551431)
  ·
    refine ⟨74484733762011054795827147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49656489174674036530551431 74484733762011054795827147)
    ·
      refine ⟨111727100643016582193740721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74484733762011054795827147 111727100643016582193740721)
      ·
        refine ⟨83795325482262436645305541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111727100643016582193740721 83795325482262436645305541)
        ·
          refine ⟨15711623527924206870994789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83795325482262436645305541 15711623527924206870994789)
          ·
            refine ⟨2945929411485788788311523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15711623527924206870994789 2945929411485788788311523)
            ·
              refine ⟨4418894117228683182467285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2945929411485788788311523 4418894117228683182467285)
              ·
                refine ⟨103567830872547262089077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4418894117228683182467285 103567830872547262089077)
                ·
                  rfl

theorem cell21_1361459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_1361459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361459 prefixEnd_1361459 := by exact prefixLift 1361459
  have htrace : WordTrace (prefixWord ++ tailWord_1361459) baseStart_1361459 baseEnd_1361459 := by
    simpa [prefixWord, tailWord_1361459, baseEnd_1361459] using wordTrace_append hprefix tailTrace_1361459
  have hstable : (prefixWord ++ tailWord_1361459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361459).length < 2 ^ (prefixWord ++ tailWord_1361459).sum := by decide
  have hdescent : baseEnd_1361459 < baseStart_1361459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361583 : List Nat := [1, 1, 2, 1, 2, 4, 4, 3, 3]
def baseStart_1361583 : Nat := 118140960795 + 1361583 * 2 ^ 59
def prefixEnd_1361583 : Nat := 4983230072969 + 3 ^ 40 * 1361583 * 2
def baseEnd_1361583 : Nat := 310731791107045126200311

theorem tailTrace_1361583 : CollatzResearch.WordTrace tailWord_1361583 prefixEnd_1361583 310731791107045126200311 := by
  unfold tailWord_1361583
  simp only [CollatzResearch.WordTrace]
  refine ⟨49661011826224805708065403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33107341217483203805376935 49661011826224805708065403)
  ·
    refine ⟨74491517739337208562098105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49661011826224805708065403 74491517739337208562098105)
    ·
      refine ⟨55868638304502906421573579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74491517739337208562098105 55868638304502906421573579)
      ·
        refine ⟨83802957456754359632360369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55868638304502906421573579 83802957456754359632360369)
        ·
          refine ⟨62852218092565769724270277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83802957456754359632360369 62852218092565769724270277)
          ·
            refine ⟨11784790892356081823300677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62852218092565769724270277 11784790892356081823300677)
            ·
              refine ⟨2209648292316765341868877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11784790892356081823300677 2209648292316765341868877)
              ·
                refine ⟨828618109618787003200829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2209648292316765341868877 828618109618787003200829)
                ·
                  refine ⟨310731791107045126200311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828618109618787003200829 310731791107045126200311)
                  ·
                    rfl

theorem cell21_1361583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 3].length) (baseStart_1361583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361583 prefixEnd_1361583 := by exact prefixLift 1361583
  have htrace : WordTrace (prefixWord ++ tailWord_1361583) baseStart_1361583 baseEnd_1361583 := by
    simpa [prefixWord, tailWord_1361583, baseEnd_1361583] using wordTrace_append hprefix tailTrace_1361583
  have hstable : (prefixWord ++ tailWord_1361583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361583).length < 2 ^ (prefixWord ++ tailWord_1361583).sum := by decide
  have hdescent : baseEnd_1361583 < baseStart_1361583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361614 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1361614 : Nat := 118140960795 + 1361614 * 2 ^ 59
def prefixEnd_1361614 : Nat := 4983230072969 + 3 ^ 40 * 1361614 * 2
def baseEnd_1361614 : Nat := 310738865729395961183581

theorem tailTrace_1361614 : CollatzResearch.WordTrace tailWord_1361614 prefixEnd_1361614 310738865729395961183581 := by
  unfold tailWord_1361614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6207767811139062250305487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33108094992741665334962597 6207767811139062250305487)
  ·
    refine ⟨9311651716708593375458231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6207767811139062250305487 9311651716708593375458231)
    ·
      refine ⟨13967477575062890063187347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9311651716708593375458231 13967477575062890063187347)
      ·
        refine ⟨20951216362594335094781021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13967477575062890063187347 20951216362594335094781021)
        ·
          refine ⟨7856706135972875660542883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20951216362594335094781021 7856706135972875660542883)
          ·
            refine ⟨11785059203959313490814325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7856706135972875660542883 11785059203959313490814325)
            ·
              refine ⟨1104849300371185639763843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11785059203959313490814325 1104849300371185639763843)
              ·
                refine ⟨1657273950556778459645765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1104849300371185639763843 1657273950556778459645765)
                ·
                  refine ⟨310738865729395961183581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1657273950556778459645765 310738865729395961183581)
                  ·
                    rfl

theorem cell21_1361614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1361614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361614 prefixEnd_1361614 := by exact prefixLift 1361614
  have htrace : WordTrace (prefixWord ++ tailWord_1361614) baseStart_1361614 baseEnd_1361614 := by
    simpa [prefixWord, tailWord_1361614, baseEnd_1361614] using wordTrace_append hprefix tailTrace_1361614
  have hstable : (prefixWord ++ tailWord_1361614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361614).length < 2 ^ (prefixWord ++ tailWord_1361614).sum := by decide
  have hdescent : baseEnd_1361614 < baseStart_1361614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361687 : List Nat := [1, 1, 3, 4, 2, 1, 2, 7]
def baseStart_1361687 : Nat := 118140960795 + 1361687 * 2 ^ 59
def prefixEnd_1361687 : Nat := 4983230072969 + 3 ^ 40 * 1361687 * 2
def baseEnd_1361687 : Nat := 103585175107988018822255

theorem tailTrace_1361687 : CollatzResearch.WordTrace tailWord_1361687 prefixEnd_1361687 103585175107988018822255 := by
  unfold tailWord_1361687
  simp only [CollatzResearch.WordTrace]
  refine ⟨49664805017848031469851315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33109870011898687646567543 49664805017848031469851315)
  ·
    refine ⟨74497207526772047204776973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49664805017848031469851315 74497207526772047204776973)
    ·
      refine ⟨27936452822539517701791365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74497207526772047204776973 27936452822539517701791365)
      ·
        refine ⟨5238084904226159569085881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27936452822539517701791365 5238084904226159569085881)
        ·
          refine ⟨3928563678169619676814411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238084904226159569085881 3928563678169619676814411)
          ·
            refine ⟨5892845517254429515221617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3928563678169619676814411 5892845517254429515221617)
            ·
              refine ⟨4419634137940822136416213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5892845517254429515221617 4419634137940822136416213)
              ·
                refine ⟨103585175107988018822255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4419634137940822136416213 103585175107988018822255)
                ·
                  rfl

theorem cell21_1361687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_1361687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361687 prefixEnd_1361687 := by exact prefixLift 1361687
  have htrace : WordTrace (prefixWord ++ tailWord_1361687) baseStart_1361687 baseEnd_1361687 := by
    simpa [prefixWord, tailWord_1361687, baseEnd_1361687] using wordTrace_append hprefix tailTrace_1361687
  have hstable : (prefixWord ++ tailWord_1361687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361687).length < 2 ^ (prefixWord ++ tailWord_1361687).sum := by decide
  have hdescent : baseEnd_1361687 < baseStart_1361687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361710 : List Nat := [4, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_1361710 : Nat := 118140960795 + 1361710 * 2 ^ 59
def prefixEnd_1361710 : Nat := 4983230072969 + 3 ^ 40 * 1361710 * 2
def baseEnd_1361710 : Nat := 310760774237321127583385

theorem tailTrace_1361710 : CollatzResearch.WordTrace tailWord_1361710 prefixEnd_1361710 310760774237321127583385 := by
  unfold tailWord_1361710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208205487095588299742323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 33110429264509804265292389 6208205487095588299742323)
  ·
    refine ⟨9312308230643382449613485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6208205487095588299742323 9312308230643382449613485)
    ·
      refine ⟨3492115586491268418605057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9312308230643382449613485 3492115586491268418605057)
      ·
        refine ⟨2619086689868451313953793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492115586491268418605057 2619086689868451313953793)
        ·
          refine ⟨1964315017401338485465345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619086689868451313953793 1964315017401338485465345)
          ·
            refine ⟨1473236263051003864099009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964315017401338485465345 1473236263051003864099009)
            ·
              refine ⟨1104927197288252898074257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473236263051003864099009 1104927197288252898074257)
              ·
                refine ⟨828695397966189673555693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1104927197288252898074257 828695397966189673555693)
                ·
                  refine ⟨310760774237321127583385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828695397966189673555693 310760774237321127583385)
                  ·
                    rfl

theorem cell21_1361710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_1361710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361710 prefixEnd_1361710 := by exact prefixLift 1361710
  have htrace : WordTrace (prefixWord ++ tailWord_1361710) baseStart_1361710 baseEnd_1361710 := by
    simpa [prefixWord, tailWord_1361710, baseEnd_1361710] using wordTrace_append hprefix tailTrace_1361710
  have hstable : (prefixWord ++ tailWord_1361710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361710).length < 2 ^ (prefixWord ++ tailWord_1361710).sum := by decide
  have hdescent : baseEnd_1361710 < baseStart_1361710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361721 : List Nat := [1, 2, 1, 7, 1, 2, 1, 6]
def baseStart_1361721 : Nat := 118140960795 + 1361721 * 2 ^ 59
def prefixEnd_1361721 : Nat := 4983230072969 + 3 ^ 40 * 1361721 * 2
def baseEnd_1361721 : Nat := 103587761529062517633343

theorem tailTrace_1361721 : CollatzResearch.WordTrace tailWord_1361721 prefixEnd_1361721 103587761529062517633343 := by
  unfold tailWord_1361721
  simp only [CollatzResearch.WordTrace]
  refine ⟨49666045099724855276589017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33110696733149903517726011 49666045099724855276589017)
  ·
    refine ⟨37249533824793641457441763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49666045099724855276589017 37249533824793641457441763)
    ·
      refine ⟨55874300737190462186162645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37249533824793641457441763 55874300737190462186162645)
      ·
        refine ⟨1309553923527901457488187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 55874300737190462186162645 1309553923527901457488187)
        ·
          refine ⟨1964330885291852186232281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309553923527901457488187 1964330885291852186232281)
          ·
            refine ⟨1473248163968889139674211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964330885291852186232281 1473248163968889139674211)
            ·
              refine ⟨2209872245953333709511317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473248163968889139674211 2209872245953333709511317)
              ·
                refine ⟨103587761529062517633343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2209872245953333709511317 103587761529062517633343)
                ·
                  rfl

theorem cell21_1361721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 6].length) (baseStart_1361721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361721 prefixEnd_1361721 := by exact prefixLift 1361721
  have htrace : WordTrace (prefixWord ++ tailWord_1361721) baseStart_1361721 baseEnd_1361721 := by
    simpa [prefixWord, tailWord_1361721, baseEnd_1361721] using wordTrace_append hprefix tailTrace_1361721
  have hstable : (prefixWord ++ tailWord_1361721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361721).length < 2 ^ (prefixWord ++ tailWord_1361721).sum := by decide
  have hdescent : baseEnd_1361721 < baseStart_1361721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361763 : List Nat := [1, 1, 1, 5, 4, 1, 8]
def baseStart_1361763 : Nat := 118140960795 + 1361763 * 2 ^ 59
def prefixEnd_1361763 : Nat := 4983230072969 + 3 ^ 40 * 1361763 * 2
def baseEnd_1361763 : Nat := 34530318839933868133327

theorem tailTrace_1361763 : CollatzResearch.WordTrace tailWord_1361763 prefixEnd_1361763 34530318839933868133327 := by
  unfold tailWord_1361763
  simp only [CollatzResearch.WordTrace]
  refine ⟨49667576965572696449617943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33111717977048464299745295 49667576965572696449617943)
  ·
    refine ⟨74501365448359044674426915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49667576965572696449617943 74501365448359044674426915)
    ·
      refine ⟨111752048172538567011640373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74501365448359044674426915 111752048172538567011640373)
      ·
        refine ⟨10476754516175490657341285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111752048172538567011640373 10476754516175490657341285)
        ·
          refine ⟨1964391471782904498251491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10476754516175490657341285 1964391471782904498251491)
          ·
            refine ⟨2946587207674356747377237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964391471782904498251491 2946587207674356747377237)
            ·
              refine ⟨34530318839933868133327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2946587207674356747377237 34530318839933868133327)
              ·
                rfl

theorem cell21_1361763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_1361763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361763 prefixEnd_1361763 := by exact prefixLift 1361763
  have htrace : WordTrace (prefixWord ++ tailWord_1361763) baseStart_1361763 baseEnd_1361763 := by
    simpa [prefixWord, tailWord_1361763, baseEnd_1361763] using wordTrace_append hprefix tailTrace_1361763
  have hstable : (prefixWord ++ tailWord_1361763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361763).length < 2 ^ (prefixWord ++ tailWord_1361763).sum := by decide
  have hdescent : baseEnd_1361763 < baseStart_1361763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361814 : List Nat := [5, 3, 1, 1, 2, 2, 7]
def baseStart_1361814 : Nat := 118140960795 + 1361814 * 2 ^ 59
def prefixEnd_1361814 : Nat := 4983230072969 + 3 ^ 40 * 1361814 * 2
def baseEnd_1361814 : Nat := 34531612050471117538871

theorem tailTrace_1361814 : CollatzResearch.WordTrace tailWord_1361814 prefixEnd_1361814 34531612050471117538871 := by
  unfold tailWord_1361814
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104339818024245759982781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 33112958058925288106482997 3104339818024245759982781)
  ·
    refine ⟨1164127431759092159993543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3104339818024245759982781 1164127431759092159993543)
    ·
      refine ⟨1746191147638638239990315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1164127431759092159993543 1746191147638638239990315)
      ·
        refine ⟨2619286721457957359985473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746191147638638239990315 2619286721457957359985473)
        ·
          refine ⟨1964465041093468019989105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2619286721457957359985473 1964465041093468019989105)
          ·
            refine ⟨1473348780820101014991829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1964465041093468019989105 1473348780820101014991829)
            ·
              refine ⟨34531612050471117538871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1473348780820101014991829 34531612050471117538871)
              ·
                rfl

theorem cell21_1361814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 7].length) (baseStart_1361814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361814 prefixEnd_1361814 := by exact prefixLift 1361814
  have htrace : WordTrace (prefixWord ++ tailWord_1361814) baseStart_1361814 baseEnd_1361814 := by
    simpa [prefixWord, tailWord_1361814, baseEnd_1361814] using wordTrace_append hprefix tailTrace_1361814
  have hstable : (prefixWord ++ tailWord_1361814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361814).length < 2 ^ (prefixWord ++ tailWord_1361814).sum := by decide
  have hdescent : baseEnd_1361814 < baseStart_1361814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361828 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1361828 : Nat := 118140960795 + 1361828 * 2 ^ 59
def prefixEnd_1361828 : Nat := 4983230072969 + 3 ^ 40 * 1361828 * 2
def baseEnd_1361828 : Nat := 310787703444979144616477

theorem tailTrace_1361828 : CollatzResearch.WordTrace tailWord_1361828 prefixEnd_1361828 310787703444979144616477 := by
  unfold tailWord_1361828
  simp only [CollatzResearch.WordTrace]
  refine ⟨24834973855168606275367069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 33113298473558141700489425 24834973855168606275367069)
  ·
    refine ⟨9313115195688227353262651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24834973855168606275367069 9313115195688227353262651)
    ·
      refine ⟨13969672793532341029893977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9313115195688227353262651 13969672793532341029893977)
      ·
        refine ⟨10477254595149255772420483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13969672793532341029893977 10477254595149255772420483)
        ·
          refine ⟨15715881892723883658630725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10477254595149255772420483 15715881892723883658630725)
          ·
            refine ⟨2946727854885728185993261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15715881892723883658630725 2946727854885728185993261)
            ·
              refine ⟨1105022945582148069747473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2946727854885728185993261 1105022945582148069747473)
              ·
                refine ⟨828767209186611052310605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1105022945582148069747473 828767209186611052310605)
                ·
                  refine ⟨310787703444979144616477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828767209186611052310605 310787703444979144616477)
                  ·
                    rfl

theorem cell21_1361828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1361828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361828 prefixEnd_1361828 := by exact prefixLift 1361828
  have htrace : WordTrace (prefixWord ++ tailWord_1361828) baseStart_1361828 baseEnd_1361828 := by
    simpa [prefixWord, tailWord_1361828, baseEnd_1361828] using wordTrace_append hprefix tailTrace_1361828
  have hstable : (prefixWord ++ tailWord_1361828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361828).length < 2 ^ (prefixWord ++ tailWord_1361828).sum := by decide
  have hdescent : baseEnd_1361828 < baseStart_1361828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361887 : List Nat := [1, 1, 2, 3, 4, 2, 1, 4, 3]
def baseStart_1361887 : Nat := 118140960795 + 1361887 * 2 ^ 59
def prefixEnd_1361887 : Nat := 4983230072969 + 3 ^ 40 * 1361887 * 2
def baseEnd_1361887 : Nat := 310801168048808153133023

theorem tailTrace_1361887 : CollatzResearch.WordTrace tailWord_1361887 prefixEnd_1361887 310801168048808153133023 := by
  unfold tailWord_1361887
  simp only [CollatzResearch.WordTrace]
  refine ⟨49672099617123465627131915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 33114733078082310418087943 49672099617123465627131915)
  ·
    refine ⟨74508149425685198440697873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49672099617123465627131915 74508149425685198440697873)
    ·
      refine ⟨55881112069263898830523405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74508149425685198440697873 55881112069263898830523405)
      ·
        refine ⟨20955417025973962061446277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55881112069263898830523405 20955417025973962061446277)
        ·
          refine ⟨3929140692370117886521177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20955417025973962061446277 3929140692370117886521177)
          ·
            refine ⟨2946855519277588414890883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3929140692370117886521177 2946855519277588414890883)
            ·
              refine ⟨4420283278916382622336325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2946855519277588414890883 4420283278916382622336325)
              ·
                refine ⟨828803114796821741688061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4420283278916382622336325 828803114796821741688061)
                ·
                  refine ⟨310801168048808153133023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 828803114796821741688061 310801168048808153133023)
                  ·
                    rfl

theorem cell21_1361887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 4, 3].length) (baseStart_1361887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361887 prefixEnd_1361887 := by exact prefixLift 1361887
  have htrace : WordTrace (prefixWord ++ tailWord_1361887) baseStart_1361887 baseEnd_1361887 := by
    simpa [prefixWord, tailWord_1361887, baseEnd_1361887] using wordTrace_append hprefix tailTrace_1361887
  have hstable : (prefixWord ++ tailWord_1361887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361887).length < 2 ^ (prefixWord ++ tailWord_1361887).sum := by decide
  have hdescent : baseEnd_1361887 < baseStart_1361887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361890 : List Nat := [3, 3, 3, 1, 3, 1, 1, 6]
def baseStart_1361890 : Nat := 118140960795 + 1361890 * 2 ^ 59
def prefixEnd_1361890 : Nat := 4983230072969 + 3 ^ 40 * 1361890 * 2
def baseEnd_1361890 : Nat := 103600617563226938194339

theorem tailTrace_1361890 : CollatzResearch.WordTrace tailWord_1361890 prefixEnd_1361890 103600617563226938194339 := by
  unfold tailWord_1361890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418052259028149284872781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33114806024075064759660749 12418052259028149284872781)
  ·
    refine ⟨4656769597135555981827293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12418052259028149284872781 4656769597135555981827293)
    ·
      refine ⟨1746288598925833493185235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4656769597135555981827293 1746288598925833493185235)
      ·
        refine ⟨2619432898388750239777853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1746288598925833493185235 2619432898388750239777853)
        ·
          refine ⟨982287336895781339916695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2619432898388750239777853 982287336895781339916695)
          ·
            refine ⟨1473431005343672009875043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982287336895781339916695 1473431005343672009875043)
            ·
              refine ⟨2210146508015508014812565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1473431005343672009875043 2210146508015508014812565)
              ·
                refine ⟨103600617563226938194339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2210146508015508014812565 103600617563226938194339)
                ·
                  rfl

theorem cell21_1361890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_1361890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361890 prefixEnd_1361890 := by exact prefixLift 1361890
  have htrace : WordTrace (prefixWord ++ tailWord_1361890) baseStart_1361890 baseEnd_1361890 := by
    simpa [prefixWord, tailWord_1361890, baseEnd_1361890] using wordTrace_append hprefix tailTrace_1361890
  have hstable : (prefixWord ++ tailWord_1361890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361890).length < 2 ^ (prefixWord ++ tailWord_1361890).sum := by decide
  have hdescent : baseEnd_1361890 < baseStart_1361890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1361946 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_1361946 : Nat := 118140960795 + 1361946 * 2 ^ 59
def prefixEnd_1361946 : Nat := 4983230072969 + 3 ^ 40 * 1361946 * 2
def baseEnd_1361946 : Nat := 310814632652637161649569

theorem tailTrace_1361946 : CollatzResearch.WordTrace tailWord_1361946 prefixEnd_1361946 310814632652637161649569 := by
  unfold tailWord_1361946
  simp only [CollatzResearch.WordTrace]
  refine ⟨12418562880977429675882423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 33116167682606479135686461 12418562880977429675882423)
  ·
    refine ⟨18627844321466144513823635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12418562880977429675882423 18627844321466144513823635)
    ·
      refine ⟨27941766482199216770735453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18627844321466144513823635 27941766482199216770735453)
      ·
        refine ⟨10478162430824706289025795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27941766482199216770735453 10478162430824706289025795)
        ·
          refine ⟨15717243646237059433538693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10478162430824706289025795 15717243646237059433538693)
          ·
            refine ⟨2946983183669448643788505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15717243646237059433538693 2946983183669448643788505)
            ·
              refine ⟨2210237387752086482841379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2946983183669448643788505 2210237387752086482841379)
              ·
                refine ⟨3315356081628129724262069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2210237387752086482841379 3315356081628129724262069)
                ·
                  refine ⟨310814632652637161649569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3315356081628129724262069 310814632652637161649569)
                  ·
                    rfl

theorem cell21_1361946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_1361946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1361946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1361946 prefixEnd_1361946 := by exact prefixLift 1361946
  have htrace : WordTrace (prefixWord ++ tailWord_1361946) baseStart_1361946 baseEnd_1361946 := by
    simpa [prefixWord, tailWord_1361946, baseEnd_1361946] using wordTrace_append hprefix tailTrace_1361946
  have hstable : (prefixWord ++ tailWord_1361946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1361946).length < 2 ^ (prefixWord ++ tailWord_1361946).sum := by decide
  have hdescent : baseEnd_1361946 < baseStart_1361946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1361946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
