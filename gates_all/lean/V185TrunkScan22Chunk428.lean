import V185TrunkScan22Chunk427

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3816730 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 2, 3]
def baseStart_3816730 : Nat := 118140960795 + 3816730 * 2 ^ 59
def prefixEnd_3816730 : Nat := 4983230072969 + 3 ^ 40 * 3816730 * 2
def baseEnd_3816730 : Nat := 1306544678956638173348123

theorem tailTrace_3816730 : CollatzResearch.WordTrace tailWord_3816730 prefixEnd_3816730 1306544678956638173348123 := by
  unfold tailWord_3816730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34801894865661632608257911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92805052975097686955354429 34801894865661632608257911)
  ·
    refine ⟨52202842298492448912386867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34801894865661632608257911 52202842298492448912386867)
    ·
      refine ⟨78304263447738673368580301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52202842298492448912386867 78304263447738673368580301)
      ·
        refine ⟨29364098792902002513217613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78304263447738673368580301 29364098792902002513217613)
        ·
          refine ⟨11011537047338250942456605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29364098792902002513217613 11011537047338250942456605)
          ·
            refine ⟨4129326392751844103421227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11011537047338250942456605 4129326392751844103421227)
            ·
              refine ⟨6193989589127766155131841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4129326392751844103421227 6193989589127766155131841)
              ·
                refine ⟨4645492191845824616348881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6193989589127766155131841 4645492191845824616348881)
                ·
                  refine ⟨3484119143884368462261661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4645492191845824616348881 3484119143884368462261661)
                  ·
                    refine ⟨1306544678956638173348123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484119143884368462261661 1306544678956638173348123)
                    ·
                      rfl

theorem cell22_3816730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_3816730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816730 prefixEnd_3816730 := by exact prefixLift 3816730
  have htrace : WordTrace (prefixWord ++ tailWord_3816730) baseStart_3816730 baseEnd_3816730 := by
    simpa [prefixWord, tailWord_3816730, baseEnd_3816730] using wordTrace_append hprefix tailTrace_3816730
  have hstable : (prefixWord ++ tailWord_3816730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816730).length < 2 ^ (prefixWord ++ tailWord_3816730).sum := by decide
  have hdescent : baseEnd_3816730 < baseStart_3816730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816775 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3816775 : Nat := 118140960795 + 3816775 * 2 ^ 59
def prefixEnd_3816775 : Nat := 4983230072969 + 3 ^ 40 * 3816775 * 2
def baseEnd_3816775 : Nat := 1306560083376273055972985

theorem tailTrace_3816775 : CollatzResearch.WordTrace tailWord_3816775 prefixEnd_3816775 1306560083376273055972985 := by
  unfold tailWord_3816775
  simp only [CollatzResearch.WordTrace]
  refine ⟨139209220747483503118419779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92806147164989002078946519 139209220747483503118419779)
  ·
    refine ⟨208813831121225254677629669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139209220747483503118419779 208813831121225254677629669)
    ·
      refine ⟨39152593335229735252055563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208813831121225254677629669 39152593335229735252055563)
      ·
        refine ⟨58728890002844602878083345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39152593335229735252055563 58728890002844602878083345)
        ·
          refine ⟨44046667502133452158562509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58728890002844602878083345 44046667502133452158562509)
          ·
            refine ⟨16517500313300044559460941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44046667502133452158562509 16517500313300044559460941)
            ·
              refine ⟨6194062617487516709797853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16517500313300044559460941 6194062617487516709797853)
              ·
                refine ⟨2322773481557818766174195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6194062617487516709797853 2322773481557818766174195)
                ·
                  refine ⟨3484160222336728149261293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2322773481557818766174195 3484160222336728149261293)
                  ·
                    refine ⟨1306560083376273055972985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484160222336728149261293 1306560083376273055972985)
                    ·
                      rfl

theorem cell22_3816775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3816775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816775 prefixEnd_3816775 := by exact prefixLift 3816775
  have htrace : WordTrace (prefixWord ++ tailWord_3816775) baseStart_3816775 baseEnd_3816775 := by
    simpa [prefixWord, tailWord_3816775, baseEnd_3816775] using wordTrace_append hprefix tailTrace_3816775
  have hstable : (prefixWord ++ tailWord_3816775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816775).length < 2 ^ (prefixWord ++ tailWord_3816775).sum := by decide
  have hdescent : baseEnd_3816775 < baseStart_3816775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816835 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 1, 4]
def baseStart_3816835 : Nat := 118140960795 + 3816835 * 2 ^ 59
def prefixEnd_3816835 : Nat := 4983230072969 + 3 ^ 40 * 3816835 * 2
def baseEnd_3816835 : Nat := 1306580622602452899472801

theorem tailTrace_3816835 : CollatzResearch.WordTrace tailWord_3816835 prefixEnd_3816835 1306580622602452899472801 := by
  unfold tailWord_3816835
  simp only [CollatzResearch.WordTrace]
  refine ⟨139211409127266133365603959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92807606084844088910402639 139211409127266133365603959)
  ·
    refine ⟨208817113690899200048405939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139211409127266133365603959 208817113690899200048405939)
    ·
      refine ⟨313225670536348800072608909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208817113690899200048405939 313225670536348800072608909)
      ·
        refine ⟨117459626451130800027228341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313225670536348800072608909 117459626451130800027228341)
        ·
          refine ⟨11011839979793512502552657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117459626451130800027228341 11011839979793512502552657)
          ·
            refine ⟨8258879984845134376914493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11011839979793512502552657 8258879984845134376914493)
            ·
              refine ⟨3097079994316925391342935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8258879984845134376914493 3097079994316925391342935)
              ·
                refine ⟨4645619991475388087014403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097079994316925391342935 4645619991475388087014403)
                ·
                  refine ⟨6968429987213082130521605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4645619991475388087014403 6968429987213082130521605)
                  ·
                    refine ⟨1306580622602452899472801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6968429987213082130521605 1306580622602452899472801)
                    ·
                      rfl

theorem cell22_3816835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 1, 4].length) (baseStart_3816835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816835 prefixEnd_3816835 := by exact prefixLift 3816835
  have htrace : WordTrace (prefixWord ++ tailWord_3816835) baseStart_3816835 baseEnd_3816835 := by
    simpa [prefixWord, tailWord_3816835, baseEnd_3816835] using wordTrace_append hprefix tailTrace_3816835
  have hstable : (prefixWord ++ tailWord_3816835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816835).length < 2 ^ (prefixWord ++ tailWord_3816835).sum := by decide
  have hdescent : baseEnd_3816835 < baseStart_3816835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816893 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3816893 : Nat := 118140960795 + 3816893 * 2 ^ 59
def prefixEnd_3816893 : Nat := 4983230072969 + 3 ^ 40 * 3816893 * 2
def baseEnd_3816893 : Nat := 1306600477187760081522623

theorem tailTrace_3816893 : CollatzResearch.WordTrace tailWord_3816893 prefixEnd_3816893 1306600477187760081522623 := by
  unfold tailWord_3816893
  simp only [CollatzResearch.WordTrace]
  refine ⟨139213524561056009271215333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92809016374037339514143555 139213524561056009271215333)
  ·
    refine ⟨26102535855198001738352875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139213524561056009271215333 26102535855198001738352875)
    ·
      refine ⟨39153803782797002607529313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26102535855198001738352875 39153803782797002607529313)
      ·
        refine ⟨29365352837097751955646985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39153803782797002607529313 29365352837097751955646985)
        ·
          refine ⟨22024014627823313966735239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29365352837097751955646985 22024014627823313966735239)
          ·
            refine ⟨33036021941734970950102859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22024014627823313966735239 33036021941734970950102859)
            ·
              refine ⟨49554032912602456425154289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33036021941734970950102859 49554032912602456425154289)
              ·
                refine ⟨37165524684451842318865717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49554032912602456425154289 37165524684451842318865717)
                ·
                  refine ⟨3484267939167360217393661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37165524684451842318865717 3484267939167360217393661)
                  ·
                    refine ⟨1306600477187760081522623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484267939167360217393661 1306600477187760081522623)
                    ·
                      rfl

theorem cell22_3816893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3816893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816893 prefixEnd_3816893 := by exact prefixLift 3816893
  have htrace : WordTrace (prefixWord ++ tailWord_3816893) baseStart_3816893 baseEnd_3816893 := by
    simpa [prefixWord, tailWord_3816893, baseEnd_3816893] using wordTrace_append hprefix tailTrace_3816893
  have hstable : (prefixWord ++ tailWord_3816893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816893).length < 2 ^ (prefixWord ++ tailWord_3816893).sum := by decide
  have hdescent : baseEnd_3816893 < baseStart_3816893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816968 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_3816968 : Nat := 118140960795 + 3816968 * 2 ^ 59
def prefixEnd_3816968 : Nat := 4983230072969 + 3 ^ 40 * 3816968 * 2
def baseEnd_3816968 : Nat := 435542050406828295299131

theorem tailTrace_3816968 : CollatzResearch.WordTrace tailWord_3816968 prefixEnd_3816968 435542050406828295299131 := by
  unfold tailWord_3816968
  simp only [CollatzResearch.WordTrace]
  refine ⟨69608130017892148540097779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92810840023856198053463705 69608130017892148540097779)
  ·
    refine ⟨104412195026838222810146669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69608130017892148540097779 104412195026838222810146669)
    ·
      refine ⟨39154573135064333553805001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104412195026838222810146669 39154573135064333553805001)
      ·
        refine ⟨29365929851298250165353751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39154573135064333553805001 29365929851298250165353751)
        ·
          refine ⟨44048894776947375248030627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29365929851298250165353751 44048894776947375248030627)
          ·
            refine ⟨66073342165421062872045941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44048894776947375248030627 66073342165421062872045941)
            ·
              refine ⟨6194375828008224644254307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66073342165421062872045941 6194375828008224644254307)
              ·
                refine ⟨9291563742012336966381461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6194375828008224644254307 9291563742012336966381461)
                ·
                  refine ⟨435542050406828295299131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9291563742012336966381461 435542050406828295299131)
                  ·
                    rfl

theorem cell22_3816968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_3816968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816968 prefixEnd_3816968 := by exact prefixLift 3816968
  have htrace : WordTrace (prefixWord ++ tailWord_3816968) baseStart_3816968 baseEnd_3816968 := by
    simpa [prefixWord, tailWord_3816968, baseEnd_3816968] using wordTrace_append hprefix tailTrace_3816968
  have hstable : (prefixWord ++ tailWord_3816968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816968).length < 2 ^ (prefixWord ++ tailWord_3816968).sum := by decide
  have hdescent : baseEnd_3816968 < baseStart_3816968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3816974 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_3816974 : Nat := 118140960795 + 3816974 * 2 ^ 59
def prefixEnd_3816974 : Nat := 4983230072969 + 3 ^ 40 * 3816974 * 2
def baseEnd_3816974 : Nat := 435542735047700956749125

theorem tailTrace_3816974 : CollatzResearch.WordTrace tailWord_3816974 prefixEnd_3816974 435542735047700956749125 := by
  unfold tailWord_3816974
  simp only [CollatzResearch.WordTrace]
  refine ⟨17402059859220320013114247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92810985915841706736609317 17402059859220320013114247)
  ·
    refine ⟨26103089788830480019671371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17402059859220320013114247 26103089788830480019671371)
    ·
      refine ⟨39154634683245720029507057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26103089788830480019671371 39154634683245720029507057)
      ·
        refine ⟨29365976012434290022130293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39154634683245720029507057 29365976012434290022130293)
        ·
          refine ⟨2753060251165714689574715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29365976012434290022130293 2753060251165714689574715)
          ·
            refine ⟨4129590376748572034362073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2753060251165714689574715 4129590376748572034362073)
            ·
              refine ⟨3097192782561429025771555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4129590376748572034362073 3097192782561429025771555)
              ·
                refine ⟨4645789173842143538657333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097192782561429025771555 4645789173842143538657333)
                ·
                  refine ⟨435542735047700956749125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4645789173842143538657333 435542735047700956749125)
                  ·
                    rfl

theorem cell22_3816974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_3816974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3816974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3816974 prefixEnd_3816974 := by exact prefixLift 3816974
  have htrace : WordTrace (prefixWord ++ tailWord_3816974) baseStart_3816974 baseEnd_3816974 := by
    simpa [prefixWord, tailWord_3816974, baseEnd_3816974] using wordTrace_append hprefix tailTrace_3816974
  have hstable : (prefixWord ++ tailWord_3816974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3816974).length < 2 ^ (prefixWord ++ tailWord_3816974).sum := by decide
  have hdescent : baseEnd_3816974 < baseStart_3816974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3816974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817017 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_3817017 : Nat := 118140960795 + 3817017 * 2 ^ 59
def prefixEnd_3817017 : Nat := 4983230072969 + 3 ^ 40 * 3817017 * 2
def baseEnd_3817017 : Nat := 1306642924921865091422243

theorem tailTrace_3817017 : CollatzResearch.WordTrace tailWord_3817017 prefixEnd_3817017 1306642924921865091422243 := by
  unfold tailWord_3817017
  simp only [CollatzResearch.WordTrace]
  refine ⟨139218047212606778448729305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92812031475071185632486203 139218047212606778448729305)
  ·
    refine ⟨104413535409455083836546979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139218047212606778448729305 104413535409455083836546979)
    ·
      refine ⟨156620303114182625754820469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104413535409455083836546979 156620303114182625754820469)
      ·
        refine ⟨14683153416954621164514419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156620303114182625754820469 14683153416954621164514419)
        ·
          refine ⟨22024730125431931746771629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14683153416954621164514419 22024730125431931746771629)
          ·
            refine ⟨8259273797036974405039361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22024730125431931746771629 8259273797036974405039361)
            ·
              refine ⟨6194455347777730803779521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259273797036974405039361 6194455347777730803779521)
              ·
                refine ⟨4645841510833298102834641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194455347777730803779521 4645841510833298102834641)
                ·
                  refine ⟨3484381133124973577125981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4645841510833298102834641 3484381133124973577125981)
                  ·
                    refine ⟨1306642924921865091422243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484381133124973577125981 1306642924921865091422243)
                    ·
                      rfl

theorem cell22_3817017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_3817017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817017 prefixEnd_3817017 := by exact prefixLift 3817017
  have htrace : WordTrace (prefixWord ++ tailWord_3817017) baseStart_3817017 baseEnd_3817017 := by
    simpa [prefixWord, tailWord_3817017, baseEnd_3817017] using wordTrace_append hprefix tailTrace_3817017
  have hstable : (prefixWord ++ tailWord_3817017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817017).length < 2 ^ (prefixWord ++ tailWord_3817017).sum := by decide
  have hdescent : baseEnd_3817017 < baseStart_3817017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817135 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 4, 3]
def baseStart_3817135 : Nat := 118140960795 + 3817135 * 2 ^ 59
def prefixEnd_3817135 : Nat := 4983230072969 + 3 ^ 40 * 3817135 * 2
def baseEnd_3817135 : Nat := 1306683318733352116971881

theorem tailTrace_3817135 : CollatzResearch.WordTrace tailWord_3817135 prefixEnd_3817135 1306683318733352116971881 := by
  unfold tailWord_3817135
  simp only [CollatzResearch.WordTrace]
  refine ⟨139222351026179284601524859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92814900684119523067683239 139222351026179284601524859)
  ·
    refine ⟨208833526539268926902287289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139222351026179284601524859 208833526539268926902287289)
    ·
      refine ⟨156625144904451695176715467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208833526539268926902287289 156625144904451695176715467)
      ·
        refine ⟨234937717356677542765073201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156625144904451695176715467 234937717356677542765073201)
        ·
          refine ⟨176203288017508157073804901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 234937717356677542765073201 176203288017508157073804901)
          ·
            refine ⟨33038116503282779451338419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176203288017508157073804901 33038116503282779451338419)
            ·
              refine ⟨49557174754924169177007629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33038116503282779451338419 49557174754924169177007629)
              ·
                refine ⟨18583940533096563441377861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49557174754924169177007629 18583940533096563441377861)
                ·
                  refine ⟨3484488849955605645258349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18583940533096563441377861 3484488849955605645258349)
                  ·
                    refine ⟨1306683318733352116971881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484488849955605645258349 1306683318733352116971881)
                    ·
                      rfl

theorem cell22_3817135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 4, 3].length) (baseStart_3817135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817135 prefixEnd_3817135 := by exact prefixLift 3817135
  have htrace : WordTrace (prefixWord ++ tailWord_3817135) baseStart_3817135 baseEnd_3817135 := by
    simpa [prefixWord, tailWord_3817135, baseEnd_3817135] using wordTrace_append hprefix tailTrace_3817135
  have hstable : (prefixWord ++ tailWord_3817135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817135).length < 2 ^ (prefixWord ++ tailWord_3817135).sum := by decide
  have hdescent : baseEnd_3817135 < baseStart_3817135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817152 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 2, 3]
def baseStart_3817152 : Nat := 118140960795 + 3817152 * 2 ^ 59
def prefixEnd_3817152 : Nat := 4983230072969 + 3 ^ 40 * 3817152 * 2
def baseEnd_3817152 : Nat := 1306689138180769739296829

theorem tailTrace_3817152 : CollatzResearch.WordTrace tailWord_3817152 prefixEnd_3817152 1306689138180769739296829 := by
  unfold tailWord_3817152
  simp only [CollatzResearch.WordTrace]
  refine ⟨69611485533558848252446855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92815314044745131003262473 69611485533558848252446855)
  ·
    refine ⟨104417228300338272378670283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69611485533558848252446855 104417228300338272378670283)
    ·
      refine ⟨156625842450507408568005425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104417228300338272378670283 156625842450507408568005425)
      ·
        refine ⟨117469381837880556426004069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156625842450507408568005425 117469381837880556426004069)
        ·
          refine ⟨22025509094602604329875763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117469381837880556426004069 22025509094602604329875763)
          ·
            refine ⟨33038263641903906494813645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22025509094602604329875763 33038263641903906494813645)
            ·
              refine ⟨12389348865713964935555117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33038263641903906494813645 12389348865713964935555117)
              ·
                refine ⟨4646005824642736850833169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12389348865713964935555117 4646005824642736850833169)
                ·
                  refine ⟨3484504368482052638124877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646005824642736850833169 3484504368482052638124877)
                  ·
                    refine ⟨1306689138180769739296829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484504368482052638124877 1306689138180769739296829)
                    ·
                      rfl

theorem cell22_3817152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 2, 3].length) (baseStart_3817152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817152 prefixEnd_3817152 := by exact prefixLift 3817152
  have htrace : WordTrace (prefixWord ++ tailWord_3817152) baseStart_3817152 baseEnd_3817152 := by
    simpa [prefixWord, tailWord_3817152, baseEnd_3817152] using wordTrace_append hprefix tailTrace_3817152
  have hstable : (prefixWord ++ tailWord_3817152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817152).length < 2 ^ (prefixWord ++ tailWord_3817152).sum := by decide
  have hdescent : baseEnd_3817152 < baseStart_3817152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817163 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 2, 7]
def baseStart_3817163 : Nat := 118140960795 + 3817163 * 2 ^ 59
def prefixEnd_3817163 : Nat := 4983230072969 + 3 ^ 40 * 3817163 * 2
def baseEnd_3817163 : Nat := 1306692903705569377271795

theorem tailTrace_3817163 : CollatzResearch.WordTrace tailWord_3817163 prefixEnd_3817163 1306692903705569377271795 := by
  unfold tailWord_3817163
  simp only [CollatzResearch.WordTrace]
  refine ⟨139223372270077845383544143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92815581513385230255696095 139223372270077845383544143)
  ·
    refine ⟨208835058405116768075316215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139223372270077845383544143 208835058405116768075316215)
    ·
      refine ⟨313252587607675152112974323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208835058405116768075316215 313252587607675152112974323)
      ·
        refine ⟨469878881411512728169461485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313252587607675152112974323 469878881411512728169461485)
        ·
          refine ⟨176204580529317273063548057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 469878881411512728169461485 176204580529317273063548057)
          ·
            refine ⟨132153435396987954797661043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176204580529317273063548057 132153435396987954797661043)
            ·
              refine ⟨198230153095481932196491565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132153435396987954797661043 198230153095481932196491565)
              ·
                refine ⟨74336307410805724573684337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198230153095481932196491565 74336307410805724573684337)
                ·
                  refine ⟨55752230558104293430263253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74336307410805724573684337 55752230558104293430263253)
                  ·
                    refine ⟨1306692903705569377271795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55752230558104293430263253 1306692903705569377271795)
                    ·
                      rfl

theorem cell22_3817163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_3817163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817163 prefixEnd_3817163 := by exact prefixLift 3817163
  have htrace : WordTrace (prefixWord ++ tailWord_3817163) baseStart_3817163 baseEnd_3817163 := by
    simpa [prefixWord, tailWord_3817163, baseEnd_3817163] using wordTrace_append hprefix tailTrace_3817163
  have hstable : (prefixWord ++ tailWord_3817163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817163).length < 2 ^ (prefixWord ++ tailWord_3817163).sum := by decide
  have hdescent : baseEnd_3817163 < baseStart_3817163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817222 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3817222 : Nat := 118140960795 + 3817222 * 2 ^ 59
def prefixEnd_3817222 : Nat := 4983230072969 + 3 ^ 40 * 3817222 * 2
def baseEnd_3817222 : Nat := 435571033537104296682205

theorem tailTrace_3817222 : CollatzResearch.WordTrace tailWord_3817222 prefixEnd_3817222 435571033537104296682205 := by
  unfold tailWord_3817222
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350797630527003076873185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92817016117909398973294613 4350797630527003076873185)
  ·
    refine ⟨3263098222895252307654889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4350797630527003076873185 3263098222895252307654889)
    ·
      refine ⟨2447323667171439230741167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3263098222895252307654889 2447323667171439230741167)
      ·
        refine ⟨3670985500757158846111751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2447323667171439230741167 3670985500757158846111751)
        ·
          refine ⟨5506478251135738269167627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3670985500757158846111751 5506478251135738269167627)
          ·
            refine ⟨8259717376703607403751441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506478251135738269167627 8259717376703607403751441)
            ·
              refine ⟨6194788032527705552813581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259717376703607403751441 6194788032527705552813581)
              ·
                refine ⟨2323045512197889582305093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6194788032527705552813581 2323045512197889582305093)
                ·
                  refine ⟨435571033537104296682205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323045512197889582305093 435571033537104296682205)
                  ·
                    rfl

theorem cell22_3817222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3817222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817222 prefixEnd_3817222 := by exact prefixLift 3817222
  have htrace : WordTrace (prefixWord ++ tailWord_3817222) baseStart_3817222 baseEnd_3817222 := by
    simpa [prefixWord, tailWord_3817222, baseEnd_3817222] using wordTrace_append hprefix tailTrace_3817222
  have hstable : (prefixWord ++ tailWord_3817222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817222).length < 2 ^ (prefixWord ++ tailWord_3817222).sum := by decide
  have hdescent : baseEnd_3817222 < baseStart_3817222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817274 : List Nat := [3, 1, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_3817274 : Nat := 118140960795 + 3817274 * 2 ^ 59
def prefixEnd_3817274 : Nat := 4983230072969 + 3 ^ 40 * 3817274 * 2
def baseEnd_3817274 : Nat := 1306730901274002087746455

theorem tailTrace_3817274 : CollatzResearch.WordTrace tailWord_3817274 prefixEnd_3817274 1306730901274002087746455 := by
  unfold tailWord_3817274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34806855193168927835208719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92818280515117140893889917 34806855193168927835208719)
  ·
    refine ⟨52210282789753391752813079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34806855193168927835208719 52210282789753391752813079)
    ·
      refine ⟨78315424184630087629219619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52210282789753391752813079 78315424184630087629219619)
      ·
        refine ⟨117473136276945131443829429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78315424184630087629219619 117473136276945131443829429)
        ·
          refine ⟨11013106525963606072859009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117473136276945131443829429 11013106525963606072859009)
          ·
            refine ⟨8259829894472704554644257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11013106525963606072859009 8259829894472704554644257)
            ·
              refine ⟨6194872420854528415983193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8259829894472704554644257 6194872420854528415983193)
              ·
                refine ⟨4646154315640896311987395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6194872420854528415983193 4646154315640896311987395)
                ·
                  refine ⟨6969231473461344467981093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646154315640896311987395 6969231473461344467981093)
                  ·
                    refine ⟨1306730901274002087746455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969231473461344467981093 1306730901274002087746455)
                    ·
                      rfl

theorem cell22_3817274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_3817274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817274 prefixEnd_3817274 := by exact prefixLift 3817274
  have htrace : WordTrace (prefixWord ++ tailWord_3817274) baseStart_3817274 baseEnd_3817274 := by
    simpa [prefixWord, tailWord_3817274, baseEnd_3817274] using wordTrace_append hprefix tailTrace_3817274
  have hstable : (prefixWord ++ tailWord_3817274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817274).length < 2 ^ (prefixWord ++ tailWord_3817274).sum := by decide
  have hdescent : baseEnd_3817274 < baseStart_3817274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817285 : List Nat := [1, 3, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3817285 : Nat := 118140960795 + 3817285 * 2 ^ 59
def prefixEnd_3817285 : Nat := 4983230072969 + 3 ^ 40 * 3817285 * 2
def baseEnd_3817285 : Nat := 1306734666798801725721421

theorem tailTrace_3817285 : CollatzResearch.WordTrace tailWord_3817285 prefixEnd_3817285 1306734666798801725721421 := by
  unfold tailWord_3817285
  simp only [CollatzResearch.WordTrace]
  refine ⟨139227821975635860219485309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92818547983757240146323539 139227821975635860219485309)
  ·
    refine ⟨52210433240863447582306991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139227821975635860219485309 52210433240863447582306991)
    ·
      refine ⟨78315649861295171373460487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52210433240863447582306991 78315649861295171373460487)
      ·
        refine ⟨117473474791942757060190731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78315649861295171373460487 117473474791942757060190731)
        ·
          refine ⟨176210212187914135590286097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117473474791942757060190731 176210212187914135590286097)
          ·
            refine ⟨132157659140935601692714573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176210212187914135590286097 132157659140935601692714573)
            ·
              refine ⟨49559122177850850634767965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132157659140935601692714573 49559122177850850634767965)
              ·
                refine ⟨18584670816694068988037987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49559122177850850634767965 18584670816694068988037987)
                ·
                  refine ⟨27877006225041103482056981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18584670816694068988037987 27877006225041103482056981)
                  ·
                    refine ⟨1306734666798801725721421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27877006225041103482056981 1306734666798801725721421)
                    ·
                      rfl

theorem cell22_3817285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3817285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817285 prefixEnd_3817285 := by exact prefixLift 3817285
  have htrace : WordTrace (prefixWord ++ tailWord_3817285) baseStart_3817285 baseEnd_3817285 := by
    simpa [prefixWord, tailWord_3817285, baseEnd_3817285] using wordTrace_append hprefix tailTrace_3817285
  have hstable : (prefixWord ++ tailWord_3817285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817285).length < 2 ^ (prefixWord ++ tailWord_3817285).sum := by decide
  have hdescent : baseEnd_3817285 < baseStart_3817285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817287 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 4, 3]
def baseStart_3817287 : Nat := 118140960795 + 3817287 * 2 ^ 59
def prefixEnd_3817287 : Nat := 4983230072969 + 3 ^ 40 * 3817287 * 2
def baseEnd_3817287 : Nat := 1306735351439674387171415

theorem tailTrace_3817287 : CollatzResearch.WordTrace tailWord_3817287 prefixEnd_3817287 1306735351439674387171415 := by
  unfold tailWord_3817287
  simp only [CollatzResearch.WordTrace]
  refine ⟨139227894921628614561058115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92818596614419076374038743 139227894921628614561058115)
  ·
    refine ⟨208841842382442921841587173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139227894921628614561058115 208841842382442921841587173)
    ·
      refine ⟨39157845446708047845297595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208841842382442921841587173 39157845446708047845297595)
      ·
        refine ⟨58736768170062071767946393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39157845446708047845297595 58736768170062071767946393)
        ·
          refine ⟨44052576127546553825959795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58736768170062071767946393 44052576127546553825959795)
          ·
            refine ⟨66078864191319830738939693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44052576127546553825959795 66078864191319830738939693)
            ·
              refine ⟨24779574071744936527102385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66078864191319830738939693 24779574071744936527102385)
              ·
                refine ⟨18584680553808702395326789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24779574071744936527102385 18584680553808702395326789)
                ·
                  refine ⟨3484627603839131699123773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18584680553808702395326789 3484627603839131699123773)
                  ·
                    refine ⟨1306735351439674387171415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484627603839131699123773 1306735351439674387171415)
                    ·
                      rfl

theorem cell22_3817287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_3817287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817287 prefixEnd_3817287 := by exact prefixLift 3817287
  have htrace : WordTrace (prefixWord ++ tailWord_3817287) baseStart_3817287 baseEnd_3817287 := by
    simpa [prefixWord, tailWord_3817287, baseEnd_3817287] using wordTrace_append hprefix tailTrace_3817287
  have hstable : (prefixWord ++ tailWord_3817287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817287).length < 2 ^ (prefixWord ++ tailWord_3817287).sum := by decide
  have hdescent : baseEnd_3817287 < baseStart_3817287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817424 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_3817424 : Nat := 118140960795 + 3817424 * 2 ^ 59
def prefixEnd_3817424 : Nat := 4983230072969 + 3 ^ 40 * 3817424 * 2
def baseEnd_3817424 : Nat := 435594083113150565498665

theorem tailTrace_3817424 : CollatzResearch.WordTrace tailWord_3817424 prefixEnd_3817424 435594083113150565498665 := by
  unfold tailWord_3817424
  simp only [CollatzResearch.WordTrace]
  refine ⟨69616445861066143479397663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92821927814754857972530217 69616445861066143479397663)
  ·
    refine ⟨104424668791599215219096495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69616445861066143479397663 104424668791599215219096495)
    ·
      refine ⟨156637003187398822828644743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104424668791599215219096495 156637003187398822828644743)
      ·
        refine ⟨234955504781098234242967115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156637003187398822828644743 234955504781098234242967115)
        ·
          refine ⟨352433257171647351364450673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 234955504781098234242967115 352433257171647351364450673)
          ·
            refine ⟨264324942878735513523338005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352433257171647351364450673 264324942878735513523338005)
            ·
              refine ⟨12390231697440727196406469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 264324942878735513523338005 12390231697440727196406469)
              ·
                refine ⟨2323168443270136349326213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12390231697440727196406469 2323168443270136349326213)
                ·
                  refine ⟨435594083113150565498665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323168443270136349326213 435594083113150565498665)
                  ·
                    rfl

theorem cell22_3817424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_3817424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817424 prefixEnd_3817424 := by exact prefixLift 3817424
  have htrace : WordTrace (prefixWord ++ tailWord_3817424) baseStart_3817424 baseEnd_3817424 := by
    simpa [prefixWord, tailWord_3817424, baseEnd_3817424] using wordTrace_append hprefix tailTrace_3817424
  have hstable : (prefixWord ++ tailWord_3817424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817424).length < 2 ^ (prefixWord ++ tailWord_3817424).sum := by decide
  have hdescent : baseEnd_3817424 < baseStart_3817424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817439 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 1, 5]
def baseStart_3817439 : Nat := 118140960795 + 3817439 * 2 ^ 59
def prefixEnd_3817439 : Nat := 4983230072969 + 3 ^ 40 * 3817439 * 2
def baseEnd_3817439 : Nat := 1306787384145996657370949

theorem tailTrace_3817439 : CollatzResearch.WordTrace tailWord_3817439 prefixEnd_3817439 1306787384145996657370949 := by
  unfold tailWord_3817439
  simp only [CollatzResearch.WordTrace]
  refine ⟨139233438817077944520591371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92822292544718629680394247 139233438817077944520591371)
  ·
    refine ⟨208850158225616916780887057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139233438817077944520591371 208850158225616916780887057)
    ·
      refine ⟨156637618669212687585665293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208850158225616916780887057 156637618669212687585665293)
      ·
        refine ⟨58739107000954757844624485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156637618669212687585665293 58739107000954757844624485)
        ·
          refine ⟨11013582562679017095867091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58739107000954757844624485 11013582562679017095867091)
          ·
            refine ⟨16520373844018525643800637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11013582562679017095867091 16520373844018525643800637)
            ·
              refine ⟨6195140191506947116425239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16520373844018525643800637 6195140191506947116425239)
              ·
                refine ⟨9292710287260420674637859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195140191506947116425239 9292710287260420674637859)
                ·
                  refine ⟨13939065430890631011956789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9292710287260420674637859 13939065430890631011956789)
                  ·
                    refine ⟨1306787384145996657370949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13939065430890631011956789 1306787384145996657370949)
                    ·
                      rfl

theorem cell22_3817439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 1, 5].length) (baseStart_3817439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817439 prefixEnd_3817439 := by exact prefixLift 3817439
  have htrace : WordTrace (prefixWord ++ tailWord_3817439) baseStart_3817439 baseEnd_3817439 := by
    simpa [prefixWord, tailWord_3817439, baseEnd_3817439] using wordTrace_append hprefix tailTrace_3817439
  have hstable : (prefixWord ++ tailWord_3817439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817439).length < 2 ^ (prefixWord ++ tailWord_3817439).sum := by decide
  have hdescent : baseEnd_3817439 < baseStart_3817439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817454 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3817454 : Nat := 118140960795 + 3817454 * 2 ^ 59
def prefixEnd_3817454 : Nat := 4983230072969 + 3 ^ 40 * 3817454 * 2
def baseEnd_3817454 : Nat := 1306792518952541618245903

theorem tailTrace_3817454 : CollatzResearch.WordTrace tailWord_3817454 prefixEnd_3817454 1306792518952541618245903 := by
  unfold tailWord_3817454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17404248239002950260298427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92822657274682401388258277 17404248239002950260298427)
  ·
    refine ⟨26106372358504425390447641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17404248239002950260298427 26106372358504425390447641)
    ·
      refine ⟨19579779268878319042835731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26106372358504425390447641 19579779268878319042835731)
      ·
        refine ⟨29369668903317478564253597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19579779268878319042835731 29369668903317478564253597)
        ·
          refine ⟨11013625838744054461595099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29369668903317478564253597 11013625838744054461595099)
          ·
            refine ⟨16520438758116081692392649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11013625838744054461595099 16520438758116081692392649)
            ·
              refine ⟨12390329068587061269294487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16520438758116081692392649 12390329068587061269294487)
              ·
                refine ⟨18585493602880591903941731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390329068587061269294487 18585493602880591903941731)
                ·
                  refine ⟨27878240404320887855912597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18585493602880591903941731 27878240404320887855912597)
                  ·
                    refine ⟨1306792518952541618245903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27878240404320887855912597 1306792518952541618245903)
                    ·
                      rfl

theorem cell22_3817454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3817454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817454 prefixEnd_3817454 := by exact prefixLift 3817454
  have htrace : WordTrace (prefixWord ++ tailWord_3817454) baseStart_3817454 baseEnd_3817454 := by
    simpa [prefixWord, tailWord_3817454, baseEnd_3817454] using wordTrace_append hprefix tailTrace_3817454
  have hstable : (prefixWord ++ tailWord_3817454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817454).length < 2 ^ (prefixWord ++ tailWord_3817454).sum := by decide
  have hdescent : baseEnd_3817454 < baseStart_3817454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817578 : List Nat := [3, 1, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3817578 : Nat := 118140960795 + 3817578 * 2 ^ 59
def prefixEnd_3817578 : Nat := 4983230072969 + 3 ^ 40 * 3817578 * 2
def baseEnd_3817578 : Nat := 1306834966686646628145523

theorem tailTrace_3817578 : CollatzResearch.WordTrace tailWord_3817578 prefixEnd_3817578 1306834966686646628145523 := by
  unfold tailWord_3817578
  simp only [CollatzResearch.WordTrace]
  refine ⟨34809627140893592814975347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92825672375716247506600925 34809627140893592814975347)
  ·
    refine ⟨52214440711340389222463021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34809627140893592814975347 52214440711340389222463021)
    ·
      refine ⟨19580415266752645958423633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52214440711340389222463021 19580415266752645958423633)
      ·
        refine ⟨14685311450064484468817725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19580415266752645958423633 14685311450064484468817725)
        ·
          refine ⟨5506991793774181675806647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14685311450064484468817725 5506991793774181675806647)
          ·
            refine ⟨8260487690661272513709971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5506991793774181675806647 8260487690661272513709971)
            ·
              refine ⟨12390731535991908770564957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260487690661272513709971 12390731535991908770564957)
              ·
                refine ⟨4646524325996965788961859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12390731535991908770564957 4646524325996965788961859)
                ·
                  refine ⟨6969786488995448683442789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4646524325996965788961859 6969786488995448683442789)
                  ·
                    refine ⟨1306834966686646628145523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6969786488995448683442789 1306834966686646628145523)
                    ·
                      rfl

theorem cell22_3817578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3817578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817578 prefixEnd_3817578 := by exact prefixLift 3817578
  have htrace : WordTrace (prefixWord ++ tailWord_3817578) baseStart_3817578 baseEnd_3817578 := by
    simpa [prefixWord, tailWord_3817578, baseEnd_3817578] using wordTrace_append hprefix tailTrace_3817578
  have hstable : (prefixWord ++ tailWord_3817578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817578).length < 2 ^ (prefixWord ++ tailWord_3817578).sum := by decide
  have hdescent : baseEnd_3817578 < baseStart_3817578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817591 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 4, 3]
def baseStart_3817591 : Nat := 118140960795 + 3817591 * 2 ^ 59
def prefixEnd_3817591 : Nat := 4983230072969 + 3 ^ 40 * 3817591 * 2
def baseEnd_3817591 : Nat := 1306839416852318927570483

theorem tailTrace_3817591 : CollatzResearch.WordTrace tailWord_3817591 prefixEnd_3817591 1306839416852318927570483 := by
  unfold tailWord_3817591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139238982712527274480124627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92825988475018182986749751 139238982712527274480124627)
  ·
    refine ⟨208858474068790911720186941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139238982712527274480124627 208858474068790911720186941)
    ·
      refine ⟨78321927775796591895070103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208858474068790911720186941 78321927775796591895070103)
      ·
        refine ⟨117482891663694887842605155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78321927775796591895070103 117482891663694887842605155)
        ·
          refine ⟨176224337495542331763907733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117482891663694887842605155 176224337495542331763907733)
          ·
            refine ⟨8260515820103546801433175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 176224337495542331763907733 8260515820103546801433175)
            ·
              refine ⟨12390773730155320202149763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8260515820103546801433175 12390773730155320202149763)
              ·
                refine ⟨18586160595232980303224645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12390773730155320202149763 18586160595232980303224645)
                ·
                  refine ⟨3484905111606183806854621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18586160595232980303224645 3484905111606183806854621)
                  ·
                    refine ⟨1306839416852318927570483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3484905111606183806854621 1306839416852318927570483)
                    ·
                      rfl

theorem cell22_3817591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_3817591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817591 prefixEnd_3817591 := by exact prefixLift 3817591
  have htrace : WordTrace (prefixWord ++ tailWord_3817591) baseStart_3817591 baseEnd_3817591 := by
    simpa [prefixWord, tailWord_3817591, baseEnd_3817591] using wordTrace_append hprefix tailTrace_3817591
  have hstable : (prefixWord ++ tailWord_3817591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817591).length < 2 ^ (prefixWord ++ tailWord_3817591).sum := by decide
  have hdescent : baseEnd_3817591 < baseStart_3817591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817604 : List Nat := [2, 3, 2, 1, 2, 1, 2, 9]
def baseStart_3817604 : Nat := 118140960795 + 3817604 * 2 ^ 59
def prefixEnd_3817604 : Nat := 4983230072969 + 3 ^ 40 * 3817604 * 2
def baseEnd_3817604 : Nat := 145204874113110136332827

theorem tailTrace_3817604 : CollatzResearch.WordTrace tailWord_3817604 prefixEnd_3817604 145204874113110136332827 := by
  unfold tailWord_3817604
  simp only [CollatzResearch.WordTrace]
  refine ⟨69619728430740088850173933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92826304574320118466898577 69619728430740088850173933)
  ·
    refine ⟨26107398161527533318815225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69619728430740088850173933 26107398161527533318815225)
    ·
      refine ⟨19580548621145649989111419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26107398161527533318815225 19580548621145649989111419)
      ·
        refine ⟨29370822931718474983667129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19580548621145649989111419 29370822931718474983667129)
        ·
          refine ⟨22028117198788856237750347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29370822931718474983667129 22028117198788856237750347)
          ·
            refine ⟨33042175798183284356625521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22028117198788856237750347 33042175798183284356625521)
            ·
              refine ⟨24781631848637463267469141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33042175798183284356625521 24781631848637463267469141)
              ·
                refine ⟨145204874113110136332827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24781631848637463267469141 145204874113110136332827)
                ·
                  rfl

theorem cell22_3817604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_3817604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817604 prefixEnd_3817604 := by exact prefixLift 3817604
  have htrace : WordTrace (prefixWord ++ tailWord_3817604) baseStart_3817604 baseEnd_3817604 := by
    simpa [prefixWord, tailWord_3817604, baseEnd_3817604] using wordTrace_append hprefix tailTrace_3817604
  have hstable : (prefixWord ++ tailWord_3817604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817604).length < 2 ^ (prefixWord ++ tailWord_3817604).sum := by decide
  have hdescent : baseEnd_3817604 < baseStart_3817604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817608 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 1, 5]
def baseStart_3817608 : Nat := 118140960795 + 3817608 * 2 ^ 59
def prefixEnd_3817608 : Nat := 4983230072969 + 3 ^ 40 * 3817608 * 2
def baseEnd_3817608 : Nat := 1306845236299736549895431

theorem tailTrace_3817608 : CollatzResearch.WordTrace tailWord_3817608 prefixEnd_3817608 1306845236299736549895431 := by
  unfold tailWord_3817608
  simp only [CollatzResearch.WordTrace]
  refine ⟨69619801376732843191746739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92826401835643790922328985 69619801376732843191746739)
  ·
    refine ⟨104429702065099264787620109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69619801376732843191746739 104429702065099264787620109)
    ·
      refine ⟨39161138274412224295357541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104429702065099264787620109 39161138274412224295357541)
      ·
        refine ⟨7342713426452292055379539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39161138274412224295357541 7342713426452292055379539)
        ·
          refine ⟨11014070139678438083069309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7342713426452292055379539 11014070139678438083069309)
          ·
            refine ⟨4130276302379414281150991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11014070139678438083069309 4130276302379414281150991)
            ·
              refine ⟨6195414453569121421726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4130276302379414281150991 6195414453569121421726487)
              ·
                refine ⟨9293121680353682132589731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195414453569121421726487 9293121680353682132589731)
                ·
                  refine ⟨13939682520530523198884597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293121680353682132589731 13939682520530523198884597)
                  ·
                    refine ⟨1306845236299736549895431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13939682520530523198884597 1306845236299736549895431)
                    ·
                      rfl

theorem cell22_3817608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_3817608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817608 prefixEnd_3817608 := by exact prefixLift 3817608
  have htrace : WordTrace (prefixWord ++ tailWord_3817608) baseStart_3817608 baseEnd_3817608 := by
    simpa [prefixWord, tailWord_3817608, baseEnd_3817608] using wordTrace_append hprefix tailTrace_3817608
  have hstable : (prefixWord ++ tailWord_3817608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817608).length < 2 ^ (prefixWord ++ tailWord_3817608).sum := by decide
  have hdescent : baseEnd_3817608 < baseStart_3817608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817760 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 2, 3]
def baseStart_3817760 : Nat := 118140960795 + 3817760 * 2 ^ 59
def prefixEnd_3817760 : Nat := 4983230072969 + 3 ^ 40 * 3817760 * 2
def baseEnd_3817760 : Nat := 1306897269006058820094965

theorem tailTrace_3817760 : CollatzResearch.WordTrace tailWord_3817760 prefixEnd_3817760 1306897269006058820094965 := by
  unfold tailWord_3817760
  simp only [CollatzResearch.WordTrace]
  refine ⟨69622573324457508171513367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92830097765943344228684489 69622573324457508171513367)
  ·
    refine ⟨104433859986686262257270051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69622573324457508171513367 104433859986686262257270051)
    ·
      refine ⟨156650789980029393385905077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104433859986686262257270051 156650789980029393385905077)
      ·
        refine ⟨14686011560627755629928601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156650789980029393385905077 14686011560627755629928601)
        ·
          refine ⟨11014508670470816722446451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14686011560627755629928601 11014508670470816722446451)
          ·
            refine ⟨16521763005706225083669677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11014508670470816722446451 16521763005706225083669677)
            ·
              refine ⟨6195661127139834406376129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16521763005706225083669677 6195661127139834406376129)
              ·
                refine ⟨4646745845354875804782097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6195661127139834406376129 4646745845354875804782097)
                ·
                  refine ⟨3485059384016156853586573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646745845354875804782097 3485059384016156853586573)
                  ·
                    refine ⟨1306897269006058820094965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485059384016156853586573 1306897269006058820094965)
                    ·
                      rfl

theorem cell22_3817760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_3817760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817760 prefixEnd_3817760 := by exact prefixLift 3817760
  have htrace : WordTrace (prefixWord ++ tailWord_3817760) baseStart_3817760 baseEnd_3817760 := by
    simpa [prefixWord, tailWord_3817760, baseEnd_3817760] using wordTrace_append hprefix tailTrace_3817760
  have hstable : (prefixWord ++ tailWord_3817760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817760).length < 2 ^ (prefixWord ++ tailWord_3817760).sum := by decide
  have hdescent : baseEnd_3817760 < baseStart_3817760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817777 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 2, 3]
def baseStart_3817777 : Nat := 118140960795 + 3817777 * 2 ^ 59
def prefixEnd_3817777 : Nat := 4983230072969 + 3 ^ 40 * 3817777 * 2
def baseEnd_3817777 : Nat := 1306903088453476442419913

theorem tailTrace_3817777 : CollatzResearch.WordTrace tailWord_3817777 prefixEnd_3817777 1306903088453476442419913 := by
  unfold tailWord_3817777
  simp only [CollatzResearch.WordTrace]
  refine ⟨139245766689853428246395585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92830511126568952164263723 139245766689853428246395585)
  ·
    refine ⟨104434325017390071184796689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139245766689853428246395585 104434325017390071184796689)
    ·
      refine ⟨78325743763042553388597517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104434325017390071184796689 78325743763042553388597517)
      ·
        refine ⟨29372153911140957520724069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78325743763042553388597517 29372153911140957520724069)
        ·
          refine ⟨5507278858338929535135763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29372153911140957520724069 5507278858338929535135763)
          ·
            refine ⟨8260918287508394302703645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507278858338929535135763 8260918287508394302703645)
            ·
              refine ⟨3097844357815647863513867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8260918287508394302703645 3097844357815647863513867)
              ·
                refine ⟨4646766536723471795270801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3097844357815647863513867 4646766536723471795270801)
                ·
                  refine ⟨3485074902542603846453101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4646766536723471795270801 3485074902542603846453101)
                  ·
                    refine ⟨1306903088453476442419913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485074902542603846453101 1306903088453476442419913)
                    ·
                      rfl

theorem cell22_3817777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 2, 3].length) (baseStart_3817777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817777 prefixEnd_3817777 := by exact prefixLift 3817777
  have htrace : WordTrace (prefixWord ++ tailWord_3817777) baseStart_3817777 baseEnd_3817777 := by
    simpa [prefixWord, tailWord_3817777, baseEnd_3817777] using wordTrace_append hprefix tailTrace_3817777
  have hstable : (prefixWord ++ tailWord_3817777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817777).length < 2 ^ (prefixWord ++ tailWord_3817777).sum := by decide
  have hdescent : baseEnd_3817777 < baseStart_3817777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817788 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 3, 3]
def baseStart_3817788 : Nat := 118140960795 + 3817788 * 2 ^ 59
def prefixEnd_3817788 : Nat := 4983230072969 + 3 ^ 40 * 3817788 * 2
def baseEnd_3817788 : Nat := 1306906853978276080394879

theorem tailTrace_3817788 : CollatzResearch.WordTrace tailWord_3817788 prefixEnd_3817788 1306906853978276080394879 := by
  unfold tailWord_3817788
  simp only [CollatzResearch.WordTrace]
  refine ⟨69623083946406788562523009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92830778595209051416697345 69623083946406788562523009)
  ·
    refine ⟨52217312959805091421892257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69623083946406788562523009 52217312959805091421892257)
    ·
      refine ⟨39162984719853818566419193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52217312959805091421892257 39162984719853818566419193)
      ·
        refine ⟨29372238539890363924814395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39162984719853818566419193 29372238539890363924814395)
        ·
          refine ⟨44058357809835545887221593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29372238539890363924814395 44058357809835545887221593)
          ·
            refine ⟨33043768357376659415416195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44058357809835545887221593 33043768357376659415416195)
            ·
              refine ⟨49565652536064989123124293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33043768357376659415416195 49565652536064989123124293)
              ·
                refine ⟨9293559850512185460585805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49565652536064989123124293 9293559850512185460585805)
                ·
                  refine ⟨3485084943942069547719677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9293559850512185460585805 3485084943942069547719677)
                  ·
                    refine ⟨1306906853978276080394879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485084943942069547719677 1306906853978276080394879)
                    ·
                      rfl

theorem cell22_3817788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_3817788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817788 prefixEnd_3817788 := by exact prefixLift 3817788
  have htrace : WordTrace (prefixWord ++ tailWord_3817788) baseStart_3817788 baseEnd_3817788 := by
    simpa [prefixWord, tailWord_3817788, baseEnd_3817788] using wordTrace_append hprefix tailTrace_3817788
  have hstable : (prefixWord ++ tailWord_3817788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817788).length < 2 ^ (prefixWord ++ tailWord_3817788).sum := by decide
  have hdescent : baseEnd_3817788 < baseStart_3817788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817790 : List Nat := [4, 2, 1, 2, 1, 4, 2, 6]
def baseStart_3817790 : Nat := 118140960795 + 3817790 * 2 ^ 59
def prefixEnd_3817790 : Nat := 4983230072969 + 3 ^ 40 * 3817790 * 2
def baseEnd_3817790 : Nat := 145211948735460971316097

theorem tailTrace_3817790 : CollatzResearch.WordTrace tailWord_3817790 prefixEnd_3817790 145211948735460971316097 := by
  unfold tailWord_3817790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17405780104850791433327353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92830827225870887644412549 17405780104850791433327353)
  ·
    refine ⟨13054335078638093574995515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17405780104850791433327353 13054335078638093574995515)
    ·
      refine ⟨19581502617957140362493273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13054335078638093574995515 19581502617957140362493273)
      ·
        refine ⟨14686126963467855271869955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19581502617957140362493273 14686126963467855271869955)
        ·
          refine ⟨22029190445201782907804933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14686126963467855271869955 22029190445201782907804933)
          ·
            refine ⟨4130473208475334295213425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22029190445201782907804933 4130473208475334295213425)
            ·
              refine ⟨3097854906356500721410069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4130473208475334295213425 3097854906356500721410069)
              ·
                refine ⟨145211948735460971316097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3097854906356500721410069 145211948735460971316097)
                ·
                  rfl

theorem cell22_3817790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_3817790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817790 prefixEnd_3817790 := by exact prefixLift 3817790
  have htrace : WordTrace (prefixWord ++ tailWord_3817790) baseStart_3817790 baseEnd_3817790 := by
    simpa [prefixWord, tailWord_3817790, baseEnd_3817790] using wordTrace_append hprefix tailTrace_3817790
  have hstable : (prefixWord ++ tailWord_3817790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817790).length < 2 ^ (prefixWord ++ tailWord_3817790).sum := by decide
  have hdescent : baseEnd_3817790 < baseStart_3817790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817816 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 2, 5]
def baseStart_3817816 : Nat := 118140960795 + 3817816 * 2 ^ 59
def prefixEnd_3817816 : Nat := 4983230072969 + 3 ^ 40 * 3817816 * 2
def baseEnd_3817816 : Nat := 1306916438950493340694793

theorem tailTrace_3817816 : CollatzResearch.WordTrace tailWord_3817816 prefixEnd_3817816 1306916438950493340694793 := by
  unfold tailWord_3817816
  simp only [CollatzResearch.WordTrace]
  refine ⟨69623594568356068953532651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92831459424474758604710201 69623594568356068953532651)
  ·
    refine ⟨104435391852534103430298977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69623594568356068953532651 104435391852534103430298977)
    ·
      refine ⟨78326543889400577572724233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104435391852534103430298977 78326543889400577572724233)
      ·
        refine ⟨58744907917050433179543175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78326543889400577572724233 58744907917050433179543175)
        ·
          refine ⟨88117361875575649769314763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58744907917050433179543175 88117361875575649769314763)
          ·
            refine ⟨132176042813363474653972145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88117361875575649769314763 132176042813363474653972145)
            ·
              refine ⟨99132032110022605990479109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132176042813363474653972145 99132032110022605990479109)
              ·
                refine ⟨18587256020629238623214833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99132032110022605990479109 18587256020629238623214833)
                ·
                  refine ⟨13940442015471928967411125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18587256020629238623214833 13940442015471928967411125)
                  ·
                    refine ⟨1306916438950493340694793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13940442015471928967411125 1306916438950493340694793)
                    ·
                      rfl

theorem cell22_3817816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_3817816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817816 prefixEnd_3817816 := by exact prefixLift 3817816
  have htrace : WordTrace (prefixWord ++ tailWord_3817816) baseStart_3817816 baseEnd_3817816 := by
    simpa [prefixWord, tailWord_3817816, baseEnd_3817816] using wordTrace_append hprefix tailTrace_3817816
  have hstable : (prefixWord ++ tailWord_3817816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817816).length < 2 ^ (prefixWord ++ tailWord_3817816).sum := by decide
  have hdescent : baseEnd_3817816 < baseStart_3817816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817895 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3817895 : Nat := 118140960795 + 3817895 * 2 ^ 59
def prefixEnd_3817895 : Nat := 4983230072969 + 3 ^ 40 * 3817895 * 2
def baseEnd_3817895 : Nat := 1306943482264963467969551

theorem tailTrace_3817895 : CollatzResearch.WordTrace tailWord_3817895 prefixEnd_3817895 1306943482264963467969551 := by
  unfold tailWord_3817895
  simp only [CollatzResearch.WordTrace]
  refine ⟨139250070503425934399191139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92833380335617289599460759 139250070503425934399191139)
  ·
    refine ⟨208875105755138901598786709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139250070503425934399191139 208875105755138901598786709)
    ·
      refine ⟨9791020582272136012443127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 208875105755138901598786709 9791020582272136012443127)
      ·
        refine ⟨14686530873408204018664691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791020582272136012443127 14686530873408204018664691)
        ·
          refine ⟨22029796310112306027997037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14686530873408204018664691 22029796310112306027997037)
          ·
            refine ⟨8261173616292114760498889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22029796310112306027997037 8261173616292114760498889)
            ·
              refine ⟨6195880212219086070374167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261173616292114760498889 6195880212219086070374167)
              ·
                refine ⟨9293820318328629105561251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6195880212219086070374167 9293820318328629105561251)
                ·
                  refine ⟨13940730477492943658341877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9293820318328629105561251 13940730477492943658341877)
                  ·
                    refine ⟨1306943482264963467969551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13940730477492943658341877 1306943482264963467969551)
                    ·
                      rfl

theorem cell22_3817895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3817895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817895 prefixEnd_3817895 := by exact prefixLift 3817895
  have htrace : WordTrace (prefixWord ++ tailWord_3817895) baseStart_3817895 baseEnd_3817895 := by
    simpa [prefixWord, tailWord_3817895, baseEnd_3817895] using wordTrace_append hprefix tailTrace_3817895
  have hstable : (prefixWord ++ tailWord_3817895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817895).length < 2 ^ (prefixWord ++ tailWord_3817895).sum := by decide
  have hdescent : baseEnd_3817895 < baseStart_3817895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817923 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 7, 3]
def baseStart_3817923 : Nat := 118140960795 + 3817923 * 2 ^ 59
def prefixEnd_3817923 : Nat := 4983230072969 + 3 ^ 40 * 3817923 * 2
def baseEnd_3817923 : Nat := 1306953067237180728269465

theorem tailTrace_3817923 : CollatzResearch.WordTrace tailWord_3817923 prefixEnd_3817923 1306953067237180728269465 := by
  unfold tailWord_3817923
  simp only [CollatzResearch.WordTrace]
  refine ⟨139251091747324495181210423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92834061164882996787473615 139251091747324495181210423)
  ·
    refine ⟨208876637620986742771815635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139251091747324495181210423 208876637620986742771815635)
    ·
      refine ⟨313314956431480114157723453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208876637620986742771815635 313314956431480114157723453)
      ·
        refine ⟨117493108661805042809146295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313314956431480114157723453 117493108661805042809146295)
        ·
          refine ⟨176239662992707564213719443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117493108661805042809146295 176239662992707564213719443)
          ·
            refine ⟨264359494489061346320579165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176239662992707564213719443 264359494489061346320579165)
            ·
              refine ⟨99134810433398004870217187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264359494489061346320579165 99134810433398004870217187)
              ·
                refine ⟨148702215650097007305325781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99134810433398004870217187 148702215650097007305325781)
                ·
                  refine ⟨3485208179299148608718573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 148702215650097007305325781 3485208179299148608718573)
                  ·
                    refine ⟨1306953067237180728269465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485208179299148608718573 1306953067237180728269465)
                    ·
                      rfl

theorem cell22_3817923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 7, 3].length) (baseStart_3817923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817923 prefixEnd_3817923 := by exact prefixLift 3817923
  have htrace : WordTrace (prefixWord ++ tailWord_3817923) baseStart_3817923 baseEnd_3817923 := by
    simpa [prefixWord, tailWord_3817923, baseEnd_3817923] using wordTrace_append hprefix tailTrace_3817923
  have hstable : (prefixWord ++ tailWord_3817923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817923).length < 2 ^ (prefixWord ++ tailWord_3817923).sum := by decide
  have hdescent : baseEnd_3817923 < baseStart_3817923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3817991 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 1, 3]
def baseStart_3817991 : Nat := 118140960795 + 3817991 * 2 ^ 59
def prefixEnd_3817991 : Nat := 4983230072969 + 3 ^ 40 * 3817991 * 2
def baseEnd_3817991 : Nat := 1306976345026851217569257

theorem tailTrace_3817991 : CollatzResearch.WordTrace tailWord_3817991 prefixEnd_3817991 1306976345026851217569257 := by
  unfold tailWord_3817991
  simp only [CollatzResearch.WordTrace]
  refine ⟨139253571911078142794685827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92835714607385428529790551 139253571911078142794685827)
  ·
    refine ⟨208880357866617214192028741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139253571911078142794685827 208880357866617214192028741)
    ·
      refine ⟨39165067099990727661005389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208880357866617214192028741 39165067099990727661005389)
      ·
        refine ⟨14686900162496522872877021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39165067099990727661005389 14686900162496522872877021)
        ·
          refine ⟨5507587560936196077328883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14686900162496522872877021 5507587560936196077328883)
          ·
            refine ⟨8261381341404294115993325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507587560936196077328883 8261381341404294115993325)
            ·
              refine ⟨3098018003026610293497497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8261381341404294115993325 3098018003026610293497497)
              ·
                refine ⟨2323513502269957720123123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098018003026610293497497 2323513502269957720123123)
                ·
                  refine ⟨3485270253404936580184685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323513502269957720123123 3485270253404936580184685)
                  ·
                    refine ⟨1306976345026851217569257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485270253404936580184685 1306976345026851217569257)
                    ·
                      rfl

theorem cell22_3817991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_3817991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3817991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3817991 prefixEnd_3817991 := by exact prefixLift 3817991
  have htrace : WordTrace (prefixWord ++ tailWord_3817991) baseStart_3817991 baseEnd_3817991 := by
    simpa [prefixWord, tailWord_3817991, baseEnd_3817991] using wordTrace_append hprefix tailTrace_3817991
  have hstable : (prefixWord ++ tailWord_3817991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3817991).length < 2 ^ (prefixWord ++ tailWord_3817991).sum := by decide
  have hdescent : baseEnd_3817991 < baseStart_3817991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3817991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818004 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 5]
def baseStart_3818004 : Nat := 118140960795 + 3818004 * 2 ^ 59
def prefixEnd_3818004 : Nat := 4983230072969 + 3 ^ 40 * 3818004 * 2
def baseEnd_3818004 : Nat := 435660265064174505664739

theorem tailTrace_3818004 : CollatzResearch.WordTrace tailWord_3818004 prefixEnd_3818004 435660265064174505664739 := by
  unfold tailWord_3818004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69627023030015523007454533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92836030706687364009939377 69627023030015523007454533)
  ·
    refine ⟨13055066818127910563897725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69627023030015523007454533 13055066818127910563897725)
    ·
      refine ⟨4895650056797966461461647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13055066818127910563897725 4895650056797966461461647)
      ·
        refine ⟨7343475085196949692192471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4895650056797966461461647 7343475085196949692192471)
        ·
          refine ⟨11015212627795424538288707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7343475085196949692192471 11015212627795424538288707)
          ·
            refine ⟨16522818941693136807433061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11015212627795424538288707 16522818941693136807433061)
            ·
              refine ⟨3098028551567463151393699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16522818941693136807433061 3098028551567463151393699)
              ·
                refine ⟨4647042827351194727090549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098028551567463151393699 4647042827351194727090549)
                ·
                  refine ⟨435660265064174505664739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647042827351194727090549 435660265064174505664739)
                  ·
                    rfl

theorem cell22_3818004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_3818004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818004 prefixEnd_3818004 := by exact prefixLift 3818004
  have htrace : WordTrace (prefixWord ++ tailWord_3818004) baseStart_3818004 baseEnd_3818004 := by
    simpa [prefixWord, tailWord_3818004, baseEnd_3818004] using wordTrace_append hprefix tailTrace_3818004
  have hstable : (prefixWord ++ tailWord_3818004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818004).length < 2 ^ (prefixWord ++ tailWord_3818004).sum := by decide
  have hdescent : baseEnd_3818004 < baseStart_3818004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818028 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_3818028 : Nat := 118140960795 + 3818028 * 2 ^ 59
def prefixEnd_3818028 : Nat := 4983230072969 + 3 ^ 40 * 3818028 * 2
def baseEnd_3818028 : Nat := 1306989010882995454394143

theorem tailTrace_3818028 : CollatzResearch.WordTrace tailWord_3818028 prefixEnd_3818028 1306989010882995454394143 := by
  unfold tailWord_3818028
  simp only [CollatzResearch.WordTrace]
  refine ⟨69627460705972049056891369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92836614274629398742521825 69627460705972049056891369)
  ·
    refine ⟨52220595529479036792668527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69627460705972049056891369 52220595529479036792668527)
    ·
      refine ⟨78330893294218555189002791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52220595529479036792668527 78330893294218555189002791)
      ·
        refine ⟨117496339941327832783504187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78330893294218555189002791 117496339941327832783504187)
        ·
          refine ⟨176244509911991749175256281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117496339941327832783504187 176244509911991749175256281)
          ·
            refine ⟨132183382433993811881442211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176244509911991749175256281 132183382433993811881442211)
            ·
              refine ⟨198275073650990717822163317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132183382433993811881442211 198275073650990717822163317)
              ·
                refine ⟨18588288154780379795827811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 198275073650990717822163317 18588288154780379795827811)
                ·
                  refine ⟨27882432232170569693741717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18588288154780379795827811 27882432232170569693741717)
                  ·
                    refine ⟨1306989010882995454394143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27882432232170569693741717 1306989010882995454394143)
                    ·
                      rfl

theorem cell22_3818028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_3818028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818028 prefixEnd_3818028 := by exact prefixLift 3818028
  have htrace : WordTrace (prefixWord ++ tailWord_3818028) baseStart_3818028 baseEnd_3818028 := by
    simpa [prefixWord, tailWord_3818028, baseEnd_3818028] using wordTrace_append hprefix tailTrace_3818028
  have hstable : (prefixWord ++ tailWord_3818028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818028).length < 2 ^ (prefixWord ++ tailWord_3818028).sum := by decide
  have hdescent : baseEnd_3818028 < baseStart_3818028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818047 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 2, 3]
def baseStart_3818047 : Nat := 118140960795 + 3818047 * 2 ^ 59
def prefixEnd_3818047 : Nat := 4983230072969 + 3 ^ 40 * 3818047 * 2
def baseEnd_3818047 : Nat := 1306995514971285738169085

theorem tailTrace_3818047 : CollatzResearch.WordTrace tailWord_3818047 prefixEnd_3818047 1306995514971285738169085 := by
  unfold tailWord_3818047
  simp only [CollatzResearch.WordTrace]
  refine ⟨139255614398875264358724395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92837076265916842905816263 139255614398875264358724395)
  ·
    refine ⟨208883421598312896538086593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139255614398875264358724395 208883421598312896538086593)
    ·
      refine ⟨156662566198734672403564945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208883421598312896538086593 156662566198734672403564945)
      ·
        refine ⟨117496924649051004302673709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156662566198734672403564945 117496924649051004302673709)
        ·
          refine ⟨44061346743394126613502641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117496924649051004302673709 44061346743394126613502641)
          ·
            refine ⟨33046010057545594960126981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44061346743394126613502641 33046010057545594960126981)
            ·
              refine ⟨6196126885789799055023809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33046010057545594960126981 6196126885789799055023809)
              ·
                refine ⟨4647095164342349291267857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196126885789799055023809 4647095164342349291267857)
                ·
                  refine ⟨3485321373256761968450893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647095164342349291267857 3485321373256761968450893)
                  ·
                    refine ⟨1306995514971285738169085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485321373256761968450893 1306995514971285738169085)
                    ·
                      rfl

theorem cell22_3818047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 2, 3].length) (baseStart_3818047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818047 prefixEnd_3818047 := by exact prefixLift 3818047
  have htrace : WordTrace (prefixWord ++ tailWord_3818047) baseStart_3818047 baseEnd_3818047 := by
    simpa [prefixWord, tailWord_3818047, baseEnd_3818047] using wordTrace_append hprefix tailTrace_3818047
  have hstable : (prefixWord ++ tailWord_3818047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818047).length < 2 ^ (prefixWord ++ tailWord_3818047).sum := by decide
  have hdescent : baseEnd_3818047 < baseStart_3818047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818049 : List Nat := [1, 2, 5, 1, 1, 2, 4, 2, 4]
def baseStart_3818049 : Nat := 118140960795 + 3818049 * 2 ^ 59
def prefixEnd_3818049 : Nat := 4983230072969 + 3 ^ 40 * 3818049 * 2
def baseEnd_3818049 : Nat := 435665399870719466539693

theorem tailTrace_3818049 : CollatzResearch.WordTrace tailWord_3818049 prefixEnd_3818049 435665399870719466539693 := by
  unfold tailWord_3818049
  simp only [CollatzResearch.WordTrace]
  refine ⟨139255687344868018700297201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92837124896578679133531467 139255687344868018700297201)
  ·
    refine ⟨104441765508651014025222901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139255687344868018700297201 104441765508651014025222901)
    ·
      refine ⟨9791415516436032564864647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104441765508651014025222901 9791415516436032564864647)
      ·
        refine ⟨14687123274654048847296971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9791415516436032564864647 14687123274654048847296971)
        ·
          refine ⟨22030684911981073270945457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687123274654048847296971 22030684911981073270945457)
          ·
            refine ⟨16523013683985804953209093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22030684911981073270945457 16523013683985804953209093)
            ·
              refine ⟨3098065065747338428726705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16523013683985804953209093 3098065065747338428726705)
              ·
                refine ⟨2323548799310503821545029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098065065747338428726705 2323548799310503821545029)
                ·
                  refine ⟨435665399870719466539693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323548799310503821545029 435665399870719466539693)
                  ·
                    rfl

theorem cell22_3818049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_3818049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818049 prefixEnd_3818049 := by exact prefixLift 3818049
  have htrace : WordTrace (prefixWord ++ tailWord_3818049) baseStart_3818049 baseEnd_3818049 := by
    simpa [prefixWord, tailWord_3818049, baseEnd_3818049] using wordTrace_append hprefix tailTrace_3818049
  have hstable : (prefixWord ++ tailWord_3818049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818049).length < 2 ^ (prefixWord ++ tailWord_3818049).sum := by decide
  have hdescent : baseEnd_3818049 < baseStart_3818049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818105 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 7]
def baseStart_3818105 : Nat := 118140960795 + 3818105 * 2 ^ 59
def prefixEnd_3818105 : Nat := 4983230072969 + 3 ^ 40 * 3818105 * 2
def baseEnd_3818105 : Nat := 435671789852197640072969

theorem tailTrace_3818105 : CollatzResearch.WordTrace tailWord_3818105 prefixEnd_3818105 435671789852197640072969 := by
  unfold tailWord_3818105
  simp only [CollatzResearch.WordTrace]
  refine ⟨139257729832665140264335769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92838486555110093509557179 139257729832665140264335769)
  ·
    refine ⟨104443297374498855198251827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139257729832665140264335769 104443297374498855198251827)
    ·
      refine ⟨156664946061748282797377741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104443297374498855198251827 156664946061748282797377741)
      ·
        refine ⟨58749354773155606049016653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156664946061748282797377741 58749354773155606049016653)
        ·
          refine ⟨22031008039933352268381245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58749354773155606049016653 22031008039933352268381245)
          ·
            refine ⟨8261628014975007100642967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22031008039933352268381245 8261628014975007100642967)
            ·
              refine ⟨12392442022462510650964451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8261628014975007100642967 12392442022462510650964451)
              ·
                refine ⟨18588663033693765976446677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12392442022462510650964451 18588663033693765976446677)
                ·
                  refine ⟨435671789852197640072969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18588663033693765976446677 435671789852197640072969)
                  ·
                    rfl

theorem cell22_3818105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_3818105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818105 prefixEnd_3818105 := by exact prefixLift 3818105
  have htrace : WordTrace (prefixWord ++ tailWord_3818105) baseStart_3818105 baseEnd_3818105 := by
    simpa [prefixWord, tailWord_3818105, baseEnd_3818105] using wordTrace_append hprefix tailTrace_3818105
  have hstable : (prefixWord ++ tailWord_3818105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818105).length < 2 ^ (prefixWord ++ tailWord_3818105).sum := by decide
  have hdescent : baseEnd_3818105 < baseStart_3818105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818109 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3818109 : Nat := 118140960795 + 3818109 * 2 ^ 59
def prefixEnd_3818109 : Nat := 4983230072969 + 3 ^ 40 * 3818109 * 2
def baseEnd_3818109 : Nat := 1307016738838338243118895

theorem tailTrace_3818109 : CollatzResearch.WordTrace tailWord_3818109 prefixEnd_3818109 1307016738838338243118895 := by
  unfold tailWord_3818109
  simp only [CollatzResearch.WordTrace]
  refine ⟨139257875724650648947481381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92838583816433765964987587 139257875724650648947481381)
  ·
    refine ⟨26110851698371996677652759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139257875724650648947481381 26110851698371996677652759)
    ·
      refine ⟨39166277547557995016479139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26110851698371996677652759 39166277547557995016479139)
      ·
        refine ⟨58749416321336992524718709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39166277547557995016479139 58749416321336992524718709)
        ·
          refine ⟨5507757780125343049192379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58749416321336992524718709 5507757780125343049192379)
          ·
            refine ⟨8261636670188014573788569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507757780125343049192379 8261636670188014573788569)
            ·
              refine ⟨6196227502641010930341427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261636670188014573788569 6196227502641010930341427)
              ·
                refine ⟨9294341253961516395512141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6196227502641010930341427 9294341253961516395512141)
                ·
                  refine ⟨3485377970235568648317053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294341253961516395512141 3485377970235568648317053)
                  ·
                    refine ⟨1307016738838338243118895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485377970235568648317053 1307016738838338243118895)
                    ·
                      rfl

theorem cell22_3818109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3818109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818109 prefixEnd_3818109 := by exact prefixLift 3818109
  have htrace : WordTrace (prefixWord ++ tailWord_3818109) baseStart_3818109 baseEnd_3818109 := by
    simpa [prefixWord, tailWord_3818109, baseEnd_3818109] using wordTrace_append hprefix tailTrace_3818109
  have hstable : (prefixWord ++ tailWord_3818109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818109).length < 2 ^ (prefixWord ++ tailWord_3818109).sum := by decide
  have hdescent : baseEnd_3818109 < baseStart_3818109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818216 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3818216 : Nat := 118140960795 + 3818216 * 2 ^ 59
def prefixEnd_3818216 : Nat := 4983230072969 + 3 ^ 40 * 3818216 * 2
def baseEnd_3818216 : Nat := 1307053367125025630693567

theorem tailTrace_3818216 : CollatzResearch.WordTrace tailWord_3818216 prefixEnd_3818216 1307053367125025630693567 := by
  unfold tailWord_3818216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69630889167631503110813251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92841185556842004147751001 69630889167631503110813251)
  ·
    refine ⟨104446333751447254666219877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69630889167631503110813251 104446333751447254666219877)
    ·
      refine ⟨19583687578396360249916227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104446333751447254666219877 19583687578396360249916227)
      ·
        refine ⟨29375531367594540374874341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19583687578396360249916227 29375531367594540374874341)
        ·
          refine ⟨5507912131423976320288939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29375531367594540374874341 5507912131423976320288939)
          ·
            refine ⟨8261868197135964480433409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5507912131423976320288939 8261868197135964480433409)
            ·
              refine ⟨6196401147851973360325057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8261868197135964480433409 6196401147851973360325057)
              ·
                refine ⟨4647300860888980020243793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196401147851973360325057 4647300860888980020243793)
                ·
                  refine ⟨3485475645666735015182845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647300860888980020243793 3485475645666735015182845)
                  ·
                    refine ⟨1307053367125025630693567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485475645666735015182845 1307053367125025630693567)
                    ·
                      rfl

theorem cell22_3818216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3818216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818216 prefixEnd_3818216 := by exact prefixLift 3818216
  have htrace : WordTrace (prefixWord ++ tailWord_3818216) baseStart_3818216 baseEnd_3818216 := by
    simpa [prefixWord, tailWord_3818216, baseEnd_3818216] using wordTrace_append hprefix tailTrace_3818216
  have hstable : (prefixWord ++ tailWord_3818216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818216).length < 2 ^ (prefixWord ++ tailWord_3818216).sum := by decide
  have hdescent : baseEnd_3818216 < baseStart_3818216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818225 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3818225 : Nat := 118140960795 + 3818225 * 2 ^ 59
def prefixEnd_3818225 : Nat := 4983230072969 + 3 ^ 40 * 3818225 * 2
def baseEnd_3818225 : Nat := 1307056448008952607218539

theorem tailTrace_3818225 : CollatzResearch.WordTrace tailWord_3818225 prefixEnd_3818225 1307056448008952607218539 := by
  unfold tailWord_3818225
  simp only [CollatzResearch.WordTrace]
  refine ⟨139262106592230400758704129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92841404394820267172469419 139262106592230400758704129)
  ·
    refine ⟨104446579944172800569028097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139262106592230400758704129 104446579944172800569028097)
    ·
      refine ⟨78334934958129600426771073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104446579944172800569028097 78334934958129600426771073)
      ·
        refine ⟨58751201218597200320078305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78334934958129600426771073 58751201218597200320078305)
        ·
          refine ⟨44063400913947900240058729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58751201218597200320078305 44063400913947900240058729)
          ·
            refine ⟨33047550685460925180044047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44063400913947900240058729 33047550685460925180044047)
            ·
              refine ⟨49571326028191387770066071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33047550685460925180044047 49571326028191387770066071)
              ·
                refine ⟨74356989042287081655099107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49571326028191387770066071 74356989042287081655099107)
                ·
                  refine ⟨111535483563430622482648661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74356989042287081655099107 111535483563430622482648661)
                  ·
                    refine ⟨1307056448008952607218539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111535483563430622482648661 1307056448008952607218539)
                    ·
                      rfl

theorem cell22_3818225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3818225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818225 prefixEnd_3818225 := by exact prefixLift 3818225
  have htrace : WordTrace (prefixWord ++ tailWord_3818225) baseStart_3818225 baseEnd_3818225 := by
    simpa [prefixWord, tailWord_3818225, baseEnd_3818225] using wordTrace_append hprefix tailTrace_3818225
  have hstable : (prefixWord ++ tailWord_3818225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818225).length < 2 ^ (prefixWord ++ tailWord_3818225).sum := by decide
  have hdescent : baseEnd_3818225 < baseStart_3818225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818227 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 3, 3]
def baseStart_3818227 : Nat := 118140960795 + 3818227 * 2 ^ 59
def prefixEnd_3818227 : Nat := 4983230072969 + 3 ^ 40 * 3818227 * 2
def baseEnd_3818227 : Nat := 1307057132649825268668533

theorem tailTrace_3818227 : CollatzResearch.WordTrace tailWord_3818227 prefixEnd_3818227 1307057132649825268668533 := by
  unfold tailWord_3818227
  simp only [CollatzResearch.WordTrace]
  refine ⟨139262179538223155100276935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92841453025482103400184623 139262179538223155100276935)
  ·
    refine ⟨208893269307334732650415403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139262179538223155100276935 208893269307334732650415403)
    ·
      refine ⟨313339903961002098975623105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208893269307334732650415403 313339903961002098975623105)
      ·
        refine ⟨235004927970751574231717329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313339903961002098975623105 235004927970751574231717329)
        ·
          refine ⟨176253695978063680673787997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235004927970751574231717329 176253695978063680673787997)
          ·
            refine ⟨66095135991773880252670499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176253695978063680673787997 66095135991773880252670499)
            ·
              refine ⟨99142703987660820379005749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66095135991773880252670499 99142703987660820379005749)
              ·
                refine ⟨9294628498843201910531789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99142703987660820379005749 9294628498843201910531789)
                ·
                  refine ⟨3485485687066200716449421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294628498843201910531789 3485485687066200716449421)
                  ·
                    refine ⟨1307057132649825268668533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485485687066200716449421 1307057132649825268668533)
                    ·
                      rfl

theorem cell22_3818227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 3, 3].length) (baseStart_3818227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818227 prefixEnd_3818227 := by exact prefixLift 3818227
  have htrace : WordTrace (prefixWord ++ tailWord_3818227) baseStart_3818227 baseEnd_3818227 := by
    simpa [prefixWord, tailWord_3818227, baseEnd_3818227] using wordTrace_append hprefix tailTrace_3818227
  have hstable : (prefixWord ++ tailWord_3818227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818227).length < 2 ^ (prefixWord ++ tailWord_3818227).sum := by decide
  have hdescent : baseEnd_3818227 < baseStart_3818227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818244 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3818244 : Nat := 118140960795 + 3818244 * 2 ^ 59
def prefixEnd_3818244 : Nat := 4983230072969 + 3 ^ 40 * 3818244 * 2
def baseEnd_3818244 : Nat := 1307062952097242890993481

theorem tailTrace_3818244 : CollatzResearch.WordTrace tailWord_3818244 prefixEnd_3818244 1307062952097242890993481 := by
  unfold tailWord_3818244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69631399789580783501822893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92841866386107711335763857 69631399789580783501822893)
  ·
    refine ⟨26111774921092793813183585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69631399789580783501822893 26111774921092793813183585)
    ·
      refine ⟨19583831190819595359887689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26111774921092793813183585 19583831190819595359887689)
      ·
        refine ⟨14687873393114696519915767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19583831190819595359887689 14687873393114696519915767)
        ·
          refine ⟨22031810089672044779873651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687873393114696519915767 22031810089672044779873651)
          ·
            refine ⟨33047715134508067169810477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22031810089672044779873651 33047715134508067169810477)
            ·
              refine ⟨12392893175440525188678929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33047715134508067169810477 12392893175440525188678929)
              ·
                refine ⟨9294669881580393891509197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12392893175440525188678929 9294669881580393891509197)
                ·
                  refine ⟨3485501205592647709315949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9294669881580393891509197 3485501205592647709315949)
                  ·
                    refine ⟨1307062952097242890993481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485501205592647709315949 1307062952097242890993481)
                    ·
                      rfl

theorem cell22_3818244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3818244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818244 prefixEnd_3818244 := by exact prefixLift 3818244
  have htrace : WordTrace (prefixWord ++ tailWord_3818244) baseStart_3818244 baseEnd_3818244 := by
    simpa [prefixWord, tailWord_3818244, baseEnd_3818244] using wordTrace_append hprefix tailTrace_3818244
  have hstable : (prefixWord ++ tailWord_3818244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818244).length < 2 ^ (prefixWord ++ tailWord_3818244).sum := by decide
  have hdescent : baseEnd_3818244 < baseStart_3818244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818255 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_3818255 : Nat := 118140960795 + 3818255 * 2 ^ 59
def prefixEnd_3818255 : Nat := 4983230072969 + 3 ^ 40 * 3818255 * 2
def baseEnd_3818255 : Nat := 1307066717622042528968447

theorem tailTrace_3818255 : CollatzResearch.WordTrace tailWord_3818255 prefixEnd_3818255 1307066717622042528968447 := by
  unfold tailWord_3818255
  simp only [CollatzResearch.WordTrace]
  refine ⟨139263200782121715882296219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92842133854747810588197479 139263200782121715882296219)
  ·
    refine ⟨208894801173182573823444329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139263200782121715882296219 208894801173182573823444329)
    ·
      refine ⟨156671100879886930367583247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208894801173182573823444329 156671100879886930367583247)
      ·
        refine ⟨235006651319830395551374871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156671100879886930367583247 235006651319830395551374871)
        ·
          refine ⟨352509976979745593327062307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235006651319830395551374871 352509976979745593327062307)
          ·
            refine ⟨528764965469618389990593461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352509976979745593327062307 528764965469618389990593461)
            ·
              refine ⟨49571715512776724061618137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 528764965469618389990593461 49571715512776724061618137)
              ·
                refine ⟨37178786634582543046213603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49571715512776724061618137 37178786634582543046213603)
                ·
                  refine ⟨55768179951873814569320405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37178786634582543046213603 55768179951873814569320405)
                  ·
                    refine ⟨1307066717622042528968447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55768179951873814569320405 1307066717622042528968447)
                    ·
                      rfl

theorem cell22_3818255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_3818255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818255 prefixEnd_3818255 := by exact prefixLift 3818255
  have htrace : WordTrace (prefixWord ++ tailWord_3818255) baseStart_3818255 baseEnd_3818255 := by
    simpa [prefixWord, tailWord_3818255, baseEnd_3818255] using wordTrace_append hprefix tailTrace_3818255
  have hstable : (prefixWord ++ tailWord_3818255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818255).length < 2 ^ (prefixWord ++ tailWord_3818255).sum := by decide
  have hdescent : baseEnd_3818255 < baseStart_3818255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818261 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 1, 3]
def baseStart_3818261 : Nat := 118140960795 + 3818261 * 2 ^ 59
def prefixEnd_3818261 : Nat := 4983230072969 + 3 ^ 40 * 3818261 * 2
def baseEnd_3818261 : Nat := 1307068771544660513318429

theorem tailTrace_3818261 : CollatzResearch.WordTrace tailWord_3818261 prefixEnd_3818261 1307068771544660513318429 := by
  unfold tailWord_3818261
  simp only [CollatzResearch.WordTrace]
  refine ⟨139263419620099978907014637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92842279746733319271343091 139263419620099978907014637)
  ·
    refine ⟨52223782357537492090130489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139263419620099978907014637 52223782357537492090130489)
    ·
      refine ⟨39167836768153119067597867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52223782357537492090130489 39167836768153119067597867)
      ·
        refine ⟨58751755152229678601396801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39167836768153119067597867 58751755152229678601396801)
        ·
          refine ⟨44063816364172258951047601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58751755152229678601396801 44063816364172258951047601)
          ·
            refine ⟨33047862273129194213285701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44063816364172258951047601 33047862273129194213285701)
            ·
              refine ⟨6196474176211723914991069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33047862273129194213285701 6196474176211723914991069)
              ·
                refine ⟨2323677816079396468121651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6196474176211723914991069 2323677816079396468121651)
                ·
                  refine ⟨3485516724119094702182477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323677816079396468121651 3485516724119094702182477)
                  ·
                    refine ⟨1307068771544660513318429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485516724119094702182477 1307068771544660513318429)
                    ·
                      rfl

theorem cell22_3818261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_3818261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818261 prefixEnd_3818261 := by exact prefixLift 3818261
  have htrace : WordTrace (prefixWord ++ tailWord_3818261) baseStart_3818261 baseEnd_3818261 := by
    simpa [prefixWord, tailWord_3818261, baseEnd_3818261] using wordTrace_append hprefix tailTrace_3818261
  have hstable : (prefixWord ++ tailWord_3818261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818261).length < 2 ^ (prefixWord ++ tailWord_3818261).sum := by decide
  have hdescent : baseEnd_3818261 < baseStart_3818261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818272 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_3818272 : Nat := 118140960795 + 3818272 * 2 ^ 59
def prefixEnd_3818272 : Nat := 4983230072969 + 3 ^ 40 * 3818272 * 2
def baseEnd_3818272 : Nat := 1307072537069460151293395

theorem tailTrace_3818272 : CollatzResearch.WordTrace tailWord_3818272 prefixEnd_3818272 1307072537069460151293395 := by
  unfold tailWord_3818272
  simp only [CollatzResearch.WordTrace]
  refine ⟨69631910411530063892832535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92842547215373418523776713 69631910411530063892832535)
  ·
    refine ⟨104447865617295095839248803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69631910411530063892832535 104447865617295095839248803)
    ·
      refine ⟨156671798425942643758873205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104447865617295095839248803 156671798425942643758873205)
      ·
        refine ⟨14687981102432122852394363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156671798425942643758873205 14687981102432122852394363)
        ·
          refine ⟨22031971653648184278591545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14687981102432122852394363 22031971653648184278591545)
          ·
            refine ⟨16523978740236138208943659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22031971653648184278591545 16523978740236138208943659)
            ·
              refine ⟨24785968110354207313415489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16523978740236138208943659 24785968110354207313415489)
              ·
                refine ⟨18589476082765655485061617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24785968110354207313415489 18589476082765655485061617)
                ·
                  refine ⟨13942107062074241613796213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18589476082765655485061617 13942107062074241613796213)
                  ·
                    refine ⟨1307072537069460151293395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13942107062074241613796213 1307072537069460151293395)
                    ·
                      rfl

theorem cell22_3818272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_3818272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818272 prefixEnd_3818272 := by exact prefixLift 3818272
  have htrace : WordTrace (prefixWord ++ tailWord_3818272) baseStart_3818272 baseEnd_3818272 := by
    simpa [prefixWord, tailWord_3818272, baseEnd_3818272] using wordTrace_append hprefix tailTrace_3818272
  have hstable : (prefixWord ++ tailWord_3818272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818272).length < 2 ^ (prefixWord ++ tailWord_3818272).sum := by decide
  have hdescent : baseEnd_3818272 < baseStart_3818272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818274 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3818274 : Nat := 118140960795 + 3818274 * 2 ^ 59
def prefixEnd_3818274 : Nat := 4983230072969 + 3 ^ 40 * 3818274 * 2
def baseEnd_3818274 : Nat := 435691073903444270914463

theorem tailTrace_3818274 : CollatzResearch.WordTrace tailWord_3818274 prefixEnd_3818274 435691073903444270914463 := by
  unfold tailWord_3818274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34815973442263220531809469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92842595846035254751491917 34815973442263220531809469)
  ·
    refine ⟨13055990040848707699428551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34815973442263220531809469 13055990040848707699428551)
    ·
      refine ⟨19583985061273061549142827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13055990040848707699428551 19583985061273061549142827)
      ·
        refine ⟨29375977591909592323714241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19583985061273061549142827 29375977591909592323714241)
        ·
          refine ⟨22031983193932194242785681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29375977591909592323714241 22031983193932194242785681)
          ·
            refine ⟨16523987395449145682089261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22031983193932194242785681 16523987395449145682089261)
            ·
              refine ⟨6196495273293429630783473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16523987395449145682089261 6196495273293429630783473)
              ·
                refine ⟨4647371454970072223087605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6196495273293429630783473 4647371454970072223087605)
                ·
                  refine ⟨435691073903444270914463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4647371454970072223087605 435691073903444270914463)
                  ·
                    rfl

theorem cell22_3818274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3818274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818274 prefixEnd_3818274 := by exact prefixLift 3818274
  have htrace : WordTrace (prefixWord ++ tailWord_3818274) baseStart_3818274 baseEnd_3818274 := by
    simpa [prefixWord, tailWord_3818274, baseEnd_3818274] using wordTrace_append hprefix tailTrace_3818274
  have hstable : (prefixWord ++ tailWord_3818274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818274).length < 2 ^ (prefixWord ++ tailWord_3818274).sum := by decide
  have hdescent : baseEnd_3818274 < baseStart_3818274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818336 : List Nat := [2, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_3818336 : Nat := 118140960795 + 3818336 * 2 ^ 59
def prefixEnd_3818336 : Nat := 4983230072969 + 3 ^ 40 * 3818336 * 2
def baseEnd_3818336 : Nat := 435698148525795105897733

theorem tailTrace_3818336 : CollatzResearch.WordTrace tailWord_3818336 prefixEnd_3818336 435698148525795105897733 := by
  unfold tailWord_3818336
  simp only [CollatzResearch.WordTrace]
  refine ⟨69633077547414133357997431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92844103396552177810663241 69633077547414133357997431)
  ·
    refine ⟨104449616321121200036996147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69633077547414133357997431 104449616321121200036996147)
    ·
      refine ⟨156674424481681800055494221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104449616321121200036996147 156674424481681800055494221)
      ·
        refine ⟨58752909180630675020810333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156674424481681800055494221 58752909180630675020810333)
        ·
          refine ⟨22032340942736503132803875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58752909180630675020810333 22032340942736503132803875)
          ·
            refine ⟨33048511414104754699205813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22032340942736503132803875 33048511414104754699205813)
            ·
              refine ⟨3098297945072320753050545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33048511414104754699205813 3098297945072320753050545)
              ·
                refine ⟨2323723458804240564787909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098297945072320753050545 2323723458804240564787909)
                ·
                  refine ⟨435698148525795105897733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323723458804240564787909 435698148525795105897733)
                  ·
                    rfl

theorem cell22_3818336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_3818336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818336 prefixEnd_3818336 := by exact prefixLift 3818336
  have htrace : WordTrace (prefixWord ++ tailWord_3818336) baseStart_3818336 baseEnd_3818336 := by
    simpa [prefixWord, tailWord_3818336, baseEnd_3818336] using wordTrace_append hprefix tailTrace_3818336
  have hstable : (prefixWord ++ tailWord_3818336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818336).length < 2 ^ (prefixWord ++ tailWord_3818336).sum := by decide
  have hdescent : baseEnd_3818336 < baseStart_3818336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818520 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 2, 3]
def baseStart_3818520 : Nat := 118140960795 + 3818520 * 2 ^ 59
def prefixEnd_3818520 : Nat := 4983230072969 + 3 ^ 40 * 3818520 * 2
def baseEnd_3818520 : Nat := 1307157432537670171092635

theorem tailTrace_3818520 : CollatzResearch.WordTrace tailWord_3818520 prefixEnd_3818520 1307157432537670171092635 := by
  unfold tailWord_3818520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69636433063080833070346507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92848577417441110760462009 69636433063080833070346507)
  ·
    refine ⟨104454649594621249605519761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69636433063080833070346507 104454649594621249605519761)
    ·
      refine ⟨78340987195965937204139821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104454649594621249605519761 78340987195965937204139821)
      ·
        refine ⟨29377870198487226451552433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78340987195965937204139821 29377870198487226451552433)
        ·
          refine ⟨22033402648865419838664325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29377870198487226451552433 22033402648865419838664325)
          ·
            refine ⟨4131262996662266219749561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22033402648865419838664325 4131262996662266219749561)
            ·
              refine ⟨3098447247496699664812171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131262996662266219749561 3098447247496699664812171)
              ·
                refine ⟨4647670871245049497218257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098447247496699664812171 4647670871245049497218257)
                ·
                  refine ⟨3485753153433787122913693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647670871245049497218257 3485753153433787122913693)
                  ·
                    refine ⟨1307157432537670171092635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485753153433787122913693 1307157432537670171092635)
                    ·
                      rfl

theorem cell22_3818520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_3818520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818520 prefixEnd_3818520 := by exact prefixLift 3818520
  have htrace : WordTrace (prefixWord ++ tailWord_3818520) baseStart_3818520 baseEnd_3818520 := by
    simpa [prefixWord, tailWord_3818520, baseEnd_3818520] using wordTrace_append hprefix tailTrace_3818520
  have hstable : (prefixWord ++ tailWord_3818520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818520).length < 2 ^ (prefixWord ++ tailWord_3818520).sum := by decide
  have hdescent : baseEnd_3818520 < baseStart_3818520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818559 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_3818559 : Nat := 118140960795 + 3818559 * 2 ^ 59
def prefixEnd_3818559 : Nat := 4983230072969 + 3 ^ 40 * 3818559 * 2
def baseEnd_3818559 : Nat := 1307170783034687069367515

theorem tailTrace_3818559 : CollatzResearch.WordTrace tailWord_3818559 prefixEnd_3818559 1307170783034687069367515 := by
  unfold tailWord_3818559
  simp only [CollatzResearch.WordTrace]
  refine ⟨139274288573020375801362731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92849525715346917200908487 139274288573020375801362731)
  ·
    refine ⟨208911432859530563702044097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139274288573020375801362731 208911432859530563702044097)
    ·
      refine ⟨156683574644647922776533073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208911432859530563702044097 156683574644647922776533073)
      ·
        refine ⟨117512680983485942082399805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156683574644647922776533073 117512680983485942082399805)
        ·
          refine ⟨44067255368807228280899927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117512680983485942082399805 44067255368807228280899927)
          ·
            refine ⟨66100883053210842421349891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44067255368807228280899927 66100883053210842421349891)
            ·
              refine ⟨99151324579816263632024837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66100883053210842421349891 99151324579816263632024837)
              ·
                refine ⟨18590873358715549431004657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99151324579816263632024837 18590873358715549431004657)
                ·
                  refine ⟨13943155019036662073253493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18590873358715549431004657 13943155019036662073253493)
                  ·
                    refine ⟨1307170783034687069367515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13943155019036662073253493 1307170783034687069367515)
                    ·
                      rfl

theorem cell22_3818559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_3818559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818559 prefixEnd_3818559 := by exact prefixLift 3818559
  have htrace : WordTrace (prefixWord ++ tailWord_3818559) baseStart_3818559 baseEnd_3818559 := by
    simpa [prefixWord, tailWord_3818559, baseEnd_3818559] using wordTrace_append hprefix tailTrace_3818559
  have hstable : (prefixWord ++ tailWord_3818559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818559).length < 2 ^ (prefixWord ++ tailWord_3818559).sum := by decide
  have hdescent : baseEnd_3818559 < baseStart_3818559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818565 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 1, 3]
def baseStart_3818565 : Nat := 118140960795 + 3818565 * 2 ^ 59
def prefixEnd_3818565 : Nat := 4983230072969 + 3 ^ 40 * 3818565 * 2
def baseEnd_3818565 : Nat := 1307172836957305053717497

theorem tailTrace_3818565 : CollatzResearch.WordTrace tailWord_3818565 prefixEnd_3818565 1307172836957305053717497 := by
  unfold tailWord_3818565
  simp only [CollatzResearch.WordTrace]
  refine ⟨139274507410998638826081149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92849671607332425884054099 139274507410998638826081149)
  ·
    refine ⟨52227940279124489559780431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139274507410998638826081149 52227940279124489559780431)
    ·
      refine ⟨78341910418686734339670647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52227940279124489559780431 78341910418686734339670647)
      ·
        refine ⟨117512865628030101509505971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78341910418686734339670647 117512865628030101509505971)
        ·
          refine ⟨176269298442045152264258957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117512865628030101509505971 176269298442045152264258957)
          ·
            refine ⟨66100986915766932099097109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176269298442045152264258957 66100986915766932099097109)
            ·
              refine ⟨3098483761676574942145177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66100986915766932099097109 3098483761676574942145177)
              ·
                refine ⟨2323862821257431206608883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3098483761676574942145177 2323862821257431206608883)
                ·
                  refine ⟨3485794231886146809913325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2323862821257431206608883 3485794231886146809913325)
                  ·
                    refine ⟨1307172836957305053717497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485794231886146809913325 1307172836957305053717497)
                    ·
                      rfl

theorem cell22_3818565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 1, 3].length) (baseStart_3818565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818565 prefixEnd_3818565 := by exact prefixLift 3818565
  have htrace : WordTrace (prefixWord ++ tailWord_3818565) baseStart_3818565 baseEnd_3818565 := by
    simpa [prefixWord, tailWord_3818565, baseEnd_3818565] using wordTrace_append hprefix tailTrace_3818565
  have hstable : (prefixWord ++ tailWord_3818565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818565).length < 2 ^ (prefixWord ++ tailWord_3818565).sum := by decide
  have hdescent : baseEnd_3818565 < baseStart_3818565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818582 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3818582 : Nat := 118140960795 + 3818582 * 2 ^ 59
def prefixEnd_3818582 : Nat := 4983230072969 + 3 ^ 40 * 3818582 * 2
def baseEnd_3818582 : Nat := 1307178656404722676042445

theorem tailTrace_3818582 : CollatzResearch.WordTrace tailWord_3818582 prefixEnd_3818582 1307178656404722676042445 := by
  unfold tailWord_3818582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8704695465746065670590625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92850084967958033819633333 8704695465746065670590625)
  ·
    refine ⟨6528521599309549252942969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8704695465746065670590625 6528521599309549252942969)
    ·
      refine ⟨4896391199482161939707227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6528521599309549252942969 4896391199482161939707227)
      ·
        refine ⟨7344586799223242909560841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896391199482161939707227 7344586799223242909560841)
        ·
          refine ⟨5508440099417432182170631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7344586799223242909560841 5508440099417432182170631)
          ·
            refine ⟨8262660149126148273255947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5508440099417432182170631 8262660149126148273255947)
            ·
              refine ⟨12393990223689222409883921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8262660149126148273255947 12393990223689222409883921)
              ·
                refine ⟨9295492667766916807412941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12393990223689222409883921 9295492667766916807412941)
                ·
                  refine ⟨3485809750412593802779853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9295492667766916807412941 3485809750412593802779853)
                  ·
                    refine ⟨1307178656404722676042445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485809750412593802779853 1307178656404722676042445)
                    ·
                      rfl

theorem cell22_3818582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3818582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818582 prefixEnd_3818582 := by exact prefixLift 3818582
  have htrace : WordTrace (prefixWord ++ tailWord_3818582) baseStart_3818582 baseEnd_3818582 := by
    simpa [prefixWord, tailWord_3818582, baseEnd_3818582] using wordTrace_append hprefix tailTrace_3818582
  have hstable : (prefixWord ++ tailWord_3818582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818582).length < 2 ^ (prefixWord ++ tailWord_3818582).sum := by decide
  have hdescent : baseEnd_3818582 < baseStart_3818582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818591 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 1, 4]
def baseStart_3818591 : Nat := 118140960795 + 3818591 * 2 ^ 59
def prefixEnd_3818591 : Nat := 4983230072969 + 3 ^ 40 * 3818591 * 2
def baseEnd_3818591 : Nat := 1307181737288649652567417

theorem tailTrace_3818591 : CollatzResearch.WordTrace tailWord_3818591 prefixEnd_3818591 1307181737288649652567417 := by
  unfold tailWord_3818591
  simp only [CollatzResearch.WordTrace]
  refine ⟨139275455708904445266527627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92850303805936296844351751 139275455708904445266527627)
  ·
    refine ⟨208913183563356667899791441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139275455708904445266527627 208913183563356667899791441)
    ·
      refine ⟨156684887672517500924843581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208913183563356667899791441 156684887672517500924843581)
      ·
        refine ⟨58756832877194062846816343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156684887672517500924843581 58756832877194062846816343)
        ·
          refine ⟨88135249315791094270224515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58756832877194062846816343 88135249315791094270224515)
          ·
            refine ⟨132202873973686641405336773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88135249315791094270224515 132202873973686641405336773)
            ·
              refine ⟨24788038870066245263500645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132202873973686641405336773 24788038870066245263500645)
              ·
                refine ⟨4647757288137420986906371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24788038870066245263500645 4647757288137420986906371)
                ·
                  refine ⟨6971635932206131480359557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4647757288137420986906371 6971635932206131480359557)
                  ·
                    refine ⟨1307181737288649652567417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6971635932206131480359557 1307181737288649652567417)
                    ·
                      rfl

theorem cell22_3818591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_3818591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818591 prefixEnd_3818591 := by exact prefixLift 3818591
  have htrace : WordTrace (prefixWord ++ tailWord_3818591) baseStart_3818591 baseEnd_3818591 := by
    simpa [prefixWord, tailWord_3818591, baseEnd_3818591] using wordTrace_append hprefix tailTrace_3818591
  have hstable : (prefixWord ++ tailWord_3818591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818591).length < 2 ^ (prefixWord ++ tailWord_3818591).sum := by decide
  have hdescent : baseEnd_3818591 < baseStart_3818591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818638 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_3818638 : Nat := 118140960795 + 3818638 * 2 ^ 59
def prefixEnd_3818638 : Nat := 4983230072969 + 3 ^ 40 * 3818638 * 2
def baseEnd_3818638 : Nat := 1307197826349157196642273

theorem tailTrace_3818638 : CollatzResearch.WordTrace tailWord_3818638 prefixEnd_3818638 1307197826349157196642273 := by
  unfold tailWord_3818638
  simp only [CollatzResearch.WordTrace]
  refine ⟨17409646242466771536686071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92851446626489448195659045 17409646242466771536686071)
  ·
    refine ⟨26114469363700157305029107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17409646242466771536686071 26114469363700157305029107)
    ·
      refine ⟨39171704045550235957543661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26114469363700157305029107 39171704045550235957543661)
      ·
        refine ⟨14689389017081338484078873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39171704045550235957543661 14689389017081338484078873)
        ·
          refine ⟨11017041762811003863059155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14689389017081338484078873 11017041762811003863059155)
          ·
            refine ⟨16525562644216505794588733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017041762811003863059155 16525562644216505794588733)
            ·
              refine ⟨6197085991581189672970775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16525562644216505794588733 6197085991581189672970775)
              ·
                refine ⟨9295628987371784509456163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197085991581189672970775 9295628987371784509456163)
                ·
                  refine ⟨13943443481057676764184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9295628987371784509456163 13943443481057676764184245)
                  ·
                    refine ⟨1307197826349157196642273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13943443481057676764184245 1307197826349157196642273)
                    ·
                      rfl

theorem cell22_3818638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_3818638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818638 prefixEnd_3818638 := by exact prefixLift 3818638
  have htrace : WordTrace (prefixWord ++ tailWord_3818638) baseStart_3818638 baseEnd_3818638 := by
    simpa [prefixWord, tailWord_3818638, baseEnd_3818638] using wordTrace_append hprefix tailTrace_3818638
  have hstable : (prefixWord ++ tailWord_3818638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818638).length < 2 ^ (prefixWord ++ tailWord_3818638).sum := by decide
  have hdescent : baseEnd_3818638 < baseStart_3818638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818689 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 2, 3]
def baseStart_3818689 : Nat := 118140960795 + 3818689 * 2 ^ 59
def prefixEnd_3818689 : Nat := 4983230072969 + 3 ^ 40 * 3818689 * 2
def baseEnd_3818689 : Nat := 1307215284691410063617117

theorem tailTrace_3818689 : CollatzResearch.WordTrace tailWord_3818689 prefixEnd_3818689 1307215284691410063617117 := by
  unfold tailWord_3818689
  simp only [CollatzResearch.WordTrace]
  refine ⟨139279030062549408003595121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92852686708366272002396747 139279030062549408003595121)
  ·
    refine ⟨104459272546912056002696341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139279030062549408003595121 104459272546912056002696341)
    ·
      refine ⟨4896528400636502625126391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 104459272546912056002696341 4896528400636502625126391)
      ·
        refine ⟨7344792600954753937689587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896528400636502625126391 7344792600954753937689587)
        ·
          refine ⟨11017188901432130906534381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7344792600954753937689587 11017188901432130906534381)
          ·
            refine ⟨4131445838037049089950393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11017188901432130906534381 4131445838037049089950393)
            ·
              refine ⟨3098584378527786817462795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131445838037049089950393 3098584378527786817462795)
              ·
                refine ⟨4647876567791680226194193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098584378527786817462795 4647876567791680226194193)
                ·
                  refine ⟨3485907425843760169645645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4647876567791680226194193 3485907425843760169645645)
                  ·
                    refine ⟨1307215284691410063617117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485907425843760169645645 1307215284691410063617117)
                    ·
                      rfl

theorem cell22_3818689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_3818689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818689 prefixEnd_3818689 := by exact prefixLift 3818689
  have htrace : WordTrace (prefixWord ++ tailWord_3818689) baseStart_3818689 baseEnd_3818689 := by
    simpa [prefixWord, tailWord_3818689, baseEnd_3818689] using wordTrace_append hprefix tailTrace_3818689
  have hstable : (prefixWord ++ tailWord_3818689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818689).length < 2 ^ (prefixWord ++ tailWord_3818689).sum := by decide
  have hdescent : baseEnd_3818689 < baseStart_3818689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818773 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 4, 3]
def baseStart_3818773 : Nat := 118140960795 + 3818773 * 2 ^ 59
def prefixEnd_3818773 : Nat := 4983230072969 + 3 ^ 40 * 3818773 * 2
def baseEnd_3818773 : Nat := 1307244039608061844516859

theorem tailTrace_3818773 : CollatzResearch.WordTrace tailWord_3818773 prefixEnd_3818773 1307244039608061844516859 := by
  unfold tailWord_3818773
  simp only [CollatzResearch.WordTrace]
  refine ⟨139282093794245090349652973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92854729196163393566435315 139282093794245090349652973)
  ·
    refine ⟨52230785172841908881119865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139282093794245090349652973 52230785172841908881119865)
    ·
      refine ⟨39173088879631431660839899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52230785172841908881119865 39173088879631431660839899)
      ·
        refine ⟨58759633319447147491259849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39173088879631431660839899 58759633319447147491259849)
        ·
          refine ⟨44069724989585360618444887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58759633319447147491259849 44069724989585360618444887)
          ·
            refine ⟨66104587484378040927667331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44069724989585360618444887 66104587484378040927667331)
            ·
              refine ⟨99156881226567061391500997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66104587484378040927667331 99156881226567061391500997)
              ·
                refine ⟨18591915229981324010906437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99156881226567061391500997 18591915229981324010906437)
                ·
                  refine ⟨3485984105621498252044957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18591915229981324010906437 3485984105621498252044957)
                  ·
                    refine ⟨1307244039608061844516859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3485984105621498252044957 1307244039608061844516859)
                    ·
                      rfl

theorem cell22_3818773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 4, 3].length) (baseStart_3818773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818773 prefixEnd_3818773 := by exact prefixLift 3818773
  have htrace : WordTrace (prefixWord ++ tailWord_3818773) baseStart_3818773 baseEnd_3818773 := by
    simpa [prefixWord, tailWord_3818773, baseEnd_3818773] using wordTrace_append hprefix tailTrace_3818773
  have hstable : (prefixWord ++ tailWord_3818773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818773).length < 2 ^ (prefixWord ++ tailWord_3818773).sum := by decide
  have hdescent : baseEnd_3818773 < baseStart_3818773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818775 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 4]
def baseStart_3818775 : Nat := 118140960795 + 3818775 * 2 ^ 59
def prefixEnd_3818775 : Nat := 4983230072969 + 3 ^ 40 * 3818775 * 2
def baseEnd_3818775 : Nat := 435748241416311501988951

theorem tailTrace_3818775 : CollatzResearch.WordTrace tailWord_3818775 prefixEnd_3818775 435748241416311501988951 := by
  unfold tailWord_3818775
  simp only [CollatzResearch.WordTrace]
  refine ⟨139282166740237844691225779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92854777826825229794150519 139282166740237844691225779)
  ·
    refine ⟨208923250110356767036838669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139282166740237844691225779 208923250110356767036838669)
    ·
      refine ⟨78346218791383787638814501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 208923250110356767036838669 78346218791383787638814501)
      ·
        refine ⟨14689916023384460182277719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78346218791383787638814501 14689916023384460182277719)
        ·
          refine ⟨22034874035076690273416579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689916023384460182277719 22034874035076690273416579)
          ·
            refine ⟨33052311052615035410124869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22034874035076690273416579 33052311052615035410124869)
            ·
              refine ⟨6197308322365319139398413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33052311052615035410124869 6197308322365319139398413)
              ·
                refine ⟨2323990620886994677274405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6197308322365319139398413 2323990620886994677274405)
                ·
                  refine ⟨435748241416311501988951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2323990620886994677274405 435748241416311501988951)
                  ·
                    rfl

theorem cell22_3818775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 4].length) (baseStart_3818775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818775 prefixEnd_3818775 := by exact prefixLift 3818775
  have htrace : WordTrace (prefixWord ++ tailWord_3818775) baseStart_3818775 baseEnd_3818775 := by
    simpa [prefixWord, tailWord_3818775, baseEnd_3818775] using wordTrace_append hprefix tailTrace_3818775
  have hstable : (prefixWord ++ tailWord_3818775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818775).length < 2 ^ (prefixWord ++ tailWord_3818775).sum := by decide
  have hdescent : baseEnd_3818775 < baseStart_3818775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818788 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_3818788 : Nat := 118140960795 + 3818788 * 2 ^ 59
def prefixEnd_3818788 : Nat := 4983230072969 + 3 ^ 40 * 3818788 * 2
def baseEnd_3818788 : Nat := 1307249174414606805391813

theorem tailTrace_3818788 : CollatzResearch.WordTrace tailWord_3818788 prefixEnd_3818788 1307249174414606805391813 := by
  unfold tailWord_3818788
  simp only [CollatzResearch.WordTrace]
  refine ⟨69641320444595373955724509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92855093926127165274299345 69641320444595373955724509)
  ·
    refine ⟨26115495166723265233396691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69641320444595373955724509 26115495166723265233396691)
    ·
      refine ⟨39173242750084897850095037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26115495166723265233396691 39173242750084897850095037)
      ·
        refine ⟨14689966031281836693785639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39173242750084897850095037 14689966031281836693785639)
        ·
          refine ⟨22034949046922755040678459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14689966031281836693785639 22034949046922755040678459)
          ·
            refine ⟨33052423570384132561017689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22034949046922755040678459 33052423570384132561017689)
            ·
              refine ⟨24789317677788099420763267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33052423570384132561017689 24789317677788099420763267)
              ·
                refine ⟨37183976516682149131144901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24789317677788099420763267 37183976516682149131144901)
                ·
                  refine ⟨6971995596877902962089669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37183976516682149131144901 6971995596877902962089669)
                  ·
                    refine ⟨1307249174414606805391813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6971995596877902962089669 1307249174414606805391813)
                    ·
                      rfl

theorem cell22_3818788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_3818788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818788 prefixEnd_3818788 := by exact prefixLift 3818788
  have htrace : WordTrace (prefixWord ++ tailWord_3818788) baseStart_3818788 baseEnd_3818788 := by
    simpa [prefixWord, tailWord_3818788, baseEnd_3818788] using wordTrace_append hprefix tailTrace_3818788
  have hstable : (prefixWord ++ tailWord_3818788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818788).length < 2 ^ (prefixWord ++ tailWord_3818788).sum := by decide
  have hdescent : baseEnd_3818788 < baseStart_3818788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818820 : List Nat := [2, 3, 4, 1, 1, 2, 1, 8]
def baseStart_3818820 : Nat := 118140960795 + 3818820 * 2 ^ 59
def prefixEnd_3818820 : Nat := 4983230072969 + 3 ^ 40 * 3818820 * 2
def baseEnd_3818820 : Nat := 145251125407618820954635

theorem tailTrace_3818820 : CollatzResearch.WordTrace tailWord_3818820 prefixEnd_3818820 145251125407618820954635 := by
  unfold tailWord_3818820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69641904012537408688306957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92855872016716544917742609 69641904012537408688306957)
  ·
    refine ⟨26115714004701528258115109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69641904012537408688306957 26115714004701528258115109)
    ·
      refine ⟨4896696375881536548396583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26115714004701528258115109 4896696375881536548396583)
      ·
        refine ⟨7345044563822304822594875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4896696375881536548396583 7345044563822304822594875)
        ·
          refine ⟨11017566845733457233892313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7345044563822304822594875 11017566845733457233892313)
          ·
            refine ⟨8263175134300092925419235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11017566845733457233892313 8263175134300092925419235)
            ·
              refine ⟨12394762701450139388128853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8263175134300092925419235 12394762701450139388128853)
              ·
                refine ⟨145251125407618820954635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12394762701450139388128853 145251125407618820954635)
                ·
                  rfl

theorem cell22_3818820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_3818820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818820 prefixEnd_3818820 := by exact prefixLift 3818820
  have htrace : WordTrace (prefixWord ++ tailWord_3818820) baseStart_3818820 baseEnd_3818820 := by
    simpa [prefixWord, tailWord_3818820, baseEnd_3818820] using wordTrace_append hprefix tailTrace_3818820
  have hstable : (prefixWord ++ tailWord_3818820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818820).length < 2 ^ (prefixWord ++ tailWord_3818820).sum := by decide
  have hdescent : baseEnd_3818820 < baseStart_3818820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818848 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_3818848 : Nat := 118140960795 + 3818848 * 2 ^ 59
def prefixEnd_3818848 : Nat := 4983230072969 + 3 ^ 40 * 3818848 * 2
def baseEnd_3818848 : Nat := 435756571213595549630543

theorem tailTrace_3818848 : CollatzResearch.WordTrace tailWord_3818848 prefixEnd_3818848 435756571213595549630543 := by
  unfold tailWord_3818848
  simp only [CollatzResearch.WordTrace]
  refine ⟨69642414634486689079316599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92856552845982252105755465 69642414634486689079316599)
  ·
    refine ⟨104463621951730033618974899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69642414634486689079316599 104463621951730033618974899)
    ·
      refine ⟨156695432927595050428462349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104463621951730033618974899 156695432927595050428462349)
      ·
        refine ⟨58760787347848143910673381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156695432927595050428462349 58760787347848143910673381)
        ·
          refine ⟨11017647627721526983251259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58760787347848143910673381 11017647627721526983251259)
          ·
            refine ⟨16526471441582290474876889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11017647627721526983251259 16526471441582290474876889)
            ·
              refine ⟨12394853581186717856157667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16526471441582290474876889 12394853581186717856157667)
              ·
                refine ⟨18592280371780076784236501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12394853581186717856157667 18592280371780076784236501)
                ·
                  refine ⟨435756571213595549630543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18592280371780076784236501 435756571213595549630543)
                  ·
                    rfl

theorem cell22_3818848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_3818848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818848 prefixEnd_3818848 := by exact prefixLift 3818848
  have htrace : WordTrace (prefixWord ++ tailWord_3818848) baseStart_3818848 baseEnd_3818848 := by
    simpa [prefixWord, tailWord_3818848, baseEnd_3818848] using wordTrace_append hprefix tailTrace_3818848
  have hstable : (prefixWord ++ tailWord_3818848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818848).length < 2 ^ (prefixWord ++ tailWord_3818848).sum := by decide
  have hdescent : baseEnd_3818848 < baseStart_3818848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818852 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 3, 3]
def baseStart_3818852 : Nat := 118140960795 + 3818852 * 2 ^ 59
def prefixEnd_3818852 : Nat := 4983230072969 + 3 ^ 40 * 3818852 * 2
def baseEnd_3818852 : Nat := 1307271082922531971791617

theorem tailTrace_3818852 : CollatzResearch.WordTrace tailWord_3818852 prefixEnd_3818852 1307271082922531971791617 := by
  unfold tailWord_3818852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69642487580479443420889405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92856650107305924561185873 69642487580479443420889405)
  ·
    refine ⟨26115932842679791282833527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69642487580479443420889405 26115932842679791282833527)
    ·
      refine ⟨39173899264019686924250291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26115932842679791282833527 39173899264019686924250291)
      ·
        refine ⟨58760848896029530386375437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39173899264019686924250291 58760848896029530386375437)
        ·
          refine ⟨22035318336011073894890789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58760848896029530386375437 22035318336011073894890789)
          ·
            refine ⟨4131622188002076355292023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22035318336011073894890789 4131622188002076355292023)
            ·
              refine ⟨6197433282003114532938035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131622188002076355292023 6197433282003114532938035)
              ·
                refine ⟨9296149923004671799407053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197433282003114532938035 9296149923004671799407053)
                ·
                  refine ⟨3486056221126751924777645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9296149923004671799407053 3486056221126751924777645)
                  ·
                    refine ⟨1307271082922531971791617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486056221126751924777645 1307271082922531971791617)
                    ·
                      rfl

theorem cell22_3818852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 3, 3].length) (baseStart_3818852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818852 prefixEnd_3818852 := by exact prefixLift 3818852
  have htrace : WordTrace (prefixWord ++ tailWord_3818852) baseStart_3818852 baseEnd_3818852 := by
    simpa [prefixWord, tailWord_3818852, baseEnd_3818852] using wordTrace_append hprefix tailTrace_3818852
  have hstable : (prefixWord ++ tailWord_3818852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818852).length < 2 ^ (prefixWord ++ tailWord_3818852).sum := by decide
  have hdescent : baseEnd_3818852 < baseStart_3818852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818865 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 5]
def baseStart_3818865 : Nat := 118140960795 + 3818865 * 2 ^ 59
def prefixEnd_3818865 : Nat := 4983230072969 + 3 ^ 40 * 3818865 * 2
def baseEnd_3818865 : Nat := 435758511029401423738859

theorem tailTrace_3818865 : CollatzResearch.WordTrace tailWord_3818865 prefixEnd_3818865 435758511029401423738859 := by
  unfold tailWord_3818865
  simp only [CollatzResearch.WordTrace]
  refine ⟨139285449309911790062002049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92856966206607860041334699 139285449309911790062002049)
  ·
    refine ⟨104464086982433842546501537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139285449309911790062002049 104464086982433842546501537)
    ·
      refine ⟨78348065236825381909876153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104464086982433842546501537 78348065236825381909876153)
      ·
        refine ⟨58761048927619036432407115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78348065236825381909876153 58761048927619036432407115)
        ·
          refine ⟨88141573391428554648610673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58761048927619036432407115 88141573391428554648610673)
          ·
            refine ⟨66106180043571415986458005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88141573391428554648610673 66106180043571415986458005)
            ·
              refine ⟨3098727189542410124365219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66106180043571415986458005 3098727189542410124365219)
              ·
                refine ⟨4648090784313615186547829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098727189542410124365219 4648090784313615186547829)
                ·
                  refine ⟨435758511029401423738859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648090784313615186547829 435758511029401423738859)
                  ·
                    rfl

theorem cell22_3818865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_3818865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818865 prefixEnd_3818865 := by exact prefixLift 3818865
  have htrace : WordTrace (prefixWord ++ tailWord_3818865) baseStart_3818865 baseEnd_3818865 := by
    simpa [prefixWord, tailWord_3818865, baseEnd_3818865] using wordTrace_append hprefix tailTrace_3818865
  have hstable : (prefixWord ++ tailWord_3818865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818865).length < 2 ^ (prefixWord ++ tailWord_3818865).sum := by decide
  have hdescent : baseEnd_3818865 < baseStart_3818865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818968 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_3818968 : Nat := 118140960795 + 3818968 * 2 ^ 59
def prefixEnd_3818968 : Nat := 4983230072969 + 3 ^ 40 * 3818968 * 2
def baseEnd_3818968 : Nat := 1307310792093146335891261

theorem tailTrace_3818968 : CollatzResearch.WordTrace tailWord_3818968 prefixEnd_3818968 1307310792093146335891261 := by
  unfold tailWord_3818968
  simp only [CollatzResearch.WordTrace]
  refine ⟨69644603014269319326500779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92859470685692425768667705 69644603014269319326500779)
  ·
    refine ⟨104466904521403978989751169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69644603014269319326500779 104466904521403978989751169)
    ·
      refine ⟨78350178391052984242313377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104466904521403978989751169 78350178391052984242313377)
      ·
        refine ⟨58762633793289738181735033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78350178391052984242313377 58762633793289738181735033)
        ·
          refine ⟨44071975344967303636301275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58762633793289738181735033 44071975344967303636301275)
          ·
            refine ⟨66107963017450955454451913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44071975344967303636301275 66107963017450955454451913)
            ·
              refine ⟨49580972263088216590838935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66107963017450955454451913 49580972263088216590838935)
              ·
                refine ⟨74371458394632324886258403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49580972263088216590838935 74371458394632324886258403)
                ·
                  refine ⟨111557187591948487329387605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74371458394632324886258403 111557187591948487329387605)
                  ·
                    refine ⟨1307310792093146335891261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 111557187591948487329387605 1307310792093146335891261)
                    ·
                      rfl

theorem cell22_3818968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_3818968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818968 prefixEnd_3818968 := by exact prefixLift 3818968
  have htrace : WordTrace (prefixWord ++ tailWord_3818968) baseStart_3818968 baseEnd_3818968 := by
    simpa [prefixWord, tailWord_3818968, baseEnd_3818968] using wordTrace_append hprefix tailTrace_3818968
  have hstable : (prefixWord ++ tailWord_3818968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818968).length < 2 ^ (prefixWord ++ tailWord_3818968).sum := by decide
  have hdescent : baseEnd_3818968 < baseStart_3818968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3818989 : List Nat := [1, 5, 1, 3, 2, 2, 2, 6]
def baseStart_3818989 : Nat := 118140960795 + 3818989 * 2 ^ 59
def prefixEnd_3818989 : Nat := 4983230072969 + 3 ^ 40 * 3818989 * 2
def baseEnd_3818989 : Nat := 145257553424701031235133

theorem tailTrace_3818989 : CollatzResearch.WordTrace tailWord_3818989 prefixEnd_3818989 145257553424701031235133 := by
  unfold tailWord_3818989
  simp only [CollatzResearch.WordTrace]
  refine ⟨139289971961462559239516021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92859981307641706159677347 139289971961462559239516021)
  ·
    refine ⟨13058434871387114928704627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139289971961462559239516021 13058434871387114928704627)
    ·
      refine ⟨19587652307080672393056941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13058434871387114928704627 19587652307080672393056941)
      ·
        refine ⟨7345369615155252147396353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19587652307080672393056941 7345369615155252147396353)
        ·
          refine ⟨5509027211366439110547265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7345369615155252147396353 5509027211366439110547265)
          ·
            refine ⟨4131770408524829332910449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5509027211366439110547265 4131770408524829332910449)
            ·
              refine ⟨3098827806393621999682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4131770408524829332910449 3098827806393621999682837)
              ·
                refine ⟨145257553424701031235133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3098827806393621999682837 145257553424701031235133)
                ·
                  rfl

theorem cell22_3818989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 6].length) (baseStart_3818989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3818989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3818989 prefixEnd_3818989 := by exact prefixLift 3818989
  have htrace : WordTrace (prefixWord ++ tailWord_3818989) baseStart_3818989 baseEnd_3818989 := by
    simpa [prefixWord, tailWord_3818989, baseEnd_3818989] using wordTrace_append hprefix tailTrace_3818989
  have hstable : (prefixWord ++ tailWord_3818989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3818989).length < 2 ^ (prefixWord ++ tailWord_3818989).sum := by decide
  have hdescent : baseEnd_3818989 < baseStart_3818989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3818989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819004 : List Nat := [2, 2, 2, 1, 2, 1, 5, 3, 1, 3]
def baseStart_3819004 : Nat := 118140960795 + 3819004 * 2 ^ 59
def prefixEnd_3819004 : Nat := 4983230072969 + 3 ^ 40 * 3819004 * 2
def baseEnd_3819004 : Nat := 1307323115628854241991151

theorem tailTrace_3819004 : CollatzResearch.WordTrace tailWord_3819004 prefixEnd_3819004 1307323115628854241991151 := by
  unfold tailWord_3819004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69645259528204108400656033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92860346037605477867541377 69645259528204108400656033)
  ·
    refine ⟨52233944646153081300492025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69645259528204108400656033 52233944646153081300492025)
    ·
      refine ⟨39175458484614810975369019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52233944646153081300492025 39175458484614810975369019)
      ·
        refine ⟨58763187726922216463053529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39175458484614810975369019 58763187726922216463053529)
        ·
          refine ⟨44072390795191662347290147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58763187726922216463053529 44072390795191662347290147)
          ·
            refine ⟨66108586192787493520935221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44072390795191662347290147 66108586192787493520935221)
            ·
              refine ⟨6197679955573827517587677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66108586192787493520935221 6197679955573827517587677)
              ·
                refine ⟨2324129983340185319095379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6197679955573827517587677 2324129983340185319095379)
                ·
                  refine ⟨3486194975010277978643069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324129983340185319095379 3486194975010277978643069)
                  ·
                    refine ⟨1307323115628854241991151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486194975010277978643069 1307323115628854241991151)
                    ·
                      rfl

theorem cell22_3819004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_3819004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819004 prefixEnd_3819004 := by exact prefixLift 3819004
  have htrace : WordTrace (prefixWord ++ tailWord_3819004) baseStart_3819004 baseEnd_3819004 := by
    simpa [prefixWord, tailWord_3819004, baseEnd_3819004] using wordTrace_append hprefix tailTrace_3819004
  have hstable : (prefixWord ++ tailWord_3819004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819004).length < 2 ^ (prefixWord ++ tailWord_3819004).sum := by decide
  have hdescent : baseEnd_3819004 < baseStart_3819004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819064 : List Nat := [2, 1, 2, 1, 4, 3, 3, 1, 1, 4]
def baseStart_3819064 : Nat := 118140960795 + 3819064 * 2 ^ 59
def prefixEnd_3819064 : Nat := 4983230072969 + 3 ^ 40 * 3819064 * 2
def baseEnd_3819064 : Nat := 1307343654855034085490967

theorem tailTrace_3819064 : CollatzResearch.WordTrace tailWord_3819064 prefixEnd_3819064 1307343654855034085490967 := by
  unfold tailWord_3819064
  simp only [CollatzResearch.WordTrace]
  refine ⟨69646353718095423524248123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92861804957460564698997497 69646353718095423524248123)
  ·
    refine ⟨104469530577143135286372185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69646353718095423524248123 104469530577143135286372185)
    ·
      refine ⟨78352147932857351464779139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104469530577143135286372185 78352147932857351464779139)
      ·
        refine ⟨117528221899286027197168709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78352147932857351464779139 117528221899286027197168709)
        ·
          refine ⟨22036541606116130099469133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117528221899286027197168709 22036541606116130099469133)
          ·
            refine ⟨8263703102293548787300925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22036541606116130099469133 8263703102293548787300925)
            ·
              refine ⟨3098888663360080795237847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8263703102293548787300925 3098888663360080795237847)
              ·
                refine ⟨4648332995040121192856771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3098888663360080795237847 4648332995040121192856771)
                ·
                  refine ⟨6972499492560181789285157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648332995040121192856771 6972499492560181789285157)
                  ·
                    refine ⟨1307343654855034085490967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972499492560181789285157 1307343654855034085490967)
                    ·
                      rfl

theorem cell22_3819064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 1, 1, 4].length) (baseStart_3819064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819064 prefixEnd_3819064 := by exact prefixLift 3819064
  have htrace : WordTrace (prefixWord ++ tailWord_3819064) baseStart_3819064 baseEnd_3819064 := by
    simpa [prefixWord, tailWord_3819064, baseEnd_3819064] using wordTrace_append hprefix tailTrace_3819064
  have hstable : (prefixWord ++ tailWord_3819064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819064).length < 2 ^ (prefixWord ++ tailWord_3819064).sum := by decide
  have hdescent : baseEnd_3819064 < baseStart_3819064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819079 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 4]
def baseStart_3819079 : Nat := 118140960795 + 3819079 * 2 ^ 59
def prefixEnd_3819079 : Nat := 4983230072969 + 3 ^ 40 * 3819079 * 2
def baseEnd_3819079 : Nat := 435782929887193015455307

theorem tailTrace_3819079 : CollatzResearch.WordTrace tailWord_3819079 prefixEnd_3819079 435782929887193015455307 := by
  unfold tailWord_3819079
  simp only [CollatzResearch.WordTrace]
  refine ⟨139293254531136504610292291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92862169687424336406861527 139293254531136504610292291)
  ·
    refine ⟨208939881796704756915438437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139293254531136504610292291 208939881796704756915438437)
    ·
      refine ⟨39176227836882141921644707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 208939881796704756915438437 39176227836882141921644707)
      ·
        refine ⟨58764341755323212882467061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39176227836882141921644707 58764341755323212882467061)
        ·
          refine ⟨5509157039561551207731287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58764341755323212882467061 5509157039561551207731287)
          ·
            refine ⟨8263735559342326811596931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5509157039561551207731287 8263735559342326811596931)
            ·
              refine ⟨12395603339013490217395397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8263735559342326811596931 12395603339013490217395397)
              ·
                refine ⟨2324175626065029415761637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12395603339013490217395397 2324175626065029415761637)
                ·
                  refine ⟨435782929887193015455307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2324175626065029415761637 435782929887193015455307)
                  ·
                    rfl

theorem cell22_3819079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 4].length) (baseStart_3819079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819079 prefixEnd_3819079 := by exact prefixLift 3819079
  have htrace : WordTrace (prefixWord ++ tailWord_3819079) baseStart_3819079 baseEnd_3819079 := by
    simpa [prefixWord, tailWord_3819079, baseEnd_3819079] using wordTrace_append hprefix tailTrace_3819079
  have hstable : (prefixWord ++ tailWord_3819079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819079).length < 2 ^ (prefixWord ++ tailWord_3819079).sum := by decide
  have hdescent : baseEnd_3819079 < baseStart_3819079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819107 : List Nat := [1, 1, 1, 5, 1, 4, 3, 6]
def baseStart_3819107 : Nat := 118140960795 + 3819107 * 2 ^ 59
def prefixEnd_3819107 : Nat := 4983230072969 + 3 ^ 40 * 3819107 * 2
def baseEnd_3819107 : Nat := 145262041625977367407315

theorem tailTrace_3819107 : CollatzResearch.WordTrace tailWord_3819107 prefixEnd_3819107 145262041625977367407315 := by
  unfold tailWord_3819107
  simp only [CollatzResearch.WordTrace]
  refine ⟨139294275775035065392311575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92862850516690043594874383 139294275775035065392311575)
  ·
    refine ⟨208941413662552598088467363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139294275775035065392311575 208941413662552598088467363)
    ·
      refine ⟨313412120493828897132701045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208941413662552598088467363 313412120493828897132701045)
      ·
        refine ⟨29382386296296459106190723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 313412120493828897132701045 29382386296296459106190723)
        ·
          refine ⟨44073579444444688659286085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29382386296296459106190723 44073579444444688659286085)
          ·
            refine ⟨8263796145833379123616141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44073579444444688659286085 8263796145833379123616141)
            ·
              refine ⟨3098923554687517171356053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8263796145833379123616141 3098923554687517171356053)
              ·
                refine ⟨145262041625977367407315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3098923554687517171356053 145262041625977367407315)
                ·
                  rfl

theorem cell22_3819107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 6].length) (baseStart_3819107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819107 prefixEnd_3819107 := by exact prefixLift 3819107
  have htrace : WordTrace (prefixWord ++ tailWord_3819107) baseStart_3819107 baseEnd_3819107 := by
    simpa [prefixWord, tailWord_3819107, baseEnd_3819107] using wordTrace_append hprefix tailTrace_3819107
  have hstable : (prefixWord ++ tailWord_3819107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819107).length < 2 ^ (prefixWord ++ tailWord_3819107).sum := by decide
  have hdescent : baseEnd_3819107 < baseStart_3819107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819109 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 2, 4]
def baseStart_3819109 : Nat := 118140960795 + 3819109 * 2 ^ 59
def prefixEnd_3819109 : Nat := 4983230072969 + 3 ^ 40 * 3819109 * 2
def baseEnd_3819109 : Nat := 1307359059274668968115829

theorem tailTrace_3819109 : CollatzResearch.WordTrace tailWord_3819109 prefixEnd_3819109 1307359059274668968115829 := by
  unfold tailWord_3819109
  simp only [CollatzResearch.WordTrace]
  refine ⟨139294348721027819733884381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92862899147351879822589587 139294348721027819733884381)
  ·
    refine ⟨52235380770385432400206643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139294348721027819733884381 52235380770385432400206643)
    ·
      refine ⟨78353071155578148600309965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52235380770385432400206643 78353071155578148600309965)
      ·
        refine ⟨29382401683341805725116237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78353071155578148600309965 29382401683341805725116237)
        ·
          refine ⟨11018400631253177146918589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29382401683341805725116237 11018400631253177146918589)
          ·
            refine ⟨4131900236719941430094471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11018400631253177146918589 4131900236719941430094471)
            ·
              refine ⟨6197850355079912145141707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4131900236719941430094471 6197850355079912145141707)
              ·
                refine ⟨9296775532619868217712561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6197850355079912145141707 9296775532619868217712561)
                ·
                  refine ⟨6972581649464901163284421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9296775532619868217712561 6972581649464901163284421)
                  ·
                    refine ⟨1307359059274668968115829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972581649464901163284421 1307359059274668968115829)
                    ·
                      rfl

theorem cell22_3819109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 2, 4].length) (baseStart_3819109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819109 prefixEnd_3819109 := by exact prefixLift 3819109
  have htrace : WordTrace (prefixWord ++ tailWord_3819109) baseStart_3819109 baseEnd_3819109 := by
    simpa [prefixWord, tailWord_3819109, baseEnd_3819109] using wordTrace_append hprefix tailTrace_3819109
  have hstable : (prefixWord ++ tailWord_3819109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819109).length < 2 ^ (prefixWord ++ tailWord_3819109).sum := by decide
  have hdescent : baseEnd_3819109 < baseStart_3819109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819246 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_3819246 : Nat := 118140960795 + 3819246 * 2 ^ 59
def prefixEnd_3819246 : Nat := 4983230072969 + 3 ^ 40 * 3819246 * 2
def baseEnd_3819246 : Nat := 1307405957174446277440409

theorem tailTrace_3819246 : CollatzResearch.WordTrace tailWord_3819246 prefixEnd_3819246 1307405957174446277440409 := by
  unfold tailWord_3819246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17412418190191436516452699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92866230347687661421081061 17412418190191436516452699)
  ·
    refine ⟨26118627285287154774679049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17412418190191436516452699 26118627285287154774679049)
    ·
      refine ⟨19588970463965366081009287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26118627285287154774679049 19588970463965366081009287)
      ·
        refine ⟨29383455695948049121513931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19588970463965366081009287 29383455695948049121513931)
        ·
          refine ⟨44075183543922073682270897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29383455695948049121513931 44075183543922073682270897)
          ·
            refine ⟨33056387657941555261703173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44075183543922073682270897 33056387657941555261703173)
            ·
              refine ⟨6198072685864041611569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33056387657941555261703173 6198072685864041611569345)
              ·
                refine ⟨4648554514398031208677009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6198072685864041611569345 4648554514398031208677009)
                ·
                  refine ⟨3486415885798523406507757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4648554514398031208677009 3486415885798523406507757)
                  ·
                    refine ⟨1307405957174446277440409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486415885798523406507757 1307405957174446277440409)
                    ·
                      rfl

theorem cell22_3819246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_3819246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819246 prefixEnd_3819246 := by exact prefixLift 3819246
  have htrace : WordTrace (prefixWord ++ tailWord_3819246) baseStart_3819246 baseEnd_3819246 := by
    simpa [prefixWord, tailWord_3819246, baseEnd_3819246] using wordTrace_append hprefix tailTrace_3819246
  have hstable : (prefixWord ++ tailWord_3819246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819246).length < 2 ^ (prefixWord ++ tailWord_3819246).sum := by decide
  have hdescent : baseEnd_3819246 < baseStart_3819246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819272 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3819272 : Nat := 118140960795 + 3819272 * 2 ^ 59
def prefixEnd_3819272 : Nat := 4983230072969 + 3 ^ 40 * 3819272 * 2
def baseEnd_3819272 : Nat := 1307414857505790876290329

theorem tailTrace_3819272 : CollatzResearch.WordTrace tailWord_3819272 prefixEnd_3819272 1307414857505790876290329 := by
  unfold tailWord_3819272
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650146909718649286034035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92866862546291532381378713 69650146909718649286034035)
  ·
    refine ⟨104475220364577973929051053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69650146909718649286034035 104475220364577973929051053)
    ·
      refine ⟨39178207636716740223394145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104475220364577973929051053 39178207636716740223394145)
      ·
        refine ⟨29383655727537555167545609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39178207636716740223394145 29383655727537555167545609)
        ·
          refine ⟨22037741795653166375659207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29383655727537555167545609 22037741795653166375659207)
          ·
            refine ⟨33056612693479749563488811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22037741795653166375659207 33056612693479749563488811)
            ·
              refine ⟨49584919040219624345233217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33056612693479749563488811 49584919040219624345233217)
              ·
                refine ⟨37188689280164718258924913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49584919040219624345233217 37188689280164718258924913)
                ·
                  refine ⟨27891516960123538694193685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37188689280164718258924913 27891516960123538694193685)
                  ·
                    refine ⟨1307414857505790876290329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27891516960123538694193685 1307414857505790876290329)
                    ·
                      rfl

theorem cell22_3819272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3819272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819272 prefixEnd_3819272 := by exact prefixLift 3819272
  have htrace : WordTrace (prefixWord ++ tailWord_3819272) baseStart_3819272 baseEnd_3819272 := by
    simpa [prefixWord, tailWord_3819272, baseEnd_3819272] using wordTrace_append hprefix tailTrace_3819272
  have hstable : (prefixWord ++ tailWord_3819272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819272).length < 2 ^ (prefixWord ++ tailWord_3819272).sum := by decide
  have hdescent : baseEnd_3819272 < baseStart_3819272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819274 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 5, 3]
def baseStart_3819274 : Nat := 118140960795 + 3819274 * 2 ^ 59
def prefixEnd_3819274 : Nat := 4983230072969 + 3 ^ 40 * 3819274 * 2
def baseEnd_3819274 : Nat := 1307415542146663537740323

theorem tailTrace_3819274 : CollatzResearch.WordTrace tailWord_3819274 prefixEnd_3819274 1307415542146663537740323 := by
  unfold tailWord_3819274
  simp only [CollatzResearch.WordTrace]
  refine ⟨34825091691357513228410219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92866911176953368609093917 34825091691357513228410219)
  ·
    refine ⟨52237637537036269842615329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34825091691357513228410219 52237637537036269842615329)
    ·
      refine ⟨39178228152777202381961497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52237637537036269842615329 39178228152777202381961497)
      ·
        refine ⟨29383671114582901786471123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39178228152777202381961497 29383671114582901786471123)
        ·
          refine ⟨44075506671874352679706685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29383671114582901786471123 44075506671874352679706685)
          ·
            refine ⟨16528315001952882254890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44075506671874352679706685 16528315001952882254890007)
            ·
              refine ⟨24792472502929323382335011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16528315001952882254890007 24792472502929323382335011)
              ·
                refine ⟨37188708754393985073502517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24792472502929323382335011 37188708754393985073502517)
                ·
                  refine ⟨3486441445724436100640861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37188708754393985073502517 3486441445724436100640861)
                  ·
                    refine ⟨1307415542146663537740323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486441445724436100640861 1307415542146663537740323)
                    ·
                      rfl

theorem cell22_3819274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_3819274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819274 prefixEnd_3819274 := by exact prefixLift 3819274
  have htrace : WordTrace (prefixWord ++ tailWord_3819274) baseStart_3819274 baseEnd_3819274 := by
    simpa [prefixWord, tailWord_3819274, baseEnd_3819274] using wordTrace_append hprefix tailTrace_3819274
  have hstable : (prefixWord ++ tailWord_3819274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819274).length < 2 ^ (prefixWord ++ tailWord_3819274).sum := by decide
  have hdescent : baseEnd_3819274 < baseStart_3819274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819284 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3819284 : Nat := 118140960795 + 3819284 * 2 ^ 59
def prefixEnd_3819284 : Nat := 4983230072969 + 3 ^ 40 * 3819284 * 2
def baseEnd_3819284 : Nat := 1307418965351026844990293

theorem tailTrace_3819284 : CollatzResearch.WordTrace tailWord_3819284 prefixEnd_3819284 1307418965351026844990293 := by
  unfold tailWord_3819284
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650365747696912310752453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92867154330262549747669937 69650365747696912310752453)
  ·
    refine ⟨13059443577693171058266085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69650365747696912310752453 13059443577693171058266085)
    ·
      refine ⟨2448645670817469573424891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13059443577693171058266085 2448645670817469573424891)
      ·
        refine ⟨3672968506226204360137337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2448645670817469573424891 3672968506226204360137337)
        ·
          refine ⟨2754726379669653270103003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3672968506226204360137337 2754726379669653270103003)
          ·
            refine ⟨4132089569504479905154505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2754726379669653270103003 4132089569504479905154505)
            ·
              refine ⟨3099067177128359928865879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132089569504479905154505 3099067177128359928865879)
              ·
                refine ⟨4648600765692539893298819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099067177128359928865879 4648600765692539893298819)
                ·
                  refine ⟨6972901148538809839948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4648600765692539893298819 6972901148538809839948229)
                  ·
                    refine ⟨1307418965351026844990293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6972901148538809839948229 1307418965351026844990293)
                    ·
                      rfl

theorem cell22_3819284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3819284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819284 prefixEnd_3819284 := by exact prefixLift 3819284
  have htrace : WordTrace (prefixWord ++ tailWord_3819284) baseStart_3819284 baseEnd_3819284 := by
    simpa [prefixWord, tailWord_3819284, baseEnd_3819284] using wordTrace_append hprefix tailTrace_3819284
  have hstable : (prefixWord ++ tailWord_3819284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819284).length < 2 ^ (prefixWord ++ tailWord_3819284).sum := by decide
  have hdescent : baseEnd_3819284 < baseStart_3819284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819304 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_3819304 : Nat := 118140960795 + 3819304 * 2 ^ 59
def prefixEnd_3819304 : Nat := 4983230072969 + 3 ^ 40 * 3819304 * 2
def baseEnd_3819304 : Nat := 435808603919917819830077

theorem tailTrace_3819304 : CollatzResearch.WordTrace tailWord_3819304 prefixEnd_3819304 435808603919917819830077 := by
  unfold tailWord_3819304
  simp only [CollatzResearch.WordTrace]
  refine ⟨69650730477660684018616483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92867640636880912024821977 69650730477660684018616483)
  ·
    refine ⟨104476095716491026027924725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69650730477660684018616483 104476095716491026027924725)
    ·
      refine ⟨9794633973421033690117943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104476095716491026027924725 9794633973421033690117943)
      ·
        refine ⟨14691950960131550535176915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9794633973421033690117943 14691950960131550535176915)
        ·
          refine ⟨22037926440197325802765373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14691950960131550535176915 22037926440197325802765373)
          ·
            refine ⟨8264222415073997176037015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22037926440197325802765373 8264222415073997176037015)
            ·
              refine ⟨12396333622610995764055523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8264222415073997176037015 12396333622610995764055523)
              ·
                refine ⟨18594500433916493646083285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12396333622610995764055523 18594500433916493646083285)
                ·
                  refine ⟨435808603919917819830077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18594500433916493646083285 435808603919917819830077)
                  ·
                    rfl

theorem cell22_3819304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_3819304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819304 prefixEnd_3819304 := by exact prefixLift 3819304
  have htrace : WordTrace (prefixWord ++ tailWord_3819304) baseStart_3819304 baseEnd_3819304 := by
    simpa [prefixWord, tailWord_3819304, baseEnd_3819304] using wordTrace_append hprefix tailTrace_3819304
  have hstable : (prefixWord ++ tailWord_3819304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819304).length < 2 ^ (prefixWord ++ tailWord_3819304).sum := by decide
  have hdescent : baseEnd_3819304 < baseStart_3819304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819439 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 5]
def baseStart_3819439 : Nat := 118140960795 + 3819439 * 2 ^ 59
def prefixEnd_3819439 : Nat := 4983230072969 + 3 ^ 40 * 3819439 * 2
def baseEnd_3819439 : Nat := 435824008339552702454939

theorem tailTrace_3819439 : CollatzResearch.WordTrace tailWord_3819439 prefixEnd_3819439 435824008339552702454939 := by
  unfold tailWord_3819439
  simp only [CollatzResearch.WordTrace]
  refine ⟨139306384809832286093397371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92870923206554857395598247 139306384809832286093397371)
  ·
    refine ⟨208959577214748429140096057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139306384809832286093397371 208959577214748429140096057)
    ·
      refine ⟨156719682911061321855072043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208959577214748429140096057 156719682911061321855072043)
      ·
        refine ⟨235079524366591982782608065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156719682911061321855072043 235079524366591982782608065)
        ·
          refine ⟨176309643274943987086956049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235079524366591982782608065 176309643274943987086956049)
          ·
            refine ⟨132232232456207990315217037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176309643274943987086956049 132232232456207990315217037)
            ·
              refine ⟨49587087171077996368206389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132232232456207990315217037 49587087171077996368206389)
              ·
                refine ⟨4648789422288562159519349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49587087171077996368206389 4648789422288562159519349)
                ·
                  refine ⟨435824008339552702454939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4648789422288562159519349 435824008339552702454939)
                  ·
                    rfl

theorem cell22_3819439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 5].length) (baseStart_3819439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819439 prefixEnd_3819439 := by exact prefixLift 3819439
  have htrace : WordTrace (prefixWord ++ tailWord_3819439) baseStart_3819439 baseEnd_3819439 := by
    simpa [prefixWord, tailWord_3819439, baseEnd_3819439] using wordTrace_append hprefix tailTrace_3819439
  have hstable : (prefixWord ++ tailWord_3819439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819439).length < 2 ^ (prefixWord ++ tailWord_3819439).sum := by decide
  have hdescent : baseEnd_3819439 < baseStart_3819439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819516 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 6, 3]
def baseStart_3819516 : Nat := 118140960795 + 3819516 * 2 ^ 59
def prefixEnd_3819516 : Nat := 4983230072969 + 3 ^ 40 * 3819516 * 2
def baseEnd_3819516 : Nat := 1307498383692255573189581

theorem tailTrace_3819516 : CollatzResearch.WordTrace tailWord_3819516 prefixEnd_3819516 1307498383692255573189581 := by
  unfold tailWord_3819516
  simp only [CollatzResearch.WordTrace]
  refine ⟨69654596615276664121975201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92872795487035552162633601 69654596615276664121975201)
  ·
    refine ⟨52240947461457498091481401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69654596615276664121975201 52240947461457498091481401)
    ·
      refine ⟨39180710596093123568611051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52240947461457498091481401 39180710596093123568611051)
      ·
        refine ⟨58771065894139685352916577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39180710596093123568611051 58771065894139685352916577)
        ·
          refine ⟨44078299420604764014687433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58771065894139685352916577 44078299420604764014687433)
          ·
            refine ⟨33058724565453573011015575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44078299420604764014687433 33058724565453573011015575)
            ·
              refine ⟨49588086848180359516523363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33058724565453573011015575 49588086848180359516523363)
              ·
                refine ⟨74382130272270539274785045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49588086848180359516523363 74382130272270539274785045)
                ·
                  refine ⟨3486662356512681528505549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74382130272270539274785045 3486662356512681528505549)
                  ·
                    refine ⟨1307498383692255573189581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3486662356512681528505549 1307498383692255573189581)
                    ·
                      rfl

theorem cell22_3819516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3819516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819516 prefixEnd_3819516 := by exact prefixLift 3819516
  have htrace : WordTrace (prefixWord ++ tailWord_3819516) baseStart_3819516 baseEnd_3819516 := by
    simpa [prefixWord, tailWord_3819516, baseEnd_3819516] using wordTrace_append hprefix tailTrace_3819516
  have hstable : (prefixWord ++ tailWord_3819516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819516).length < 2 ^ (prefixWord ++ tailWord_3819516).sum := by decide
  have hdescent : baseEnd_3819516 < baseStart_3819516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819531 : List Nat := [1, 1, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_3819531 : Nat := 118140960795 + 3819531 * 2 ^ 59
def prefixEnd_3819531 : Nat := 4983230072969 + 3 ^ 40 * 3819531 * 2
def baseEnd_3819531 : Nat := 1307503518498800534064535

theorem tailTrace_3819531 : CollatzResearch.WordTrace tailWord_3819531 prefixEnd_3819531 1307503518498800534064535 := by
  unfold tailWord_3819531
  simp only [CollatzResearch.WordTrace]
  refine ⟨139309740325498985805746447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92873160216999323870497631 139309740325498985805746447)
  ·
    refine ⟨208964610488248478708619671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139309740325498985805746447 208964610488248478708619671)
    ·
      refine ⟨313446915732372718062929507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208964610488248478708619671 313446915732372718062929507)
      ·
        refine ⟨470170373598559077094394261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313446915732372718062929507 470170373598559077094394261)
        ·
          refine ⟨22039236262432456738799731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 470170373598559077094394261 22039236262432456738799731)
          ·
            refine ⟨33058854393648685108199597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22039236262432456738799731 33058854393648685108199597)
            ·
              refine ⟨12397070397618256915574849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33058854393648685108199597 12397070397618256915574849)
              ·
                refine ⟨9297802798213692686681137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397070397618256915574849 9297802798213692686681137)
                ·
                  refine ⟨6973352098660269515010853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9297802798213692686681137 6973352098660269515010853)
                  ·
                    refine ⟨1307503518498800534064535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973352098660269515010853 1307503518498800534064535)
                    ·
                      rfl

theorem cell22_3819531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_3819531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819531 prefixEnd_3819531 := by exact prefixLift 3819531
  have htrace : WordTrace (prefixWord ++ tailWord_3819531) baseStart_3819531 baseEnd_3819531 := by
    simpa [prefixWord, tailWord_3819531, baseEnd_3819531] using wordTrace_append hprefix tailTrace_3819531
  have hstable : (prefixWord ++ tailWord_3819531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819531).length < 2 ^ (prefixWord ++ tailWord_3819531).sum := by decide
  have hdescent : baseEnd_3819531 < baseStart_3819531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819546 : List Nat := [3, 1, 1, 3, 1, 4, 2, 7]
def baseStart_3819546 : Nat := 118140960795 + 3819546 * 2 ^ 59
def prefixEnd_3819546 : Nat := 4983230072969 + 3 ^ 40 * 3819546 * 2
def baseEnd_3819546 : Nat := 145278739256149499437721

theorem tailTrace_3819546 : CollatzResearch.WordTrace tailWord_3819546 prefixEnd_3819546 145278739256149499437721 := by
  unfold tailWord_3819546
  simp only [CollatzResearch.WordTrace]
  refine ⟨34827571855111160841885623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92873524946963095578361661 34827571855111160841885623)
  ·
    refine ⟨52241357782666741262828435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34827571855111160841885623 52241357782666741262828435)
    ·
      refine ⟨78362036674000111894242653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52241357782666741262828435 78362036674000111894242653)
      ·
        refine ⟨29385763752750041960340995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78362036674000111894242653 29385763752750041960340995)
        ·
          refine ⟨44078645629125062940511493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29385763752750041960340995 44078645629125062940511493)
          ·
            refine ⟨8264746055460949301345905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44078645629125062940511493 8264746055460949301345905)
            ·
              refine ⟨6198559541595711976009429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264746055460949301345905 6198559541595711976009429)
              ·
                refine ⟨145278739256149499437721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6198559541595711976009429 145278739256149499437721)
                ·
                  rfl

theorem cell22_3819546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_3819546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819546 prefixEnd_3819546 := by exact prefixLift 3819546
  have htrace : WordTrace (prefixWord ++ tailWord_3819546) baseStart_3819546 baseEnd_3819546 := by
    simpa [prefixWord, tailWord_3819546, baseEnd_3819546] using wordTrace_append hprefix tailTrace_3819546
  have hstable : (prefixWord ++ tailWord_3819546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819546).length < 2 ^ (prefixWord ++ tailWord_3819546).sum := by decide
  have hdescent : baseEnd_3819546 < baseStart_3819546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819653 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 6]
def baseStart_3819653 : Nat := 118140960795 + 3819653 * 2 ^ 59
def prefixEnd_3819653 : Nat := 4983230072969 + 3 ^ 40 * 3819653 * 2
def baseEnd_3819653 : Nat := 435848427197344294171387

theorem tailTrace_3819653 : CollatzResearch.WordTrace tailWord_3819653 prefixEnd_3819653 435848427197344294171387 := by
  unfold tailWord_3819653
  simp only [CollatzResearch.WordTrace]
  refine ⟨139314190031057000641687613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92876126687371333761125075 139314190031057000641687613)
  ·
    refine ⟨52242821261646375240632855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139314190031057000641687613 52242821261646375240632855)
    ·
      refine ⟨78364231892469562860949283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52242821261646375240632855 78364231892469562860949283)
      ·
        refine ⟨117546347838704344291423925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78364231892469562860949283 117546347838704344291423925)
        ·
          refine ⟨11019970109878532277320993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117546347838704344291423925 11019970109878532277320993)
          ·
            refine ⟨8264977582408899207990745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11019970109878532277320993 8264977582408899207990745)
            ·
              refine ⟨6198733186806674405993059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8264977582408899207990745 6198733186806674405993059)
              ·
                refine ⟨9298099780210011608989589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6198733186806674405993059 9298099780210011608989589)
                ·
                  refine ⟨435848427197344294171387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9298099780210011608989589 435848427197344294171387)
                  ·
                    rfl

theorem cell22_3819653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_3819653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819653 prefixEnd_3819653 := by exact prefixLift 3819653
  have htrace : WordTrace (prefixWord ++ tailWord_3819653) baseStart_3819653 baseEnd_3819653 := by
    simpa [prefixWord, tailWord_3819653, baseEnd_3819653] using wordTrace_append hprefix tailTrace_3819653
  have hstable : (prefixWord ++ tailWord_3819653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819653).length < 2 ^ (prefixWord ++ tailWord_3819653).sum := by decide
  have hdescent : baseEnd_3819653 < baseStart_3819653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819711 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_3819711 : Nat := 118140960795 + 3819711 * 2 ^ 59
def prefixEnd_3819711 : Nat := 4983230072969 + 3 ^ 40 * 3819711 * 2
def baseEnd_3819711 : Nat := 1307565136177340064563983

theorem tailTrace_3819711 : CollatzResearch.WordTrace tailWord_3819711 prefixEnd_3819711 1307565136177340064563983 := by
  unfold tailWord_3819711
  simp only [CollatzResearch.WordTrace]
  refine ⟨139316305464846876547298987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92877536976564584364865991 139316305464846876547298987)
  ·
    refine ⟨208974458197270314820948481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139316305464846876547298987 208974458197270314820948481)
    ·
      refine ⟨156730843647952736115711361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208974458197270314820948481 156730843647952736115711361)
      ·
        refine ⟨117548132735964552086783521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156730843647952736115711361 117548132735964552086783521)
        ·
          refine ⟨88161099551973414065087641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117548132735964552086783521 88161099551973414065087641)
          ·
            refine ⟨66120824663980060548815731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88161099551973414065087641 66120824663980060548815731)
            ·
              refine ⟨99181236995970090823223597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66120824663980060548815731 99181236995970090823223597)
              ·
                refine ⟨37192963873488784058708849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99181236995970090823223597 37192963873488784058708849)
                ·
                  refine ⟨27894722905116588044031637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37192963873488784058708849 27894722905116588044031637)
                  ·
                    refine ⟨1307565136177340064563983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27894722905116588044031637 1307565136177340064563983)
                    ·
                      rfl

theorem cell22_3819711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_3819711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819711 prefixEnd_3819711 := by exact prefixLift 3819711
  have htrace : WordTrace (prefixWord ++ tailWord_3819711) baseStart_3819711 baseEnd_3819711 := by
    simpa [prefixWord, tailWord_3819711, baseEnd_3819711] using wordTrace_append hprefix tailTrace_3819711
  have hstable : (prefixWord ++ tailWord_3819711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819711).length < 2 ^ (prefixWord ++ tailWord_3819711).sum := by decide
  have hdescent : baseEnd_3819711 < baseStart_3819711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819758 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3819758 : Nat := 118140960795 + 3819758 * 2 ^ 59
def prefixEnd_3819758 : Nat := 4983230072969 + 3 ^ 40 * 3819758 * 2
def baseEnd_3819758 : Nat := 1307581225237847608638839

theorem tailTrace_3819758 : CollatzResearch.WordTrace tailWord_3819758 prefixEnd_3819758 1307581225237847608638839 := by
  unfold tailWord_3819758
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414752461959575446782491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92878679797117735716173285 17414752461959575446782491)
  ·
    refine ⟨26122128692939363170173737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17414752461959575446782491 26122128692939363170173737)
    ·
      refine ⟨19591596519704522377630303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26122128692939363170173737 19591596519704522377630303)
      ·
        refine ⟨29387394779556783566445455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19591596519704522377630303 29387394779556783566445455)
        ·
          refine ⟨44081092169335175349668183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387394779556783566445455 44081092169335175349668183)
          ·
            refine ⟨66121638254002763024502275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44081092169335175349668183 66121638254002763024502275)
            ·
              refine ⟨99182457381004144536753413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66121638254002763024502275 99182457381004144536753413)
              ·
                refine ⟨18596710758938277100641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99182457381004144536753413 18596710758938277100641265)
                ·
                  refine ⟨13947533069203707825480949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18596710758938277100641265 13947533069203707825480949)
                  ·
                    refine ⟨1307581225237847608638839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13947533069203707825480949 1307581225237847608638839)
                    ·
                      rfl

theorem cell22_3819758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3819758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819758 prefixEnd_3819758 := by exact prefixLift 3819758
  have htrace : WordTrace (prefixWord ++ tailWord_3819758) baseStart_3819758 baseEnd_3819758 := by
    simpa [prefixWord, tailWord_3819758, baseEnd_3819758] using wordTrace_append hprefix tailTrace_3819758
  have hstable : (prefixWord ++ tailWord_3819758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819758).length < 2 ^ (prefixWord ++ tailWord_3819758).sum := by decide
  have hdescent : baseEnd_3819758 < baseStart_3819758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819771 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 12]
def baseStart_3819771 : Nat := 118140960795 + 3819771 * 2 ^ 59
def prefixEnd_3819771 : Nat := 4983230072969 + 3 ^ 40 * 3819771 * 2
def baseEnd_3819771 : Nat := 435861891801173302687933

theorem tailTrace_3819771 : CollatzResearch.WordTrace tailWord_3819771 prefixEnd_3819771 435861891801173302687933 := by
  unfold tailWord_3819771
  simp only [CollatzResearch.WordTrace]
  refine ⟨139318493844629506794483167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92878995896419671196322111 139318493844629506794483167)
  ·
    refine ⟨208977740766944260191724751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139318493844629506794483167 208977740766944260191724751)
    ·
      refine ⟨313466611150416390287587127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208977740766944260191724751 313466611150416390287587127)
      ·
        refine ⟨470199916725624585431380691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313466611150416390287587127 470199916725624585431380691)
        ·
          refine ⟨705299875088436878147071037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470199916725624585431380691 705299875088436878147071037)
          ·
            refine ⟨264487453158163829305151639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705299875088436878147071037 264487453158163829305151639)
            ·
              refine ⟨396731179737245743957727459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264487453158163829305151639 396731179737245743957727459)
              ·
                refine ⟨595096769605868615936591189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 396731179737245743957727459 595096769605868615936591189)
                ·
                  refine ⟨435861891801173302687933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 595096769605868615936591189 435861891801173302687933)
                  ·
                    rfl

theorem cell22_3819771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_3819771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819771 prefixEnd_3819771 := by exact prefixLift 3819771
  have htrace : WordTrace (prefixWord ++ tailWord_3819771) baseStart_3819771 baseEnd_3819771 := by
    simpa [prefixWord, tailWord_3819771, baseEnd_3819771] using wordTrace_append hprefix tailTrace_3819771
  have hstable : (prefixWord ++ tailWord_3819771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819771).length < 2 ^ (prefixWord ++ tailWord_3819771).sum := by decide
  have hdescent : baseEnd_3819771 < baseStart_3819771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819788 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_3819788 : Nat := 118140960795 + 3819788 * 2 ^ 59
def prefixEnd_3819788 : Nat := 4983230072969 + 3 ^ 40 * 3819788 * 2
def baseEnd_3819788 : Nat := 435863831616979176796249

theorem tailTrace_3819788 : CollatzResearch.WordTrace tailWord_3819788 prefixEnd_3819788 435863831616979176796249 := by
  unfold tailWord_3819788
  simp only [CollatzResearch.WordTrace]
  refine ⟨69659556942783959348926009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92879409257045279131901345 69659556942783959348926009)
  ·
    refine ⟨52244667707087969511694507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69659556942783959348926009 52244667707087969511694507)
    ·
      refine ⟨78367001560631954267541761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52244667707087969511694507 78367001560631954267541761)
      ·
        refine ⟨58775251170473965700656321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78367001560631954267541761 58775251170473965700656321)
        ·
          refine ⟨44081438377855474275492241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58775251170473965700656321 44081438377855474275492241)
          ·
            refine ⟨33061078783391605706619181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44081438377855474275492241 33061078783391605706619181)
            ·
              refine ⟨12397904543771852139982193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33061078783391605706619181 12397904543771852139982193)
              ·
                refine ⟨9298428407828889104986645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397904543771852139982193 9298428407828889104986645)
                ·
                  refine ⟨435863831616979176796249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9298428407828889104986645 435863831616979176796249)
                  ·
                    rfl

theorem cell22_3819788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_3819788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819788 prefixEnd_3819788 := by exact prefixLift 3819788
  have htrace : WordTrace (prefixWord ++ tailWord_3819788) baseStart_3819788 baseEnd_3819788 := by
    simpa [prefixWord, tailWord_3819788, baseEnd_3819788] using wordTrace_append hprefix tailTrace_3819788
  have hstable : (prefixWord ++ tailWord_3819788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819788).length < 2 ^ (prefixWord ++ tailWord_3819788).sum := by decide
  have hdescent : baseEnd_3819788 < baseStart_3819788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819790 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_3819790 : Nat := 118140960795 + 3819790 * 2 ^ 59
def prefixEnd_3819790 : Nat := 4983230072969 + 3 ^ 40 * 3819790 * 2
def baseEnd_3819790 : Nat := 1307592179491810191838741

theorem tailTrace_3819790 : CollatzResearch.WordTrace tailWord_3819790 prefixEnd_3819790 1307592179491810191838741 := by
  unfold tailWord_3819790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17414898353945084129928103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92879457887707115359616549 17414898353945084129928103)
  ·
    refine ⟨26122347530917626194892155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17414898353945084129928103 26122347530917626194892155)
    ·
      refine ⟨39183521296376439292338233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26122347530917626194892155 39183521296376439292338233)
      ·
        refine ⟨29387640972282329469253675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39183521296376439292338233 29387640972282329469253675)
        ·
          refine ⟨44081461458423494203880513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29387640972282329469253675 44081461458423494203880513)
          ·
            refine ⟨33061096093817620652910385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44081461458423494203880513 33061096093817620652910385)
            ·
              refine ⟨24795822070363215489682789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33061096093817620652910385 24795822070363215489682789)
              ·
                refine ⟨4649216638193102904315523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24795822070363215489682789 4649216638193102904315523)
                ·
                  refine ⟨6973824957289654356473285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649216638193102904315523 6973824957289654356473285)
                  ·
                    refine ⟨1307592179491810191838741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973824957289654356473285 1307592179491810191838741)
                    ·
                      rfl

theorem cell22_3819790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_3819790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819790 prefixEnd_3819790 := by exact prefixLift 3819790
  have htrace : WordTrace (prefixWord ++ tailWord_3819790) baseStart_3819790 baseEnd_3819790 := by
    simpa [prefixWord, tailWord_3819790, baseEnd_3819790] using wordTrace_append hprefix tailTrace_3819790
  have hstable : (prefixWord ++ tailWord_3819790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819790).length < 2 ^ (prefixWord ++ tailWord_3819790).sum := by decide
  have hdescent : baseEnd_3819790 < baseStart_3819790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819803 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_3819803 : Nat := 118140960795 + 3819803 * 2 ^ 59
def prefixEnd_3819803 : Nat := 4983230072969 + 3 ^ 40 * 3819803 * 2
def baseEnd_3819803 : Nat := 1307596629657482491263701

theorem tailTrace_3819803 : CollatzResearch.WordTrace tailWord_3819803 prefixEnd_3819803 1307596629657482491263701 := by
  unfold tailWord_3819803
  simp only [CollatzResearch.WordTrace]
  refine ⟨139319660980513576259648063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92879773987009050839765375 139319660980513576259648063)
  ·
    refine ⟨208979491470770364389472095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139319660980513576259648063 208979491470770364389472095)
    ·
      refine ⟨313469237206155546584208143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208979491470770364389472095 313469237206155546584208143)
      ·
        refine ⟨470203855809233319876312215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313469237206155546584208143 470203855809233319876312215)
        ·
          refine ⟨705305783713849979814468323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470203855809233319876312215 705305783713849979814468323)
          ·
            refine ⟨1057958675570774969721702485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 705305783713849979814468323 1057958675570774969721702485)
            ·
              refine ⟨12397953229345019176426201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1057958675570774969721702485 12397953229345019176426201)
              ·
                refine ⟨9298464922008764382319651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12397953229345019176426201 9298464922008764382319651)
                ·
                  refine ⟨13947697383013146573479477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9298464922008764382319651 13947697383013146573479477)
                  ·
                    refine ⟨1307596629657482491263701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13947697383013146573479477 1307596629657482491263701)
                    ·
                      rfl

theorem cell22_3819803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_3819803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819803 prefixEnd_3819803 := by exact prefixLift 3819803
  have htrace : WordTrace (prefixWord ++ tailWord_3819803) baseStart_3819803 baseEnd_3819803 := by
    simpa [prefixWord, tailWord_3819803, baseEnd_3819803] using wordTrace_append hprefix tailTrace_3819803
  have hstable : (prefixWord ++ tailWord_3819803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819803).length < 2 ^ (prefixWord ++ tailWord_3819803).sum := by decide
  have hdescent : baseEnd_3819803 < baseStart_3819803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819807 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 1, 4]
def baseStart_3819807 : Nat := 118140960795 + 3819807 * 2 ^ 59
def prefixEnd_3819807 : Nat := 4983230072969 + 3 ^ 40 * 3819807 * 2
def baseEnd_3819807 : Nat := 1307597998939227814163689

theorem tailTrace_3819807 : CollatzResearch.WordTrace tailWord_3819807 prefixEnd_3819807 1307597998939227814163689 := by
  unfold tailWord_3819807
  simp only [CollatzResearch.WordTrace]
  refine ⟨139319806872499084942793675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92879871248332723295195783 139319806872499084942793675)
  ·
    refine ⟨208979710308748627414190513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139319806872499084942793675 208979710308748627414190513)
    ·
      refine ⟨156734782731561470560642885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 208979710308748627414190513 156734782731561470560642885)
      ·
        refine ⟨29387771762167775730120541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156734782731561470560642885 29387771762167775730120541)
        ·
          refine ⟨11020414410812915898795203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29387771762167775730120541 11020414410812915898795203)
          ·
            refine ⟨16530621616219373848192805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11020414410812915898795203 16530621616219373848192805)
            ·
              refine ⟨3099491553041132596536151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16530621616219373848192805 3099491553041132596536151)
              ·
                refine ⟨4649237329561698894804227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3099491553041132596536151 4649237329561698894804227)
                ·
                  refine ⟨6973855994342548342206341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4649237329561698894804227 6973855994342548342206341)
                  ·
                    refine ⟨1307597998939227814163689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6973855994342548342206341 1307597998939227814163689)
                    ·
                      rfl

theorem cell22_3819807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_3819807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819807 prefixEnd_3819807 := by exact prefixLift 3819807
  have htrace : WordTrace (prefixWord ++ tailWord_3819807) baseStart_3819807 baseEnd_3819807 := by
    simpa [prefixWord, tailWord_3819807, baseEnd_3819807] using wordTrace_append hprefix tailTrace_3819807
  have hstable : (prefixWord ++ tailWord_3819807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819807).length < 2 ^ (prefixWord ++ tailWord_3819807).sum := by decide
  have hdescent : baseEnd_3819807 < baseStart_3819807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819933 : List Nat := [1, 4, 2, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3819933 : Nat := 118140960795 + 3819933 * 2 ^ 59
def prefixEnd_3819933 : Nat := 4983230072969 + 3 ^ 40 * 3819933 * 2
def baseEnd_3819933 : Nat := 1307641131314205485513303

theorem tailTrace_3819933 : CollatzResearch.WordTrace tailWord_3819933 prefixEnd_3819933 1307641131314205485513303 := by
  unfold tailWord_3819933
  simp only [CollatzResearch.WordTrace]
  refine ⟨139324402470042608461880453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92882934980028405641253635 139324402470042608461880453)
  ·
    refine ⟨26123325463132989086602585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139324402470042608461880453 26123325463132989086602585)
    ·
      refine ⟨19592494097349741814951939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26123325463132989086602585 19592494097349741814951939)
      ·
        refine ⟨29388741146024612722427909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19592494097349741814951939 29388741146024612722427909)
        ·
          refine ⟨5510388964879614885455233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29388741146024612722427909 5510388964879614885455233)
          ·
            refine ⟨4132791723659711164091425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5510388964879614885455233 4132791723659711164091425)
            ·
              refine ⟨3099593792744783373068569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132791723659711164091425 3099593792744783373068569)
              ·
                refine ⟨2324695344558587529801427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099593792744783373068569 2324695344558587529801427)
                ·
                  refine ⟨3487043016837881294702141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324695344558587529801427 3487043016837881294702141)
                  ·
                    refine ⟨1307641131314205485513303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487043016837881294702141 1307641131314205485513303)
                    ·
                      rfl

theorem cell22_3819933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3819933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819933 prefixEnd_3819933 := by exact prefixLift 3819933
  have htrace : WordTrace (prefixWord ++ tailWord_3819933) baseStart_3819933 baseEnd_3819933 := by
    simpa [prefixWord, tailWord_3819933, baseEnd_3819933] using wordTrace_append hprefix tailTrace_3819933
  have hstable : (prefixWord ++ tailWord_3819933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819933).length < 2 ^ (prefixWord ++ tailWord_3819933).sum := by decide
  have hdescent : baseEnd_3819933 < baseStart_3819933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819955 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 8, 3]
def baseStart_3819955 : Nat := 118140960795 + 3819955 * 2 ^ 59
def prefixEnd_3819955 : Nat := 4983230072969 + 3 ^ 40 * 3819955 * 2
def baseEnd_3819955 : Nat := 1307648662363804761463235

theorem tailTrace_3819955 : CollatzResearch.WordTrace tailWord_3819955 prefixEnd_3819955 1307648662363804761463235 := by
  unfold tailWord_3819955
  simp only [CollatzResearch.WordTrace]
  refine ⟨139325204875962906219181319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92883469917308604146120879 139325204875962906219181319)
  ·
    refine ⟨208987807313944359328771979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139325204875962906219181319 208987807313944359328771979)
    ·
      refine ⟨313481710970916538993157969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208987807313944359328771979 313481710970916538993157969)
      ·
        refine ⟨235111283228187404244868477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313481710970916538993157969 235111283228187404244868477)
        ·
          refine ⟨88166731210570276591825679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235111283228187404244868477 88166731210570276591825679)
          ·
            refine ⟨132250096815855414887738519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88166731210570276591825679 132250096815855414887738519)
            ·
              refine ⟨198375145223783122331607779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132250096815855414887738519 198375145223783122331607779)
              ·
                refine ⟨297562717835674683497411669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198375145223783122331607779 297562717835674683497411669)
                ·
                  refine ⟨3487063099636812697235293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 297562717835674683497411669 3487063099636812697235293)
                  ·
                    refine ⟨1307648662363804761463235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487063099636812697235293 1307648662363804761463235)
                    ·
                      rfl

theorem cell22_3819955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 8, 3].length) (baseStart_3819955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819955 prefixEnd_3819955 := by exact prefixLift 3819955
  have htrace : WordTrace (prefixWord ++ tailWord_3819955) baseStart_3819955 baseEnd_3819955 := by
    simpa [prefixWord, tailWord_3819955, baseEnd_3819955] using wordTrace_append hprefix tailTrace_3819955
  have hstable : (prefixWord ++ tailWord_3819955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819955).length < 2 ^ (prefixWord ++ tailWord_3819955).sum := by decide
  have hdescent : baseEnd_3819955 < baseStart_3819955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819957 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 6]
def baseStart_3819957 : Nat := 118140960795 + 3819957 * 2 ^ 59
def prefixEnd_3819957 : Nat := 4983230072969 + 3 ^ 40 * 3819957 * 2
def baseEnd_3819957 : Nat := 435883115668225807637743

theorem tailTrace_3819957 : CollatzResearch.WordTrace tailWord_3819957 prefixEnd_3819957 435883115668225807637743 := by
  unfold tailWord_3819957
  simp only [CollatzResearch.WordTrace]
  refine ⟨139325277821955660560754125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92883518547970440373836083 139325277821955660560754125)
  ·
    refine ⟨52246979183233372710282797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139325277821955660560754125 52246979183233372710282797)
    ·
      refine ⟨19592617193712514766356049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52246979183233372710282797 19592617193712514766356049)
      ·
        refine ⟨14694462895284386074767037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19592617193712514766356049 14694462895284386074767037)
        ·
          refine ⟨5510423585731644778037639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14694462895284386074767037 5510423585731644778037639)
          ·
            refine ⟨8265635378597467167056459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510423585731644778037639 8265635378597467167056459)
            ·
              refine ⟨12398453067896200750584689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8265635378597467167056459 12398453067896200750584689)
              ·
                refine ⟨9298839800922150562938517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12398453067896200750584689 9298839800922150562938517)
                ·
                  refine ⟨435883115668225807637743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9298839800922150562938517 435883115668225807637743)
                  ·
                    rfl

theorem cell22_3819957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_3819957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819957 prefixEnd_3819957 := by exact prefixLift 3819957
  have htrace : WordTrace (prefixWord ++ tailWord_3819957) baseStart_3819957 baseEnd_3819957 := by
    simpa [prefixWord, tailWord_3819957, baseEnd_3819957] using wordTrace_append hprefix tailTrace_3819957
  have hstable : (prefixWord ++ tailWord_3819957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819957).length < 2 ^ (prefixWord ++ tailWord_3819957).sum := by decide
  have hdescent : baseEnd_3819957 < baseStart_3819957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3819989 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 2, 3]
def baseStart_3819989 : Nat := 118140960795 + 3819989 * 2 ^ 59
def prefixEnd_3819989 : Nat := 4983230072969 + 3 ^ 40 * 3819989 * 2
def baseEnd_3819989 : Nat := 1307660301258640006113131

theorem tailTrace_3819989 : CollatzResearch.WordTrace tailWord_3819989 prefixEnd_3819989 1307660301258640006113131 := by
  unfold tailWord_3819989
  simp only [CollatzResearch.WordTrace]
  refine ⟨139326444957839730025919021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92884296638559820017279347 139326444957839730025919021)
  ·
    refine ⟨52247416859189898759719633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139326444957839730025919021 52247416859189898759719633)
    ·
      refine ⟨39185562644392424069789725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52247416859189898759719633 39185562644392424069789725)
      ·
        refine ⟨14694585991647159026171147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39185562644392424069789725 14694585991647159026171147)
        ·
          refine ⟨22041878987470738539256721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14694585991647159026171147 22041878987470738539256721)
          ·
            refine ⟨16531409240603053904442541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22041878987470738539256721 16531409240603053904442541)
            ·
              refine ⟨6199278465226145214165953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16531409240603053904442541 6199278465226145214165953)
              ·
                refine ⟨4649458848919608910624465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6199278465226145214165953 4649458848919608910624465)
                ·
                  refine ⟨3487094136689706682968349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4649458848919608910624465 3487094136689706682968349)
                  ·
                    refine ⟨1307660301258640006113131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487094136689706682968349 1307660301258640006113131)
                    ·
                      rfl

theorem cell22_3819989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_3819989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3819989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3819989 prefixEnd_3819989 := by exact prefixLift 3819989
  have htrace : WordTrace (prefixWord ++ tailWord_3819989) baseStart_3819989 baseEnd_3819989 := by
    simpa [prefixWord, tailWord_3819989, baseEnd_3819989] using wordTrace_append hprefix tailTrace_3819989
  have hstable : (prefixWord ++ tailWord_3819989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3819989).length < 2 ^ (prefixWord ++ tailWord_3819989).sum := by decide
  have hdescent : baseEnd_3819989 < baseStart_3819989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3819989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820017 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 3, 3]
def baseStart_3820017 : Nat := 118140960795 + 3820017 * 2 ^ 59
def prefixEnd_3820017 : Nat := 4983230072969 + 3 ^ 40 * 3820017 * 2
def baseEnd_3820017 : Nat := 1307669886230857266413045

theorem tailTrace_3820017 : CollatzResearch.WordTrace tailWord_3820017 prefixEnd_3820017 1307669886230857266413045 := by
  unfold tailWord_3820017
  simp only [CollatzResearch.WordTrace]
  refine ⟨139327466201738290807938305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92884977467825527205292203 139327466201738290807938305)
  ·
    refine ⟨104495599651303718105953729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139327466201738290807938305 104495599651303718105953729)
    ·
      refine ⟨78371699738477788579465297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104495599651303718105953729 78371699738477788579465297)
      ·
        refine ⟨58778774803858341434598973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78371699738477788579465297 58778774803858341434598973)
        ·
          refine ⟨22042040551446878037974615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58778774803858341434598973 22042040551446878037974615)
          ·
            refine ⟨33063060827170317056961923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22042040551446878037974615 33063060827170317056961923)
            ·
              refine ⟨49594591240755475585442885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33063060827170317056961923 49594591240755475585442885)
              ·
                refine ⟨9298985857641651672270541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49594591240755475585442885 9298985857641651672270541)
                ·
                  refine ⟨3487119696615619377101453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9298985857641651672270541 3487119696615619377101453)
                  ·
                    refine ⟨1307669886230857266413045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487119696615619377101453 1307669886230857266413045)
                    ·
                      rfl

theorem cell22_3820017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 3, 3].length) (baseStart_3820017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820017 prefixEnd_3820017 := by exact prefixLift 3820017
  have htrace : WordTrace (prefixWord ++ tailWord_3820017) baseStart_3820017 baseEnd_3820017 := by
    simpa [prefixWord, tailWord_3820017, baseEnd_3820017] using wordTrace_append hprefix tailTrace_3820017
  have hstable : (prefixWord ++ tailWord_3820017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820017).length < 2 ^ (prefixWord ++ tailWord_3820017).sum := by decide
  have hdescent : baseEnd_3820017 < baseStart_3820017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820038 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3820038 : Nat := 118140960795 + 3820038 * 2 ^ 59
def prefixEnd_3820038 : Nat := 4983230072969 + 3 ^ 40 * 3820038 * 2
def baseEnd_3820038 : Nat := 1307677074960020211637981

theorem tailTrace_3820038 : CollatzResearch.WordTrace tailWord_3820038 prefixEnd_3820038 1307677074960020211637981 := by
  unfold tailWord_3820038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354007254208194106076649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92885488089774807596301845 4354007254208194106076649)
  ·
    refine ⟨3265505440656145579557487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4354007254208194106076649 3265505440656145579557487)
    ·
      refine ⟨4898258160984218369336231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3265505440656145579557487 4898258160984218369336231)
      ·
        refine ⟨7347387241476327554004347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4898258160984218369336231 7347387241476327554004347)
        ·
          refine ⟨11021080862214491331006521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347387241476327554004347 11021080862214491331006521)
          ·
            refine ⟨8265810646660868498254891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11021080862214491331006521 8265810646660868498254891)
            ·
              refine ⟨12398715969991302747382337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8265810646660868498254891 12398715969991302747382337)
              ·
                refine ⟨9299036977493477060536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12398715969991302747382337 9299036977493477060536753)
                ·
                  refine ⟨6974277733120107795402565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9299036977493477060536753 6974277733120107795402565)
                  ·
                    refine ⟨1307677074960020211637981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6974277733120107795402565 1307677074960020211637981)
                    ·
                      rfl

theorem cell22_3820038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3820038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820038 prefixEnd_3820038 := by exact prefixLift 3820038
  have htrace : WordTrace (prefixWord ++ tailWord_3820038) baseStart_3820038 baseEnd_3820038 := by
    simpa [prefixWord, tailWord_3820038, baseEnd_3820038] using wordTrace_append hprefix tailTrace_3820038
  have hstable : (prefixWord ++ tailWord_3820038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820038).length < 2 ^ (prefixWord ++ tailWord_3820038).sum := by decide
  have hdescent : baseEnd_3820038 < baseStart_3820038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820051 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 1, 3]
def baseStart_3820051 : Nat := 118140960795 + 3820051 * 2 ^ 59
def prefixEnd_3820051 : Nat := 4983230072969 + 3 ^ 40 * 3820051 * 2
def baseEnd_3820051 : Nat := 1307681525125692511062941

theorem tailTrace_3820051 : CollatzResearch.WordTrace tailWord_3820051 prefixEnd_3820051 1307681525125692511062941 := by
  unfold tailWord_3820051
  simp only [CollatzResearch.WordTrace]
  refine ⟨139328706283615114614676007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92885804189076743076450671 139328706283615114614676007)
  ·
    refine ⟨208993059425422671922014011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139328706283615114614676007 208993059425422671922014011)
    ·
      refine ⟨313489589138134007883021017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208993059425422671922014011 313489589138134007883021017)
      ·
        refine ⟨235117191853600505912265763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313489589138134007883021017 235117191853600505912265763)
        ·
          refine ⟨352675787780400758868398645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235117191853600505912265763 352675787780400758868398645)
          ·
            refine ⟨33063355104412571143912373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 352675787780400758868398645 33063355104412571143912373)
            ·
              refine ⟨3099689541038678544741785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33063355104412571143912373 3099689541038678544741785)
              ·
                refine ⟨2324767155779008908556339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099689541038678544741785 2324767155779008908556339)
                ·
                  refine ⟨3487150733668513362834509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324767155779008908556339 3487150733668513362834509)
                  ·
                    refine ⟨1307681525125692511062941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487150733668513362834509 1307681525125692511062941)
                    ·
                      rfl

theorem cell22_3820051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 1, 3].length) (baseStart_3820051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820051 prefixEnd_3820051 := by exact prefixLift 3820051
  have htrace : WordTrace (prefixWord ++ tailWord_3820051) baseStart_3820051 baseEnd_3820051 := by
    simpa [prefixWord, tailWord_3820051, baseEnd_3820051] using wordTrace_append hprefix tailTrace_3820051
  have hstable : (prefixWord ++ tailWord_3820051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820051).length < 2 ^ (prefixWord ++ tailWord_3820051).sum := by decide
  have hdescent : baseEnd_3820051 < baseStart_3820051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820064 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_3820064 : Nat := 118140960795 + 3820064 * 2 ^ 59
def prefixEnd_3820064 : Nat := 4983230072969 + 3 ^ 40 * 3820064 * 2
def baseEnd_3820064 : Nat := 435895325097121603495967

theorem tailTrace_3820064 : CollatzResearch.WordTrace tailWord_3820064 prefixEnd_3820064 435895325097121603495967 := by
  unfold tailWord_3820064
  simp only [CollatzResearch.WordTrace]
  refine ⟨69664590216284008917449623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92886120288378678556599497 69664590216284008917449623)
  ·
    refine ⟨104496885324426013376174435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69664590216284008917449623 104496885324426013376174435)
    ·
      refine ⟨156745327986639020064261653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104496885324426013376174435 156745327986639020064261653)
      ·
        refine ⟨7347437249373704065512265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156745327986639020064261653 7347437249373704065512265)
        ·
          refine ⟨5510577937030278049134199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7347437249373704065512265 5510577937030278049134199)
          ·
            refine ⟨8265866905545417073701299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5510577937030278049134199 8265866905545417073701299)
            ·
              refine ⟨12398800358318125610551949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8265866905545417073701299 12398800358318125610551949)
              ·
                refine ⟨4649550134369297103956981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12398800358318125610551949 4649550134369297103956981)
                ·
                  refine ⟨435895325097121603495967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4649550134369297103956981 435895325097121603495967)
                  ·
                    rfl

theorem cell22_3820064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_3820064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820064 prefixEnd_3820064 := by exact prefixLift 3820064
  have htrace : WordTrace (prefixWord ++ tailWord_3820064) baseStart_3820064 baseEnd_3820064 := by
    simpa [prefixWord, tailWord_3820064, baseEnd_3820064] using wordTrace_append hprefix tailTrace_3820064
  have hstable : (prefixWord ++ tailWord_3820064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820064).length < 2 ^ (prefixWord ++ tailWord_3820064).sum := by decide
  have hdescent : baseEnd_3820064 < baseStart_3820064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820075 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 6]
def baseStart_3820075 : Nat := 118140960795 + 3820075 * 2 ^ 59
def prefixEnd_3820075 : Nat := 4983230072969 + 3 ^ 40 * 3820075 * 2
def baseEnd_3820075 : Nat := 435896580272054816154289

theorem tailTrace_3820075 : CollatzResearch.WordTrace tailWord_3820075 prefixEnd_3820075 435896580272054816154289 := by
  unfold tailWord_3820075
  simp only [CollatzResearch.WordTrace]
  refine ⟨139329581635528166713549679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92886387757018777809033119 139329581635528166713549679)
  ·
    refine ⟨208994372453292250070324519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139329581635528166713549679 208994372453292250070324519)
    ·
      refine ⟨313491558679938375105486779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208994372453292250070324519 313491558679938375105486779)
      ·
        refine ⟨470237338019907562658230169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313491558679938375105486779 470237338019907562658230169)
        ·
          refine ⟨352678003514930671993672627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470237338019907562658230169 352678003514930671993672627)
          ·
            refine ⟨529017005272396007990508941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352678003514930671993672627 529017005272396007990508941)
            ·
              refine ⟨198381376977148502996440853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 529017005272396007990508941 198381376977148502996440853)
              ·
                refine ⟨9299127045803836077958165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 198381376977148502996440853 9299127045803836077958165)
                ·
                  refine ⟨435896580272054816154289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9299127045803836077958165 435896580272054816154289)
                  ·
                    rfl

theorem cell22_3820075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_3820075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820075 prefixEnd_3820075 := by exact prefixLift 3820075
  have htrace : WordTrace (prefixWord ++ tailWord_3820075) baseStart_3820075 baseEnd_3820075 := by
    simpa [prefixWord, tailWord_3820075, baseEnd_3820075] using wordTrace_append hprefix tailTrace_3820075
  have hstable : (prefixWord ++ tailWord_3820075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820075).length < 2 ^ (prefixWord ++ tailWord_3820075).sum := by decide
  have hdescent : baseEnd_3820075 < baseStart_3820075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820102 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 1, 3]
def baseStart_3820102 : Nat := 118140960795 + 3820102 * 2 ^ 59
def prefixEnd_3820102 : Nat := 4983230072969 + 3 ^ 40 * 3820102 * 2
def baseEnd_3820102 : Nat := 1307698983467945378037785

theorem tailTrace_3820102 : CollatzResearch.WordTrace tailWord_3820102 prefixEnd_3820102 1307698983467945378037785 := by
  unfold tailWord_3820102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354080200200948447649455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92887044270953566883188373 4354080200200948447649455)
  ·
    refine ⟨6531120300301422671474183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354080200200948447649455 6531120300301422671474183)
    ·
      refine ⟨9796680450452134007211275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531120300301422671474183 9796680450452134007211275)
      ·
        refine ⟨14695020675678201010816913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9796680450452134007211275 14695020675678201010816913)
        ·
          refine ⟨11021265506758650758112685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14695020675678201010816913 11021265506758650758112685)
          ·
            refine ⟨4132974565034494034292257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11021265506758650758112685 4132974565034494034292257)
            ·
              refine ⟨3099730923775870525719193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4132974565034494034292257 3099730923775870525719193)
              ·
                refine ⟨2324798192831902894289395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3099730923775870525719193 2324798192831902894289395)
                ·
                  refine ⟨3487197289247854341434093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324798192831902894289395 3487197289247854341434093)
                  ·
                    refine ⟨1307698983467945378037785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487197289247854341434093 1307698983467945378037785)
                    ·
                      rfl

theorem cell22_3820102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_3820102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820102 prefixEnd_3820102 := by exact prefixLift 3820102
  have htrace : WordTrace (prefixWord ++ tailWord_3820102) baseStart_3820102 baseEnd_3820102 := by
    simpa [prefixWord, tailWord_3820102, baseEnd_3820102] using wordTrace_append hprefix tailTrace_3820102
  have hstable : (prefixWord ++ tailWord_3820102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820102).length < 2 ^ (prefixWord ++ tailWord_3820102).sum := by decide
  have hdescent : baseEnd_3820102 < baseStart_3820102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820105 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_3820105 : Nat := 118140960795 + 3820105 * 2 ^ 59
def prefixEnd_3820105 : Nat := 4983230072969 + 3 ^ 40 * 3820105 * 2
def baseEnd_3820105 : Nat := 1307700010429254370212775

theorem tailTrace_3820105 : CollatzResearch.WordTrace tailWord_3820105 prefixEnd_3820105 1307700010429254370212775 := by
  unfold tailWord_3820105
  simp only [CollatzResearch.WordTrace]
  refine ⟨139330675825419481837141769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92887117216946321224761179 139330675825419481837141769)
  ·
    refine ⟨104498006869064611377856327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139330675825419481837141769 104498006869064611377856327)
    ·
      refine ⟨156747010303596917066784491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104498006869064611377856327 156747010303596917066784491)
      ·
        refine ⟨235120515455395375600176737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156747010303596917066784491 235120515455395375600176737)
        ·
          refine ⟨176340386591546531700132553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235120515455395375600176737 176340386591546531700132553)
          ·
            refine ⟨132255289943659898775099415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176340386591546531700132553 132255289943659898775099415)
            ·
              refine ⟨198382934915489848162649123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132255289943659898775099415 198382934915489848162649123)
              ·
                refine ⟨297574402373234772243973685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198382934915489848162649123 297574402373234772243973685)
                ·
                  refine ⟨27897600222490759897872533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 297574402373234772243973685 27897600222490759897872533)
                  ·
                    refine ⟨1307700010429254370212775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27897600222490759897872533 1307700010429254370212775)
                    ·
                      rfl

theorem cell22_3820105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_3820105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820105 prefixEnd_3820105 := by exact prefixLift 3820105
  have htrace : WordTrace (prefixWord ++ tailWord_3820105) baseStart_3820105 baseEnd_3820105 := by
    simpa [prefixWord, tailWord_3820105, baseEnd_3820105] using wordTrace_append hprefix tailTrace_3820105
  have hstable : (prefixWord ++ tailWord_3820105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820105).length < 2 ^ (prefixWord ++ tailWord_3820105).sum := by decide
  have hdescent : baseEnd_3820105 < baseStart_3820105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820107 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 4, 3]
def baseStart_3820107 : Nat := 118140960795 + 3820107 * 2 ^ 59
def prefixEnd_3820107 : Nat := 4983230072969 + 3 ^ 40 * 3820107 * 2
def baseEnd_3820107 : Nat := 1307700695070127031662769

theorem tailTrace_3820107 : CollatzResearch.WordTrace tailWord_3820107 prefixEnd_3820107 1307700695070127031662769 := by
  unfold tailWord_3820107
  simp only [CollatzResearch.WordTrace]
  refine ⟨139330748771412236178714575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92887165847608157452476383 139330748771412236178714575)
  ·
    refine ⟨208996123157118354268071863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139330748771412236178714575 208996123157118354268071863)
    ·
      refine ⟨313494184735677531402107795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 208996123157118354268071863 313494184735677531402107795)
      ·
        refine ⟨470241277103516297103161693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313494184735677531402107795 470241277103516297103161693)
        ·
          refine ⟨176340478913818611413685635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 470241277103516297103161693 176340478913818611413685635)
          ·
            refine ⟨264510718370727917120528453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176340478913818611413685635 264510718370727917120528453)
            ·
              refine ⟨49595759694511484460099085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 264510718370727917120528453 49595759694511484460099085)
              ·
                refine ⟨18598409885441806672537157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49595759694511484460099085 18598409885441806672537157)
                ·
                  refine ⟨3487201853520338751100717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18598409885441806672537157 3487201853520338751100717)
                  ·
                    refine ⟨1307700695070127031662769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487201853520338751100717 1307700695070127031662769)
                    ·
                      rfl

theorem cell22_3820107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 4, 3].length) (baseStart_3820107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820107 prefixEnd_3820107 := by exact prefixLift 3820107
  have htrace : WordTrace (prefixWord ++ tailWord_3820107) baseStart_3820107 baseEnd_3820107 := by
    simpa [prefixWord, tailWord_3820107, baseEnd_3820107] using wordTrace_append hprefix tailTrace_3820107
  have hstable : (prefixWord ++ tailWord_3820107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820107).length < 2 ^ (prefixWord ++ tailWord_3820107).sum := by decide
  have hdescent : baseEnd_3820107 < baseStart_3820107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820259 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_3820259 : Nat := 118140960795 + 3820259 * 2 ^ 59
def prefixEnd_3820259 : Nat := 4983230072969 + 3 ^ 40 * 3820259 * 2
def baseEnd_3820259 : Nat := 1307752727776449301862303

theorem tailTrace_3820259 : CollatzResearch.WordTrace tailWord_3820259 prefixEnd_3820259 1307752727776449301862303 := by
  unfold tailWord_3820259
  simp only [CollatzResearch.WordTrace]
  refine ⟨139336292666861566138247831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92890861777907710758831887 139336292666861566138247831)
  ·
    refine ⟨209004439000292349207371747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139336292666861566138247831 209004439000292349207371747)
    ·
      refine ⟨313506658500438523811057621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209004439000292349207371747 313506658500438523811057621)
      ·
        refine ⟨7347812308604027901821663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 313506658500438523811057621 7347812308604027901821663)
        ·
          refine ⟨11021718462906041852732495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7347812308604027901821663 11021718462906041852732495)
          ·
            refine ⟨16532577694359062779098743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11021718462906041852732495 16532577694359062779098743)
            ·
              refine ⟨24798866541538594168648115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16532577694359062779098743 24798866541538594168648115)
              ·
                refine ⟨37198299812307891252972173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24798866541538594168648115 37198299812307891252972173)
                ·
                  refine ⟨13949362429615459219864565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37198299812307891252972173 13949362429615459219864565)
                  ·
                    refine ⟨1307752727776449301862303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13949362429615459219864565 1307752727776449301862303)
                    ·
                      rfl

theorem cell22_3820259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_3820259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820259 prefixEnd_3820259 := by exact prefixLift 3820259
  have htrace : WordTrace (prefixWord ++ tailWord_3820259) baseStart_3820259 baseEnd_3820259 := by
    simpa [prefixWord, tailWord_3820259, baseEnd_3820259] using wordTrace_append hprefix tailTrace_3820259
  have hstable : (prefixWord ++ tailWord_3820259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820259).length < 2 ^ (prefixWord ++ tailWord_3820259).sum := by decide
  have hdescent : baseEnd_3820259 < baseStart_3820259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820287 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_3820287 : Nat := 118140960795 + 3820287 * 2 ^ 59
def prefixEnd_3820287 : Nat := 4983230072969 + 3 ^ 40 * 3820287 * 2
def baseEnd_3820287 : Nat := 1307762312748666562162217

theorem tailTrace_3820287 : CollatzResearch.WordTrace tailWord_3820287 prefixEnd_3820287 1307762312748666562162217 := by
  unfold tailWord_3820287
  simp only [CollatzResearch.WordTrace]
  refine ⟨139337313910760126920267115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92891542607173417946844743 139337313910760126920267115)
  ·
    refine ⟨209005970866140190380400673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139337313910760126920267115 209005970866140190380400673)
    ·
      refine ⟨156754478149605142785300505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209005970866140190380400673 156754478149605142785300505)
      ·
        refine ⟨117565858612203857088975379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156754478149605142785300505 117565858612203857088975379)
        ·
          refine ⟨176348787918305785633463069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117565858612203857088975379 176348787918305785633463069)
          ·
            refine ⟨66130795469364669612548651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176348787918305785633463069 66130795469364669612548651)
            ·
              refine ⟨99196193204047004418822977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66130795469364669612548651 99196193204047004418822977)
              ·
                refine ⟨74397144903035253314117233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99196193204047004418822977 74397144903035253314117233)
                ·
                  refine ⟨55797858677276439985587925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74397144903035253314117233 55797858677276439985587925)
                  ·
                    refine ⟨1307762312748666562162217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55797858677276439985587925 1307762312748666562162217)
                    ·
                      rfl

theorem cell22_3820287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_3820287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820287 prefixEnd_3820287 := by exact prefixLift 3820287
  have htrace : WordTrace (prefixWord ++ tailWord_3820287) baseStart_3820287 baseEnd_3820287 := by
    simpa [prefixWord, tailWord_3820287, baseEnd_3820287] using wordTrace_append hprefix tailTrace_3820287
  have hstable : (prefixWord ++ tailWord_3820287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820287).length < 2 ^ (prefixWord ++ tailWord_3820287).sum := by decide
  have hdescent : baseEnd_3820287 < baseStart_3820287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820338 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3820338 : Nat := 118140960795 + 3820338 * 2 ^ 59
def prefixEnd_3820338 : Nat := 4983230072969 + 3 ^ 40 * 3820338 * 2
def baseEnd_3820338 : Nat := 1307779771090919429137061

theorem tailTrace_3820338 : CollatzResearch.WordTrace tailWord_3820338 prefixEnd_3820338 1307779771090919429137061 := by
  unfold tailWord_3820338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34834793508393840657593417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92892782689050241753582445 34834793508393840657593417)
  ·
    refine ⟨26126095131295380493195063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34834793508393840657593417 26126095131295380493195063)
    ·
      refine ⟨39189142696943070739792595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26126095131295380493195063 39189142696943070739792595)
      ·
        refine ⟨58783714045414606109688893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39189142696943070739792595 58783714045414606109688893)
        ·
          refine ⟨22043892767030477291133335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58783714045414606109688893 22043892767030477291133335)
          ·
            refine ⟨33065839150545715936700003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22043892767030477291133335 33065839150545715936700003)
            ·
              refine ⟨49598758725818573905050005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33065839150545715936700003 49598758725818573905050005)
              ·
                refine ⟨2324941815272745651799219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 49598758725818573905050005 2324941815272745651799219)
                ·
                  refine ⟨3487412722909118477698829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324941815272745651799219 3487412722909118477698829)
                  ·
                    refine ⟨1307779771090919429137061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487412722909118477698829 1307779771090919429137061)
                    ·
                      rfl

theorem cell22_3820338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3820338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820338 prefixEnd_3820338 := by exact prefixLift 3820338
  have htrace : WordTrace (prefixWord ++ tailWord_3820338) baseStart_3820338 baseEnd_3820338 := by
    simpa [prefixWord, tailWord_3820338, baseEnd_3820338] using wordTrace_append hprefix tailTrace_3820338
  have hstable : (prefixWord ++ tailWord_3820338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820338).length < 2 ^ (prefixWord ++ tailWord_3820338).sum := by decide
  have hdescent : baseEnd_3820338 < baseStart_3820338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820372 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 1, 3]
def baseStart_3820372 : Nat := 118140960795 + 3820372 * 2 ^ 59
def prefixEnd_3820372 : Nat := 4983230072969 + 3 ^ 40 * 3820372 * 2
def baseEnd_3820372 : Nat := 1307791409985754673786957

theorem tailTrace_3820372 : CollatzResearch.WordTrace tailWord_3820372 prefixEnd_3820372 1307791409985754673786957 := by
  unfold tailWord_3820372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69670207057726093218555685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92893609410301457624740913 69670207057726093218555685)
  ·
    refine ⟨13063163823323642478479191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69670207057726093218555685 13063163823323642478479191)
    ·
      refine ⟨19594745734985463717718787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13063163823323642478479191 19594745734985463717718787)
      ·
        refine ⟨29392118602478195576578181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19594745734985463717718787 29392118602478195576578181)
        ·
          refine ⟨5511022237964661670608409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29392118602478195576578181 5511022237964661670608409)
          ·
            refine ⟨4133266678473496252956307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5511022237964661670608409 4133266678473496252956307)
            ·
              refine ⟨6199900017710244379434461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4133266678473496252956307 6199900017710244379434461)
              ·
                refine ⟨2324962506641341642287923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6199900017710244379434461 2324962506641341642287923)
                ·
                  refine ⟨3487443759962012463431885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2324962506641341642287923 3487443759962012463431885)
                  ·
                    refine ⟨1307791409985754673786957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487443759962012463431885 1307791409985754673786957)
                    ·
                      rfl

theorem cell22_3820372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_3820372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820372 prefixEnd_3820372 := by exact prefixLift 3820372
  have htrace : WordTrace (prefixWord ++ tailWord_3820372) baseStart_3820372 baseEnd_3820372 := by
    simpa [prefixWord, tailWord_3820372, baseEnd_3820372] using wordTrace_append hprefix tailTrace_3820372
  have hstable : (prefixWord ++ tailWord_3820372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820372).length < 2 ^ (prefixWord ++ tailWord_3820372).sum := by decide
  have hdescent : baseEnd_3820372 < baseStart_3820372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820473 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 3, 3]
def baseStart_3820473 : Nat := 118140960795 + 3820473 * 2 ^ 59
def prefixEnd_3820473 : Nat := 4983230072969 + 3 ^ 40 * 3820473 * 2
def baseEnd_3820473 : Nat := 1307825984349824077011647

theorem tailTrace_3820473 : CollatzResearch.WordTrace tailWord_3820473 prefixEnd_3820473 1307825984349824077011647 := by
  unfold tailWord_3820473
  simp only [CollatzResearch.WordTrace]
  refine ⟨139344097888086280686538073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92896065258724187124358715 139344097888086280686538073)
  ·
    refine ⟨104508073416064710514903555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139344097888086280686538073 104508073416064710514903555)
    ·
      refine ⟨156762110124097065772355333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104508073416064710514903555 156762110124097065772355333)
      ·
        refine ⟨29392895648268199832316625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156762110124097065772355333 29392895648268199832316625)
        ·
          refine ⟨22044671736201149874237469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29392895648268199832316625 22044671736201149874237469)
          ·
            refine ⟨8266751901075431202839051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22044671736201149874237469 8266751901075431202839051)
            ·
              refine ⟨12400127851613146804258577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8266751901075431202839051 12400127851613146804258577)
              ·
                refine ⟨9300095888709860103193933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12400127851613146804258577 9300095888709860103193933)
                ·
                  refine ⟨3487535958266197538697725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9300095888709860103193933 3487535958266197538697725)
                  ·
                    refine ⟨1307825984349824077011647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487535958266197538697725 1307825984349824077011647)
                    ·
                      rfl

theorem cell22_3820473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 3].length) (baseStart_3820473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820473 prefixEnd_3820473 := by exact prefixLift 3820473
  have htrace : WordTrace (prefixWord ++ tailWord_3820473) baseStart_3820473 baseEnd_3820473 := by
    simpa [prefixWord, tailWord_3820473, baseEnd_3820473] using wordTrace_append hprefix tailTrace_3820473
  have hstable : (prefixWord ++ tailWord_3820473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820473).length < 2 ^ (prefixWord ++ tailWord_3820473).sum := by decide
  have hdescent : baseEnd_3820473 < baseStart_3820473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820516 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3820516 : Nat := 118140960795 + 3820516 * 2 ^ 59
def prefixEnd_3820516 : Nat := 4983230072969 + 3 ^ 40 * 3820516 * 2
def baseEnd_3820516 : Nat := 1307840704128586298186515

theorem tailTrace_3820516 : CollatzResearch.WordTrace tailWord_3820516 prefixEnd_3820516 1307840704128586298186515 := by
  unfold tailWord_3820516
  simp only [CollatzResearch.WordTrace]
  refine ⟨69672833113465249515176701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92897110817953666020235601 69672833113465249515176701)
  ·
    refine ⟨26127312417549468568191263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69672833113465249515176701 26127312417549468568191263)
    ·
      refine ⟨39190968626324202852286895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26127312417549468568191263 39190968626324202852286895)
      ·
        refine ⟨58786452939486304278430343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39190968626324202852286895 58786452939486304278430343)
        ·
          refine ⟨88179679409229456417645515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58786452939486304278430343 88179679409229456417645515)
          ·
            refine ⟨132269519113844184626468273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88179679409229456417645515 132269519113844184626468273)
            ·
              refine ⟨99202139335383138469851205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132269519113844184626468273 99202139335383138469851205)
              ·
                refine ⟨18600401125384338463097101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99202139335383138469851205 18600401125384338463097101)
                ·
                  refine ⟨6975150422019126923661413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18600401125384338463097101 6975150422019126923661413)
                  ·
                    refine ⟨1307840704128586298186515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975150422019126923661413 1307840704128586298186515)
                    ·
                      rfl

theorem cell22_3820516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3820516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820516 prefixEnd_3820516 := by exact prefixLift 3820516
  have htrace : WordTrace (prefixWord ++ tailWord_3820516) baseStart_3820516 baseEnd_3820516 := by
    simpa [prefixWord, tailWord_3820516, baseEnd_3820516] using wordTrace_append hprefix tailTrace_3820516
  have hstable : (prefixWord ++ tailWord_3820516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820516).length < 2 ^ (prefixWord ++ tailWord_3820516).sum := by decide
  have hdescent : baseEnd_3820516 < baseStart_3820516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820563 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 2, 3]
def baseStart_3820563 : Nat := 118140960795 + 3820563 * 2 ^ 59
def prefixEnd_3820563 : Nat := 4983230072969 + 3 ^ 40 * 3820563 * 2
def baseEnd_3820563 : Nat := 1307856793189093842261371

theorem tailTrace_3820563 : CollatzResearch.WordTrace tailWord_3820563 prefixEnd_3820563 1307856793189093842261371 := by
  unfold tailWord_3820563
  simp only [CollatzResearch.WordTrace]
  refine ⟨139347380457760226057314343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92898253638506817371542895 139347380457760226057314343)
  ·
    refine ⟨209021070686640339085971515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139347380457760226057314343 209021070686640339085971515)
    ·
      refine ⟨313531606029960508628957273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209021070686640339085971515 313531606029960508628957273)
      ·
        refine ⟨235148704522470381471717955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313531606029960508628957273 235148704522470381471717955)
        ·
          refine ⟨352723056783705572207576933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235148704522470381471717955 352723056783705572207576933)
          ·
            refine ⟨66135573146944794788920675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 352723056783705572207576933 66135573146944794788920675)
            ·
              refine ⟨99203359720417192183381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66135573146944794788920675 99203359720417192183381013)
              ·
                refine ⟨4650157486894555883595985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99203359720417192183381013 4650157486894555883595985)
                ·
                  refine ⟨3487618115170916912696989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650157486894555883595985 3487618115170916912696989)
                  ·
                    refine ⟨1307856793189093842261371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487618115170916912696989 1307856793189093842261371)
                    ·
                      rfl

theorem cell22_3820563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 2, 3].length) (baseStart_3820563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820563 prefixEnd_3820563 := by exact prefixLift 3820563
  have htrace : WordTrace (prefixWord ++ tailWord_3820563) baseStart_3820563 baseEnd_3820563 := by
    simpa [prefixWord, tailWord_3820563, baseEnd_3820563] using wordTrace_append hprefix tailTrace_3820563
  have hstable : (prefixWord ++ tailWord_3820563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820563).length < 2 ^ (prefixWord ++ tailWord_3820563).sum := by decide
  have hdescent : baseEnd_3820563 < baseStart_3820563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820614 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3820614 : Nat := 118140960795 + 3820614 * 2 ^ 59
def prefixEnd_3820614 : Nat := 4983230072969 + 3 ^ 40 * 3820614 * 2
def baseEnd_3820614 : Nat := 1307874251531346709236215

theorem tailTrace_3820614 : CollatzResearch.WordTrace tailWord_3820614 prefixEnd_3820614 1307874251531346709236215 := by
  unfold tailWord_3820614
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354663768142983180231903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92899493720383641178280597 4354663768142983180231903)
  ·
    refine ⟨6531995652214474770347855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4354663768142983180231903 6531995652214474770347855)
    ·
      refine ⟨9797993478321712155521783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6531995652214474770347855 9797993478321712155521783)
      ·
        refine ⟨14696990217482568233282675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9797993478321712155521783 14696990217482568233282675)
        ·
          refine ⟨22045485326223852349924013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14696990217482568233282675 22045485326223852349924013)
          ·
            refine ⟨8267056997333944631221505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22045485326223852349924013 8267056997333944631221505)
            ·
              refine ⟨6200292748000458473416129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8267056997333944631221505 6200292748000458473416129)
              ·
                refine ⟨4650219561000343855062097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6200292748000458473416129 4650219561000343855062097)
                ·
                  refine ⟨3487664670750257891296573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4650219561000343855062097 3487664670750257891296573)
                  ·
                    refine ⟨1307874251531346709236215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487664670750257891296573 1307874251531346709236215)
                    ·
                      rfl

theorem cell22_3820614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3820614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820614 prefixEnd_3820614 := by exact prefixLift 3820614
  have htrace : WordTrace (prefixWord ++ tailWord_3820614) baseStart_3820614 baseEnd_3820614 := by
    simpa [prefixWord, tailWord_3820614, baseEnd_3820614] using wordTrace_append hprefix tailTrace_3820614
  have hstable : (prefixWord ++ tailWord_3820614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820614).length < 2 ^ (prefixWord ++ tailWord_3820614).sum := by decide
  have hdescent : baseEnd_3820614 < baseStart_3820614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820642 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_3820642 : Nat := 118140960795 + 3820642 * 2 ^ 59
def prefixEnd_3820642 : Nat := 4983230072969 + 3 ^ 40 * 3820642 * 2
def baseEnd_3820642 : Nat := 1307883836503563969536129

theorem tailTrace_3820642 : CollatzResearch.WordTrace tailWord_3820642 prefixEnd_3820642 1307883836503563969536129 := by
  unfold tailWord_3820642
  simp only [CollatzResearch.WordTrace]
  refine ⟨34837565456118505637360045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92900174549649348366293453 34837565456118505637360045)
  ·
    refine ⟨13064087046044439614010017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34837565456118505637360045 13064087046044439614010017)
    ·
      refine ⟨9798065284533329710507513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13064087046044439614010017 9798065284533329710507513)
      ·
        refine ⟨7348548963399997282880635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9798065284533329710507513 7348548963399997282880635)
        ·
          refine ⟨11022823445099995924320953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7348548963399997282880635 11022823445099995924320953)
          ·
            refine ⟨8267117583824996943240715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11022823445099995924320953 8267117583824996943240715)
            ·
              refine ⟨12400676375737495414861073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267117583824996943240715 12400676375737495414861073)
              ·
                refine ⟨9300507281803121561145805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12400676375737495414861073 9300507281803121561145805)
                ·
                  refine ⟨3487690230676170585429677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9300507281803121561145805 3487690230676170585429677)
                  ·
                    refine ⟨1307883836503563969536129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3487690230676170585429677 1307883836503563969536129)
                    ·
                      rfl

theorem cell22_3820642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_3820642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820642 prefixEnd_3820642 := by exact prefixLift 3820642
  have htrace : WordTrace (prefixWord ++ tailWord_3820642) baseStart_3820642 baseEnd_3820642 := by
    simpa [prefixWord, tailWord_3820642, baseEnd_3820642] using wordTrace_append hprefix tailTrace_3820642
  have hstable : (prefixWord ++ tailWord_3820642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820642).length < 2 ^ (prefixWord ++ tailWord_3820642).sum := by decide
  have hdescent : baseEnd_3820642 < baseStart_3820642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820702 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_3820702 : Nat := 118140960795 + 3820702 * 2 ^ 59
def prefixEnd_3820702 : Nat := 4983230072969 + 3 ^ 40 * 3820702 * 2
def baseEnd_3820702 : Nat := 1307904375729743813035945

theorem tailTrace_3820702 : CollatzResearch.WordTrace tailWord_3820702 prefixEnd_3820702 1307904375729743813035945 := by
  unfold tailWord_3820702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419056275532081599578045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92901633469504435197749573 17419056275532081599578045)
  ·
    refine ⟨6532146103324530599841767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17419056275532081599578045 6532146103324530599841767)
    ·
      refine ⟨9798219154986795899762651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532146103324530599841767 9798219154986795899762651)
      ·
        refine ⟨14697328732480193849643977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798219154986795899762651 14697328732480193849643977)
        ·
          refine ⟨11022996549360145387232983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14697328732480193849643977 11022996549360145387232983)
          ·
            refine ⟨16534494824040218080849475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11022996549360145387232983 16534494824040218080849475)
            ·
              refine ⟨24801742236060327121274213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16534494824040218080849475 24801742236060327121274213)
              ·
                refine ⟨4650326669261311335238915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24801742236060327121274213 4650326669261311335238915)
                ·
                  refine ⟨6975490003891967002858373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650326669261311335238915 6975490003891967002858373)
                  ·
                    refine ⟨1307904375729743813035945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975490003891967002858373 1307904375729743813035945)
                    ·
                      rfl

theorem cell22_3820702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_3820702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820702 prefixEnd_3820702 := by exact prefixLift 3820702
  have htrace : WordTrace (prefixWord ++ tailWord_3820702) baseStart_3820702 baseEnd_3820702 := by
    simpa [prefixWord, tailWord_3820702, baseEnd_3820702] using wordTrace_append hprefix tailTrace_3820702
  have hstable : (prefixWord ++ tailWord_3820702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820702).length < 2 ^ (prefixWord ++ tailWord_3820702).sum := by decide
  have hdescent : baseEnd_3820702 < baseStart_3820702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820734 : List Nat := [4, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3820734 : Nat := 118140960795 + 3820734 * 2 ^ 59
def prefixEnd_3820734 : Nat := 4983230072969 + 3 ^ 40 * 3820734 * 2
def baseEnd_3820734 : Nat := 435971776661235465411949

theorem tailTrace_3820734 : CollatzResearch.WordTrace tailWord_3820734 prefixEnd_3820734 435971776661235465411949 := by
  unfold tailWord_3820734
  simp only [CollatzResearch.WordTrace]
  refine ⟨17419202167517590282723657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92902411560093814841192837 17419202167517590282723657)
  ·
    refine ⟨13064401625638192712042743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17419202167517590282723657 13064401625638192712042743)
    ·
      refine ⟨19596602438457289068064115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13064401625638192712042743 19596602438457289068064115)
      ·
        refine ⟨29394903657685933602096173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19596602438457289068064115 29394903657685933602096173)
        ·
          refine ⟨11023088871632225100786065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29394903657685933602096173 11023088871632225100786065)
          ·
            refine ⟨8267316653724168825589549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11023088871632225100786065 8267316653724168825589549)
            ·
              refine ⟨3100243745146563309596081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8267316653724168825589549 3100243745146563309596081)
              ·
                refine ⟨2325182808859922482197061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100243745146563309596081 2325182808859922482197061)
                ·
                  refine ⟨435971776661235465411949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325182808859922482197061 435971776661235465411949)
                  ·
                    rfl

theorem cell22_3820734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3820734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820734 prefixEnd_3820734 := by exact prefixLift 3820734
  have htrace : WordTrace (prefixWord ++ tailWord_3820734) baseStart_3820734 baseEnd_3820734 := by
    simpa [prefixWord, tailWord_3820734, baseEnd_3820734] using wordTrace_append hprefix tailTrace_3820734
  have hstable : (prefixWord ++ tailWord_3820734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820734).length < 2 ^ (prefixWord ++ tailWord_3820734).sum := by decide
  have hdescent : baseEnd_3820734 < baseStart_3820734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820837 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_3820837 : Nat := 118140960795 + 3820837 * 2 ^ 59
def prefixEnd_3820837 : Nat := 4983230072969 + 3 ^ 40 * 3820837 * 2
def baseEnd_3820837 : Nat := 1307950588988648460910531

theorem tailTrace_3820837 : CollatzResearch.WordTrace tailWord_3820837 prefixEnd_3820837 1307950588988648460910531 := by
  unfold tailWord_3820837
  simp only [CollatzResearch.WordTrace]
  refine ⟨139357374058767570852788765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92904916039178380568525843 139357374058767570852788765)
  ·
    refine ⟨52259015272037839069795787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139357374058767570852788765 52259015272037839069795787)
    ·
      refine ⟨78388522908056758604693681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52259015272037839069795787 78388522908056758604693681)
      ·
        refine ⟨58791392181042568953520261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78388522908056758604693681 58791392181042568953520261)
        ·
          refine ⟨11023386033945481678785049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58791392181042568953520261 11023386033945481678785049)
          ·
            refine ⟨8267539525459111259088787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11023386033945481678785049 8267539525459111259088787)
            ·
              refine ⟨12401309288188666888633181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8267539525459111259088787 12401309288188666888633181)
              ·
                refine ⟨4650490983070750083237443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12401309288188666888633181 4650490983070750083237443)
                ·
                  refine ⟨6975736474606125124856165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4650490983070750083237443 6975736474606125124856165)
                  ·
                    refine ⟨1307950588988648460910531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6975736474606125124856165 1307950588988648460910531)
                    ·
                      rfl

theorem cell22_3820837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_3820837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820837 prefixEnd_3820837 := by exact prefixLift 3820837
  have htrace : WordTrace (prefixWord ++ tailWord_3820837) baseStart_3820837 baseEnd_3820837 := by
    simpa [prefixWord, tailWord_3820837, baseEnd_3820837] using wordTrace_append hprefix tailTrace_3820837
  have hstable : (prefixWord ++ tailWord_3820837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820837).length < 2 ^ (prefixWord ++ tailWord_3820837).sum := by decide
  have hdescent : baseEnd_3820837 < baseStart_3820837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3820852 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_3820852 : Nat := 118140960795 + 3820852 * 2 ^ 59
def prefixEnd_3820852 : Nat := 4983230072969 + 3 ^ 40 * 3820852 * 2
def baseEnd_3820852 : Nat := 435985241265064473928495

theorem tailTrace_3820852 : CollatzResearch.WordTrace tailWord_3820852 prefixEnd_3820852 435985241265064473928495 := by
  unfold tailWord_3820852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69678960576856614207292405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92905280769142152276389873 69678960576856614207292405)
  ·
    refine ⟨6532402554080307581933663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69678960576856614207292405 6532402554080307581933663)
    ·
      refine ⟨9798603831120461372900495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6532402554080307581933663 9798603831120461372900495)
      ·
        refine ⟨14697905746680692059350743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9798603831120461372900495 14697905746680692059350743)
        ·
          refine ⟨22046858620021038089026115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14697905746680692059350743 22046858620021038089026115)
          ·
            refine ⟨33070287930031557133539173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22046858620021038089026115 33070287930031557133539173)
            ·
              refine ⟨6200678986880916962538595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33070287930031557133539173 6200678986880916962538595)
              ·
                refine ⟨9301018480321375443807893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6200678986880916962538595 9301018480321375443807893)
                ·
                  refine ⟨435985241265064473928495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9301018480321375443807893 435985241265064473928495)
                  ·
                    rfl

theorem cell22_3820852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_3820852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3820852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3820852 prefixEnd_3820852 := by exact prefixLift 3820852
  have htrace : WordTrace (prefixWord ++ tailWord_3820852) baseStart_3820852 baseEnd_3820852 := by
    simpa [prefixWord, tailWord_3820852, baseEnd_3820852] using wordTrace_append hprefix tailTrace_3820852
  have hstable : (prefixWord ++ tailWord_3820852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3820852).length < 2 ^ (prefixWord ++ tailWord_3820852).sum := by decide
  have hdescent : baseEnd_3820852 < baseStart_3820852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3820852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821002 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3821002 : Nat := 118140960795 + 3821002 * 2 ^ 59
def prefixEnd_3821002 : Nat := 4983230072969 + 3 ^ 40 * 3821002 * 2
def baseEnd_3821002 : Nat := 1308007071860643030535025

theorem tailTrace_3821002 : CollatzResearch.WordTrace tailWord_3821002 prefixEnd_3821002 1308007071860643030535025 := by
  unfold tailWord_3821002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34840848025792451008136315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92908928068779869355030173 34840848025792451008136315)
  ·
    refine ⟨52261272038688676512204473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34840848025792451008136315 52261272038688676512204473)
    ·
      refine ⟨39195954029016507384153355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52261272038688676512204473 39195954029016507384153355)
      ·
        refine ⟨58793931043524761076230033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39195954029016507384153355 58793931043524761076230033)
        ·
          refine ⟨44095448282643570807172525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58793931043524761076230033 44095448282643570807172525)
          ·
            refine ⟨16535793105991339052689697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44095448282643570807172525 16535793105991339052689697)
            ·
              refine ⟨12401844829493504289517273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16535793105991339052689697 12401844829493504289517273)
              ·
                refine ⟨9301383622120128217137955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12401844829493504289517273 9301383622120128217137955)
                ·
                  refine ⟨13952075433180192325706933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9301383622120128217137955 13952075433180192325706933)
                  ·
                    refine ⟨1308007071860643030535025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13952075433180192325706933 1308007071860643030535025)
                    ·
                      rfl

theorem cell22_3821002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3821002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821002 prefixEnd_3821002 := by exact prefixLift 3821002
  have htrace : WordTrace (prefixWord ++ tailWord_3821002) baseStart_3821002 baseEnd_3821002 := by
    simpa [prefixWord, tailWord_3821002, baseEnd_3821002] using wordTrace_append hprefix tailTrace_3821002
  have hstable : (prefixWord ++ tailWord_3821002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821002).length < 2 ^ (prefixWord ++ tailWord_3821002).sum := by decide
  have hdescent : baseEnd_3821002 < baseStart_3821002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821004 : List Nat := [2, 2, 1, 4, 2, 1, 1, 5, 4]
def baseStart_3821004 : Nat := 118140960795 + 3821004 * 2 ^ 59
def prefixEnd_3821004 : Nat := 4983230072969 + 3 ^ 40 * 3821004 * 2
def baseEnd_3821004 : Nat := 436002585500505230661673

theorem tailTrace_3821004 : CollatzResearch.WordTrace tailWord_3821004 prefixEnd_3821004 436002585500505230661673 := by
  unfold tailWord_3821004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69681732524581279187059033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92908976699441705582745377 69681732524581279187059033)
  ·
    refine ⟨52261299393435959390294275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69681732524581279187059033 52261299393435959390294275)
    ·
      refine ⟨78391949090153939085441413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52261299393435959390294275 78391949090153939085441413)
      ·
        refine ⟨14698490454403863578520265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78391949090153939085441413 14698490454403863578520265)
        ·
          refine ⟨11023867840802897683890199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14698490454403863578520265 11023867840802897683890199)
          ·
            refine ⟨16535801761204346525835299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11023867840802897683890199 16535801761204346525835299)
            ·
              refine ⟨24803702641806519788752949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16535801761204346525835299 24803702641806519788752949)
              ·
                refine ⟨2325347122669361230195589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24803702641806519788752949 2325347122669361230195589)
                ·
                  refine ⟨436002585500505230661673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325347122669361230195589 436002585500505230661673)
                  ·
                    rfl

theorem cell22_3821004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 5, 4].length) (baseStart_3821004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821004 prefixEnd_3821004 := by exact prefixLift 3821004
  have htrace : WordTrace (prefixWord ++ tailWord_3821004) baseStart_3821004 baseEnd_3821004 := by
    simpa [prefixWord, tailWord_3821004, baseEnd_3821004] using wordTrace_append hprefix tailTrace_3821004
  have hstable : (prefixWord ++ tailWord_3821004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821004).length < 2 ^ (prefixWord ++ tailWord_3821004).sum := by decide
  have hdescent : baseEnd_3821004 < baseStart_3821004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821047 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 5, 3]
def baseStart_3821047 : Nat := 118140960795 + 3821047 * 2 ^ 59
def prefixEnd_3821047 : Nat := 4983230072969 + 3 ^ 40 * 3821047 * 2
def baseEnd_3821047 : Nat := 1308022476280277913159887

theorem tailTrace_3821047 : CollatzResearch.WordTrace tailWord_3821047 prefixEnd_3821047 1308022476280277913159887 := by
  unfold tailWord_3821047
  simp only [CollatzResearch.WordTrace]
  refine ⟨139365033388006776717933395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92910022258671184478622263 139365033388006776717933395)
  ·
    refine ⟨209047550082010165076900093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139365033388006776717933395 209047550082010165076900093)
    ·
      refine ⟨78392831280753811903837535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209047550082010165076900093 78392831280753811903837535)
      ·
        refine ⟨117589246921130717855756303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78392831280753811903837535 117589246921130717855756303)
        ·
          refine ⟨176383870381696076783634455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117589246921130717855756303 176383870381696076783634455)
          ·
            refine ⟨264575805572544115175451683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176383870381696076783634455 264575805572544115175451683)
            ·
              refine ⟨396863708358816172763177525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264575805572544115175451683 396863708358816172763177525)
              ·
                refine ⟨37205972658639016196547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 396863708358816172763177525 37205972658639016196547893)
                ·
                  refine ⟨3488059936747407768426365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37205972658639016196547893 3488059936747407768426365)
                  ·
                    refine ⟨1308022476280277913159887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488059936747407768426365 1308022476280277913159887)
                    ·
                      rfl

theorem cell22_3821047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_3821047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821047 prefixEnd_3821047 := by exact prefixLift 3821047
  have htrace : WordTrace (prefixWord ++ tailWord_3821047) baseStart_3821047 baseEnd_3821047 := by
    simpa [prefixWord, tailWord_3821047, baseEnd_3821047] using wordTrace_append hprefix tailTrace_3821047
  have hstable : (prefixWord ++ tailWord_3821047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821047).length < 2 ^ (prefixWord ++ tailWord_3821047).sum := by decide
  have hdescent : baseEnd_3821047 < baseStart_3821047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821077 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 7]
def baseStart_3821077 : Nat := 118140960795 + 3821077 * 2 ^ 59
def prefixEnd_3821077 : Nat := 4983230072969 + 3 ^ 40 * 3821077 * 2
def baseEnd_3821077 : Nat := 436010915297789278303265

theorem tailTrace_3821077 : CollatzResearch.WordTrace tailWord_3821077 prefixEnd_3821077 436010915297789278303265 := by
  unfold tailWord_3821077
  simp only [CollatzResearch.WordTrace]
  refine ⟨139366127577898091841525485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92910751718598727894350323 139366127577898091841525485)
  ·
    refine ⟨52262297841711784440572057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139366127577898091841525485 52262297841711784440572057)
    ·
      refine ⟨39196723381283838330429043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52262297841711784440572057 39196723381283838330429043)
      ·
        refine ⟨58795085071925757495643565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39196723381283838330429043 58795085071925757495643565)
        ·
          refine ⟨22048156901972159060866337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58795085071925757495643565 22048156901972159060866337)
          ·
            refine ⟨16536117676479119295649753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22048156901972159060866337 16536117676479119295649753)
            ·
              refine ⟨12402088257359339471737315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16536117676479119295649753 12402088257359339471737315)
              ·
                refine ⟨18603132386039009207605973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12402088257359339471737315 18603132386039009207605973)
                ·
                  refine ⟨436010915297789278303265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18603132386039009207605973 436010915297789278303265)
                  ·
                    rfl

theorem cell22_3821077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_3821077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821077 prefixEnd_3821077 := by exact prefixLift 3821077
  have htrace : WordTrace (prefixWord ++ tailWord_3821077) baseStart_3821077 baseEnd_3821077 := by
    simpa [prefixWord, tailWord_3821077, baseEnd_3821077] using wordTrace_append hprefix tailTrace_3821077
  have hstable : (prefixWord ++ tailWord_3821077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821077).length < 2 ^ (prefixWord ++ tailWord_3821077).sum := by decide
  have hdescent : baseEnd_3821077 < baseStart_3821077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821137 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 3, 5]
def baseStart_3821137 : Nat := 118140960795 + 3821137 * 2 ^ 59
def prefixEnd_3821137 : Nat := 4983230072969 + 3 ^ 40 * 3821137 * 2
def baseEnd_3821137 : Nat := 1308053285119547678409611

theorem tailTrace_3821137 : CollatzResearch.WordTrace tailWord_3821137 prefixEnd_3821137 1308053285119547678409611 := by
  unfold tailWord_3821137
  simp only [CollatzResearch.WordTrace]
  refine ⟨139368315957680722088709665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92912210638453814725806443 139368315957680722088709665)
  ·
    refine ⟨104526236968260541566532249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139368315957680722088709665 104526236968260541566532249)
    ·
      refine ⟨78394677726195406174899187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104526236968260541566532249 78394677726195406174899187)
      ·
        refine ⟨117592016589293109262348781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78394677726195406174899187 117592016589293109262348781)
        ·
          refine ⟨44097006220984915973380793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117592016589293109262348781 44097006220984915973380793)
          ·
            refine ⟨33072754665738686980035595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44097006220984915973380793 33072754665738686980035595)
            ·
              refine ⟨49609131998608030470053393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33072754665738686980035595 49609131998608030470053393)
              ·
                refine ⟨37206848998956022852540045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49609131998608030470053393 37206848998956022852540045)
                ·
                  refine ⟨13952568374608508569702517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37206848998956022852540045 13952568374608508569702517)
                  ·
                    refine ⟨1308053285119547678409611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13952568374608508569702517 1308053285119547678409611)
                    ·
                      rfl

theorem cell22_3821137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3, 5].length) (baseStart_3821137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821137 prefixEnd_3821137 := by exact prefixLift 3821137
  have htrace : WordTrace (prefixWord ++ tailWord_3821137) baseStart_3821137 baseEnd_3821137 := by
    simpa [prefixWord, tailWord_3821137, baseEnd_3821137] using wordTrace_append hprefix tailTrace_3821137
  have hstable : (prefixWord ++ tailWord_3821137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821137).length < 2 ^ (prefixWord ++ tailWord_3821137).sum := by decide
  have hdescent : baseEnd_3821137 < baseStart_3821137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821152 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 1, 6]
def baseStart_3821152 : Nat := 118140960795 + 3821152 * 2 ^ 59
def prefixEnd_3821152 : Nat := 4983230072969 + 3 ^ 40 * 3821152 * 2
def baseEnd_3821152 : Nat := 1308058419926092639284565

theorem tailTrace_3821152 : CollatzResearch.WordTrace tailWord_3821152 prefixEnd_3821152 1308058419926092639284565 := by
  unfold tailWord_3821152
  simp only [CollatzResearch.WordTrace]
  refine ⟨69684431526313189825252855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92912575368417586433670473 69684431526313189825252855)
  ·
    refine ⟨104526647289469784737879283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69684431526313189825252855 104526647289469784737879283)
    ·
      refine ⟨156789970934204677106818925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104526647289469784737879283 156789970934204677106818925)
      ·
        refine ⟨58796239100326753915057097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156789970934204677106818925 58796239100326753915057097)
        ·
          refine ⟨44097179325245065436292823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58796239100326753915057097 44097179325245065436292823)
          ·
            refine ⟨66145768987867598154439235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44097179325245065436292823 66145768987867598154439235)
            ·
              refine ⟨99218653481801397231658853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66145768987867598154439235 99218653481801397231658853)
              ·
                refine ⟨18603497527837761980936035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99218653481801397231658853 18603497527837761980936035)
                ·
                  refine ⟨27905246291756642971404053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18603497527837761980936035 27905246291756642971404053)
                  ·
                    refine ⟨1308058419926092639284565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27905246291756642971404053 1308058419926092639284565)
                    ·
                      rfl

theorem cell22_3821152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_3821152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821152 prefixEnd_3821152 := by exact prefixLift 3821152
  have htrace : WordTrace (prefixWord ++ tailWord_3821152) baseStart_3821152 baseEnd_3821152 := by
    simpa [prefixWord, tailWord_3821152, baseEnd_3821152] using wordTrace_append hprefix tailTrace_3821152
  have hstable : (prefixWord ++ tailWord_3821152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821152).length < 2 ^ (prefixWord ++ tailWord_3821152).sum := by decide
  have hdescent : baseEnd_3821152 < baseStart_3821152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821173 : List Nat := [1, 3, 4, 2, 1, 2, 2, 3, 4]
def baseStart_3821173 : Nat := 118140960795 + 3821173 * 2 ^ 59
def prefixEnd_3821173 : Nat := 4983230072969 + 3 ^ 40 * 3821173 * 2
def baseEnd_3821173 : Nat := 436021869551751861503167

theorem tailTrace_3821173 : CollatzResearch.WordTrace tailWord_3821173 prefixEnd_3821173 436021869551751861503167 := by
  unfold tailWord_3821173
  simp only [CollatzResearch.WordTrace]
  refine ⟨139369628985550300237020173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92913085990366866824680115 139369628985550300237020173)
  ·
    refine ⟨52263610869581362588882565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139369628985550300237020173 52263610869581362588882565)
    ·
      refine ⟨9799427038046505485415481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52263610869581362588882565 9799427038046505485415481)
      ·
        refine ⟨7349570278534879114061611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9799427038046505485415481 7349570278534879114061611)
        ·
          refine ⟨11024355417802318671092417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7349570278534879114061611 11024355417802318671092417)
          ·
            refine ⟨8268266563351739003319313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11024355417802318671092417 8268266563351739003319313)
            ·
              refine ⟨6201199922513804252489485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268266563351739003319313 6201199922513804252489485)
              ·
                refine ⟨2325449970942676594683557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6201199922513804252489485 2325449970942676594683557)
                ·
                  refine ⟨436021869551751861503167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325449970942676594683557 436021869551751861503167)
                  ·
                    rfl

theorem cell22_3821173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_3821173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821173 prefixEnd_3821173 := by exact prefixLift 3821173
  have htrace : WordTrace (prefixWord ++ tailWord_3821173) baseStart_3821173 baseEnd_3821173 := by
    simpa [prefixWord, tailWord_3821173, baseEnd_3821173] using wordTrace_append hprefix tailTrace_3821173
  have hstable : (prefixWord ++ tailWord_3821173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821173).length < 2 ^ (prefixWord ++ tailWord_3821173).sum := by decide
  have hdescent : baseEnd_3821173 < baseStart_3821173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821216 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 3, 3]
def baseStart_3821216 : Nat := 118140960795 + 3821216 * 2 ^ 59
def prefixEnd_3821216 : Nat := 4983230072969 + 3 ^ 40 * 3821216 * 2
def baseEnd_3821216 : Nat := 1308080328434017805684369

theorem tailTrace_3821216 : CollatzResearch.WordTrace tailWord_3821216 prefixEnd_3821216 1308080328434017805684369 := by
  unfold tailWord_3821216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69685598662197259290417751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92914131549596345720557001 69685598662197259290417751)
  ·
    refine ⟨104528397993295888935626627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69685598662197259290417751 104528397993295888935626627)
    ·
      refine ⟨156792596989943833403439941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104528397993295888935626627 156792596989943833403439941)
      ·
        refine ⟨29398611935614468763144989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156792596989943833403439941 29398611935614468763144989)
        ·
          refine ⟨11024479475855425786179371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29398611935614468763144989 11024479475855425786179371)
          ·
            refine ⟨16536719213783138679269057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11024479475855425786179371 16536719213783138679269057)
            ·
              refine ⟨12402539410337354009451793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16536719213783138679269057 12402539410337354009451793)
              ·
                refine ⟨9301904557753015507088845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12402539410337354009451793 9301904557753015507088845)
                ·
                  refine ⟨3488214209157380815158317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9301904557753015507088845 3488214209157380815158317)
                  ·
                    refine ⟨1308080328434017805684369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488214209157380815158317 1308080328434017805684369)
                    ·
                      rfl

theorem cell22_3821216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_3821216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821216 prefixEnd_3821216 := by exact prefixLift 3821216
  have htrace : WordTrace (prefixWord ++ tailWord_3821216) baseStart_3821216 baseEnd_3821216 := by
    simpa [prefixWord, tailWord_3821216, baseEnd_3821216] using wordTrace_append hprefix tailTrace_3821216
  have hstable : (prefixWord ++ tailWord_3821216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821216).length < 2 ^ (prefixWord ++ tailWord_3821216).sum := by decide
  have hdescent : baseEnd_3821216 < baseStart_3821216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821224 : List Nat := [2, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_3821224 : Nat := 118140960795 + 3821224 * 2 ^ 59
def prefixEnd_3821224 : Nat := 4983230072969 + 3 ^ 40 * 3821224 * 2
def baseEnd_3821224 : Nat := 436027688999169483828115

theorem tailTrace_3821224 : CollatzResearch.WordTrace tailWord_3821224 prefixEnd_3821224 436027688999169483828115 := by
  unfold tailWord_3821224
  simp only [CollatzResearch.WordTrace]
  refine ⟨69685744554182767973563363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92914326072243690631417817 69685744554182767973563363)
  ·
    refine ⟨104528616831274151960345045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69685744554182767973563363 104528616831274151960345045)
    ·
      refine ⟨2449889456982987936570587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 104528616831274151960345045 2449889456982987936570587)
      ·
        refine ⟨3674834185474481904855881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2449889456982987936570587 3674834185474481904855881)
        ·
          refine ⟨2756125639105861428641911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3674834185474481904855881 2756125639105861428641911)
          ·
            refine ⟨4134188458658792142962867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756125639105861428641911 4134188458658792142962867)
            ·
              refine ⟨6201282687988188214444301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134188458658792142962867 6201282687988188214444301)
              ·
                refine ⟨2325481007995570580416613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6201282687988188214444301 2325481007995570580416613)
                ·
                  refine ⟨436027688999169483828115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2325481007995570580416613 436027688999169483828115)
                  ·
                    rfl

theorem cell22_3821224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_3821224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821224 prefixEnd_3821224 := by exact prefixLift 3821224
  have htrace : WordTrace (prefixWord ++ tailWord_3821224) baseStart_3821224 baseEnd_3821224 := by
    simpa [prefixWord, tailWord_3821224, baseEnd_3821224] using wordTrace_append hprefix tailTrace_3821224
  have hstable : (prefixWord ++ tailWord_3821224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821224).length < 2 ^ (prefixWord ++ tailWord_3821224).sum := by decide
  have hdescent : baseEnd_3821224 < baseStart_3821224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821229 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 9]
def baseStart_3821229 : Nat := 118140960795 + 3821229 * 2 ^ 59
def prefixEnd_3821229 : Nat := 4983230072969 + 3 ^ 40 * 3821229 * 2
def baseEnd_3821229 : Nat := 436028259533230035036443

theorem tailTrace_3821229 : CollatzResearch.WordTrace tailWord_3821229 prefixEnd_3821229 436028259533230035036443 := by
  unfold tailWord_3821229
  simp only [CollatzResearch.WordTrace]
  refine ⟨139371671473347421801058741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92914447648898281200705827 139371671473347421801058741)
  ·
    refine ⟨13066094200626320793849257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139371671473347421801058741 13066094200626320793849257)
    ·
      refine ⟨9799570650469740595386943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13066094200626320793849257 9799570650469740595386943)
      ·
        refine ⟨14699355975704610893080415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9799570650469740595386943 14699355975704610893080415)
        ·
          refine ⟨22049033963556916339620623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14699355975704610893080415 22049033963556916339620623)
          ·
            refine ⟨33073550945335374509430935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22049033963556916339620623 33073550945335374509430935)
            ·
              refine ⟨49610326418003061764146403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33073550945335374509430935 49610326418003061764146403)
              ·
                refine ⟨74415489627004592646219605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49610326418003061764146403 74415489627004592646219605)
                ·
                  refine ⟨436028259533230035036443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74415489627004592646219605 436028259533230035036443)
                  ·
                    rfl

theorem cell22_3821229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_3821229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821229 prefixEnd_3821229 := by exact prefixLift 3821229
  have htrace : WordTrace (prefixWord ++ tailWord_3821229) baseStart_3821229 baseEnd_3821229 := by
    simpa [prefixWord, tailWord_3821229, baseEnd_3821229] using wordTrace_append hprefix tailTrace_3821229
  have hstable : (prefixWord ++ tailWord_3821229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821229).length < 2 ^ (prefixWord ++ tailWord_3821229).sum := by decide
  have hdescent : baseEnd_3821229 < baseStart_3821229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821304 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 4, 4]
def baseStart_3821304 : Nat := 118140960795 + 3821304 * 2 ^ 59
def prefixEnd_3821304 : Nat := 4983230072969 + 3 ^ 40 * 3821304 * 2
def baseEnd_3821304 : Nat := 1308110452632414909484099

theorem tailTrace_3821304 : CollatzResearch.WordTrace tailWord_3821304 prefixEnd_3821304 1308110452632414909484099 := by
  unfold tailWord_3821304
  simp only [CollatzResearch.WordTrace]
  refine ⟨69687203474037854805019483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92916271298717139740025977 69687203474037854805019483)
  ·
    refine ⟨104530805211056782207529225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69687203474037854805019483 104530805211056782207529225)
    ·
      refine ⟨78398103908292586655646919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104530805211056782207529225 78398103908292586655646919)
      ·
        refine ⟨117597155862438879983470379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78398103908292586655646919 117597155862438879983470379)
        ·
          refine ⟨176395733793658319975205569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117597155862438879983470379 176395733793658319975205569)
          ·
            refine ⟨132296800345243739981404177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176395733793658319975205569 132296800345243739981404177)
            ·
              refine ⟨99222600258932804986053133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132296800345243739981404177 99222600258932804986053133)
              ·
                refine ⟨37208475097099801869769925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99222600258932804986053133 37208475097099801869769925)
                ·
                  refine ⟨6976589080706212850581861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37208475097099801869769925 6976589080706212850581861)
                  ·
                    refine ⟨1308110452632414909484099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976589080706212850581861 1308110452632414909484099)
                    ·
                      rfl

theorem cell22_3821304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_3821304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821304 prefixEnd_3821304 := by exact prefixLift 3821304
  have htrace : WordTrace (prefixWord ++ tailWord_3821304) baseStart_3821304 baseEnd_3821304 := by
    simpa [prefixWord, tailWord_3821304, baseEnd_3821304] using wordTrace_append hprefix tailTrace_3821304
  have hstable : (prefixWord ++ tailWord_3821304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821304).length < 2 ^ (prefixWord ++ tailWord_3821304).sum := by decide
  have hdescent : baseEnd_3821304 < baseStart_3821304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821338 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 2, 4]
def baseStart_3821338 : Nat := 118140960795 + 3821338 * 2 ^ 59
def prefixEnd_3821338 : Nat := 4983230072969 + 3 ^ 40 * 3821338 * 2
def baseEnd_3821338 : Nat := 1308122091527250154133995

theorem tailTrace_3821338 : CollatzResearch.WordTrace tailWord_3821338 prefixEnd_3821338 1308122091527250154133995 := by
  unfold tailWord_3821338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34843911757488133354194167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92917098019968355611184445 34843911757488133354194167)
  ·
    refine ⟨52265867636232200031291251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34843911757488133354194167 52265867636232200031291251)
    ·
      refine ⟨78398801454348300046936877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52265867636232200031291251 78398801454348300046936877)
      ·
        refine ⟨29399550545380612517601329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78398801454348300046936877 29399550545380612517601329)
        ·
          refine ⟨22049662909035459388200997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29399550545380612517601329 22049662909035459388200997)
          ·
            refine ⟨4134311795444148635287687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22049662909035459388200997 4134311795444148635287687)
            ·
              refine ⟨6201467693166222952931531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134311795444148635287687 6201467693166222952931531)
              ·
                refine ⟨9302201539749334429397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201467693166222952931531 9302201539749334429397297)
                ·
                  refine ⟨6976651154812000822047973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302201539749334429397297 6976651154812000822047973)
                  ·
                    refine ⟨1308122091527250154133995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976651154812000822047973 1308122091527250154133995)
                    ·
                      rfl

theorem cell22_3821338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_3821338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821338 prefixEnd_3821338 := by exact prefixLift 3821338
  have htrace : WordTrace (prefixWord ++ tailWord_3821338) baseStart_3821338 baseEnd_3821338 := by
    simpa [prefixWord, tailWord_3821338, baseEnd_3821338] using wordTrace_append hprefix tailTrace_3821338
  have hstable : (prefixWord ++ tailWord_3821338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821338).length < 2 ^ (prefixWord ++ tailWord_3821338).sum := by decide
  have hdescent : baseEnd_3821338 < baseStart_3821338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821368 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 3, 3]
def baseStart_3821368 : Nat := 118140960795 + 3821368 * 2 ^ 59
def prefixEnd_3821368 : Nat := 4983230072969 + 3 ^ 40 * 3821368 * 2
def baseEnd_3821368 : Nat := 1308132361140340075883903

theorem tailTrace_3821368 : CollatzResearch.WordTrace tailWord_3821368 prefixEnd_3821368 1308132361140340075883903 := by
  unfold tailWord_3821368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69688370609921924270184379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92917827479895899026912505 69688370609921924270184379)
  ·
    refine ⟨104532555914882886405276569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69688370609921924270184379 104532555914882886405276569)
    ·
      refine ⟨78399416936162164803957427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104532555914882886405276569 78399416936162164803957427)
      ·
        refine ⟨117599125404243247205936141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78399416936162164803957427 117599125404243247205936141)
        ·
          refine ⟨44099672026591217702226053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117599125404243247205936141 44099672026591217702226053)
          ·
            refine ⟨8268688504985853319167385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44099672026591217702226053 8268688504985853319167385)
            ·
              refine ⟨6201516378739389989375539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268688504985853319167385 6201516378739389989375539)
              ·
                refine ⟨9302274568109084984063309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201516378739389989375539 9302274568109084984063309)
                ·
                  refine ⟨3488352963040906869023741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302274568109084984063309 3488352963040906869023741)
                  ·
                    refine ⟨1308132361140340075883903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488352963040906869023741 1308132361140340075883903)
                    ·
                      rfl

theorem cell22_3821368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_3821368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821368 prefixEnd_3821368 := by exact prefixLift 3821368
  have htrace : WordTrace (prefixWord ++ tailWord_3821368) baseStart_3821368 baseEnd_3821368 := by
    simpa [prefixWord, tailWord_3821368, baseEnd_3821368] using wordTrace_append hprefix tailTrace_3821368
  have hstable : (prefixWord ++ tailWord_3821368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821368).length < 2 ^ (prefixWord ++ tailWord_3821368).sum := by decide
  have hdescent : baseEnd_3821368 < baseStart_3821368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821456 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 2, 4]
def baseStart_3821456 : Nat := 118140960795 + 3821456 * 2 ^ 59
def prefixEnd_3821456 : Nat := 4983230072969 + 3 ^ 40 * 3821456 * 2
def baseEnd_3821456 : Nat := 1308162485338737179683633

theorem tailTrace_3821456 : CollatzResearch.WordTrace tailWord_3821456 prefixEnd_3821456 1308162485338737179683633 := by
  unfold tailWord_3821456
  simp only [CollatzResearch.WordTrace]
  refine ⟨69689975421762519784786111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92919967229016693046381481 69689975421762519784786111)
  ·
    refine ⟨104534963132643779677179167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69689975421762519784786111 104534963132643779677179167)
    ·
      refine ⟨156802444698965669515768751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104534963132643779677179167 156802444698965669515768751)
      ·
        refine ⟨235203667048448504273653127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156802444698965669515768751 235203667048448504273653127)
        ·
          refine ⟨352805500572672756410479691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235203667048448504273653127 352805500572672756410479691)
          ·
            refine ⟨529208250859009134615719537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352805500572672756410479691 529208250859009134615719537)
            ·
              refine ⟨396906188144256850961789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 529208250859009134615719537 396906188144256850961789653)
              ·
                refine ⟨9302488784631019944416945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 396906188144256850961789653 9302488784631019944416945)
                ·
                  refine ⟨6976866588473264958312709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9302488784631019944416945 6976866588473264958312709)
                  ·
                    refine ⟨1308162485338737179683633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6976866588473264958312709 1308162485338737179683633)
                    ·
                      rfl

theorem cell22_3821456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_3821456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821456 prefixEnd_3821456 := by exact prefixLift 3821456
  have htrace : WordTrace (prefixWord ++ tailWord_3821456) baseStart_3821456 baseEnd_3821456 := by
    simpa [prefixWord, tailWord_3821456, baseEnd_3821456] using wordTrace_append hprefix tailTrace_3821456
  have hstable : (prefixWord ++ tailWord_3821456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821456).length < 2 ^ (prefixWord ++ tailWord_3821456).sum := by decide
  have hdescent : baseEnd_3821456 < baseStart_3821456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821458 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_3821458 : Nat := 118140960795 + 3821458 * 2 ^ 59
def prefixEnd_3821458 : Nat := 4983230072969 + 3 ^ 40 * 3821458 * 2
def baseEnd_3821458 : Nat := 1308163169979609841133627

theorem tailTrace_3821458 : CollatzResearch.WordTrace tailWord_3821458 prefixEnd_3821458 1308163169979609841133627 := by
  unfold tailWord_3821458
  simp only [CollatzResearch.WordTrace]
  refine ⟨34845005947379448477786257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92920015859678529274096685 34845005947379448477786257)
  ·
    refine ⟨26133754460534586358339693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34845005947379448477786257 26133754460534586358339693)
    ·
      refine ⟨9800157922700469884377385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26133754460534586358339693 9800157922700469884377385)
      ·
        refine ⟨7350118442025352413283039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9800157922700469884377385 7350118442025352413283039)
        ·
          refine ⟨11025177663038028619924559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7350118442025352413283039 11025177663038028619924559)
          ·
            refine ⟨16537766494557042929886839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11025177663038028619924559 16537766494557042929886839)
            ·
              refine ⟨24806649741835564394830259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16537766494557042929886839 24806649741835564394830259)
              ·
                refine ⟨37209974612753346592245389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24806649741835564394830259 37209974612753346592245389)
                ·
                  refine ⟨13953740479782504972092021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37209974612753346592245389 13953740479782504972092021)
                  ·
                    refine ⟨1308163169979609841133627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13953740479782504972092021 1308163169979609841133627)
                    ·
                      rfl

theorem cell22_3821458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_3821458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821458 prefixEnd_3821458 := by exact prefixLift 3821458
  have htrace : WordTrace (prefixWord ++ tailWord_3821458) baseStart_3821458 baseEnd_3821458 := by
    simpa [prefixWord, tailWord_3821458, baseEnd_3821458] using wordTrace_append hprefix tailTrace_3821458
  have hstable : (prefixWord ++ tailWord_3821458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821458).length < 2 ^ (prefixWord ++ tailWord_3821458).sum := by decide
  have hdescent : baseEnd_3821458 < baseStart_3821458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821471 : List Nat := [1, 1, 2, 5, 3, 10]
def baseStart_3821471 : Nat := 118140960795 + 3821471 * 2 ^ 59
def prefixEnd_3821471 : Nat := 4983230072969 + 3 ^ 40 * 3821471 * 2
def baseEnd_3821471 : Nat := 16150217532657804204427

theorem tailTrace_3821471 : CollatzResearch.WordTrace tailWord_3821471 prefixEnd_3821471 16150217532657804204427 := by
  unfold tailWord_3821471
  simp only [CollatzResearch.WordTrace]
  refine ⟨139380497938470697131368267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92920331958980464754245511 139380497938470697131368267)
  ·
    refine ⟨209070746907706045697052401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139380497938470697131368267 209070746907706045697052401)
    ·
      refine ⟨156803060180779534272789301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209070746907706045697052401 156803060180779534272789301)
      ·
        refine ⟨14700286891948081338073997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156803060180779534272789301 14700286891948081338073997)
        ·
          refine ⟨5512607584480530501777749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14700286891948081338073997 5512607584480530501777749)
          ·
            refine ⟨16150217532657804204427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5512607584480530501777749 16150217532657804204427)
            ·
              rfl

theorem cell22_3821471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 10].length) (baseStart_3821471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821471 prefixEnd_3821471 := by exact prefixLift 3821471
  have htrace : WordTrace (prefixWord ++ tailWord_3821471) baseStart_3821471 baseEnd_3821471 := by
    simpa [prefixWord, tailWord_3821471, baseEnd_3821471] using wordTrace_append hprefix tailTrace_3821471
  have hstable : (prefixWord ++ tailWord_3821471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821471).length < 2 ^ (prefixWord ++ tailWord_3821471).sum := by decide
  have hdescent : baseEnd_3821471 < baseStart_3821471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821492 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3821492 : Nat := 118140960795 + 3821492 * 2 ^ 59
def prefixEnd_3821492 : Nat := 4983230072969 + 3 ^ 40 * 3821492 * 2
def baseEnd_3821492 : Nat := 1308174808874445085783523

theorem tailTrace_3821492 : CollatzResearch.WordTrace tailWord_3821492 prefixEnd_3821492 1308174808874445085783523 := by
  unfold tailWord_3821492
  simp only [CollatzResearch.WordTrace]
  refine ⟨69690631935697308858941365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92920842580929745145255153 69690631935697308858941365)
  ·
    refine ⟨6533496743971622705525753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69690631935697308858941365 6533496743971622705525753)
    ·
      refine ⟨4900122557978717029144315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6533496743971622705525753 4900122557978717029144315)
      ·
        refine ⟨7350183836968075543716473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4900122557978717029144315 7350183836968075543716473)
        ·
          refine ⟨5512637877726056657787355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7350183836968075543716473 5512637877726056657787355)
          ·
            refine ⟨8268956816589084986681033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512637877726056657787355 8268956816589084986681033)
            ·
              refine ⟨6201717612441813740010775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8268956816589084986681033 6201717612441813740010775)
              ·
                refine ⟨9302576418662720610016163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6201717612441813740010775 9302576418662720610016163)
                ·
                  refine ⟨13953864627994080915024245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9302576418662720610016163 13953864627994080915024245)
                  ·
                    refine ⟨1308174808874445085783523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13953864627994080915024245 1308174808874445085783523)
                    ·
                      rfl

theorem cell22_3821492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3821492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821492 prefixEnd_3821492 := by exact prefixLift 3821492
  have htrace : WordTrace (prefixWord ++ tailWord_3821492) baseStart_3821492 baseEnd_3821492 := by
    simpa [prefixWord, tailWord_3821492, baseEnd_3821492] using wordTrace_append hprefix tailTrace_3821492
  have hstable : (prefixWord ++ tailWord_3821492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821492).length < 2 ^ (prefixWord ++ tailWord_3821492).sum := by decide
  have hdescent : baseEnd_3821492 < baseStart_3821492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821503 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 3, 3]
def baseStart_3821503 : Nat := 118140960795 + 3821503 * 2 ^ 59
def prefixEnd_3821503 : Nat := 4983230072969 + 3 ^ 40 * 3821503 * 2
def baseEnd_3821503 : Nat := 1308178574399244723758489

theorem tailTrace_3821503 : CollatzResearch.WordTrace tailWord_3821503 prefixEnd_3821503 1308178574399244723758489 := by
  unfold tailWord_3821503
  simp only [CollatzResearch.WordTrace]
  refine ⟨139381665074354766596533163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92921110049569844397688775 139381665074354766596533163)
  ·
    refine ⟨209072497611532149894799745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139381665074354766596533163 209072497611532149894799745)
    ·
      refine ⟨156804373208649112421099809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209072497611532149894799745 156804373208649112421099809)
      ·
        refine ⟨117603279906486834315824857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156804373208649112421099809 117603279906486834315824857)
        ·
          refine ⟨88202459929865125736868643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117603279906486834315824857 88202459929865125736868643)
          ·
            refine ⟨132303689894797688605302965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88202459929865125736868643 132303689894797688605302965)
            ·
              refine ⟨12403470927637283306747153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132303689894797688605302965 12403470927637283306747153)
              ·
                refine ⟨9302603195727962480060365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12403470927637283306747153 9302603195727962480060365)
                ·
                  refine ⟨3488476198397985930022637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9302603195727962480060365 3488476198397985930022637)
                  ·
                    refine ⟨1308178574399244723758489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488476198397985930022637 1308178574399244723758489)
                    ·
                      rfl

theorem cell22_3821503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 3, 3].length) (baseStart_3821503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821503 prefixEnd_3821503 := by exact prefixLift 3821503
  have htrace : WordTrace (prefixWord ++ tailWord_3821503) baseStart_3821503 baseEnd_3821503 := by
    simpa [prefixWord, tailWord_3821503, baseEnd_3821503] using wordTrace_append hprefix tailTrace_3821503
  have hstable : (prefixWord ++ tailWord_3821503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821503).length < 2 ^ (prefixWord ++ tailWord_3821503).sum := by decide
  have hdescent : baseEnd_3821503 < baseStart_3821503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821520 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 1, 3]
def baseStart_3821520 : Nat := 118140960795 + 3821520 * 2 ^ 59
def prefixEnd_3821520 : Nat := 4983230072969 + 3 ^ 40 * 3821520 * 2
def baseEnd_3821520 : Nat := 1308184393846662346083437

theorem tailTrace_3821520 : CollatzResearch.WordTrace tailWord_3821520 prefixEnd_3821520 1308184393846662346083437 := by
  unfold tailWord_3821520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69691142557646589249951007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92921523410195452333268009 69691142557646589249951007)
  ·
    refine ⟨104536713836469883874926511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69691142557646589249951007 104536713836469883874926511)
    ·
      refine ⟨156805070754704825812389767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104536713836469883874926511 156805070754704825812389767)
      ·
        refine ⟨235207606132057238718584651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156805070754704825812389767 235207606132057238718584651)
        ·
          refine ⟨352811409198085858077876977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235207606132057238718584651 352811409198085858077876977)
          ·
            refine ⟨264608556898564393558407733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 352811409198085858077876977 264608556898564393558407733)
            ·
              refine ⟨24807052209240411896100725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264608556898564393558407733 24807052209240411896100725)
              ·
                refine ⟨2325661144616288615259443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24807052209240411896100725 2325661144616288615259443)
                ·
                  refine ⟨3488491716924432922889165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325661144616288615259443 3488491716924432922889165)
                  ·
                    refine ⟨1308184393846662346083437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488491716924432922889165 1308184393846662346083437)
                    ·
                      rfl

theorem cell22_3821520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 1, 3].length) (baseStart_3821520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821520 prefixEnd_3821520 := by exact prefixLift 3821520
  have htrace : WordTrace (prefixWord ++ tailWord_3821520) baseStart_3821520 baseEnd_3821520 := by
    simpa [prefixWord, tailWord_3821520, baseEnd_3821520] using wordTrace_append hprefix tailTrace_3821520
  have hstable : (prefixWord ++ tailWord_3821520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821520).length < 2 ^ (prefixWord ++ tailWord_3821520).sum := by decide
  have hdescent : baseEnd_3821520 < baseStart_3821520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821526 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_3821526 : Nat := 118140960795 + 3821526 * 2 ^ 59
def prefixEnd_3821526 : Nat := 4983230072969 + 3 ^ 40 * 3821526 * 2
def baseEnd_3821526 : Nat := 1308186447769280330433419

theorem tailTrace_3821526 : CollatzResearch.WordTrace tailWord_3821526 prefixEnd_3821526 1308186447769280330433419 := by
  unfold tailWord_3821526
  simp only [CollatzResearch.WordTrace]
  refine ⟨8711406497079465095288777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92921669302180961016413621 8711406497079465095288777)
  ·
    refine ⟨6533554872809598821466583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8711406497079465095288777 6533554872809598821466583)
    ·
      refine ⟨9800332309214398232199875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6533554872809598821466583 9800332309214398232199875)
      ·
        refine ⟨14700498463821597348299813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9800332309214398232199875 14700498463821597348299813)
        ·
          refine ⟨2756343461966549502806215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14700498463821597348299813 2756343461966549502806215)
          ·
            refine ⟨4134515192949824254209323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756343461966549502806215 4134515192949824254209323)
            ·
              refine ⟨6201772789424736381313985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4134515192949824254209323 6201772789424736381313985)
              ·
                refine ⟨4651329592068552285985489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6201772789424736381313985 4651329592068552285985489)
                ·
                  refine ⟨3488497194051414214489117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4651329592068552285985489 3488497194051414214489117)
                  ·
                    refine ⟨1308186447769280330433419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488497194051414214489117 1308186447769280330433419)
                    ·
                      rfl

theorem cell22_3821526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_3821526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821526 prefixEnd_3821526 := by exact prefixLift 3821526
  have htrace : WordTrace (prefixWord ++ tailWord_3821526) baseStart_3821526 baseEnd_3821526 := by
    simpa [prefixWord, tailWord_3821526, baseEnd_3821526] using wordTrace_append hprefix tailTrace_3821526
  have hstable : (prefixWord ++ tailWord_3821526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821526).length < 2 ^ (prefixWord ++ tailWord_3821526).sum := by decide
  have hdescent : baseEnd_3821526 < baseStart_3821526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821563 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 1, 4]
def baseStart_3821563 : Nat := 118140960795 + 3821563 * 2 ^ 59
def prefixEnd_3821563 : Nat := 4983230072969 + 3 ^ 40 * 3821563 * 2
def baseEnd_3821563 : Nat := 1308199113625424567258305

theorem tailTrace_3821563 : CollatzResearch.WordTrace tailWord_3821563 prefixEnd_3821563 1308199113625424567258305 := by
  unfold tailWord_3821563
  simp only [CollatzResearch.WordTrace]
  refine ⟨139383853454137396843717343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92922568969424931229144895 139383853454137396843717343)
  ·
    refine ⟨209075780181206095265576015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139383853454137396843717343 209075780181206095265576015)
    ·
      refine ⟨313613670271809142898364023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209075780181206095265576015 313613670271809142898364023)
      ·
        refine ⟨470420505407713714347546035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313613670271809142898364023 470420505407713714347546035)
        ·
          refine ⟨705630758111570571521319053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470420505407713714347546035 705630758111570571521319053)
          ·
            refine ⟨264611534291838964320494645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 705630758111570571521319053 264611534291838964320494645)
            ·
              refine ⟨24807331339859902905046373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 264611534291838964320494645 24807331339859902905046373)
              ·
                refine ⟨4651374626223731794696195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24807331339859902905046373 4651374626223731794696195)
                ·
                  refine ⟨6977061939335597692044293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651374626223731794696195 6977061939335597692044293)
                  ·
                    refine ⟨1308199113625424567258305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977061939335597692044293 1308199113625424567258305)
                    ·
                      rfl

theorem cell22_3821563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 4].length) (baseStart_3821563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821563 prefixEnd_3821563 := by exact prefixLift 3821563
  have htrace : WordTrace (prefixWord ++ tailWord_3821563) baseStart_3821563 baseEnd_3821563 := by
    simpa [prefixWord, tailWord_3821563, baseEnd_3821563] using wordTrace_append hprefix tailTrace_3821563
  have hstable : (prefixWord ++ tailWord_3821563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821563).length < 2 ^ (prefixWord ++ tailWord_3821563).sum := by decide
  have hdescent : baseEnd_3821563 < baseStart_3821563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821588 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3821588 : Nat := 118140960795 + 3821588 * 2 ^ 59
def prefixEnd_3821588 : Nat := 4983230072969 + 3 ^ 40 * 3821588 * 2
def baseEnd_3821588 : Nat := 1308207671636332835383229

theorem tailTrace_3821588 : CollatzResearch.WordTrace tailWord_3821588 prefixEnd_3821588 1308207671636332835383229 := by
  unfold tailWord_3821588
  simp only [CollatzResearch.WordTrace]
  refine ⟨69692382639523413056688709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92923176852697884075584945 69692382639523413056688709)
  ·
    refine ⟨13067321744910639948129133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69692382639523413056688709 13067321744910639948129133)
    ·
      refine ⟨4900245654341489980548425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13067321744910639948129133 4900245654341489980548425)
      ·
        refine ⟨3675184240756117485411319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4900245654341489980548425 3675184240756117485411319)
        ·
          refine ⟨5512776361134176228116979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3675184240756117485411319 5512776361134176228116979)
          ·
            refine ⟨8269164541701264342175469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5512776361134176228116979 8269164541701264342175469)
            ·
              refine ⟨3100936703137974128315801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8269164541701264342175469 3100936703137974128315801)
              ·
                refine ⟨2325702527353480596236851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3100936703137974128315801 2325702527353480596236851)
                ·
                  refine ⟨3488553791030220894355277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325702527353480596236851 3488553791030220894355277)
                  ·
                    refine ⟨1308207671636332835383229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488553791030220894355277 1308207671636332835383229)
                    ·
                      rfl

theorem cell22_3821588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3821588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821588 prefixEnd_3821588 := by exact prefixLift 3821588
  have htrace : WordTrace (prefixWord ++ tailWord_3821588) baseStart_3821588 baseEnd_3821588 := by
    simpa [prefixWord, tailWord_3821588, baseEnd_3821588] using wordTrace_append hprefix tailTrace_3821588
  have hstable : (prefixWord ++ tailWord_3821588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821588).length < 2 ^ (prefixWord ++ tailWord_3821588).sum := by decide
  have hdescent : baseEnd_3821588 < baseStart_3821588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821653 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 2, 6]
def baseStart_3821653 : Nat := 118140960795 + 3821653 * 2 ^ 59
def prefixEnd_3821653 : Nat := 4983230072969 + 3 ^ 40 * 3821653 * 2
def baseEnd_3821653 : Nat := 1308229922464694332508029

theorem tailTrace_3821653 : CollatzResearch.WordTrace tailWord_3821653 prefixEnd_3821653 1308229922464694332508029 := by
  unfold tailWord_3821653
  simp only [CollatzResearch.WordTrace]
  refine ⟨139387136023811342214493613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92924757349207561476329075 139387136023811342214493613)
  ·
    refine ⟨52270176008929253330435105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139387136023811342214493613 52270176008929253330435105)
    ·
      refine ⟨39202632006696939997826329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52270176008929253330435105 39202632006696939997826329)
      ·
        refine ⟨29401974005022704998369747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39202632006696939997826329 29401974005022704998369747)
        ·
          refine ⟨44102961007534057497554621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29401974005022704998369747 44102961007534057497554621)
          ·
            refine ⟨16538610377825271561582983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44102961007534057497554621 16538610377825271561582983)
            ·
              refine ⟨24807915566737907342374475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16538610377825271561582983 24807915566737907342374475)
              ·
                refine ⟨37211873350106861013561713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24807915566737907342374475 37211873350106861013561713)
                ·
                  refine ⟨27908905012580145760171285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37211873350106861013561713 27908905012580145760171285)
                  ·
                    refine ⟨1308229922464694332508029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27908905012580145760171285 1308229922464694332508029)
                    ·
                      rfl

theorem cell22_3821653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_3821653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821653 prefixEnd_3821653 := by exact prefixLift 3821653
  have htrace : WordTrace (prefixWord ++ tailWord_3821653) baseStart_3821653 baseEnd_3821653 := by
    simpa [prefixWord, tailWord_3821653, baseEnd_3821653] using wordTrace_append hprefix tailTrace_3821653
  have hstable : (prefixWord ++ tailWord_3821653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821653).length < 2 ^ (prefixWord ++ tailWord_3821653).sum := by decide
  have hdescent : baseEnd_3821653 < baseStart_3821653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821689 : List Nat := [1, 2, 1, 3, 4, 2, 2, 3, 1, 3]
def baseStart_3821689 : Nat := 118140960795 + 3821689 * 2 ^ 59
def prefixEnd_3821689 : Nat := 4983230072969 + 3 ^ 40 * 3821689 * 2
def baseEnd_3821689 : Nat := 1308242246000402238607919

theorem tailTrace_3821689 : CollatzResearch.WordTrace tailWord_3821689 prefixEnd_3821689 1308242246000402238607919 := by
  unfold tailWord_3821689
  simp only [CollatzResearch.WordTrace]
  refine ⟨139388449051680920362804121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92925632701120613575202747 139388449051680920362804121)
  ·
    refine ⟨104541336788760690272103091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139388449051680920362804121 104541336788760690272103091)
    ·
      refine ⟨156812005183141035408154637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104541336788760690272103091 156812005183141035408154637)
      ·
        refine ⟨58804501943677888278057989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156812005183141035408154637 58804501943677888278057989)
        ·
          refine ⟨11025844114439604052135873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58804501943677888278057989 11025844114439604052135873)
          ·
            refine ⟨8269383085829703039101905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11025844114439604052135873 8269383085829703039101905)
            ·
              refine ⟨6202037314372277279326429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269383085829703039101905 6202037314372277279326429)
              ·
                refine ⟨2325763992889603979747411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6202037314372277279326429 2325763992889603979747411)
                ·
                  refine ⟨3488645989334405969621117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2325763992889603979747411 3488645989334405969621117)
                  ·
                    refine ⟨1308242246000402238607919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488645989334405969621117 1308242246000402238607919)
                    ·
                      rfl

theorem cell22_3821689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 1, 3].length) (baseStart_3821689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821689 prefixEnd_3821689 := by exact prefixLift 3821689
  have htrace : WordTrace (prefixWord ++ tailWord_3821689) baseStart_3821689 baseEnd_3821689 := by
    simpa [prefixWord, tailWord_3821689, baseEnd_3821689] using wordTrace_append hprefix tailTrace_3821689
  have hstable : (prefixWord ++ tailWord_3821689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821689).length < 2 ^ (prefixWord ++ tailWord_3821689).sum := by decide
  have hdescent : baseEnd_3821689 < baseStart_3821689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821760 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 4, 4]
def baseStart_3821760 : Nat := 118140960795 + 3821760 * 2 ^ 59
def prefixEnd_3821760 : Nat := 4983230072969 + 3 ^ 40 * 3821760 * 2
def baseEnd_3821760 : Nat := 1308266550751381720082701

theorem tailTrace_3821760 : CollatzResearch.WordTrace tailWord_3821760 prefixEnd_3821760 1308266550751381720082701 := by
  unfold tailWord_3821760
  simp only [CollatzResearch.WordTrace]
  refine ⟨69695519317211849744319367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92927359089615799659092489 69695519317211849744319367)
  ·
    refine ⟨104543278975817774616479051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69695519317211849744319367 104543278975817774616479051)
    ·
      refine ⟨156814918463726661924718577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104543278975817774616479051 156814918463726661924718577)
      ·
        refine ⟨117611188847794996443538933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156814918463726661924718577 117611188847794996443538933)
        ·
          refine ⟨11026048954480780916581775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117611188847794996443538933 11026048954480780916581775)
          ·
            refine ⟨16539073431721171374872663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11026048954480780916581775 16539073431721171374872663)
            ·
              refine ⟨24808610147581757062308995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16539073431721171374872663 24808610147581757062308995)
              ·
                refine ⟨37212915221372635593463493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24808610147581757062308995 37212915221372635593463493)
                ·
                  refine ⟨6977421604007369173774405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37212915221372635593463493 6977421604007369173774405)
                  ·
                    refine ⟨1308266550751381720082701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977421604007369173774405 1308266550751381720082701)
                    ·
                      rfl

theorem cell22_3821760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 4, 4].length) (baseStart_3821760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821760 prefixEnd_3821760 := by exact prefixLift 3821760
  have htrace : WordTrace (prefixWord ++ tailWord_3821760) baseStart_3821760 baseEnd_3821760 := by
    simpa [prefixWord, tailWord_3821760, baseEnd_3821760] using wordTrace_append hprefix tailTrace_3821760
  have hstable : (prefixWord ++ tailWord_3821760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821760).length < 2 ^ (prefixWord ++ tailWord_3821760).sum := by decide
  have hdescent : baseEnd_3821760 < baseStart_3821760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821835 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 2, 5]
def baseStart_3821835 : Nat := 118140960795 + 3821835 * 2 ^ 59
def prefixEnd_3821835 : Nat := 4983230072969 + 3 ^ 40 * 3821835 * 2
def baseEnd_3821835 : Nat := 1308292224784106524457471

theorem tailTrace_3821835 : CollatzResearch.WordTrace tailWord_3821835 prefixEnd_3821835 1308292224784106524457471 := by
  unfold tailWord_3821835
  simp only [CollatzResearch.WordTrace]
  refine ⟨139393774109151987297618959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92929182739434658198412639 139393774109151987297618959)
  ·
    refine ⟨209090661163727980946428439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139393774109151987297618959 209090661163727980946428439)
    ·
      refine ⟨313635991745591971419642659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209090661163727980946428439 313635991745591971419642659)
      ·
        refine ⟨470453987618387957129463989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313635991745591971419642659 470453987618387957129463989)
        ·
          refine ⟨44105061339223870980887249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 470453987618387957129463989 44105061339223870980887249)
          ·
            refine ⟨33078796004417903235665437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44105061339223870980887249 33078796004417903235665437)
            ·
              refine ⟨12404548501656713713374539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33078796004417903235665437 12404548501656713713374539)
              ·
                refine ⟨18606822752485070570061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12404548501656713713374539 18606822752485070570061809)
                ·
                  refine ⟨13955117064363802927546357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18606822752485070570061809 13955117064363802927546357)
                  ·
                    refine ⟨1308292224784106524457471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13955117064363802927546357 1308292224784106524457471)
                    ·
                      rfl

theorem cell22_3821835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 5].length) (baseStart_3821835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821835 prefixEnd_3821835 := by exact prefixLift 3821835
  have htrace : WordTrace (prefixWord ++ tailWord_3821835) baseStart_3821835 baseEnd_3821835 := by
    simpa [prefixWord, tailWord_3821835, baseEnd_3821835] using wordTrace_append hprefix tailTrace_3821835
  have hstable : (prefixWord ++ tailWord_3821835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821835).length < 2 ^ (prefixWord ++ tailWord_3821835).sum := by decide
  have hdescent : baseEnd_3821835 < baseStart_3821835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821880 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 3, 5]
def baseStart_3821880 : Nat := 118140960795 + 3821880 * 2 ^ 59
def prefixEnd_3821880 : Nat := 4983230072969 + 3 ^ 40 * 3821880 * 2
def baseEnd_3821880 : Nat := 1308307629203741407082333

theorem tailTrace_3821880 : CollatzResearch.WordTrace tailWord_3821880 prefixEnd_3821880 1308307629203741407082333 := by
  unfold tailWord_3821880
  simp only [CollatzResearch.WordTrace]
  refine ⟨69697707696994479991503547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92930276929325973322004729 69697707696994479991503547)
  ·
    refine ⟨104546561545491719987255321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69697707696994479991503547 104546561545491719987255321)
    ·
      refine ⟨78409921159118789990441491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104546561545491719987255321 78409921159118789990441491)
      ·
        refine ⟨117614881738678184985662237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78409921159118789990441491 117614881738678184985662237)
        ·
          refine ⟨44105580652004319369623339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117614881738678184985662237 44105580652004319369623339)
          ·
            refine ⟨66158370978006479054435009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44105580652004319369623339 66158370978006479054435009)
            ·
              refine ⟨49618778233504859290826257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66158370978006479054435009 49618778233504859290826257)
              ·
                refine ⟨37214083675128644468119693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49618778233504859290826257 37214083675128644468119693)
                ·
                  refine ⟨13955281378173241675544885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37214083675128644468119693 13955281378173241675544885)
                  ·
                    refine ⟨1308307629203741407082333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13955281378173241675544885 1308307629203741407082333)
                    ·
                      rfl

theorem cell22_3821880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_3821880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821880 prefixEnd_3821880 := by exact prefixLift 3821880
  have htrace : WordTrace (prefixWord ++ tailWord_3821880) baseStart_3821880 baseEnd_3821880 := by
    simpa [prefixWord, tailWord_3821880, baseEnd_3821880] using wordTrace_append hprefix tailTrace_3821880
  have hstable : (prefixWord ++ tailWord_3821880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821880).length < 2 ^ (prefixWord ++ tailWord_3821880).sum := by decide
  have hdescent : baseEnd_3821880 < baseStart_3821880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821882 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_3821882 : Nat := 118140960795 + 3821882 * 2 ^ 59
def prefixEnd_3821882 : Nat := 4983230072969 + 3 ^ 40 * 3821882 * 2
def baseEnd_3821882 : Nat := 436102771281538022844109

theorem tailTrace_3821882 : CollatzResearch.WordTrace tailWord_3821882 prefixEnd_3821882 436102771281538022844109 := by
  unfold tailWord_3821882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34848872084995428581144975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92930325559987809549719933 34848872084995428581144975)
  ·
    refine ⟨52273308127493142871717463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34848872084995428581144975 52273308127493142871717463)
    ·
      refine ⟨78409962191239714307576195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52273308127493142871717463 78409962191239714307576195)
      ·
        refine ⟨117614943286859571461364293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78409962191239714307576195 117614943286859571461364293)
        ·
          refine ⟨22052801866286169649005805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117614943286859571461364293 22052801866286169649005805)
          ·
            refine ⟨8269800699857313618377177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22052801866286169649005805 8269800699857313618377177)
            ·
              refine ⟨6202350524892985213782883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8269800699857313618377177 6202350524892985213782883)
              ·
                refine ⟨9303525787339477820674325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6202350524892985213782883 9303525787339477820674325)
                ·
                  refine ⟨436102771281538022844109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9303525787339477820674325 436102771281538022844109)
                  ·
                    rfl

theorem cell22_3821882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_3821882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821882 prefixEnd_3821882 := by exact prefixLift 3821882
  have htrace : WordTrace (prefixWord ++ tailWord_3821882) baseStart_3821882 baseEnd_3821882 := by
    simpa [prefixWord, tailWord_3821882, baseEnd_3821882] using wordTrace_append hprefix tailTrace_3821882
  have hstable : (prefixWord ++ tailWord_3821882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821882).length < 2 ^ (prefixWord ++ tailWord_3821882).sum := by decide
  have hdescent : baseEnd_3821882 < baseStart_3821882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821895 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 3, 6]
def baseStart_3821895 : Nat := 118140960795 + 3821895 * 2 ^ 59
def prefixEnd_3821895 : Nat := 4983230072969 + 3 ^ 40 * 3821895 * 2
def baseEnd_3821895 : Nat := 1308312764010286367957287

theorem tailTrace_3821895 : CollatzResearch.WordTrace tailWord_3821895 prefixEnd_3821895 1308312764010286367957287 := by
  unfold tailWord_3821895
  simp only [CollatzResearch.WordTrace]
  refine ⟨139395962488934617544803139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92930641659289745029868759 139395962488934617544803139)
  ·
    refine ⟨209093943733401926317204709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139395962488934617544803139 209093943733401926317204709)
    ·
      refine ⟨39205114450012861184475883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209093943733401926317204709 39205114450012861184475883)
      ·
        refine ⟨58807671675019291776713825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39205114450012861184475883 58807671675019291776713825)
        ·
          refine ⟨44105753756264468832535369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58807671675019291776713825 44105753756264468832535369)
          ·
            refine ⟨33079315317198351624401527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44105753756264468832535369 33079315317198351624401527)
            ·
              refine ⟨49618972975797527436602291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33079315317198351624401527 49618972975797527436602291)
              ·
                refine ⟨74428459463696291154903437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49618972975797527436602291 74428459463696291154903437)
                ·
                  refine ⟨27910672298886109183088789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74428459463696291154903437 27910672298886109183088789)
                  ·
                    refine ⟨1308312764010286367957287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27910672298886109183088789 1308312764010286367957287)
                    ·
                      rfl

theorem cell22_3821895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_3821895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821895 prefixEnd_3821895 := by exact prefixLift 3821895
  have htrace : WordTrace (prefixWord ++ tailWord_3821895) baseStart_3821895 baseEnd_3821895 := by
    simpa [prefixWord, tailWord_3821895, baseEnd_3821895] using wordTrace_append hprefix tailTrace_3821895
  have hstable : (prefixWord ++ tailWord_3821895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821895).length < 2 ^ (prefixWord ++ tailWord_3821895).sum := by decide
  have hdescent : baseEnd_3821895 < baseStart_3821895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3821927 : List Nat := [1, 1, 5, 1, 3, 3, 8]
def baseStart_3821927 : Nat := 118140960795 + 3821927 * 2 ^ 59
def prefixEnd_3821927 : Nat := 4983230072969 + 3 ^ 40 * 3821927 * 2
def baseEnd_3821927 : Nat := 48456434009786998191007

theorem tailTrace_3821927 : CollatzResearch.WordTrace tailWord_3821927 prefixEnd_3821927 48456434009786998191007 := by
  unfold tailWord_3821927
  simp only [CollatzResearch.WordTrace]
  refine ⟨139397129624818687009968035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92931419749879124673312023 139397129624818687009968035)
  ·
    refine ⟨209095694437228030514952053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139397129624818687009968035 209095694437228030514952053)
    ·
      refine ⟨19602721353490127860776755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209095694437228030514952053 19602721353490127860776755)
      ·
        refine ⟨29404082030235191791165133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19602721353490127860776755 29404082030235191791165133)
        ·
          refine ⟨11026530761338196921686925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29404082030235191791165133 11026530761338196921686925)
          ·
            refine ⟨4134949035501823845632597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11026530761338196921686925 4134949035501823845632597)
            ·
              refine ⟨48456434009786998191007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4134949035501823845632597 48456434009786998191007)
              ·
                rfl

theorem cell22_3821927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 8].length) (baseStart_3821927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3821927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3821927 prefixEnd_3821927 := by exact prefixLift 3821927
  have htrace : WordTrace (prefixWord ++ tailWord_3821927) baseStart_3821927 baseEnd_3821927 := by
    simpa [prefixWord, tailWord_3821927, baseEnd_3821927] using wordTrace_append hprefix tailTrace_3821927
  have hstable : (prefixWord ++ tailWord_3821927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3821927).length < 2 ^ (prefixWord ++ tailWord_3821927).sum := by decide
  have hdescent : baseEnd_3821927 < baseStart_3821927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3821927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822002 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3822002 : Nat := 118140960795 + 3822002 * 2 ^ 59
def prefixEnd_3822002 : Nat := 4983230072969 + 3 ^ 40 * 3822002 * 2
def baseEnd_3822002 : Nat := 1308349392296973755531959

theorem tailTrace_3822002 : CollatzResearch.WordTrace tailWord_3822002 prefixEnd_3822002 1308349392296973755531959 := by
  unfold tailWord_3822002
  simp only [CollatzResearch.WordTrace]
  refine ⟨34849966274886743704737065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92933243399697983212632173 34849966274886743704737065)
  ·
    refine ⟨26137474706165057778552799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34849966274886743704737065 26137474706165057778552799)
    ·
      refine ⟨39206212059247586667829199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137474706165057778552799 39206212059247586667829199)
      ·
        refine ⟨58809318088871380001743799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39206212059247586667829199 58809318088871380001743799)
        ·
          refine ⟨88213977133307070002615699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58809318088871380001743799 88213977133307070002615699)
          ·
            refine ⟨132320965699960605003923549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88213977133307070002615699 132320965699960605003923549)
            ·
              refine ⟨49620362137485226876471331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132320965699960605003923549 49620362137485226876471331)
              ·
                refine ⟨74430543206227840314706997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49620362137485226876471331 74430543206227840314706997)
                ·
                  refine ⟨6977863425583860029503781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74430543206227840314706997 6977863425583860029503781)
                  ·
                    refine ⟨1308349392296973755531959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977863425583860029503781 1308349392296973755531959)
                    ·
                      rfl

theorem cell22_3822002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3822002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822002 prefixEnd_3822002 := by exact prefixLift 3822002
  have htrace : WordTrace (prefixWord ++ tailWord_3822002) baseStart_3822002 baseEnd_3822002 := by
    simpa [prefixWord, tailWord_3822002, baseEnd_3822002] using wordTrace_append hprefix tailTrace_3822002
  have hstable : (prefixWord ++ tailWord_3822002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822002).length < 2 ^ (prefixWord ++ tailWord_3822002).sum := by decide
  have hdescent : baseEnd_3822002 < baseStart_3822002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822036 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_3822036 : Nat := 118140960795 + 3822036 * 2 ^ 59
def prefixEnd_3822036 : Nat := 4983230072969 + 3 ^ 40 * 3822036 * 2
def baseEnd_3822036 : Nat := 1308361031191809000181855

theorem tailTrace_3822036 : CollatzResearch.WordTrace tailWord_3822036 prefixEnd_3822036 1308361031191809000181855 := by
  unfold tailWord_3822036
  simp only [CollatzResearch.WordTrace]
  refine ⟨69700552590711899312842981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92934070120949199083790641 69700552590711899312842981)
  ·
    refine ⟨13068853610758481121158059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69700552590711899312842981 13068853610758481121158059)
    ·
      refine ⟨19603280416137721681737089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13068853610758481121158059 19603280416137721681737089)
      ·
        refine ⟨14702460312103291261302817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19603280416137721681737089 14702460312103291261302817)
        ·
          refine ⟨11026845234077468445977113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14702460312103291261302817 11026845234077468445977113)
          ·
            refine ⟨8270133925558101334482835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11026845234077468445977113 8270133925558101334482835)
            ·
              refine ⟨12405200888337152001724253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270133925558101334482835 12405200888337152001724253)
              ·
                refine ⟨4651950333126432000646595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12405200888337152001724253 4651950333126432000646595)
                ·
                  refine ⟨6977925499689648000969893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4651950333126432000646595 6977925499689648000969893)
                  ·
                    refine ⟨1308361031191809000181855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6977925499689648000969893 1308361031191809000181855)
                    ·
                      rfl

theorem cell22_3822036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_3822036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822036 prefixEnd_3822036 := by exact prefixLift 3822036
  have htrace : WordTrace (prefixWord ++ tailWord_3822036) baseStart_3822036 baseEnd_3822036 := by
    simpa [prefixWord, tailWord_3822036, baseEnd_3822036] using wordTrace_append hprefix tailTrace_3822036
  have hstable : (prefixWord ++ tailWord_3822036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822036).length < 2 ^ (prefixWord ++ tailWord_3822036).sum := by decide
  have hdescent : baseEnd_3822036 < baseStart_3822036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822049 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 4, 3]
def baseStart_3822049 : Nat := 118140960795 + 3822049 * 2 ^ 59
def prefixEnd_3822049 : Nat := 4983230072969 + 3 ^ 40 * 3822049 * 2
def baseEnd_3822049 : Nat := 1308365481357481299606815

theorem tailTrace_3822049 : CollatzResearch.WordTrace tailWord_3822049 prefixEnd_3822049 1308365481357481299606815 := by
  unfold tailWord_3822049
  simp only [CollatzResearch.WordTrace]
  refine ⟨139401579330376701845909201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92934386220251134563939467 139401579330376701845909201)
  ·
    refine ⟨104551184497782526384431901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139401579330376701845909201 104551184497782526384431901)
    ·
      refine ⟨39206694186668447394161963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104551184497782526384431901 39206694186668447394161963)
      ·
        refine ⟨58810041280002671091242945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39206694186668447394161963 58810041280002671091242945)
        ·
          refine ⟨44107530960002003318432209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58810041280002671091242945 44107530960002003318432209)
          ·
            refine ⟨33080648220001502488824157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44107530960002003318432209 33080648220001502488824157)
            ·
              refine ⟨12405243082500563433309059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33080648220001502488824157 12405243082500563433309059)
              ·
                refine ⟨18607864623750845149963589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405243082500563433309059 18607864623750845149963589)
                ·
                  refine ⟨3488974616953283465618173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18607864623750845149963589 3488974616953283465618173)
                  ·
                    refine ⟨1308365481357481299606815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3488974616953283465618173 1308365481357481299606815)
                    ·
                      rfl

theorem cell22_3822049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_3822049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822049 prefixEnd_3822049 := by exact prefixLift 3822049
  have htrace : WordTrace (prefixWord ++ tailWord_3822049) baseStart_3822049 baseEnd_3822049 := by
    simpa [prefixWord, tailWord_3822049, baseEnd_3822049] using wordTrace_append hprefix tailTrace_3822049
  have hstable : (prefixWord ++ tailWord_3822049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822049).length < 2 ^ (prefixWord ++ tailWord_3822049).sum := by decide
  have hdescent : baseEnd_3822049 < baseStart_3822049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822077 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3822077 : Nat := 118140960795 + 3822077 * 2 ^ 59
def prefixEnd_3822077 : Nat := 4983230072969 + 3 ^ 40 * 3822077 * 2
def baseEnd_3822077 : Nat := 1308375066329698559906729

theorem tailTrace_3822077 : CollatzResearch.WordTrace tailWord_3822077 prefixEnd_3822077 1308375066329698559906729 := by
  unfold tailWord_3822077
  simp only [CollatzResearch.WordTrace]
  refine ⟨139402600574275262627928485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92935067049516841751952323 139402600574275262627928485)
  ·
    refine ⟨26137987607676611742736591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139402600574275262627928485 26137987607676611742736591)
    ·
      refine ⟨39206981411514917614104887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26137987607676611742736591 39206981411514917614104887)
      ·
        refine ⟨58810472117272376421157331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39206981411514917614104887 58810472117272376421157331)
        ·
          refine ⟨88215708175908564631735997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58810472117272376421157331 88215708175908564631735997)
          ·
            refine ⟨33080890565965711736900999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88215708175908564631735997 33080890565965711736900999)
            ·
              refine ⟨49621335848948567605351499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33080890565965711736900999 49621335848948567605351499)
              ·
                refine ⟨74432003773422851408027249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49621335848948567605351499 74432003773422851408027249)
                ·
                  refine ⟨55824002830067138556020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74432003773422851408027249 55824002830067138556020437)
                  ·
                    refine ⟨1308375066329698559906729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55824002830067138556020437 1308375066329698559906729)
                    ·
                      rfl

theorem cell22_3822077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3822077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822077 prefixEnd_3822077 := by exact prefixLift 3822077
  have htrace : WordTrace (prefixWord ++ tailWord_3822077) baseStart_3822077 baseEnd_3822077 := by
    simpa [prefixWord, tailWord_3822077, baseEnd_3822077] using wordTrace_append hprefix tailTrace_3822077
  have hstable : (prefixWord ++ tailWord_3822077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822077).length < 2 ^ (prefixWord ++ tailWord_3822077).sum := by decide
  have hdescent : baseEnd_3822077 < baseStart_3822077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822205 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 1, 4]
def baseStart_3822205 : Nat := 118140960795 + 3822205 * 2 ^ 59
def prefixEnd_3822205 : Nat := 4983230072969 + 3 ^ 40 * 3822205 * 2
def baseEnd_3822205 : Nat := 1308418883345548892706337

theorem tailTrace_3822205 : CollatzResearch.WordTrace tailWord_3822205 prefixEnd_3822205 1308418883345548892706337 := by
  unfold tailWord_3822205
  simp only [CollatzResearch.WordTrace]
  refine ⟨139407269117811540488588069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92938179411874360325725379 139407269117811540488588069)
  ·
    refine ⟨26138862959589663841610263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139407269117811540488588069 26138862959589663841610263)
    ·
      refine ⟨39208294439384495762415395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26138862959589663841610263 39208294439384495762415395)
      ·
        refine ⟨58812441659076743643623093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39208294439384495762415395 58812441659076743643623093)
        ·
          refine ⟨5513666405538444716589665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 58812441659076743643623093 5513666405538444716589665)
          ·
            refine ⟨4135249804153833537442249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5513666405538444716589665 4135249804153833537442249)
            ·
              refine ⟨3101437353115375153081687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4135249804153833537442249 3101437353115375153081687)
              ·
                refine ⟨4652156029673062729622531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3101437353115375153081687 4652156029673062729622531)
                ·
                  refine ⟨6978234044509594094433797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652156029673062729622531 6978234044509594094433797)
                  ·
                    refine ⟨1308418883345548892706337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978234044509594094433797 1308418883345548892706337)
                    ·
                      rfl

theorem cell22_3822205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_3822205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822205 prefixEnd_3822205 := by exact prefixLift 3822205
  have htrace : WordTrace (prefixWord ++ tailWord_3822205) baseStart_3822205 baseEnd_3822205 := by
    simpa [prefixWord, tailWord_3822205, baseEnd_3822205] using wordTrace_append hprefix tailTrace_3822205
  have hstable : (prefixWord ++ tailWord_3822205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822205).length < 2 ^ (prefixWord ++ tailWord_3822205).sum := by decide
  have hdescent : baseEnd_3822205 < baseStart_3822205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822218 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_3822218 : Nat := 118140960795 + 3822218 * 2 ^ 59
def prefixEnd_3822218 : Nat := 4983230072969 + 3 ^ 40 * 3822218 * 2
def baseEnd_3822218 : Nat := 1308423333511221192131297

theorem tailTrace_3822218 : CollatzResearch.WordTrace tailWord_3822218 prefixEnd_3822218 1308423333511221192131297 := by
  unfold tailWord_3822218
  simp only [CollatzResearch.WordTrace]
  refine ⟨34851935816691110927202827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92938495511176295805874205 34851935816691110927202827)
  ·
    refine ⟨52277903725036666390804241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34851935816691110927202827 52277903725036666390804241)
    ·
      refine ⟨39208427793777499793103181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52277903725036666390804241 39208427793777499793103181)
      ·
        refine ⟨14703160422666562422413693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39208427793777499793103181 14703160422666562422413693)
        ·
          refine ⟨5513685158499960908405135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14703160422666562422413693 5513685158499960908405135)
          ·
            refine ⟨8270527737749941362607703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5513685158499960908405135 8270527737749941362607703)
            ·
              refine ⟨12405791606624912043911555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8270527737749941362607703 12405791606624912043911555)
              ·
                refine ⟨18608687409937368065867333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405791606624912043911555 18608687409937368065867333)
                ·
                  refine ⟨3489128889363256512350125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18608687409937368065867333 3489128889363256512350125)
                  ·
                    refine ⟨1308423333511221192131297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489128889363256512350125 1308423333511221192131297)
                    ·
                      rfl

theorem cell22_3822218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_3822218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822218 prefixEnd_3822218 := by exact prefixLift 3822218
  have htrace : WordTrace (prefixWord ++ tailWord_3822218) baseStart_3822218 baseEnd_3822218 := by
    simpa [prefixWord, tailWord_3822218, baseEnd_3822218] using wordTrace_append hprefix tailTrace_3822218
  have hstable : (prefixWord ++ tailWord_3822218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822218).length < 2 ^ (prefixWord ++ tailWord_3822218).sum := by decide
  have hdescent : baseEnd_3822218 < baseStart_3822218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822259 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 7]
def baseStart_3822259 : Nat := 118140960795 + 3822259 * 2 ^ 59
def prefixEnd_3822259 : Nat := 4983230072969 + 3 ^ 40 * 3822259 * 2
def baseEnd_3822259 : Nat := 436145789549703583952057

theorem tailTrace_3822259 : CollatzResearch.WordTrace tailWord_3822259 prefixEnd_3822259 436145789549703583952057 := by
  unfold tailWord_3822259
  simp only [CollatzResearch.WordTrace]
  refine ⟨139409238659615907711053831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92939492439743938474035887 139409238659615907711053831)
  ·
    refine ⟨209113857989423861566580747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139409238659615907711053831 209113857989423861566580747)
    ·
      refine ⟨313670786984135792349871121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209113857989423861566580747 313670786984135792349871121)
      ·
        refine ⟨235253090238101844262403341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313670786984135792349871121 235253090238101844262403341)
        ·
          refine ⟨88219908839288191598401253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 235253090238101844262403341 88219908839288191598401253)
          ·
            refine ⟨16541232907366535924700235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88219908839288191598401253 16541232907366535924700235)
            ·
              refine ⟨24811849361049803887050353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16541232907366535924700235 24811849361049803887050353)
              ·
                refine ⟨18608887020787352915287765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24811849361049803887050353 18608887020787352915287765)
                ·
                  refine ⟨436145789549703583952057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18608887020787352915287765 436145789549703583952057)
                  ·
                    rfl

theorem cell22_3822259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 7].length) (baseStart_3822259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822259 prefixEnd_3822259 := by exact prefixLift 3822259
  have htrace : WordTrace (prefixWord ++ tailWord_3822259) baseStart_3822259 baseEnd_3822259 := by
    simpa [prefixWord, tailWord_3822259, baseEnd_3822259] using wordTrace_append hprefix tailTrace_3822259
  have hstable : (prefixWord ++ tailWord_3822259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822259).length < 2 ^ (prefixWord ++ tailWord_3822259).sum := by decide
  have hdescent : baseEnd_3822259 < baseStart_3822259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822276 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3822276 : Nat := 118140960795 + 3822276 * 2 ^ 59
def prefixEnd_3822276 : Nat := 4983230072969 + 3 ^ 40 * 3822276 * 2
def baseEnd_3822276 : Nat := 436147729365509458060373

theorem tailTrace_3822276 : CollatzResearch.WordTrace tailWord_3822276 prefixEnd_3822276 436147729365509458060373 := by
  unfold tailWord_3822276
  simp only [CollatzResearch.WordTrace]
  refine ⟨69704929350277159807211341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92939905800369546409615121 69704929350277159807211341)
  ·
    refine ⟨26139348506353934927704253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69704929350277159807211341 26139348506353934927704253)
    ·
      refine ⟨9802255689882725597889095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26139348506353934927704253 9802255689882725597889095)
      ·
        refine ⟨14703383534824088396833643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9802255689882725597889095 14703383534824088396833643)
        ·
          refine ⟨22055075302236132595250465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14703383534824088396833643 22055075302236132595250465)
          ·
            refine ⟨16541306476677099446437849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22055075302236132595250465 16541306476677099446437849)
            ·
              refine ⟨12405979857507824584828387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16541306476677099446437849 12405979857507824584828387)
              ·
                refine ⟨18608969786261736877242581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12405979857507824584828387 18608969786261736877242581)
                ·
                  refine ⟨436147729365509458060373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18608969786261736877242581 436147729365509458060373)
                  ·
                    rfl

theorem cell22_3822276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3822276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822276 prefixEnd_3822276 := by exact prefixLift 3822276
  have htrace : WordTrace (prefixWord ++ tailWord_3822276) baseStart_3822276 baseEnd_3822276 := by
    simpa [prefixWord, tailWord_3822276, baseEnd_3822276] using wordTrace_append hprefix tailTrace_3822276
  have hstable : (prefixWord ++ tailWord_3822276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822276).length < 2 ^ (prefixWord ++ tailWord_3822276).sum := by decide
  have hdescent : baseEnd_3822276 < baseStart_3822276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822304 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_3822304 : Nat := 118140960795 + 3822304 * 2 ^ 59
def prefixEnd_3822304 : Nat := 4983230072969 + 3 ^ 40 * 3822304 * 2
def baseEnd_3822304 : Nat := 436150924356248544827011

theorem tailTrace_3822304 : CollatzResearch.WordTrace tailWord_3822304 prefixEnd_3822304 436150924356248544827011 := by
  unfold tailWord_3822304
  simp only [CollatzResearch.WordTrace]
  refine ⟨69705439972226440198220983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92940586629635253597627977 69705439972226440198220983)
  ·
    refine ⟨104558159958339660297331475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69705439972226440198220983 104558159958339660297331475)
    ·
      refine ⟨156837239937509490445997213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104558159958339660297331475 156837239937509490445997213)
      ·
        refine ⟨58813964976566058917248955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156837239937509490445997213 58813964976566058917248955)
        ·
          refine ⟨88220947464849088375873433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58813964976566058917248955 88220947464849088375873433)
          ·
            refine ⟨66165710598636816281905075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88220947464849088375873433 66165710598636816281905075)
            ·
              refine ⟨99248565897955224422857613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66165710598636816281905075 99248565897955224422857613)
              ·
                refine ⟨37218212211733209158571605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99248565897955224422857613 37218212211733209158571605)
                ·
                  refine ⟨436150924356248544827011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37218212211733209158571605 436150924356248544827011)
                  ·
                    rfl

theorem cell22_3822304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_3822304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822304 prefixEnd_3822304 := by exact prefixLift 3822304
  have htrace : WordTrace (prefixWord ++ tailWord_3822304) baseStart_3822304 baseEnd_3822304 := by
    simpa [prefixWord, tailWord_3822304, baseEnd_3822304] using wordTrace_append hprefix tailTrace_3822304
  have hstable : (prefixWord ++ tailWord_3822304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822304).length < 2 ^ (prefixWord ++ tailWord_3822304).sum := by decide
  have hdescent : baseEnd_3822304 < baseStart_3822304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822353 : List Nat := [1, 2, 2, 1, 1, 3, 4, 3, 2, 3]
def baseStart_3822353 : Nat := 118140960795 + 3822353 * 2 ^ 59
def prefixEnd_3822353 : Nat := 4983230072969 + 3 ^ 40 * 3822353 * 2
def baseEnd_3822353 : Nat := 1308469546770125840005883

theorem tailTrace_3822353 : CollatzResearch.WordTrace tailWord_3822353 prefixEnd_3822353 1308469546770125840005883 := by
  unfold tailWord_3822353
  simp only [CollatzResearch.WordTrace]
  refine ⟨139412667121275361764975713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92941778080850241176650475 139412667121275361764975713)
  ·
    refine ⟨104559500340956521323731785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139412667121275361764975713 104559500340956521323731785)
    ·
      refine ⟨78419625255717390992798839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104559500340956521323731785 78419625255717390992798839)
      ·
        refine ⟨117629437883576086489198259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78419625255717390992798839 117629437883576086489198259)
        ·
          refine ⟨176444156825364129733797389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117629437883576086489198259 176444156825364129733797389)
          ·
            refine ⟨66166558809511548650174021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176444156825364129733797389 66166558809511548650174021)
            ·
              refine ⟨12406229776783415371907629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66166558809511548650174021 12406229776783415371907629)
              ·
                refine ⟨4652336166293780764465361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12406229776783415371907629 4652336166293780764465361)
                ·
                  refine ⟨3489252124720335573349021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652336166293780764465361 3489252124720335573349021)
                  ·
                    refine ⟨1308469546770125840005883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489252124720335573349021 1308469546770125840005883)
                    ·
                      rfl

theorem cell22_3822353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 3, 2, 3].length) (baseStart_3822353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822353 prefixEnd_3822353 := by exact prefixLift 3822353
  have htrace : WordTrace (prefixWord ++ tailWord_3822353) baseStart_3822353 baseEnd_3822353 := by
    simpa [prefixWord, tailWord_3822353, baseEnd_3822353] using wordTrace_append hprefix tailTrace_3822353
  have hstable : (prefixWord ++ tailWord_3822353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822353).length < 2 ^ (prefixWord ++ tailWord_3822353).sum := by decide
  have hdescent : baseEnd_3822353 < baseStart_3822353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822368 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 2, 4]
def baseStart_3822368 : Nat := 118140960795 + 3822368 * 2 ^ 59
def prefixEnd_3822368 : Nat := 4983230072969 + 3 ^ 40 * 3822368 * 2
def baseEnd_3822368 : Nat := 1308474681576670800880837

theorem tailTrace_3822368 : CollatzResearch.WordTrace tailWord_3822368 prefixEnd_3822368 1308474681576670800880837 := by
  unfold tailWord_3822368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69706607108110509663385879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92942142810814012884514505 69706607108110509663385879)
  ·
    refine ⟨104559910662165764495078819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69706607108110509663385879 104559910662165764495078819)
    ·
      refine ⟨156839865993248646742618229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104559910662165764495078819 156839865993248646742618229)
      ·
        refine ⟨14703737436867060632120459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 156839865993248646742618229 14703737436867060632120459)
        ·
          refine ⟨22055606155300590948180689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14703737436867060632120459 22055606155300590948180689)
          ·
            refine ⟨16541704616475443211135517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22055606155300590948180689 16541704616475443211135517)
            ·
              refine ⟨6203139231178291204175819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16541704616475443211135517 6203139231178291204175819)
              ·
                refine ⟨9304708846767436806263729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203139231178291204175819 9304708846767436806263729)
                ·
                  refine ⟨6978531635075577604697797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9304708846767436806263729 6978531635075577604697797)
                  ·
                    refine ⟨1308474681576670800880837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978531635075577604697797 1308474681576670800880837)
                    ·
                      rfl

theorem cell22_3822368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_3822368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822368 prefixEnd_3822368 := by exact prefixLift 3822368
  have htrace : WordTrace (prefixWord ++ tailWord_3822368) baseStart_3822368 baseEnd_3822368 := by
    simpa [prefixWord, tailWord_3822368, baseEnd_3822368] using wordTrace_append hprefix tailTrace_3822368
  have hstable : (prefixWord ++ tailWord_3822368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822368).length < 2 ^ (prefixWord ++ tailWord_3822368).sum := by decide
  have hdescent : baseEnd_3822368 < baseStart_3822368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822404 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3822404 : Nat := 118140960795 + 3822404 * 2 ^ 59
def prefixEnd_3822404 : Nat := 4983230072969 + 3 ^ 40 * 3822404 * 2
def baseEnd_3822404 : Nat := 1308487005112378706980727

theorem tailTrace_3822404 : CollatzResearch.WordTrace tailWord_3822404 prefixEnd_3822404 1308487005112378706980727 := by
  unfold tailWord_3822404
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707263622045298737541133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92943018162727064983388177 69707263622045298737541133)
  ·
    refine ⟨26140223858266987026577925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69707263622045298737541133 26140223858266987026577925)
    ·
      refine ⟨4901291973425060067483361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26140223858266987026577925 4901291973425060067483361)
      ·
        refine ⟨3675968980068795050612521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4901291973425060067483361 3675968980068795050612521)
        ·
          refine ⟨2756976735051596287959391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3675968980068795050612521 2756976735051596287959391)
          ·
            refine ⟨4135465102577394431939087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2756976735051596287959391 4135465102577394431939087)
            ·
              refine ⟨6203197653866091647908631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135465102577394431939087 6203197653866091647908631)
              ·
                refine ⟨9304796480799137471862947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203197653866091647908631 9304796480799137471862947)
                ·
                  refine ⟨13957194721198706207794421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9304796480799137471862947 13957194721198706207794421)
                  ·
                    refine ⟨1308487005112378706980727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13957194721198706207794421 1308487005112378706980727)
                    ·
                      rfl

theorem cell22_3822404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3822404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822404 prefixEnd_3822404 := by exact prefixLift 3822404
  have htrace : WordTrace (prefixWord ++ tailWord_3822404) baseStart_3822404 baseEnd_3822404 := by
    simpa [prefixWord, tailWord_3822404, baseEnd_3822404] using wordTrace_append hprefix tailTrace_3822404
  have hstable : (prefixWord ++ tailWord_3822404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822404).length < 2 ^ (prefixWord ++ tailWord_3822404).sum := by decide
  have hdescent : baseEnd_3822404 < baseStart_3822404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822428 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_3822428 : Nat := 118140960795 + 3822428 * 2 ^ 59
def prefixEnd_3822428 : Nat := 4983230072969 + 3 ^ 40 * 3822428 * 2
def baseEnd_3822428 : Nat := 436165073600950214793551

theorem tailTrace_3822428 : CollatzResearch.WordTrace tailWord_3822428 prefixEnd_3822428 436165073600950214793551 := by
  unfold tailWord_3822428
  simp only [CollatzResearch.WordTrace]
  refine ⟨69707701298001824786977969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92943601730669099715970625 69707701298001824786977969)
  ·
    refine ⟨52280775973501368590233477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69707701298001824786977969 52280775973501368590233477)
    ·
      refine ⟨9802645495031506610668777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52280775973501368590233477 9802645495031506610668777)
      ·
        refine ⟨7351984121273629958001583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9802645495031506610668777 7351984121273629958001583)
        ·
          refine ⟨11027976181910444937002375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7351984121273629958001583 11027976181910444937002375)
          ·
            refine ⟨16541964272865667405503563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11027976181910444937002375 16541964272865667405503563)
            ·
              refine ⟨24812946409298501108255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16541964272865667405503563 24812946409298501108255345)
              ·
                refine ⟨18609709806973875831191509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24812946409298501108255345 18609709806973875831191509)
                ·
                  refine ⟨436165073600950214793551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18609709806973875831191509 436165073600950214793551)
                  ·
                    rfl

theorem cell22_3822428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_3822428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822428 prefixEnd_3822428 := by exact prefixLift 3822428
  have htrace : WordTrace (prefixWord ++ tailWord_3822428) baseStart_3822428 baseEnd_3822428 := by
    simpa [prefixWord, tailWord_3822428, baseEnd_3822428] using wordTrace_append hprefix tailTrace_3822428
  have hstable : (prefixWord ++ tailWord_3822428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822428).length < 2 ^ (prefixWord ++ tailWord_3822428).sum := by decide
  have hdescent : baseEnd_3822428 < baseStart_3822428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 7, 4]
def baseStart_3822441 : Nat := 118140960795 + 3822441 * 2 ^ 59
def prefixEnd_3822441 : Nat := 4983230072969 + 3 ^ 40 * 3822441 * 2
def baseEnd_3822441 : Nat := 1308499670968522943805613

theorem tailTrace_3822441 : CollatzResearch.WordTrace tailWord_3822441 prefixEnd_3822441 1308499670968522943805613 := by
  unfold tailWord_3822441
  simp only [CollatzResearch.WordTrace]
  refine ⟨139415876744956552794179177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92943917829971035196119451 139415876744956552794179177)
  ·
    refine ⟨104561907558717414595634383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139415876744956552794179177 104561907558717414595634383)
    ·
      refine ⟨156842861338076121893451575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104561907558717414595634383 156842861338076121893451575)
      ·
        refine ⟨235264292007114182840177363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156842861338076121893451575 235264292007114182840177363)
        ·
          refine ⟨352896438010671274260266045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235264292007114182840177363 352896438010671274260266045)
          ·
            refine ⟨132336164254001727847599767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 352896438010671274260266045 132336164254001727847599767)
            ·
              refine ⟨198504246381002591771399651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132336164254001727847599767 198504246381002591771399651)
              ·
                refine ⟨297756369571503887657099477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 198504246381002591771399651 297756369571503887657099477)
                ·
                  refine ⟨6978664911832122366963269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 297756369571503887657099477 6978664911832122366963269)
                  ·
                    refine ⟨1308499670968522943805613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6978664911832122366963269 1308499670968522943805613)
                    ·
                      rfl

theorem cell22_3822441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 4].length) (baseStart_3822441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822441 prefixEnd_3822441 := by exact prefixLift 3822441
  have htrace : WordTrace (prefixWord ++ tailWord_3822441) baseStart_3822441 baseEnd_3822441 := by
    simpa [prefixWord, tailWord_3822441, baseEnd_3822441] using wordTrace_append hprefix tailTrace_3822441
  have hstable : (prefixWord ++ tailWord_3822441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822441).length < 2 ^ (prefixWord ++ tailWord_3822441).sum := by decide
  have hdescent : baseEnd_3822441 < baseStart_3822441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822456 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 6]
def baseStart_3822456 : Nat := 118140960795 + 3822456 * 2 ^ 59
def prefixEnd_3822456 : Nat := 4983230072969 + 3 ^ 40 * 3822456 * 2
def baseEnd_3822456 : Nat := 436168268591689301560189

theorem tailTrace_3822456 : CollatzResearch.WordTrace tailWord_3822456 prefixEnd_3822456 436168268591689301560189 := by
  unfold tailWord_3822456
  simp only [CollatzResearch.WordTrace]
  refine ⟨69708211919951105177987611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92944282559934806903983481 69708211919951105177987611)
  ·
    refine ⟨104562317879926657766981417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69708211919951105177987611 104562317879926657766981417)
    ·
      refine ⟨78421738409944993325236063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104562317879926657766981417 78421738409944993325236063)
      ·
        refine ⟨117632607614917489987854095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78421738409944993325236063 117632607614917489987854095)
        ·
          refine ⟨176448911422376234981781143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117632607614917489987854095 176448911422376234981781143)
          ·
            refine ⟨264673367133564352472671715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176448911422376234981781143 264673367133564352472671715)
            ·
              refine ⟨397010050700346528709007573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 264673367133564352472671715 397010050700346528709007573)
              ·
                refine ⟨9304923063289371766617365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 397010050700346528709007573 9304923063289371766617365)
                ·
                  refine ⟨436168268591689301560189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9304923063289371766617365 436168268591689301560189)
                  ·
                    rfl

theorem cell22_3822456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 6].length) (baseStart_3822456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822456 prefixEnd_3822456 := by exact prefixLift 3822456
  have htrace : WordTrace (prefixWord ++ tailWord_3822456) baseStart_3822456 baseEnd_3822456 := by
    simpa [prefixWord, tailWord_3822456, baseEnd_3822456] using wordTrace_append hprefix tailTrace_3822456
  have hstable : (prefixWord ++ tailWord_3822456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822456).length < 2 ^ (prefixWord ++ tailWord_3822456).sum := by decide
  have hdescent : baseEnd_3822456 < baseStart_3822456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822462 : List Nat := [4, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3822462 : Nat := 118140960795 + 3822462 * 2 ^ 59
def prefixEnd_3822462 : Nat := 4983230072969 + 3 ^ 40 * 3822462 * 2
def baseEnd_3822462 : Nat := 436168953232561963010183

theorem tailTrace_3822462 : CollatzResearch.WordTrace tailWord_3822462 prefixEnd_3822462 436168953232561963010183 := by
  unfold tailWord_3822462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17427080334735059172586705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92944428451920315587129093 17427080334735059172586705)
  ·
    refine ⟨13070310251051294379440029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17427080334735059172586705 13070310251051294379440029)
    ·
      refine ⟨4901366344144235392290011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13070310251051294379440029 4901366344144235392290011)
      ·
        refine ⟨7352049516216353088435017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4901366344144235392290011 7352049516216353088435017)
        ·
          refine ⟨5514037137162264816326263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7352049516216353088435017 5514037137162264816326263)
          ·
            refine ⟨8271055705743397224489395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514037137162264816326263 8271055705743397224489395)
            ·
              refine ⟨12406583558615095836734093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271055705743397224489395 12406583558615095836734093)
              ·
                refine ⟨4652468834480660938775285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12406583558615095836734093 4652468834480660938775285)
                ·
                  refine ⟨436168953232561963010183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4652468834480660938775285 436168953232561963010183)
                  ·
                    rfl

theorem cell22_3822462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3822462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822462 prefixEnd_3822462 := by exact prefixLift 3822462
  have htrace : WordTrace (prefixWord ++ tailWord_3822462) baseStart_3822462 baseEnd_3822462 := by
    simpa [prefixWord, tailWord_3822462, baseEnd_3822462] using wordTrace_append hprefix tailTrace_3822462
  have hstable : (prefixWord ++ tailWord_3822462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822462).length < 2 ^ (prefixWord ++ tailWord_3822462).sum := by decide
  have hdescent : baseEnd_3822462 < baseStart_3822462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822505 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 2, 3]
def baseStart_3822505 : Nat := 118140960795 + 3822505 * 2 ^ 59
def prefixEnd_3822505 : Nat := 4983230072969 + 3 ^ 40 * 3822505 * 2
def baseEnd_3822505 : Nat := 1308521579476448110205417

theorem tailTrace_3822505 : CollatzResearch.WordTrace tailWord_3822505 prefixEnd_3822505 1308521579476448110205417 := by
  unfold tailWord_3822505
  simp only [CollatzResearch.WordTrace]
  refine ⟨139418211016724691724508969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92945474011149794483005979 139418211016724691724508969)
  ·
    refine ⟨104563658262543518793381727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139418211016724691724508969 104563658262543518793381727)
    ·
      refine ⟨156845487393815278190072591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104563658262543518793381727 156845487393815278190072591)
      ·
        refine ⟨235268231090722917285108887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156845487393815278190072591 235268231090722917285108887)
        ·
          refine ⟨352902346636084375927663331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235268231090722917285108887 352902346636084375927663331)
          ·
            refine ⟨529353519954126563891494997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 352902346636084375927663331 529353519954126563891494997)
            ·
              refine ⟨6203361561962420670603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 529353519954126563891494997 6203361561962420670603457)
              ·
                refine ⟨4652521171471815502952593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203361561962420670603457 4652521171471815502952593)
                ·
                  refine ⟨3489390878603861627214445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652521171471815502952593 3489390878603861627214445)
                  ·
                    refine ⟨1308521579476448110205417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489390878603861627214445 1308521579476448110205417)
                    ·
                      rfl

theorem cell22_3822505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 2, 3].length) (baseStart_3822505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822505 prefixEnd_3822505 := by exact prefixLift 3822505
  have htrace : WordTrace (prefixWord ++ tailWord_3822505) baseStart_3822505 baseEnd_3822505 := by
    simpa [prefixWord, tailWord_3822505, baseEnd_3822505] using wordTrace_append hprefix tailTrace_3822505
  have hstable : (prefixWord ++ tailWord_3822505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822505).length < 2 ^ (prefixWord ++ tailWord_3822505).sum := by decide
  have hdescent : baseEnd_3822505 < baseStart_3822505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822563 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 7]
def baseStart_3822563 : Nat := 118140960795 + 3822563 * 2 ^ 59
def prefixEnd_3822563 : Nat := 4983230072969 + 3 ^ 40 * 3822563 * 2
def baseEnd_3822563 : Nat := 436180478020585097418413

theorem tailTrace_3822563 : CollatzResearch.WordTrace tailWord_3822563 prefixEnd_3822563 436180478020585097418413 := by
  unfold tailWord_3822563
  simp only [CollatzResearch.WordTrace]
  refine ⟨139420326450514567630120343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92946884300343045086746895 139420326450514567630120343)
  ·
    refine ⟨209130489675771851445180515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139420326450514567630120343 209130489675771851445180515)
    ·
      refine ⟨313695734513657777167770773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209130489675771851445180515 313695734513657777167770773)
      ·
        refine ⟨14704487555327708304739255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 313695734513657777167770773 14704487555327708304739255)
        ·
          refine ⟨22056731332991562457108883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14704487555327708304739255 22056731332991562457108883)
          ·
            refine ⟨33085096999487343685663325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22056731332991562457108883 33085096999487343685663325)
            ·
              refine ⟨12406911374807753882123747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33085096999487343685663325 12406911374807753882123747)
              ·
                refine ⟨18610367062211630823185621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12406911374807753882123747 18610367062211630823185621)
                ·
                  refine ⟨436180478020585097418413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18610367062211630823185621 436180478020585097418413)
                  ·
                    rfl

theorem cell22_3822563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 7].length) (baseStart_3822563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822563 prefixEnd_3822563 := by exact prefixLift 3822563
  have htrace : WordTrace (prefixWord ++ tailWord_3822563) baseStart_3822563 baseEnd_3822563 := by
    simpa [prefixWord, tailWord_3822563, baseEnd_3822563] using wordTrace_append hprefix tailTrace_3822563
  have hstable : (prefixWord ++ tailWord_3822563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822563).length < 2 ^ (prefixWord ++ tailWord_3822563).sum := by decide
  have hdescent : baseEnd_3822563 < baseStart_3822563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822567 : List Nat := [1, 1, 5, 2, 2, 2, 2, 1, 3, 3]
def baseStart_3822567 : Nat := 118140960795 + 3822567 * 2 ^ 59
def prefixEnd_3822567 : Nat := 4983230072969 + 3 ^ 40 * 3822567 * 2
def baseEnd_3822567 : Nat := 1308542803343500615155227

theorem tailTrace_3822567 : CollatzResearch.WordTrace tailWord_3822567 prefixEnd_3822567 1308542803343500615155227 := by
  unfold tailWord_3822567
  simp only [CollatzResearch.WordTrace]
  refine ⟨139420472342500076313265955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92946981561666717542177303 139420472342500076313265955)
  ·
    refine ⟨209130708513750114469898933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139420472342500076313265955 209130708513750114469898933)
    ·
      refine ⟨19606003923164073231553025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 209130708513750114469898933 19606003923164073231553025)
      ·
        refine ⟨14704502942373054923664769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19606003923164073231553025 14704502942373054923664769)
        ·
          refine ⟨11028377206779791192748577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14704502942373054923664769 11028377206779791192748577)
          ·
            refine ⟨8271282905084843394561433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11028377206779791192748577 8271282905084843394561433)
            ·
              refine ⟨6203462178813632545921075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271282905084843394561433 6203462178813632545921075)
              ·
                refine ⟨9305193268220448818881613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203462178813632545921075 9305193268220448818881613)
                ·
                  refine ⟨3489447475582668307080605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9305193268220448818881613 3489447475582668307080605)
                  ·
                    refine ⟨1308542803343500615155227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489447475582668307080605 1308542803343500615155227)
                    ·
                      rfl

theorem cell22_3822567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_3822567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822567 prefixEnd_3822567 := by exact prefixLift 3822567
  have htrace : WordTrace (prefixWord ++ tailWord_3822567) baseStart_3822567 baseEnd_3822567 := by
    simpa [prefixWord, tailWord_3822567, baseEnd_3822567] using wordTrace_append hprefix tailTrace_3822567
  have hstable : (prefixWord ++ tailWord_3822567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822567).length < 2 ^ (prefixWord ++ tailWord_3822567).sum := by decide
  have hdescent : baseEnd_3822567 < baseStart_3822567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822625 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 6]
def baseStart_3822625 : Nat := 118140960795 + 3822625 * 2 ^ 59
def prefixEnd_3822625 : Nat := 4983230072969 + 3 ^ 40 * 3822625 * 2
def baseEnd_3822625 : Nat := 436187552642935932401683

theorem tailTrace_3822625 : CollatzResearch.WordTrace tailWord_3822625 prefixEnd_3822625 436187552642935932401683 := by
  unfold tailWord_3822625
  simp only [CollatzResearch.WordTrace]
  refine ⟨139422587776289952218877329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92948391850859968145918219 139422587776289952218877329)
  ·
    refine ⟨104566940832217464164157997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139422587776289952218877329 104566940832217464164157997)
    ·
      refine ⟨39212602812081549061559249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104566940832217464164157997 39212602812081549061559249)
      ·
        refine ⟨29409452109061161796169437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39212602812081549061559249 29409452109061161796169437)
        ·
          refine ⟨11028544540897935673563539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29409452109061161796169437 11028544540897935673563539)
          ·
            refine ⟨16542816811346903510345309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11028544540897935673563539 16542816811346903510345309)
            ·
              refine ⟨6203556304255088816379491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16542816811346903510345309 6203556304255088816379491)
              ·
                refine ⟨9305334456382633224569237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6203556304255088816379491 9305334456382633224569237)
                ·
                  refine ⟨436187552642935932401683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9305334456382633224569237 436187552642935932401683)
                  ·
                    rfl

theorem cell22_3822625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_3822625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822625 prefixEnd_3822625 := by exact prefixLift 3822625
  have htrace : WordTrace (prefixWord ++ tailWord_3822625) baseStart_3822625 baseEnd_3822625 := by
    simpa [prefixWord, tailWord_3822625, baseEnd_3822625] using wordTrace_append hprefix tailTrace_3822625
  have hstable : (prefixWord ++ tailWord_3822625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822625).length < 2 ^ (prefixWord ++ tailWord_3822625).sum := by decide
  have hdescent : baseEnd_3822625 < baseStart_3822625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822644 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_3822644 : Nat := 118140960795 + 3822644 * 2 ^ 59
def prefixEnd_3822644 : Nat := 4983230072969 + 3 ^ 40 * 3822644 * 2
def baseEnd_3822644 : Nat := 1308569162017098080979991

theorem tailTrace_3822644 : CollatzResearch.WordTrace tailWord_3822644 prefixEnd_3822644 1308569162017098080979991 := by
  unfold tailWord_3822644
  simp only [CollatzResearch.WordTrace]
  refine ⟨69711640381610559231909493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92948853842147412309212657 69711640381610559231909493)
  ·
    refine ⟨6535466285775989927991515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69711640381610559231909493 6535466285775989927991515)
    ·
      refine ⟨9803199428663984891987273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6535466285775989927991515 9803199428663984891987273)
      ·
        refine ⟨7352399571497988668990455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9803199428663984891987273 7352399571497988668990455)
        ·
          refine ⟨11028599357246983003485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7352399571497988668990455 11028599357246983003485683)
          ·
            refine ⟨16542899035870474505228525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11028599357246983003485683 16542899035870474505228525)
            ·
              refine ⟨6203587138451427939460697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16542899035870474505228525 6203587138451427939460697)
              ·
                refine ⟨4652690353838570954595523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203587138451427939460697 4652690353838570954595523)
                ·
                  refine ⟨6979035530757856431893285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652690353838570954595523 6979035530757856431893285)
                  ·
                    refine ⟨1308569162017098080979991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979035530757856431893285 1308569162017098080979991)
                    ·
                      rfl

theorem cell22_3822644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_3822644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822644 prefixEnd_3822644 := by exact prefixLift 3822644
  have htrace : WordTrace (prefixWord ++ tailWord_3822644) baseStart_3822644 baseEnd_3822644 := by
    simpa [prefixWord, tailWord_3822644, baseEnd_3822644] using wordTrace_append hprefix tailTrace_3822644
  have hstable : (prefixWord ++ tailWord_3822644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822644).length < 2 ^ (prefixWord ++ tailWord_3822644).sum := by decide
  have hdescent : baseEnd_3822644 < baseStart_3822644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822657 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3822657 : Nat := 118140960795 + 3822657 * 2 ^ 59
def prefixEnd_3822657 : Nat := 4983230072969 + 3 ^ 40 * 3822657 * 2
def baseEnd_3822657 : Nat := 1308573612182770380404951

theorem tailTrace_3822657 : CollatzResearch.WordTrace tailWord_3822657 prefixEnd_3822657 1308573612182770380404951 := by
  unfold tailWord_3822657
  simp only [CollatzResearch.WordTrace]
  refine ⟨139423754912174021684042225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92949169941449347789361483 139423754912174021684042225)
  ·
    refine ⟨104567816184130516263031669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139423754912174021684042225 104567816184130516263031669)
    ·
      refine ⟨9803232767262235899659219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104567816184130516263031669 9803232767262235899659219)
      ·
        refine ⟨14704849150893353849488829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9803232767262235899659219 14704849150893353849488829)
        ·
          refine ⟨5514318431585007693558311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14704849150893353849488829 5514318431585007693558311)
          ·
            refine ⟨8271477647377511540337467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514318431585007693558311 8271477647377511540337467)
            ·
              refine ⟨12407216471066267310506201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8271477647377511540337467 12407216471066267310506201)
              ·
                refine ⟨9305412353299700482879651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12407216471066267310506201 9305412353299700482879651)
                ·
                  refine ⟨13958118529949550724319477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9305412353299700482879651 13958118529949550724319477)
                  ·
                    refine ⟨1308573612182770380404951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13958118529949550724319477 1308573612182770380404951)
                    ·
                      rfl

theorem cell22_3822657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3822657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822657 prefixEnd_3822657 := by exact prefixLift 3822657
  have htrace : WordTrace (prefixWord ++ tailWord_3822657) baseStart_3822657 baseEnd_3822657 := by
    simpa [prefixWord, tailWord_3822657, baseEnd_3822657] using wordTrace_append hprefix tailTrace_3822657
  have hstable : (prefixWord ++ tailWord_3822657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822657).length < 2 ^ (prefixWord ++ tailWord_3822657).sum := by decide
  have hdescent : baseEnd_3822657 < baseStart_3822657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822674 : List Nat := [3, 2, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3822674 : Nat := 118140960795 + 3822674 * 2 ^ 59
def prefixEnd_3822674 : Nat := 4983230072969 + 3 ^ 40 * 3822674 * 2
def baseEnd_3822674 : Nat := 1308579431630188002729899

theorem tailTrace_3822674 : CollatzResearch.WordTrace tailWord_3822674 prefixEnd_3822674 1308579431630188002729899 := by
  unfold tailWord_3822674
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856093738278108396852769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92949583302074955724940717 34856093738278108396852769)
  ·
    refine ⟨26142070303708581297639577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34856093738278108396852769 26142070303708581297639577)
    ·
      refine ⟨19606552727781435973229683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26142070303708581297639577 19606552727781435973229683)
      ·
        refine ⟨29409829091672153959844525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19606552727781435973229683 29409829091672153959844525)
        ·
          refine ⟨11028685909377057734941697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29409829091672153959844525 11028685909377057734941697)
          ·
            refine ⟨8271514432032793301206273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11028685909377057734941697 8271514432032793301206273)
            ·
              refine ⟨6203635824024594975904705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271514432032793301206273 6203635824024594975904705)
              ·
                refine ⟨4652726868018446231928529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203635824024594975904705 4652726868018446231928529)
                ·
                  refine ⟨3489545151013834673946397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4652726868018446231928529 3489545151013834673946397)
                  ·
                    refine ⟨1308579431630188002729899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489545151013834673946397 1308579431630188002729899)
                    ·
                      rfl

theorem cell22_3822674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3822674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822674 prefixEnd_3822674 := by exact prefixLift 3822674
  have htrace : WordTrace (prefixWord ++ tailWord_3822674) baseStart_3822674 baseEnd_3822674 := by
    simpa [prefixWord, tailWord_3822674, baseEnd_3822674] using wordTrace_append hprefix tailTrace_3822674
  have hstable : (prefixWord ++ tailWord_3822674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822674).length < 2 ^ (prefixWord ++ tailWord_3822674).sum := by decide
  have hdescent : baseEnd_3822674 < baseStart_3822674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822702 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_3822702 : Nat := 118140960795 + 3822702 * 2 ^ 59
def prefixEnd_3822702 : Nat := 4983230072969 + 3 ^ 40 * 3822702 * 2
def baseEnd_3822702 : Nat := 1308589016602405263029813

theorem tailTrace_3822702 : CollatzResearch.WordTrace tailWord_3822702 prefixEnd_3822702 1308589016602405263029813 := by
  unfold tailWord_3822702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17428174524626374296178795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92950264131340662912953573 17428174524626374296178795)
  ·
    refine ⟨26142261786939561444268193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17428174524626374296178795 26142261786939561444268193)
    ·
      refine ⟨19606696340204671083201145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26142261786939561444268193 19606696340204671083201145)
      ·
        refine ⟨14705022255153503312400859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19606696340204671083201145 14705022255153503312400859)
        ·
          refine ⟨22057533382730254968601289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14705022255153503312400859 22057533382730254968601289)
          ·
            refine ⟨16543150037047691226450967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22057533382730254968601289 16543150037047691226450967)
            ·
              refine ⟨24814725055571536839676451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16543150037047691226450967 24814725055571536839676451)
              ·
                refine ⟨37222087583357305259514677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24814725055571536839676451 37222087583357305259514677)
                ·
                  refine ⟨3489570710939747368079501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37222087583357305259514677 3489570710939747368079501)
                  ·
                    refine ⟨1308589016602405263029813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489570710939747368079501 1308589016602405263029813)
                    ·
                      rfl

theorem cell22_3822702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_3822702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822702 prefixEnd_3822702 := by exact prefixLift 3822702
  have htrace : WordTrace (prefixWord ++ tailWord_3822702) baseStart_3822702 baseEnd_3822702 := by
    simpa [prefixWord, tailWord_3822702, baseEnd_3822702] using wordTrace_append hprefix tailTrace_3822702
  have hstable : (prefixWord ++ tailWord_3822702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822702).length < 2 ^ (prefixWord ++ tailWord_3822702).sum := by decide
  have hdescent : baseEnd_3822702 < baseStart_3822702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822730 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3822730 : Nat := 118140960795 + 3822730 * 2 ^ 59
def prefixEnd_3822730 : Nat := 4983230072969 + 3 ^ 40 * 3822730 * 2
def baseEnd_3822730 : Nat := 1308598601574622523329727

theorem tailTrace_3822730 : CollatzResearch.WordTrace tailWord_3822730 prefixEnd_3822730 1308598601574622523329727 := by
  unfold tailWord_3822730
  simp only [CollatzResearch.WordTrace]
  refine ⟨34856604360227388787862411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92950944960606370100966429 34856604360227388787862411)
  ·
    refine ⟨52284906540341083181793617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34856604360227388787862411 52284906540341083181793617)
    ·
      refine ⟨39213679905255812386345213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52284906540341083181793617 39213679905255812386345213)
      ·
        refine ⟨14705129964470929644879455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39213679905255812386345213 14705129964470929644879455)
        ·
          refine ⟨22057694946706394467319183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14705129964470929644879455 22057694946706394467319183)
          ·
            refine ⟨33086542420059591700978775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22057694946706394467319183 33086542420059591700978775)
            ·
              refine ⟨49629813630089387551468163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33086542420059591700978775 49629813630089387551468163)
              ·
                refine ⟨74444720445134081327202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49629813630089387551468163 74444720445134081327202245)
                ·
                  refine ⟨13958385083462640248850421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74444720445134081327202245 13958385083462640248850421)
                  ·
                    refine ⟨1308598601574622523329727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13958385083462640248850421 1308598601574622523329727)
                    ·
                      rfl

theorem cell22_3822730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3822730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822730 prefixEnd_3822730 := by exact prefixLift 3822730
  have htrace : WordTrace (prefixWord ++ tailWord_3822730) baseStart_3822730 baseEnd_3822730 := by
    simpa [prefixWord, tailWord_3822730, baseEnd_3822730] using wordTrace_append hprefix tailTrace_3822730
  have hstable : (prefixWord ++ tailWord_3822730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822730).length < 2 ^ (prefixWord ++ tailWord_3822730).sum := by decide
  have hdescent : baseEnd_3822730 < baseStart_3822730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822775 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 3, 5]
def baseStart_3822775 : Nat := 118140960795 + 3822775 * 2 ^ 59
def prefixEnd_3822775 : Nat := 4983230072969 + 3 ^ 40 * 3822775 * 2
def baseEnd_3822775 : Nat := 1308614005994257405954589

theorem tailTrace_3822775 : CollatzResearch.WordTrace tailWord_3822775 prefixEnd_3822775 1308614005994257405954589 := by
  unfold tailWord_3822775
  simp only [CollatzResearch.WordTrace]
  refine ⟨139428058725746527836837779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92952039150497685224558519 139428058725746527836837779)
  ·
    refine ⟨209142088088619791755256669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139428058725746527836837779 209142088088619791755256669)
    ·
      refine ⟨78428283033232421908221251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209142088088619791755256669 78428283033232421908221251)
      ·
        refine ⟨117642424549848632862331877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78428283033232421908221251 117642424549848632862331877)
        ·
          refine ⟨22057954603096618661687227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117642424549848632862331877 22057954603096618661687227)
          ·
            refine ⟨33086931904644927992530841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22057954603096618661687227 33086931904644927992530841)
            ·
              refine ⟨24815198928483695994398131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33086931904644927992530841 24815198928483695994398131)
              ·
                refine ⟨37222798392725543991597197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24815198928483695994398131 37222798392725543991597197)
                ·
                  refine ⟨13958549397272078996848949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37222798392725543991597197 13958549397272078996848949)
                  ·
                    refine ⟨1308614005994257405954589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13958549397272078996848949 1308614005994257405954589)
                    ·
                      rfl

theorem cell22_3822775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_3822775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822775 prefixEnd_3822775 := by exact prefixLift 3822775
  have htrace : WordTrace (prefixWord ++ tailWord_3822775) baseStart_3822775 baseEnd_3822775 := by
    simpa [prefixWord, tailWord_3822775, baseEnd_3822775] using wordTrace_append hprefix tailTrace_3822775
  have hstable : (prefixWord ++ tailWord_3822775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822775).length < 2 ^ (prefixWord ++ tailWord_3822775).sum := by decide
  have hdescent : baseEnd_3822775 < baseStart_3822775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822792 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 4, 3]
def baseStart_3822792 : Nat := 118140960795 + 3822792 * 2 ^ 59
def prefixEnd_3822792 : Nat := 4983230072969 + 3 ^ 40 * 3822792 * 2
def baseEnd_3822792 : Nat := 1308619825441675028279537

theorem tailTrace_3822792 : CollatzResearch.WordTrace tailWord_3822792 prefixEnd_3822792 1308619825441675028279537 := by
  unfold tailWord_3822792
  simp only [CollatzResearch.WordTrace]
  refine ⟨69714339383342469870103315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92952452511123293160137753 69714339383342469870103315)
  ·
    refine ⟨104571509075013704805154973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69714339383342469870103315 104571509075013704805154973)
    ·
      refine ⟨39214315903130139301933115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104571509075013704805154973 39214315903130139301933115)
      ·
        refine ⟨58821473854695208952899673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39214315903130139301933115 58821473854695208952899673)
        ·
          refine ⟨44116105391021406714674755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58821473854695208952899673 44116105391021406714674755)
          ·
            refine ⟨66174158086532110072012133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44116105391021406714674755 66174158086532110072012133)
            ·
              refine ⟨12407654641224770638502275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66174158086532110072012133 12407654641224770638502275)
              ·
                refine ⟨18611481961837155957753413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12407654641224770638502275 18611481961837155957753413)
                ·
                  refine ⟨3489652867844466742078765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18611481961837155957753413 3489652867844466742078765)
                  ·
                    refine ⟨1308619825441675028279537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489652867844466742078765 1308619825441675028279537)
                    ·
                      rfl

theorem cell22_3822792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_3822792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822792 prefixEnd_3822792 := by exact prefixLift 3822792
  have htrace : WordTrace (prefixWord ++ tailWord_3822792) baseStart_3822792 baseEnd_3822792 := by
    simpa [prefixWord, tailWord_3822792, baseEnd_3822792] using wordTrace_append hprefix tailTrace_3822792
  have hstable : (prefixWord ++ tailWord_3822792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822792).length < 2 ^ (prefixWord ++ tailWord_3822792).sum := by decide
  have hdescent : baseEnd_3822792 < baseStart_3822792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822813 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3822813 : Nat := 118140960795 + 3822813 * 2 ^ 59
def prefixEnd_3822813 : Nat := 4983230072969 + 3 ^ 40 * 3822813 * 2
def baseEnd_3822813 : Nat := 1308627014170837973504473

theorem tailTrace_3822813 : CollatzResearch.WordTrace tailWord_3822813 prefixEnd_3822813 1308627014170837973504473 := by
  unfold tailWord_3822813
  simp only [CollatzResearch.WordTrace]
  refine ⟨139429444699608860326721093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92952963133072573551147395 139429444699608860326721093)
  ·
    refine ⟨26143020881176661311260205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139429444699608860326721093 26143020881176661311260205)
    ·
      refine ⟨9803632830441247991722577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26143020881176661311260205 9803632830441247991722577)
      ·
        refine ⟨7352724622830935993791933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9803632830441247991722577 7352724622830935993791933)
        ·
          refine ⟨2757271733561600997671975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7352724622830935993791933 2757271733561600997671975)
          ·
            refine ⟨4135907600342401496507963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757271733561600997671975 4135907600342401496507963)
            ·
              refine ⟨6203861400513602244761945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4135907600342401496507963 6203861400513602244761945)
              ·
                refine ⟨4652896050385201683571459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6203861400513602244761945 4652896050385201683571459)
                ·
                  refine ⟨6979344075577802525357189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4652896050385201683571459 6979344075577802525357189)
                  ·
                    refine ⟨1308627014170837973504473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979344075577802525357189 1308627014170837973504473)
                    ·
                      rfl

theorem cell22_3822813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3822813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822813 prefixEnd_3822813 := by exact prefixLift 3822813
  have htrace : WordTrace (prefixWord ++ tailWord_3822813) baseStart_3822813 baseEnd_3822813 := by
    simpa [prefixWord, tailWord_3822813, baseEnd_3822813] using wordTrace_append hprefix tailTrace_3822813
  have hstable : (prefixWord ++ tailWord_3822813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822813).length < 2 ^ (prefixWord ++ tailWord_3822813).sum := by decide
  have hdescent : baseEnd_3822813 < baseStart_3822813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822820 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3822820 : Nat := 118140960795 + 3822820 * 2 ^ 59
def prefixEnd_3822820 : Nat := 4983230072969 + 3 ^ 40 * 3822820 * 2
def baseEnd_3822820 : Nat := 1308629410413892288579451

theorem tailTrace_3822820 : CollatzResearch.WordTrace tailWord_3822820 prefixEnd_3822820 1308629410413892288579451 := by
  unfold tailWord_3822820
  simp only [CollatzResearch.WordTrace]
  refine ⟨69714850005291750261112957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92953133340389000348150609 69714850005291750261112957)
  ·
    refine ⟨26143068751984406347917359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69714850005291750261112957 26143068751984406347917359)
    ·
      refine ⟨39214603127976609521876039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26143068751984406347917359 39214603127976609521876039)
      ·
        refine ⟨58821904691964914282814059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39214603127976609521876039 58821904691964914282814059)
        ·
          refine ⟨88232857037947371424221089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58821904691964914282814059 88232857037947371424221089)
          ·
            refine ⟨66174642778460528568165817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88232857037947371424221089 66174642778460528568165817)
            ·
              refine ⟨49630982083845396426124363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66174642778460528568165817 49630982083845396426124363)
              ·
                refine ⟨74446473125768094639186545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49630982083845396426124363 74446473125768094639186545)
                ·
                  refine ⟨55834854844326070979389909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74446473125768094639186545 55834854844326070979389909)
                  ·
                    refine ⟨1308629410413892288579451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55834854844326070979389909 1308629410413892288579451)
                    ·
                      rfl

theorem cell22_3822820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3822820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822820 prefixEnd_3822820 := by exact prefixLift 3822820
  have htrace : WordTrace (prefixWord ++ tailWord_3822820) baseStart_3822820 baseEnd_3822820 := by
    simpa [prefixWord, tailWord_3822820, baseEnd_3822820] using wordTrace_append hprefix tailTrace_3822820
  have hstable : (prefixWord ++ tailWord_3822820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822820).length < 2 ^ (prefixWord ++ tailWord_3822820).sum := by decide
  have hdescent : baseEnd_3822820 < baseStart_3822820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822852 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3822852 : Nat := 118140960795 + 3822852 * 2 ^ 59
def prefixEnd_3822852 : Nat := 4983230072969 + 3 ^ 40 * 3822852 * 2
def baseEnd_3822852 : Nat := 1308640364667854871779353

theorem tailTrace_3822852 : CollatzResearch.WordTrace tailWord_3822852 prefixEnd_3822852 1308640364667854871779353 := by
  unfold tailWord_3822852
  simp only [CollatzResearch.WordTrace]
  refine ⟨69715433573233784993695405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92953911430978379991593873 69715433573233784993695405)
  ·
    refine ⟨26143287589962669372635777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69715433573233784993695405 26143287589962669372635777)
    ·
      refine ⟨19607465692472002029476833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26143287589962669372635777 19607465692472002029476833)
      ·
        refine ⟨14705599269354001522107625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19607465692472002029476833 14705599269354001522107625)
        ·
          refine ⟨11029199452015501141580719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14705599269354001522107625 11029199452015501141580719)
          ·
            refine ⟨16543799178023251712371079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029199452015501141580719 16543799178023251712371079)
            ·
              refine ⟨24815698767034877568556619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16543799178023251712371079 24815698767034877568556619)
              ·
                refine ⟨37223548150552316352834929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24815698767034877568556619 37223548150552316352834929)
                ·
                  refine ⟨27917661112914237264626197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37223548150552316352834929 27917661112914237264626197)
                  ·
                    refine ⟨1308640364667854871779353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27917661112914237264626197 1308640364667854871779353)
                    ·
                      rfl

theorem cell22_3822852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3822852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822852 prefixEnd_3822852 := by exact prefixLift 3822852
  have htrace : WordTrace (prefixWord ++ tailWord_3822852) baseStart_3822852 baseEnd_3822852 := by
    simpa [prefixWord, tailWord_3822852, baseEnd_3822852] using wordTrace_append hprefix tailTrace_3822852
  have hstable : (prefixWord ++ tailWord_3822852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822852).length < 2 ^ (prefixWord ++ tailWord_3822852).sum := by decide
  have hdescent : baseEnd_3822852 < baseStart_3822852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822888 : List Nat := [2, 1, 5, 1, 2, 2, 2, 3, 1, 3]
def baseStart_3822888 : Nat := 118140960795 + 3822888 * 2 ^ 59
def prefixEnd_3822888 : Nat := 4983230072969 + 3 ^ 40 * 3822888 * 2
def baseEnd_3822888 : Nat := 1308652688203562777879243

theorem tailTrace_3822888 : CollatzResearch.WordTrace tailWord_3822888 prefixEnd_3822888 1308652688203562777879243 := by
  unfold tailWord_3822888
  simp only [CollatzResearch.WordTrace]
  refine ⟨69716090087168574067850659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92954786782891432090467545 69716090087168574067850659)
  ·
    refine ⟨104574135130752861101775989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69716090087168574067850659 104574135130752861101775989)
    ·
      refine ⟨9803825168508080728291499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104574135130752861101775989 9803825168508080728291499)
      ·
        refine ⟨14705737752762121092437249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9803825168508080728291499 14705737752762121092437249)
        ·
          refine ⟨11029303314571590819327937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14705737752762121092437249 11029303314571590819327937)
          ·
            refine ⟨8271977485928693114495953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11029303314571590819327937 8271977485928693114495953)
            ·
              refine ⟨6203983114446519835871965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8271977485928693114495953 6203983114446519835871965)
              ·
                refine ⟨2326493667917444938451987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6203983114446519835871965 2326493667917444938451987)
                ·
                  refine ⟨3489740501876167407677981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2326493667917444938451987 3489740501876167407677981)
                  ·
                    refine ⟨1308652688203562777879243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489740501876167407677981 1308652688203562777879243)
                    ·
                      rfl

theorem cell22_3822888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_3822888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822888 prefixEnd_3822888 := by exact prefixLift 3822888
  have htrace : WordTrace (prefixWord ++ tailWord_3822888) baseStart_3822888 baseEnd_3822888 := by
    simpa [prefixWord, tailWord_3822888, baseEnd_3822888] using wordTrace_append hprefix tailTrace_3822888
  have hstable : (prefixWord ++ tailWord_3822888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822888).length < 2 ^ (prefixWord ++ tailWord_3822888).sum := by decide
  have hdescent : baseEnd_3822888 < baseStart_3822888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822895 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 10]
def baseStart_3822895 : Nat := 118140960795 + 3822895 * 2 ^ 59
def prefixEnd_3822895 : Nat := 4983230072969 + 3 ^ 40 * 3822895 * 2
def baseEnd_3822895 : Nat := 436218361482205697651407

theorem tailTrace_3822895 : CollatzResearch.WordTrace tailWord_3822895 prefixEnd_3822895 436218361482205697651407 := by
  unfold tailWord_3822895
  simp only [CollatzResearch.WordTrace]
  refine ⟨139432435485311788331206139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92954956990207858887470759 139432435485311788331206139)
  ·
    refine ⟨209148653227967682496809209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139432435485311788331206139 209148653227967682496809209)
    ·
      refine ⟨156861489920975761872606907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209148653227967682496809209 156861489920975761872606907)
      ·
        refine ⟨235292234881463642808910361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156861489920975761872606907 235292234881463642808910361)
        ·
          refine ⟨176469176161097732106682771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235292234881463642808910361 176469176161097732106682771)
          ·
            refine ⟨264703764241646598160024157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176469176161097732106682771 264703764241646598160024157)
            ·
              refine ⟨99263911590617474310009059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264703764241646598160024157 99263911590617474310009059)
              ·
                refine ⟨148895867385926211465013589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99263911590617474310009059 148895867385926211465013589)
                ·
                  refine ⟨436218361482205697651407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 148895867385926211465013589 436218361482205697651407)
                  ·
                    rfl

theorem cell22_3822895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 10].length) (baseStart_3822895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822895 prefixEnd_3822895 := by exact prefixLift 3822895
  have htrace : WordTrace (prefixWord ++ tailWord_3822895) baseStart_3822895 baseEnd_3822895 := by
    simpa [prefixWord, tailWord_3822895, baseEnd_3822895] using wordTrace_append hprefix tailTrace_3822895
  have hstable : (prefixWord ++ tailWord_3822895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822895).length < 2 ^ (prefixWord ++ tailWord_3822895).sum := by decide
  have hdescent : baseEnd_3822895 < baseStart_3822895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822912 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 6]
def baseStart_3822912 : Nat := 118140960795 + 3822912 * 2 ^ 59
def prefixEnd_3822912 : Nat := 4983230072969 + 3 ^ 40 * 3822912 * 2
def baseEnd_3822912 : Nat := 436220301298011571759723

theorem tailTrace_3822912 : CollatzResearch.WordTrace tailWord_3822912 prefixEnd_3822912 436220301298011571759723 := by
  unfold tailWord_3822912
  simp only [CollatzResearch.WordTrace]
  refine ⟨69716527763125100117287495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92955370350833466823049993 69716527763125100117287495)
  ·
    refine ⟨104574791644687650175931243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69716527763125100117287495 104574791644687650175931243)
    ·
      refine ⟨156862187467031475263896865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104574791644687650175931243 156862187467031475263896865)
      ·
        refine ⟨117646640600273606447922649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156862187467031475263896865 117646640600273606447922649)
        ·
          refine ⟨88234980450205204835941987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117646640600273606447922649 88234980450205204835941987)
          ·
            refine ⟨132352470675307807253912981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88234980450205204835941987 132352470675307807253912981)
            ·
              refine ⟨6204022062905053465027171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132352470675307807253912981 6204022062905053465027171)
              ·
                refine ⟨9306033094357580197540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204022062905053465027171 9306033094357580197540757)
                ·
                  refine ⟨436220301298011571759723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9306033094357580197540757 436220301298011571759723)
                  ·
                    rfl

theorem cell22_3822912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 6].length) (baseStart_3822912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822912 prefixEnd_3822912 := by exact prefixLift 3822912
  have htrace : WordTrace (prefixWord ++ tailWord_3822912) baseStart_3822912 baseEnd_3822912 := by
    simpa [prefixWord, tailWord_3822912, baseEnd_3822912] using wordTrace_append hprefix tailTrace_3822912
  have hstable : (prefixWord ++ tailWord_3822912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822912).length < 2 ^ (prefixWord ++ tailWord_3822912).sum := by decide
  have hdescent : baseEnd_3822912 < baseStart_3822912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822944 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 4, 3]
def baseStart_3822944 : Nat := 118140960795 + 3822944 * 2 ^ 59
def prefixEnd_3822944 : Nat := 4983230072969 + 3 ^ 40 * 3822944 * 2
def baseEnd_3822944 : Nat := 1308671858147997298479071

theorem tailTrace_3822944 : CollatzResearch.WordTrace tailWord_3822944 prefixEnd_3822944 1308671858147997298479071 := by
  unfold tailWord_3822944
  simp only [CollatzResearch.WordTrace]
  refine ⟨69717111331067134849869943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92956148441422846466493257 69717111331067134849869943)
  ·
    refine ⟨104575666996600702274804915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69717111331067134849869943 104575666996600702274804915)
    ·
      refine ⟨156863500494901053412207373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104575666996600702274804915 156863500494901053412207373)
      ·
        refine ⟨58823812685587895029577765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156863500494901053412207373 58823812685587895029577765)
        ·
          refine ⟨11029464878547730318045831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58823812685587895029577765 11029464878547730318045831)
          ·
            refine ⟨16544197317821595477068747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11029464878547730318045831 16544197317821595477068747)
            ·
              refine ⟨24816295976732393215603121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16544197317821595477068747 24816295976732393215603121)
              ·
                refine ⟨18612221982549294911702341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24816295976732393215603121 18612221982549294911702341)
                ·
                  refine ⟨3489791621727992795944189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18612221982549294911702341 3489791621727992795944189)
                  ·
                    refine ⟨1308671858147997298479071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3489791621727992795944189 1308671858147997298479071)
                    ·
                      rfl

theorem cell22_3822944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_3822944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822944 prefixEnd_3822944 := by exact prefixLift 3822944
  have htrace : WordTrace (prefixWord ++ tailWord_3822944) baseStart_3822944 baseEnd_3822944 := by
    simpa [prefixWord, tailWord_3822944, baseEnd_3822944] using wordTrace_append hprefix tailTrace_3822944
  have hstable : (prefixWord ++ tailWord_3822944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822944).length < 2 ^ (prefixWord ++ tailWord_3822944).sum := by decide
  have hdescent : baseEnd_3822944 < baseStart_3822944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3822957 : List Nat := [1, 5, 1, 1, 1, 3, 10]
def baseStart_3822957 : Nat := 118140960795 + 3822957 * 2 ^ 59
def prefixEnd_3822957 : Nat := 4983230072969 + 3 ^ 40 * 3822957 * 2
def baseEnd_3822957 : Nat := 48469492900506281403853

theorem tailTrace_3822957 : CollatzResearch.WordTrace tailWord_3822957 prefixEnd_3822957 48469492900506281403853 := by
  unfold tailWord_3822957
  simp only [CollatzResearch.WordTrace]
  refine ⟨139434696811087172919963125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92956464540724781946642083 139434696811087172919963125)
  ·
    refine ⟨13072002826039422461246543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 139434696811087172919963125 13072002826039422461246543)
    ·
      refine ⟨19608004239059133691869815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13072002826039422461246543 19608004239059133691869815)
      ·
        refine ⟨29412006358588700537804723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19608004239059133691869815 29412006358588700537804723)
        ·
          refine ⟨44118009537883050806707085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29412006358588700537804723 44118009537883050806707085)
          ·
            refine ⟨16544253576706144052515157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44118009537883050806707085 16544253576706144052515157)
            ·
              refine ⟨48469492900506281403853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16544253576706144052515157 48469492900506281403853)
              ·
                rfl

theorem cell22_3822957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 10].length) (baseStart_3822957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3822957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3822957 prefixEnd_3822957 := by exact prefixLift 3822957
  have htrace : WordTrace (prefixWord ++ tailWord_3822957) baseStart_3822957 baseEnd_3822957 := by
    simpa [prefixWord, tailWord_3822957, baseEnd_3822957] using wordTrace_append hprefix tailTrace_3822957
  have hstable : (prefixWord ++ tailWord_3822957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3822957).length < 2 ^ (prefixWord ++ tailWord_3822957).sum := by decide
  have hdescent : baseEnd_3822957 < baseStart_3822957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3822957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823042 : List Nat := [3, 5, 2, 1, 1, 1, 3, 6]
def baseStart_3823042 : Nat := 118140960795 + 3823042 * 2 ^ 59
def prefixEnd_3823042 : Nat := 4983230072969 + 3 ^ 40 * 3823042 * 2
def baseEnd_3823042 : Nat := 145411711727861967725419

theorem tailTrace_3823042 : CollatzResearch.WordTrace tailWord_3823042 prefixEnd_3823042 145411711727861967725419 := by
  unfold tailWord_3823042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859449253944808109201845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92958531343852821624538253 34859449253944808109201845)
  ·
    refine ⟨3268073367557325760237673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34859449253944808109201845 3268073367557325760237673)
    ·
      refine ⟨2451055025667994320178255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3268073367557325760237673 2451055025667994320178255)
      ·
        refine ⟨3676582538501991480267383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2451055025667994320178255 3676582538501991480267383)
        ·
          refine ⟨5514873807752987220401075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676582538501991480267383 5514873807752987220401075)
          ·
            refine ⟨8272310711629480830601613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5514873807752987220401075 8272310711629480830601613)
            ·
              refine ⟨3102116516861055311475605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8272310711629480830601613 3102116516861055311475605)
              ·
                refine ⟨145411711727861967725419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3102116516861055311475605 145411711727861967725419)
                ·
                  rfl

theorem cell22_3823042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_3823042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823042 prefixEnd_3823042 := by exact prefixLift 3823042
  have htrace : WordTrace (prefixWord ++ tailWord_3823042) baseStart_3823042 baseEnd_3823042 := by
    simpa [prefixWord, tailWord_3823042, baseEnd_3823042] using wordTrace_append hprefix tailTrace_3823042
  have hstable : (prefixWord ++ tailWord_3823042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823042).length < 2 ^ (prefixWord ++ tailWord_3823042).sum := by decide
  have hdescent : baseEnd_3823042 < baseStart_3823042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823049 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 1, 4]
def baseStart_3823049 : Nat := 118140960795 + 3823049 * 2 ^ 59
def prefixEnd_3823049 : Nat := 4983230072969 + 3 ^ 40 * 3823049 * 2
def baseEnd_3823049 : Nat := 1308707801793812024603749

theorem tailTrace_3823049 : CollatzResearch.WordTrace tailWord_3823049 prefixEnd_3823049 1308707801793812024603749 := by
  unfold tailWord_3823049
  simp only [CollatzResearch.WordTrace]
  refine ⟨139438052326753872632312201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92958701551169248421541467 139438052326753872632312201)
  ·
    refine ⟨104578539245065404474234151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139438052326753872632312201 104578539245065404474234151)
    ·
      refine ⟨156867808867598106711351227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104578539245065404474234151 156867808867598106711351227)
      ·
        refine ⟨235301713301397160067026841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156867808867598106711351227 235301713301397160067026841)
        ·
          refine ⟨176476284976047870050270131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 235301713301397160067026841 176476284976047870050270131)
          ·
            refine ⟨264714427464071805075405197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176476284976047870050270131 264714427464071805075405197)
            ·
              refine ⟨99267910299026926903276949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264714427464071805075405197 99267910299026926903276949)
              ·
                refine ⟨4653183295266887198591107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99267910299026926903276949 4653183295266887198591107)
                ·
                  refine ⟨6979774942900330797886661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653183295266887198591107 6979774942900330797886661)
                  ·
                    refine ⟨1308707801793812024603749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979774942900330797886661 1308707801793812024603749)
                    ·
                      rfl

theorem cell22_3823049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 4].length) (baseStart_3823049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823049 prefixEnd_3823049 := by exact prefixLift 3823049
  have htrace : WordTrace (prefixWord ++ tailWord_3823049) baseStart_3823049 baseEnd_3823049 := by
    simpa [prefixWord, tailWord_3823049, baseEnd_3823049] using wordTrace_append hprefix tailTrace_3823049
  have hstable : (prefixWord ++ tailWord_3823049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823049).length < 2 ^ (prefixWord ++ tailWord_3823049).sum := by decide
  have hdescent : baseEnd_3823049 < baseStart_3823049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823066 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 1, 4]
def baseStart_3823066 : Nat := 118140960795 + 3823066 * 2 ^ 59
def prefixEnd_3823066 : Nat := 4983230072969 + 3 ^ 40 * 3823066 * 2
def baseEnd_3823066 : Nat := 1308713621241229646928697

theorem tailTrace_3823066 : CollatzResearch.WordTrace tailWord_3823066 prefixEnd_3823066 1308713621241229646928697 := by
  unfold tailWord_3823066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34859668091923071133920263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92959114911794856357120701 34859668091923071133920263)
  ·
    refine ⟨52289502137884606700880395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34859668091923071133920263 52289502137884606700880395)
    ·
      refine ⟨78434253206826910051320593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52289502137884606700880395 78434253206826910051320593)
      ·
        refine ⟨58825689905120182538490445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78434253206826910051320593 58825689905120182538490445)
        ·
          refine ⟨22059633714420068451933917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58825689905120182538490445 22059633714420068451933917)
          ·
            refine ⟨8272362642907525669475219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22059633714420068451933917 8272362642907525669475219)
            ·
              refine ⟨12408543964361288504212829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272362642907525669475219 12408543964361288504212829)
              ·
                refine ⟨4653203986635483189079811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12408543964361288504212829 4653203986635483189079811)
                ·
                  refine ⟨6979805979953224783619717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653203986635483189079811 6979805979953224783619717)
                  ·
                    refine ⟨1308713621241229646928697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6979805979953224783619717 1308713621241229646928697)
                    ·
                      rfl

theorem cell22_3823066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_3823066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823066 prefixEnd_3823066 := by exact prefixLift 3823066
  have htrace : WordTrace (prefixWord ++ tailWord_3823066) baseStart_3823066 baseEnd_3823066 := by
    simpa [prefixWord, tailWord_3823066, baseEnd_3823066] using wordTrace_append hprefix tailTrace_3823066
  have hstable : (prefixWord ++ tailWord_3823066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823066).length < 2 ^ (prefixWord ++ tailWord_3823066).sum := by decide
  have hdescent : baseEnd_3823066 < baseStart_3823066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823096 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 5]
def baseStart_3823096 : Nat := 118140960795 + 3823096 * 2 ^ 59
def prefixEnd_3823096 : Nat := 4983230072969 + 3 ^ 40 * 3823096 * 2
def baseEnd_3823096 : Nat := 1308723890854319568678605

theorem tailTrace_3823096 : CollatzResearch.WordTrace tailWord_3823096 prefixEnd_3823096 1308723890854319568678605 := by
  unfold tailWord_3823096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69719883278791799829636571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92959844371722399772848761 69719883278791799829636571)
  ·
    refine ⟨104579824918187699744454857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69719883278791799829636571 104579824918187699744454857)
    ·
      refine ⟨78434868688640774808341143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104579824918187699744454857 78434868688640774808341143)
      ·
        refine ⟨117652303032961162212511715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78434868688640774808341143 117652303032961162212511715)
        ·
          refine ⟨176478454549441743318767573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117652303032961162212511715 176478454549441743318767573)
          ·
            refine ⟨4136213778502540859033615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 176478454549441743318767573 4136213778502540859033615)
            ·
              refine ⟨6204320667753811288550423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136213778502540859033615 6204320667753811288550423)
              ·
                refine ⟨9306481001630716932825635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6204320667753811288550423 9306481001630716932825635)
                ·
                  refine ⟨13959721502446075399238453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9306481001630716932825635 13959721502446075399238453)
                  ·
                    refine ⟨1308723890854319568678605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13959721502446075399238453 1308723890854319568678605)
                    ·
                      rfl

theorem cell22_3823096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_3823096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823096 prefixEnd_3823096 := by exact prefixLift 3823096
  have htrace : WordTrace (prefixWord ++ tailWord_3823096) baseStart_3823096 baseEnd_3823096 := by
    simpa [prefixWord, tailWord_3823096, baseEnd_3823096] using wordTrace_append hprefix tailTrace_3823096
  have hstable : (prefixWord ++ tailWord_3823096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823096).length < 2 ^ (prefixWord ++ tailWord_3823096).sum := by decide
  have hdescent : baseEnd_3823096 < baseStart_3823096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823115 : List Nat := [1, 1, 1, 1, 9, 1, 1, 3, 4]
def baseStart_3823115 : Nat := 118140960795 + 3823115 * 2 ^ 59
def prefixEnd_3823115 : Nat := 4983230072969 + 3 ^ 40 * 3823115 * 2
def baseEnd_3823115 : Nat := 436243464980869950817849

theorem tailTrace_3823115 : CollatzResearch.WordTrace tailWord_3823115 prefixEnd_3823115 436243464980869950817849 := by
  unfold tailWord_3823115
  simp only [CollatzResearch.WordTrace]
  refine ⟨139440459544514765904214799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92960306363009843936143199 139440459544514765904214799)
  ·
    refine ⟨209160689316772148856322199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139440459544514765904214799 209160689316772148856322199)
    ·
      refine ⟨313741033975158223284483299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209160689316772148856322199 313741033975158223284483299)
      ·
        refine ⟨470611550962737334926724949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313741033975158223284483299 470611550962737334926724949)
        ·
          refine ⟨2757489556422289071836279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 470611550962737334926724949 2757489556422289071836279)
          ·
            refine ⟨4136234334633433607754419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757489556422289071836279 4136234334633433607754419)
            ·
              refine ⟨6204351501950150411631629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136234334633433607754419 6204351501950150411631629)
              ·
                refine ⟨2326631813231306404361861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6204351501950150411631629 2326631813231306404361861)
                ·
                  refine ⟨436243464980869950817849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326631813231306404361861 436243464980869950817849)
                  ·
                    rfl

theorem cell22_3823115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 3, 4].length) (baseStart_3823115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823115 prefixEnd_3823115 := by exact prefixLift 3823115
  have htrace : WordTrace (prefixWord ++ tailWord_3823115) baseStart_3823115 baseEnd_3823115 := by
    simpa [prefixWord, tailWord_3823115, baseEnd_3823115] using wordTrace_append hprefix tailTrace_3823115
  have hstable : (prefixWord ++ tailWord_3823115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823115).length < 2 ^ (prefixWord ++ tailWord_3823115).sum := by decide
  have hdescent : baseEnd_3823115 < baseStart_3823115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823216 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 6]
def baseStart_3823216 : Nat := 118140960795 + 3823216 * 2 ^ 59
def prefixEnd_3823216 : Nat := 4983230072969 + 3 ^ 40 * 3823216 * 2
def baseEnd_3823216 : Nat := 436254989768893085226079

theorem tailTrace_3823216 : CollatzResearch.WordTrace tailWord_3823216 prefixEnd_3823216 436254989768893085226079 := by
  unfold tailWord_3823216
  simp only [CollatzResearch.WordTrace]
  refine ⟨69722071658574430076820751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92962762211432573435761001 69722071658574430076820751)
  ·
    refine ⟨104583107487861645115231127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69722071658574430076820751 104583107487861645115231127)
    ·
      refine ⟨156874661231792467672846691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104583107487861645115231127 156874661231792467672846691)
      ·
        refine ⟨235311991847688701509270037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156874661231792467672846691 235311991847688701509270037)
        ·
          refine ⟨11030249617860407883247033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235311991847688701509270037 11030249617860407883247033)
          ·
            refine ⟨8272687213395305912435275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11030249617860407883247033 8272687213395305912435275)
            ·
              refine ⟨12409030820092958868652913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8272687213395305912435275 12409030820092958868652913)
              ·
                refine ⟨9306773115069719151489685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12409030820092958868652913 9306773115069719151489685)
                ·
                  refine ⟨436254989768893085226079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9306773115069719151489685 436254989768893085226079)
                  ·
                    rfl

theorem cell22_3823216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 6].length) (baseStart_3823216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823216 prefixEnd_3823216 := by exact prefixLift 3823216
  have htrace : WordTrace (prefixWord ++ tailWord_3823216) baseStart_3823216 baseEnd_3823216 := by
    simpa [prefixWord, tailWord_3823216, baseEnd_3823216] using wordTrace_append hprefix tailTrace_3823216
  have hstable : (prefixWord ++ tailWord_3823216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823216).length < 2 ^ (prefixWord ++ tailWord_3823216).sum := by decide
  have hdescent : baseEnd_3823216 < baseStart_3823216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823233 : List Nat := [1, 2, 4, 2, 1, 2, 1, 5, 4]
def baseStart_3823233 : Nat := 118140960795 + 3823233 * 2 ^ 59
def prefixEnd_3823233 : Nat := 4983230072969 + 3 ^ 40 * 3823233 * 2
def baseEnd_3823233 : Nat := 436256929584698959334395

theorem tailTrace_3823233 : CollatzResearch.WordTrace tailWord_3823233 prefixEnd_3823233 436256929584698959334395 := by
  unfold tailWord_3823233
  simp only [CollatzResearch.WordTrace]
  refine ⟨139444763358087272057010353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92963175572058181371340235 139444763358087272057010353)
  ·
    refine ⟨104583572518565454042757765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139444763358087272057010353 104583572518565454042757765)
    ·
      refine ⟨19609419847231022633017081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104583572518565454042757765 19609419847231022633017081)
      ·
        refine ⟨14707064885423266974762811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19609419847231022633017081 14707064885423266974762811)
        ·
          refine ⟨22060597328134900462144217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14707064885423266974762811 22060597328134900462144217)
          ·
            refine ⟨16545447996101175346608163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22060597328134900462144217 16545447996101175346608163)
            ·
              refine ⟨24818171994151763019912245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16545447996101175346608163 24818171994151763019912245)
              ·
                refine ⟨2326703624451727783116773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24818171994151763019912245 2326703624451727783116773)
                ·
                  refine ⟨436256929584698959334395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326703624451727783116773 436256929584698959334395)
                  ·
                    rfl

theorem cell22_3823233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_3823233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823233 prefixEnd_3823233 := by exact prefixLift 3823233
  have htrace : WordTrace (prefixWord ++ tailWord_3823233) baseStart_3823233 baseEnd_3823233 := by
    simpa [prefixWord, tailWord_3823233, baseEnd_3823233] using wordTrace_append hprefix tailTrace_3823233
  have hstable : (prefixWord ++ tailWord_3823233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823233).length < 2 ^ (prefixWord ++ tailWord_3823233).sum := by decide
  have hdescent : baseEnd_3823233 < baseStart_3823233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823244 : List Nat := [2, 2, 1, 2, 1, 1, 13]
def baseStart_3823244 : Nat := 118140960795 + 3823244 * 2 ^ 59
def prefixEnd_3823244 : Nat := 4983230072969 + 3 ^ 40 * 3823244 * 2
def baseEnd_3823244 : Nat := 48473131639959130221413

theorem tailTrace_3823244 : CollatzResearch.WordTrace tailWord_3823244 prefixEnd_3823244 48473131639959130221413 := by
  unfold tailWord_3823244
  simp only [CollatzResearch.WordTrace]
  refine ⟨69722582280523710467830393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92963443040698280623773857 69722582280523710467830393)
  ·
    refine ⟨52291936710392782850872795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69722582280523710467830393 52291936710392782850872795)
    ·
      refine ⟨78437905065589174276309193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52291936710392782850872795 78437905065589174276309193)
      ·
        refine ⟨58828428799191880707231895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78437905065589174276309193 58828428799191880707231895)
        ·
          refine ⟨88242643198787821060847843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58828428799191880707231895 88242643198787821060847843)
          ·
            refine ⟨132363964798181731591271765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88242643198787821060847843 132363964798181731591271765)
            ·
              refine ⟨48473131639959130221413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 132363964798181731591271765 48473131639959130221413)
              ·
                rfl

theorem cell22_3823244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 13].length) (baseStart_3823244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823244 prefixEnd_3823244 := by exact prefixLift 3823244
  have htrace : WordTrace (prefixWord ++ tailWord_3823244) baseStart_3823244 baseEnd_3823244 := by
    simpa [prefixWord, tailWord_3823244, baseEnd_3823244] using wordTrace_append hprefix tailTrace_3823244
  have hstable : (prefixWord ++ tailWord_3823244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823244).length < 2 ^ (prefixWord ++ tailWord_3823244).sum := by decide
  have hdescent : baseEnd_3823244 < baseStart_3823244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823383 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 5]
def baseStart_3823383 : Nat := 118140960795 + 3823383 * 2 ^ 59
def prefixEnd_3823383 : Nat := 4983230072969 + 3 ^ 40 * 3823383 * 2
def baseEnd_3823383 : Nat := 1308822136819546486752725

theorem tailTrace_3823383 : CollatzResearch.WordTrace tailWord_3823383 prefixEnd_3823383 1308822136819546486752725 := by
  unfold tailWord_3823383
  simp only [CollatzResearch.WordTrace]
  refine ⟨139450234307543847674970803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92966822871695898449980535 139450234307543847674970803)
  ·
    refine ⟨209175351461315771512456205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139450234307543847674970803 209175351461315771512456205)
    ·
      refine ⟨78440756797993414317171077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209175351461315771512456205 78440756797993414317171077)
      ·
        refine ⟨14707641899623765184469577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78440756797993414317171077 14707641899623765184469577)
        ·
          refine ⟨11030731424717823888352183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14707641899623765184469577 11030731424717823888352183)
          ·
            refine ⟨16546097137076735832528275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11030731424717823888352183 16546097137076735832528275)
            ·
              refine ⟨24819145705615103748792413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16546097137076735832528275 24819145705615103748792413)
              ·
                refine ⟨9307179639605663905797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24819145705615103748792413 9307179639605663905797155)
                ·
                  refine ⟨13960769459408495858695733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9307179639605663905797155 13960769459408495858695733)
                  ·
                    refine ⟨1308822136819546486752725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13960769459408495858695733 1308822136819546486752725)
                    ·
                      rfl

theorem cell22_3823383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_3823383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823383 prefixEnd_3823383 := by exact prefixLift 3823383
  have htrace : WordTrace (prefixWord ++ tailWord_3823383) baseStart_3823383 baseEnd_3823383 := by
    simpa [prefixWord, tailWord_3823383, baseEnd_3823383] using wordTrace_append hprefix tailTrace_3823383
  have hstable : (prefixWord ++ tailWord_3823383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823383).length < 2 ^ (prefixWord ++ tailWord_3823383).sum := by decide
  have hdescent : baseEnd_3823383 < baseStart_3823383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823413 : List Nat := [1, 3, 3, 1, 4, 1, 9]
def baseStart_3823413 : Nat := 118140960795 + 3823413 * 2 ^ 59
def prefixEnd_3823413 : Nat := 4983230072969 + 3 ^ 40 * 3823413 * 2
def baseEnd_3823413 : Nat := 48475274312319866981579

theorem tailTrace_3823413 : CollatzResearch.WordTrace tailWord_3823413 prefixEnd_3823413 48475274312319866981579 := by
  unfold tailWord_3823413
  simp only [CollatzResearch.WordTrace]
  refine ⟨139451328497435162798562893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92967552331623441865708595 139451328497435162798562893)
  ·
    refine ⟨52294248186538186049461085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139451328497435162798562893 52294248186538186049461085)
    ·
      refine ⟨19610343069951819768547907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52294248186538186049461085 19610343069951819768547907)
      ·
        refine ⟨29415514604927729652821861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19610343069951819768547907 29415514604927729652821861)
        ·
          refine ⟨5515408988423949309904099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29415514604927729652821861 5515408988423949309904099)
          ·
            refine ⟨8273113482635923964856149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515408988423949309904099 8273113482635923964856149)
            ·
              refine ⟨48475274312319866981579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8273113482635923964856149 48475274312319866981579)
              ·
                rfl

theorem cell22_3823413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 9].length) (baseStart_3823413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823413 prefixEnd_3823413 := by exact prefixLift 3823413
  have htrace : WordTrace (prefixWord ++ tailWord_3823413) baseStart_3823413 baseEnd_3823413 := by
    simpa [prefixWord, tailWord_3823413, baseEnd_3823413] using wordTrace_append hprefix tailTrace_3823413
  have hstable : (prefixWord ++ tailWord_3823413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823413).length < 2 ^ (prefixWord ++ tailWord_3823413).sum := by decide
  have hdescent : baseEnd_3823413 < baseStart_3823413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823417 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 4, 3]
def baseStart_3823417 : Nat := 118140960795 + 3823417 * 2 ^ 59
def prefixEnd_3823417 : Nat := 4983230072969 + 3 ^ 40 * 3823417 * 2
def baseEnd_3823417 : Nat := 1308833775714381731402621

theorem tailTrace_3823417 : CollatzResearch.WordTrace tailWord_3823417 prefixEnd_3823417 1308833775714381731402621 := by
  unfold tailWord_3823417
  simp only [CollatzResearch.WordTrace]
  refine ⟨139451474389420671481708505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92967649592947114321139003 139451474389420671481708505)
  ·
    refine ⟨104588605792065503611281379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139451474389420671481708505 104588605792065503611281379)
    ·
      refine ⟨156882908688098255416922069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104588605792065503611281379 156882908688098255416922069)
      ·
        refine ⟨3676943172377302861334111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 156882908688098255416922069 3676943172377302861334111)
        ·
          refine ⟨5515414758565954292001167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3676943172377302861334111 5515414758565954292001167)
          ·
            refine ⟨8273122137848931438001751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5515414758565954292001167 8273122137848931438001751)
            ·
              refine ⟨12409683206773397157002627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273122137848931438001751 12409683206773397157002627)
              ·
                refine ⟨18614524810160095735503941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12409683206773397157002627 18614524810160095735503941)
                ·
                  refine ⟨3490223401905017950406989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18614524810160095735503941 3490223401905017950406989)
                  ·
                    refine ⟨1308833775714381731402621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490223401905017950406989 1308833775714381731402621)
                    ·
                      rfl

theorem cell22_3823417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 3].length) (baseStart_3823417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823417 prefixEnd_3823417 := by exact prefixLift 3823417
  have htrace : WordTrace (prefixWord ++ tailWord_3823417) baseStart_3823417 baseEnd_3823417 := by
    simpa [prefixWord, tailWord_3823417, baseEnd_3823417] using wordTrace_append hprefix tailTrace_3823417
  have hstable : (prefixWord ++ tailWord_3823417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823417).length < 2 ^ (prefixWord ++ tailWord_3823417).sum := by decide
  have hdescent : baseEnd_3823417 < baseStart_3823417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823445 : List Nat := [1, 3, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_3823445 : Nat := 118140960795 + 3823445 * 2 ^ 59
def prefixEnd_3823445 : Nat := 4983230072969 + 3 ^ 40 * 3823445 * 2
def baseEnd_3823445 : Nat := 1308843360686598991702535

theorem tailTrace_3823445 : CollatzResearch.WordTrace tailWord_3823445 prefixEnd_3823445 1308843360686598991702535 := by
  unfold tailWord_3823445
  simp only [CollatzResearch.WordTrace]
  refine ⟨139452495633319232263727789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92968330422212821509151859 139452495633319232263727789)
  ·
    refine ⟨52294685862494712098897921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139452495633319232263727789 52294685862494712098897921)
    ·
      refine ⟨39221014396871034074173441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52294685862494712098897921 39221014396871034074173441)
      ·
        refine ⟨29415760797653275555630081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39221014396871034074173441 29415760797653275555630081)
        ·
          refine ⟨22061820598239956666722561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29415760797653275555630081 22061820598239956666722561)
          ·
            refine ⟨16546365448679967500041921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22061820598239956666722561 16546365448679967500041921)
            ·
              refine ⟨12409774086509975625031441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16546365448679967500041921 12409774086509975625031441)
              ·
                refine ⟨9307330564882481718773581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12409774086509975625031441 9307330564882481718773581)
                ·
                  refine ⟨3490248961830930644540093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9307330564882481718773581 3490248961830930644540093)
                  ·
                    refine ⟨1308843360686598991702535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490248961830930644540093 1308843360686598991702535)
                    ·
                      rfl

theorem cell22_3823445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_3823445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823445 prefixEnd_3823445 := by exact prefixLift 3823445
  have htrace : WordTrace (prefixWord ++ tailWord_3823445) baseStart_3823445 baseEnd_3823445 := by
    simpa [prefixWord, tailWord_3823445, baseEnd_3823445] using wordTrace_append hprefix tailTrace_3823445
  have hstable : (prefixWord ++ tailWord_3823445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823445).length < 2 ^ (prefixWord ++ tailWord_3823445).sum := by decide
  have hdescent : baseEnd_3823445 < baseStart_3823445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823447 : List Nat := [1, 1, 3, 2, 6, 1, 2, 6]
def baseStart_3823447 : Nat := 118140960795 + 3823447 * 2 ^ 59
def prefixEnd_3823447 : Nat := 4983230072969 + 3 ^ 40 * 3823447 * 2
def baseEnd_3823447 : Nat := 145427116147496850350281

theorem tailTrace_3823447 : CollatzResearch.WordTrace tailWord_3823447 prefixEnd_3823447 145427116147496850350281 := by
  unfold tailWord_3823447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139452568579311986605300595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92968379052874657736867063 139452568579311986605300595)
  ·
    refine ⟨209178852868967979907950893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139452568579311986605300595 209178852868967979907950893)
    ·
      refine ⟨78442069825862992465481585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209178852868967979907950893 78442069825862992465481585)
      ·
        refine ⟨58831552369397244349111189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78442069825862992465481585 58831552369397244349111189)
        ·
          refine ⟨2757729017315495828864587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 58831552369397244349111189 2757729017315495828864587)
          ·
            refine ⟨4136593525973243743296881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757729017315495828864587 4136593525973243743296881)
            ·
              refine ⟨3102445144479932807472661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4136593525973243743296881 3102445144479932807472661)
              ·
                refine ⟨145427116147496850350281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3102445144479932807472661 145427116147496850350281)
                ·
                  rfl

theorem cell22_3823447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 6].length) (baseStart_3823447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823447 prefixEnd_3823447 := by exact prefixLift 3823447
  have htrace : WordTrace (prefixWord ++ tailWord_3823447) baseStart_3823447 baseEnd_3823447 := by
    simpa [prefixWord, tailWord_3823447, baseEnd_3823447] using wordTrace_append hprefix tailTrace_3823447
  have hstable : (prefixWord ++ tailWord_3823447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823447).length < 2 ^ (prefixWord ++ tailWord_3823447).sum := by decide
  have hdescent : baseEnd_3823447 < baseStart_3823447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823488 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 3, 4]
def baseStart_3823488 : Nat := 118140960795 + 3823488 * 2 ^ 59
def prefixEnd_3823488 : Nat := 4983230072969 + 3 ^ 40 * 3823488 * 2
def baseEnd_3823488 : Nat := 1308858080465361212877403

theorem tailTrace_3823488 : CollatzResearch.WordTrace tailWord_3823488 prefixEnd_3823488 1308858080465361212877403 := by
  unfold tailWord_3823488
  simp only [CollatzResearch.WordTrace]
  refine ⟨69727031986081725303771559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92969375981442300405028745 69727031986081725303771559)
  ·
    refine ⟨104590547979122587955657339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69727031986081725303771559 104590547979122587955657339)
    ·
      refine ⟨156885821968683881933486009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104590547979122587955657339 156885821968683881933486009)
      ·
        refine ⟨117664366476512911450114507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156885821968683881933486009 117664366476512911450114507)
        ·
          refine ⟨176496549714769367175171761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117664366476512911450114507 176496549714769367175171761)
          ·
            refine ⟨132372412286077025381378821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176496549714769367175171761 132372412286077025381378821)
            ·
              refine ⟨24819827303639442259008529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132372412286077025381378821 24819827303639442259008529)
              ·
                refine ⟨18614870477729581694256397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24819827303639442259008529 18614870477729581694256397)
                ·
                  refine ⟨6980576429148593135346149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18614870477729581694256397 6980576429148593135346149)
                  ·
                    refine ⟨1308858080465361212877403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6980576429148593135346149 1308858080465361212877403)
                    ·
                      rfl

theorem cell22_3823488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3, 4].length) (baseStart_3823488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823488 prefixEnd_3823488 := by exact prefixLift 3823488
  have htrace : WordTrace (prefixWord ++ tailWord_3823488) baseStart_3823488 baseEnd_3823488 := by
    simpa [prefixWord, tailWord_3823488, baseEnd_3823488] using wordTrace_append hprefix tailTrace_3823488
  have hstable : (prefixWord ++ tailWord_3823488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823488).length < 2 ^ (prefixWord ++ tailWord_3823488).sum := by decide
  have hdescent : baseEnd_3823488 < baseStart_3823488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823505 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 1, 4]
def baseStart_3823505 : Nat := 118140960795 + 3823505 * 2 ^ 59
def prefixEnd_3823505 : Nat := 4983230072969 + 3 ^ 40 * 3823505 * 2
def baseEnd_3823505 : Nat := 1308863899912778835202351

theorem tailTrace_3823505 : CollatzResearch.WordTrace tailWord_3823505 prefixEnd_3823505 1308863899912778835202351 := by
  unfold tailWord_3823505
  simp only [CollatzResearch.WordTrace]
  refine ⟨139454684013101862510911969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92969789342067908340607979 139454684013101862510911969)
  ·
    refine ⟨104591013009826396883183977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139454684013101862510911969 104591013009826396883183977)
    ·
      refine ⟨78443259757369797662387983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104591013009826396883183977 78443259757369797662387983)
      ·
        refine ⟨117664889636054696493581975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78443259757369797662387983 117664889636054696493581975)
        ·
          refine ⟨176497334454082044740372963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117664889636054696493581975 176497334454082044740372963)
          ·
            refine ⟨264746001681123067110559445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176497334454082044740372963 264746001681123067110559445)
            ·
              refine ⟨6204984414401321885403737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 264746001681123067110559445 6204984414401321885403737)
              ·
                refine ⟨4653738310800991414052803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6204984414401321885403737 4653738310800991414052803)
                ·
                  refine ⟨6980607466201487121079205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4653738310800991414052803 6980607466201487121079205)
                  ·
                    refine ⟨1308863899912778835202351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6980607466201487121079205 1308863899912778835202351)
                    ·
                      rfl

theorem cell22_3823505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 4].length) (baseStart_3823505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823505 prefixEnd_3823505 := by exact prefixLift 3823505
  have htrace : WordTrace (prefixWord ++ tailWord_3823505) baseStart_3823505 baseEnd_3823505 := by
    simpa [prefixWord, tailWord_3823505, baseEnd_3823505] using wordTrace_append hprefix tailTrace_3823505
  have hstable : (prefixWord ++ tailWord_3823505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823505).length < 2 ^ (prefixWord ++ tailWord_3823505).sum := by decide
  have hdescent : baseEnd_3823505 < baseStart_3823505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823520 : List Nat := [2, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_3823520 : Nat := 118140960795 + 3823520 * 2 ^ 59
def prefixEnd_3823520 : Nat := 4983230072969 + 3 ^ 40 * 3823520 * 2
def baseEnd_3823520 : Nat := 436289678239774598692435

theorem tailTrace_3823520 : CollatzResearch.WordTrace tailWord_3823520 prefixEnd_3823520 436289678239774598692435 := by
  unfold tailWord_3823520
  simp only [CollatzResearch.WordTrace]
  refine ⟨69727615554023760036354007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92970154072031680048472009 69727615554023760036354007)
  ·
    refine ⟨104591423331035640054531011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69727615554023760036354007 104591423331035640054531011)
    ·
      refine ⟨156887134996553460081796517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104591423331035640054531011 156887134996553460081796517)
      ·
        refine ⟨29416337811853773765336847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 156887134996553460081796517 29416337811853773765336847)
        ·
          refine ⟨44124506717780660648005271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29416337811853773765336847 44124506717780660648005271)
          ·
            refine ⟨66186760076670990972007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44124506717780660648005271 66186760076670990972007907)
            ·
              refine ⟨99280140115006486458011861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66186760076670990972007907 99280140115006486458011861)
              ·
                refine ⟨2326878283945464526359653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 99280140115006486458011861 2326878283945464526359653)
                ·
                  refine ⟨436289678239774598692435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326878283945464526359653 436289678239774598692435)
                  ·
                    rfl

theorem cell22_3823520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_3823520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823520 prefixEnd_3823520 := by exact prefixLift 3823520
  have htrace : WordTrace (prefixWord ++ tailWord_3823520) baseStart_3823520 baseEnd_3823520 := by
    simpa [prefixWord, tailWord_3823520, baseEnd_3823520] using wordTrace_append hprefix tailTrace_3823520
  have hstable : (prefixWord ++ tailWord_3823520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823520).length < 2 ^ (prefixWord ++ tailWord_3823520).sum := by decide
  have hdescent : baseEnd_3823520 < baseStart_3823520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823537 : List Nat := [1, 2, 2, 4, 2, 2, 1, 4, 4]
def baseStart_3823537 : Nat := 118140960795 + 3823537 * 2 ^ 59
def prefixEnd_3823537 : Nat := 4983230072969 + 3 ^ 40 * 3823537 * 2
def baseEnd_3823537 : Nat := 436291618055580472800751

theorem tailTrace_3823537 : CollatzResearch.WordTrace tailWord_3823537 prefixEnd_3823537 436291618055580472800751 := by
  unfold tailWord_3823537
  simp only [CollatzResearch.WordTrace]
  refine ⟨139455851148985931976076865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92970567432657287984051243 139455851148985931976076865)
  ·
    refine ⟨104591888361739448982057649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139455851148985931976076865 104591888361739448982057649)
    ·
      refine ⟨78443916271304586736543237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104591888361739448982057649 78443916271304586736543237)
      ·
        refine ⟨14708234300869610013101857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78443916271304586736543237 14708234300869610013101857)
        ·
          refine ⟨11031175725652207509826393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14708234300869610013101857 11031175725652207509826393)
          ·
            refine ⟨8273381794239155632369795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11031175725652207509826393 8273381794239155632369795)
            ·
              refine ⟨12410072691358733448554693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8273381794239155632369795 12410072691358733448554693)
              ·
                refine ⟨2326888629629762521604005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12410072691358733448554693 2326888629629762521604005)
                ·
                  refine ⟨436291618055580472800751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326888629629762521604005 436291618055580472800751)
                  ·
                    rfl

theorem cell22_3823537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_3823537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823537 prefixEnd_3823537 := by exact prefixLift 3823537
  have htrace : WordTrace (prefixWord ++ tailWord_3823537) baseStart_3823537 baseEnd_3823537 := by
    simpa [prefixWord, tailWord_3823537, baseEnd_3823537] using wordTrace_append hprefix tailTrace_3823537
  have hstable : (prefixWord ++ tailWord_3823537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823537).length < 2 ^ (prefixWord ++ tailWord_3823537).sum := by decide
  have hdescent : baseEnd_3823537 < baseStart_3823537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823614 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_3823614 : Nat := 118140960795 + 3823614 * 2 ^ 59
def prefixEnd_3823614 : Nat := 4983230072969 + 3 ^ 40 * 3823614 * 2
def baseEnd_3823614 : Nat := 1308901212840338884227017

theorem tailTrace_3823614 : CollatzResearch.WordTrace tailWord_3823614 prefixEnd_3823614 1308901212840338884227017 := by
  unfold tailWord_3823614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17432332446213371765828737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92972439713137982751086597 17432332446213371765828737)
  ·
    refine ⟨13074249334660028824371553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17432332446213371765828737 13074249334660028824371553)
    ·
      refine ⟨9805687000995021618278665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13074249334660028824371553 9805687000995021618278665)
      ·
        refine ⟨7354265250746266213708999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9805687000995021618278665 7354265250746266213708999)
        ·
          refine ⟨11031397876119399320563499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354265250746266213708999 11031397876119399320563499)
          ·
            refine ⟨16547096814179098980845249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11031397876119399320563499 16547096814179098980845249)
            ·
              refine ⟨12410322610634324235633937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547096814179098980845249 12410322610634324235633937)
              ·
                refine ⟨9307741957975743176725453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12410322610634324235633937 9307741957975743176725453)
                ·
                  refine ⟨3490403234240903691272045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9307741957975743176725453 3490403234240903691272045)
                  ·
                    refine ⟨1308901212840338884227017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490403234240903691272045 1308901212840338884227017)
                    ·
                      rfl

theorem cell22_3823614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_3823614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823614 prefixEnd_3823614 := by exact prefixLift 3823614
  have htrace : WordTrace (prefixWord ++ tailWord_3823614) baseStart_3823614 baseEnd_3823614 := by
    simpa [prefixWord, tailWord_3823614, baseEnd_3823614] using wordTrace_append hprefix tailTrace_3823614
  have hstable : (prefixWord ++ tailWord_3823614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823614).length < 2 ^ (prefixWord ++ tailWord_3823614).sum := by decide
  have hdescent : baseEnd_3823614 < baseStart_3823614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823622 : List Nat := [6, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_3823622 : Nat := 118140960795 + 3823622 * 2 ^ 59
def prefixEnd_3823622 : Nat := 4983230072969 + 3 ^ 40 * 3823622 * 2
def baseEnd_3823622 : Nat := 436301317134609843342331

theorem tailTrace_3823622 : CollatzResearch.WordTrace tailWord_3823622 prefixEnd_3823622 436301317134609843342331 := by
  unfold tailWord_3823622
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358092229802437234153785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 92972634235785327661947413 4358092229802437234153785)
  ·
    refine ⟨3268569172351827925615339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4358092229802437234153785 3268569172351827925615339)
    ·
      refine ⟨4902853758527741888423009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268569172351827925615339 4902853758527741888423009)
      ·
        refine ⟨3677140318895806416317257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902853758527741888423009 3677140318895806416317257)
        ·
          refine ⟨2757855239171854812237943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677140318895806416317257 2757855239171854812237943)
          ·
            refine ⟨4136782858757782218356915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2757855239171854812237943 4136782858757782218356915)
            ·
              refine ⟨6205174288136673327535373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136782858757782218356915 6205174288136673327535373)
              ·
                refine ⟨2326940358051252497825765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6205174288136673327535373 2326940358051252497825765)
                ·
                  refine ⟨436301317134609843342331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2326940358051252497825765 436301317134609843342331)
                  ·
                    rfl

theorem cell22_3823622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_3823622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823622 prefixEnd_3823622 := by exact prefixLift 3823622
  have htrace : WordTrace (prefixWord ++ tailWord_3823622) baseStart_3823622 baseEnd_3823622 := by
    simpa [prefixWord, tailWord_3823622, baseEnd_3823622] using wordTrace_append hprefix tailTrace_3823622
  have hstable : (prefixWord ++ tailWord_3823622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823622).length < 2 ^ (prefixWord ++ tailWord_3823622).sum := by decide
  have hdescent : baseEnd_3823622 < baseStart_3823622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823704 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 2, 3]
def baseStart_3823704 : Nat := 118140960795 + 3823704 * 2 ^ 59
def prefixEnd_3823704 : Nat := 4983230072969 + 3 ^ 40 * 3823704 * 2
def baseEnd_3823704 : Nat := 1308932021679608649476741

theorem tailTrace_3823704 : CollatzResearch.WordTrace tailWord_3823704 prefixEnd_3823704 1308932021679608649476741 := by
  unfold tailWord_3823704
  simp only [CollatzResearch.WordTrace]
  refine ⟨69730971069690459748703083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92974628092920612998270777 69730971069690459748703083)
  ·
    refine ⟨104596456604535689623054625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69730971069690459748703083 104596456604535689623054625)
    ·
      refine ⟨78447342453401767217290969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104596456604535689623054625 78447342453401767217290969)
      ·
        refine ⟨58835506840051325412968227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78447342453401767217290969 58835506840051325412968227)
        ·
          refine ⟨88253260260076988119452341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58835506840051325412968227 88253260260076988119452341)
          ·
            refine ⟨8273743149382217636198657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88253260260076988119452341 8273743149382217636198657)
            ·
              refine ⟨6205307362036663227148993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8273743149382217636198657 6205307362036663227148993)
              ·
                refine ⟨4653980521527497420361745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205307362036663227148993 4653980521527497420361745)
                ·
                  refine ⟨3490485391145623065271309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4653980521527497420361745 3490485391145623065271309)
                  ·
                    refine ⟨1308932021679608649476741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490485391145623065271309 1308932021679608649476741)
                    ·
                      rfl

theorem cell22_3823704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_3823704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823704 prefixEnd_3823704 := by exact prefixLift 3823704
  have htrace : WordTrace (prefixWord ++ tailWord_3823704) baseStart_3823704 baseEnd_3823704 := by
    simpa [prefixWord, tailWord_3823704, baseEnd_3823704] using wordTrace_append hprefix tailTrace_3823704
  have hstable : (prefixWord ++ tailWord_3823704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823704).length < 2 ^ (prefixWord ++ tailWord_3823704).sum := by decide
  have hdescent : baseEnd_3823704 < baseStart_3823704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823717 : List Nat := [1, 3, 1, 3, 2, 4, 1, 7]
def baseStart_3823717 : Nat := 118140960795 + 3823717 * 2 ^ 59
def prefixEnd_3823717 : Nat := 4983230072969 + 3 ^ 40 * 3823717 * 2
def baseEnd_3823717 : Nat := 145437385760586772100189

theorem tailTrace_3823717 : CollatzResearch.WordTrace tailWord_3823717 prefixEnd_3823717 145437385760586772100189 := by
  unfold tailWord_3823717
  simp only [CollatzResearch.WordTrace]
  refine ⟨139462416288333822717629405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92974944192222548478419603 139462416288333822717629405)
  ·
    refine ⟨52298406108125183519111027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139462416288333822717629405 52298406108125183519111027)
    ·
      refine ⟨78447609162187775278666541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52298406108125183519111027 78447609162187775278666541)
      ·
        refine ⟨29417853435820415729499953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78447609162187775278666541 29417853435820415729499953)
        ·
          refine ⟨22063390076865311797124965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29417853435820415729499953 22063390076865311797124965)
          ·
            refine ⟨4136885639412245961960931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22063390076865311797124965 4136885639412245961960931)
            ·
              refine ⟨6205328459118368942941397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4136885639412245961960931 6205328459118368942941397)
              ·
                refine ⟨145437385760586772100189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6205328459118368942941397 145437385760586772100189)
                ·
                  rfl

theorem cell22_3823717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 7].length) (baseStart_3823717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823717 prefixEnd_3823717 := by exact prefixLift 3823717
  have htrace : WordTrace (prefixWord ++ tailWord_3823717) baseStart_3823717 baseEnd_3823717 := by
    simpa [prefixWord, tailWord_3823717, baseEnd_3823717] using wordTrace_append hprefix tailTrace_3823717
  have hstable : (prefixWord ++ tailWord_3823717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823717).length < 2 ^ (prefixWord ++ tailWord_3823717).sum := by decide
  have hdescent : baseEnd_3823717 < baseStart_3823717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823734 : List Nat := [5, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3823734 : Nat := 118140960795 + 3823734 * 2 ^ 59
def prefixEnd_3823734 : Nat := 4983230072969 + 3 ^ 40 * 3823734 * 2
def baseEnd_3823734 : Nat := 145438032365855396802961

theorem tailTrace_3823734 : CollatzResearch.WordTrace tailWord_3823734 prefixEnd_3823734 145438032365855396802961 := by
  unfold tailWord_3823734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8716439770579514663812391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 92975357552848156413998837 8716439770579514663812391)
  ·
    refine ⟨13074659655869271995718587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8716439770579514663812391 13074659655869271995718587)
    ·
      refine ⟨19611989483803907993577881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13074659655869271995718587 19611989483803907993577881)
      ·
        refine ⟨14708992112852930995183411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19611989483803907993577881 14708992112852930995183411)
        ·
          refine ⟨22063488169279396492775117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14708992112852930995183411 22063488169279396492775117)
          ·
            refine ⟨8273808063479773684790669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22063488169279396492775117 8273808063479773684790669)
            ·
              refine ⟨3102678023804915131796501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8273808063479773684790669 3102678023804915131796501)
              ·
                refine ⟨145438032365855396802961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3102678023804915131796501 145438032365855396802961)
                ·
                  rfl

theorem cell22_3823734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3823734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823734 prefixEnd_3823734 := by exact prefixLift 3823734
  have htrace : WordTrace (prefixWord ++ tailWord_3823734) baseStart_3823734 baseEnd_3823734 := by
    simpa [prefixWord, tailWord_3823734, baseEnd_3823734] using wordTrace_append hprefix tailTrace_3823734
  have hstable : (prefixWord ++ tailWord_3823734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823734).length < 2 ^ (prefixWord ++ tailWord_3823734).sum := by decide
  have hdescent : baseEnd_3823734 < baseStart_3823734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823760 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 5]
def baseStart_3823760 : Nat := 118140960795 + 3823760 * 2 ^ 59
def prefixEnd_3823760 : Nat := 4983230072969 + 3 ^ 40 * 3823760 * 2
def baseEnd_3823760 : Nat := 1308951191624043170076569

theorem tailTrace_3823760 : CollatzResearch.WordTrace tailWord_3823760 prefixEnd_3823760 1308951191624043170076569 := by
  unfold tailWord_3823760
  simp only [CollatzResearch.WordTrace]
  refine ⟨69731992313589020530722367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92975989751452027374296489 69731992313589020530722367)
  ·
    refine ⟨104597988470383530796083551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69731992313589020530722367 104597988470383530796083551)
    ·
      refine ⟨156896982705575296194125327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104597988470383530796083551 156896982705575296194125327)
      ·
        refine ⟨235345474058362944291187991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156896982705575296194125327 235345474058362944291187991)
        ·
          refine ⟨353018211087544416436781987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235345474058362944291187991 353018211087544416436781987)
          ·
            refine ⟨529527316631316624655172981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353018211087544416436781987 529527316631316624655172981)
            ·
              refine ⟨49643185934185933561422467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 529527316631316624655172981 49643185934185933561422467)
              ·
                refine ⟨74464778901278900342133701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49643185934185933561422467 74464778901278900342133701)
                ·
                  refine ⟨13962146043989793814150069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74464778901278900342133701 13962146043989793814150069)
                  ·
                    refine ⟨1308951191624043170076569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13962146043989793814150069 1308951191624043170076569)
                    ·
                      rfl

theorem cell22_3823760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_3823760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823760 prefixEnd_3823760 := by exact prefixLift 3823760
  have htrace : WordTrace (prefixWord ++ tailWord_3823760) baseStart_3823760 baseEnd_3823760 := by
    simpa [prefixWord, tailWord_3823760, baseEnd_3823760] using wordTrace_append hprefix tailTrace_3823760
  have hstable : (prefixWord ++ tailWord_3823760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823760).length < 2 ^ (prefixWord ++ tailWord_3823760).sum := by decide
  have hdescent : baseEnd_3823760 < baseStart_3823760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823762 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_3823762 : Nat := 118140960795 + 3823762 * 2 ^ 59
def prefixEnd_3823762 : Nat := 4983230072969 + 3 ^ 40 * 3823762 * 2
def baseEnd_3823762 : Nat := 436317292088305277175521

theorem tailTrace_3823762 : CollatzResearch.WordTrace tailWord_3823762 prefixEnd_3823762 436317292088305277175521 := by
  unfold tailWord_3823762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34866014393292698850754385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92976038382113863602011693 34866014393292698850754385)
  ·
    refine ⟨26149510794969524138065789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34866014393292698850754385 26149510794969524138065789)
    ·
      refine ⟨9806066548113571551774671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26149510794969524138065789 9806066548113571551774671)
      ·
        refine ⟨14709099822170357327662007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9806066548113571551774671 14709099822170357327662007)
        ·
          refine ⟨22063649733255535991493011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14709099822170357327662007 22063649733255535991493011)
          ·
            refine ⟨33095474599883303987239517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22063649733255535991493011 33095474599883303987239517)
            ·
              refine ⟨12410802974956238995214819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33095474599883303987239517 12410802974956238995214819)
              ·
                refine ⟨18616204462434358492822229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410802974956238995214819 18616204462434358492822229)
                ·
                  refine ⟨436317292088305277175521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18616204462434358492822229 436317292088305277175521)
                  ·
                    rfl

theorem cell22_3823762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_3823762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823762 prefixEnd_3823762 := by exact prefixLift 3823762
  have htrace : WordTrace (prefixWord ++ tailWord_3823762) baseStart_3823762 baseEnd_3823762 := by
    simpa [prefixWord, tailWord_3823762, baseEnd_3823762] using wordTrace_append hprefix tailTrace_3823762
  have hstable : (prefixWord ++ tailWord_3823762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823762).length < 2 ^ (prefixWord ++ tailWord_3823762).sum := by decide
  have hdescent : baseEnd_3823762 < baseStart_3823762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823777 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 5]
def baseStart_3823777 : Nat := 118140960795 + 3823777 * 2 ^ 59
def prefixEnd_3823777 : Nat := 4983230072969 + 3 ^ 40 * 3823777 * 2
def baseEnd_3823777 : Nat := 1308957011071460792401517

theorem tailTrace_3823777 : CollatzResearch.WordTrace tailWord_3823777 prefixEnd_3823777 1308957011071460792401517 := by
  unfold tailWord_3823777
  simp only [CollatzResearch.WordTrace]
  refine ⟨139464604668116452964813585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92976403112077635309875723 139464604668116452964813585)
  ·
    refine ⟨104598453501087339723610189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139464604668116452964813585 104598453501087339723610189)
    ·
      refine ⟨39224420062907752396353821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104598453501087339723610189 39224420062907752396353821)
      ·
        refine ⟨14709157523590407148632683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39224420062907752396353821 14709157523590407148632683)
        ·
          refine ⟨22063736285385610722949025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14709157523590407148632683 22063736285385610722949025)
          ·
            refine ⟨16547802214039208042211769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22063736285385610722949025 16547802214039208042211769)
            ·
              refine ⟨12410851660529406031658827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16547802214039208042211769 12410851660529406031658827)
              ·
                refine ⟨18616277490794109047488241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12410851660529406031658827 18616277490794109047488241)
                ·
                  refine ⟨13962208118095581785616181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18616277490794109047488241 13962208118095581785616181)
                  ·
                    refine ⟨1308957011071460792401517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13962208118095581785616181 1308957011071460792401517)
                    ·
                      rfl

theorem cell22_3823777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 5].length) (baseStart_3823777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823777 prefixEnd_3823777 := by exact prefixLift 3823777
  have htrace : WordTrace (prefixWord ++ tailWord_3823777) baseStart_3823777 baseEnd_3823777 := by
    simpa [prefixWord, tailWord_3823777, baseEnd_3823777] using wordTrace_append hprefix tailTrace_3823777
  have hstable : (prefixWord ++ tailWord_3823777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823777).length < 2 ^ (prefixWord ++ tailWord_3823777).sum := by decide
  have hdescent : baseEnd_3823777 < baseStart_3823777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823835 : List Nat := [1, 1, 1, 1, 1, 1, 1, 15]
def baseStart_3823835 : Nat := 118140960795 + 3823835 * 2 ^ 59
def prefixEnd_3823835 : Nat := 4983230072969 + 3 ^ 40 * 3823835 * 2
def baseEnd_3823835 : Nat := 145441873961863108272371

theorem tailTrace_3823835 : CollatzResearch.WordTrace tailWord_3823835 prefixEnd_3823835 145441873961863108272371 := by
  unfold tailWord_3823835
  simp only [CollatzResearch.WordTrace]
  refine ⟨139466720101906328870424959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92977813401270885913616639 139466720101906328870424959)
  ·
    refine ⟨209200080152859493305637439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139466720101906328870424959 209200080152859493305637439)
    ·
      refine ⟨313800120229289239958456159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209200080152859493305637439 313800120229289239958456159)
      ·
        refine ⟨470700180343933859937684239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313800120229289239958456159 470700180343933859937684239)
        ·
          refine ⟨706050270515900789906526359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 470700180343933859937684239 706050270515900789906526359)
          ·
            refine ⟨1059075405773851184859789539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 706050270515900789906526359 1059075405773851184859789539)
            ·
              refine ⟨1588613108660776777289684309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1059075405773851184859789539 1588613108660776777289684309)
              ·
                refine ⟨145441873961863108272371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 15 1588613108660776777289684309 145441873961863108272371)
                ·
                  rfl

theorem cell22_3823835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15].length) (baseStart_3823835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823835 prefixEnd_3823835 := by exact prefixLift 3823835
  have htrace : WordTrace (prefixWord ++ tailWord_3823835) baseStart_3823835 baseEnd_3823835 := by
    simpa [prefixWord, tailWord_3823835, baseEnd_3823835] using wordTrace_append hprefix tailTrace_3823835
  have hstable : (prefixWord ++ tailWord_3823835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823835).length < 2 ^ (prefixWord ++ tailWord_3823835).sum := by decide
  have hdescent : baseEnd_3823835 < baseStart_3823835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823843 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 1, 4]
def baseStart_3823843 : Nat := 118140960795 + 3823843 * 2 ^ 59
def prefixEnd_3823843 : Nat := 4983230072969 + 3 ^ 40 * 3823843 * 2
def baseEnd_3823843 : Nat := 1308979604220258620251315

theorem tailTrace_3823843 : CollatzResearch.WordTrace tailWord_3823843 prefixEnd_3823843 1308979604220258620251315 := by
  unfold tailWord_3823843
  simp only [CollatzResearch.WordTrace]
  refine ⟨139467011885877346236716183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92978007923918230824477455 139467011885877346236716183)
  ·
    refine ⟨209200517828816019355074275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139467011885877346236716183 209200517828816019355074275)
    ·
      refine ⟨313800776743224029032611413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209200517828816019355074275 313800776743224029032611413)
      ·
        refine ⟨3677352852459656590225915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 313800776743224029032611413 3677352852459656590225915)
        ·
          refine ⟨5516029278689484885338873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3677352852459656590225915 5516029278689484885338873)
          ·
            refine ⟨4137021959017113664004155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5516029278689484885338873 4137021959017113664004155)
            ·
              refine ⟨6205532938525670496006233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4137021959017113664004155 6205532938525670496006233)
              ·
                refine ⟨4654149703894252872004675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6205532938525670496006233 4654149703894252872004675)
                ·
                  refine ⟨6981224555841379308007013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654149703894252872004675 6981224555841379308007013)
                  ·
                    refine ⟨1308979604220258620251315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6981224555841379308007013 1308979604220258620251315)
                    ·
                      rfl

theorem cell22_3823843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 1, 4].length) (baseStart_3823843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823843 prefixEnd_3823843 := by exact prefixLift 3823843
  have htrace : WordTrace (prefixWord ++ tailWord_3823843) baseStart_3823843 baseEnd_3823843 := by
    simpa [prefixWord, tailWord_3823843, baseEnd_3823843] using wordTrace_append hprefix tailTrace_3823843
  have hstable : (prefixWord ++ tailWord_3823843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823843).length < 2 ^ (prefixWord ++ tailWord_3823843).sum := by decide
  have hdescent : baseEnd_3823843 < baseStart_3823843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823882 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 2, 6]
def baseStart_3823882 : Nat := 118140960795 + 3823882 * 2 ^ 59
def prefixEnd_3823882 : Nat := 4983230072969 + 3 ^ 40 * 3823882 * 2
def baseEnd_3823882 : Nat := 1308992954717275518526195

theorem tailTrace_3823882 : CollatzResearch.WordTrace tailWord_3823882 prefixEnd_3823882 1308992954717275518526195 := by
  unfold tailWord_3823882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34867108583184013974346475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92978956221824037264923933 34867108583184013974346475)
  ·
    refine ⟨52300662874776020961519713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34867108583184013974346475 52300662874776020961519713)
    ·
      refine ⟨39225497156082015721139785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52300662874776020961519713 39225497156082015721139785)
      ·
        refine ⟨29419122867061511790854839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39225497156082015721139785 29419122867061511790854839)
        ·
          refine ⟨44128684300592267686282259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29419122867061511790854839 44128684300592267686282259)
          ·
            refine ⟨66193026450888401529423389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44128684300592267686282259 66193026450888401529423389)
            ·
              refine ⟨24822384919083150573533771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66193026450888401529423389 24822384919083150573533771)
              ·
                refine ⟨37233577378624725860300657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24822384919083150573533771 37233577378624725860300657)
                ·
                  refine ⟨27925183033968544395225493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37233577378624725860300657 27925183033968544395225493)
                  ·
                    refine ⟨1308992954717275518526195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27925183033968544395225493 1308992954717275518526195)
                    ·
                      rfl

theorem cell22_3823882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_3823882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823882 prefixEnd_3823882 := by exact prefixLift 3823882
  have htrace : WordTrace (prefixWord ++ tailWord_3823882) baseStart_3823882 baseEnd_3823882 := by
    simpa [prefixWord, tailWord_3823882, baseEnd_3823882] using wordTrace_append hprefix tailTrace_3823882
  have hstable : (prefixWord ++ tailWord_3823882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823882).length < 2 ^ (prefixWord ++ tailWord_3823882).sum := by decide
  have hdescent : baseEnd_3823882 < baseStart_3823882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823884 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 3, 3]
def baseStart_3823884 : Nat := 118140960795 + 3823884 * 2 ^ 59
def prefixEnd_3823884 : Nat := 4983230072969 + 3 ^ 40 * 3823884 * 2
def baseEnd_3823884 : Nat := 1308993639358148179976189

theorem tailTrace_3823884 : CollatzResearch.WordTrace tailWord_3823884 prefixEnd_3823884 1308993639358148179976189 := by
  unfold tailWord_3823884
  simp only [CollatzResearch.WordTrace]
  refine ⟨69734253639364405119479353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92979004852485873492639137 69734253639364405119479353)
  ·
    refine ⟨52300690229523303839609515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69734253639364405119479353 52300690229523303839609515)
    ·
      refine ⟨78451035344284955759414273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52300690229523303839609515 78451035344284955759414273)
      ·
        refine ⟨58838276508213716819560705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78451035344284955759414273 58838276508213716819560705)
        ·
          refine ⟨44128707381160287614670529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58838276508213716819560705 44128707381160287614670529)
          ·
            refine ⟨33096530535870215711002897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44128707381160287614670529 33096530535870215711002897)
            ·
              refine ⟨24822397901902661783252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33096530535870215711002897 24822397901902661783252173)
              ·
                refine ⟨9308399213213498168719565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24822397901902661783252173 9308399213213498168719565)
                ·
                  refine ⟨3490649704955061813269837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9308399213213498168719565 3490649704955061813269837)
                  ·
                    refine ⟨1308993639358148179976189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3490649704955061813269837 1308993639358148179976189)
                    ·
                      rfl

theorem cell22_3823884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_3823884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823884 prefixEnd_3823884 := by exact prefixLift 3823884
  have htrace : WordTrace (prefixWord ++ tailWord_3823884) baseStart_3823884 baseEnd_3823884 := by
    simpa [prefixWord, tailWord_3823884, baseEnd_3823884] using wordTrace_append hprefix tailTrace_3823884
  have hstable : (prefixWord ++ tailWord_3823884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823884).length < 2 ^ (prefixWord ++ tailWord_3823884).sum := by decide
  have hdescent : baseEnd_3823884 < baseStart_3823884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3823929 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 2, 5]
def baseStart_3823929 : Nat := 118140960795 + 3823929 * 2 ^ 59
def prefixEnd_3823929 : Nat := 4983230072969 + 3 ^ 40 * 3823929 * 2
def baseEnd_3823929 : Nat := 1309009043777783062601051

theorem tailTrace_3823929 : CollatzResearch.WordTrace tailWord_3823929 prefixEnd_3823929 1309009043777783062601051 := by
  unfold tailWord_3823929
  simp only [CollatzResearch.WordTrace]
  refine ⟨139470148563565782924346841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92980099042377188616231227 139470148563565782924346841)
  ·
    refine ⟨104602611422674337193260131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139470148563565782924346841 104602611422674337193260131)
    ·
      refine ⟨156903917134011505789890197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104602611422674337193260131 156903917134011505789890197)
      ·
        refine ⟨7354871115656789333901103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 156903917134011505789890197 7354871115656789333901103)
        ·
          refine ⟨11032306673485184000851655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7354871115656789333901103 11032306673485184000851655)
          ·
            refine ⟨16548460010227776001277483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11032306673485184000851655 16548460010227776001277483)
            ·
              refine ⟨24822690015341664001916225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16548460010227776001277483 24822690015341664001916225)
              ·
                refine ⟨18617017511506248001437169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24822690015341664001916225 18617017511506248001437169)
                ·
                  refine ⟨13962763133629686001077877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18617017511506248001437169 13962763133629686001077877)
                  ·
                    refine ⟨1309009043777783062601051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13962763133629686001077877 1309009043777783062601051)
                    ·
                      rfl

theorem cell22_3823929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 2, 5].length) (baseStart_3823929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3823929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3823929 prefixEnd_3823929 := by exact prefixLift 3823929
  have htrace : WordTrace (prefixWord ++ tailWord_3823929) baseStart_3823929 baseEnd_3823929 := by
    simpa [prefixWord, tailWord_3823929, baseEnd_3823929] using wordTrace_append hprefix tailTrace_3823929
  have hstable : (prefixWord ++ tailWord_3823929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3823929).length < 2 ^ (prefixWord ++ tailWord_3823929).sum := by decide
  have hdescent : baseEnd_3823929 < baseStart_3823929 := by decide
  rcases family_descends (prefixWord ++ tailWord_3823929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824004 : List Nat := [2, 3, 2, 1, 1, 2, 4, 7]
def baseStart_3824004 : Nat := 118140960795 + 3824004 * 2 ^ 59
def prefixEnd_3824004 : Nat := 4983230072969 + 3 ^ 40 * 3824004 * 2
def baseEnd_3824004 : Nat := 145448301978945318552869

theorem tailTrace_3824004 : CollatzResearch.WordTrace tailWord_3824004 prefixEnd_3824004 145448301978945318552869 := by
  unfold tailWord_3824004
  simp only [CollatzResearch.WordTrace]
  refine ⟨69736442019147035366663533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92981922692196047155551377 69736442019147035366663533)
  ·
    refine ⟨26151165757180138262498825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69736442019147035366663533 26151165757180138262498825)
    ·
      refine ⟨19613374317885103696874119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26151165757180138262498825 19613374317885103696874119)
      ·
        refine ⟨29420061476827655545311179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19613374317885103696874119 29420061476827655545311179)
        ·
          refine ⟨44130092215241483317966769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29420061476827655545311179 44130092215241483317966769)
          ·
            refine ⟨33097569161431112488475077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44130092215241483317966769 33097569161431112488475077)
            ·
              refine ⟨6205794217768333591589077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33097569161431112488475077 6205794217768333591589077)
              ·
                refine ⟨145448301978945318552869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6205794217768333591589077 145448301978945318552869)
                ·
                  rfl

theorem cell22_3824004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 7].length) (baseStart_3824004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824004 prefixEnd_3824004 := by exact prefixLift 3824004
  have htrace : WordTrace (prefixWord ++ tailWord_3824004) baseStart_3824004 baseEnd_3824004 := by
    simpa [prefixWord, tailWord_3824004, baseEnd_3824004] using wordTrace_append hprefix tailTrace_3824004
  have hstable : (prefixWord ++ tailWord_3824004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824004).length < 2 ^ (prefixWord ++ tailWord_3824004).sum := by decide
  have hdescent : baseEnd_3824004 < baseStart_3824004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824096 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 1, 4]
def baseStart_3824096 : Nat := 118140960795 + 3824096 * 2 ^ 59
def prefixEnd_3824096 : Nat := 4983230072969 + 3 ^ 40 * 3824096 * 2
def baseEnd_3824096 : Nat := 1309066211290650293675539

theorem tailTrace_3824096 : CollatzResearch.WordTrace tailWord_3824096 prefixEnd_3824096 1309066211290650293675539 := by
  unfold tailWord_3824096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69738119776980385222838071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92984159702640513630450761 69738119776980385222838071)
  ·
    refine ⟨104607179665470577834257107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69738119776980385222838071 104607179665470577834257107)
    ·
      refine ⟨156910769498205866751385661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104607179665470577834257107 156910769498205866751385661)
      ·
        refine ⟨58841538561827200031769623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 156910769498205866751385661 58841538561827200031769623)
        ·
          refine ⟨88262307842740800047654435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58841538561827200031769623 88262307842740800047654435)
          ·
            refine ⟨132393461764111200071481653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88262307842740800047654435 132393461764111200071481653)
            ·
              refine ⟨12411887040385425006701405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132393461764111200071481653 12411887040385425006701405)
              ·
                refine ⟨4654457640144534377513027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12411887040385425006701405 4654457640144534377513027)
                ·
                  refine ⟨6981686460216801566269541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4654457640144534377513027 6981686460216801566269541)
                  ·
                    refine ⟨1309066211290650293675539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6981686460216801566269541 1309066211290650293675539)
                    ·
                      rfl

theorem cell22_3824096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_3824096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824096 prefixEnd_3824096 := by exact prefixLift 3824096
  have htrace : WordTrace (prefixWord ++ tailWord_3824096) baseStart_3824096 baseEnd_3824096 := by
    simpa [prefixWord, tailWord_3824096, baseEnd_3824096] using wordTrace_append hprefix tailTrace_3824096
  have hstable : (prefixWord ++ tailWord_3824096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824096).length < 2 ^ (prefixWord ++ tailWord_3824096).sum := by decide
  have hdescent : baseEnd_3824096 < baseStart_3824096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824156 : List Nat := [2, 2, 3, 1, 2, 4, 8]
def baseStart_3824156 : Nat := 118140960795 + 3824156 * 2 ^ 59
def prefixEnd_3824156 : Nat := 4983230072969 + 3 ^ 40 * 3824156 * 2
def baseEnd_3824156 : Nat := 48484694463586301376865

theorem tailTrace_3824156 : CollatzResearch.WordTrace tailWord_3824156 prefixEnd_3824156 48484694463586301376865 := by
  unfold tailWord_3824156
  simp only [CollatzResearch.WordTrace]
  refine ⟨69739213966871700346430161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92985618622495600461906881 69739213966871700346430161)
  ·
    refine ⟨52304410475153775259822621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69739213966871700346430161 52304410475153775259822621)
    ·
      refine ⟨19614153928182665722433483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52304410475153775259822621 19614153928182665722433483)
      ·
        refine ⟨29421230892273998583650225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19614153928182665722433483 29421230892273998583650225)
        ·
          refine ⟨22065923169205498937737669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29421230892273998583650225 22065923169205498937737669)
          ·
            refine ⟨4137360594226031050825813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22065923169205498937737669 4137360594226031050825813)
            ·
              refine ⟨48484694463586301376865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4137360594226031050825813 48484694463586301376865)
              ·
                rfl

theorem cell22_3824156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 8].length) (baseStart_3824156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824156 prefixEnd_3824156 := by exact prefixLift 3824156
  have htrace : WordTrace (prefixWord ++ tailWord_3824156) baseStart_3824156 baseEnd_3824156 := by
    simpa [prefixWord, tailWord_3824156, baseEnd_3824156] using wordTrace_append hprefix tailTrace_3824156
  have hstable : (prefixWord ++ tailWord_3824156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824156).length < 2 ^ (prefixWord ++ tailWord_3824156).sum := by decide
  have hdescent : baseEnd_3824156 < baseStart_3824156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824306 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3824306 : Nat := 118140960795 + 3824306 * 2 ^ 59
def prefixEnd_3824306 : Nat := 4983230072969 + 3 ^ 40 * 3824306 * 2
def baseEnd_3824306 : Nat := 1309138098582279745924895

theorem tailTrace_3824306 : CollatzResearch.WordTrace tailWord_3824306 prefixEnd_3824306 1309138098582279745924895 := by
  unfold tailWord_3824306
  simp only [CollatzResearch.WordTrace]
  refine ⟨34870974720799994077705193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92989265922133317540547181 34870974720799994077705193)
  ·
    refine ⟨26153231040599995558278895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34870974720799994077705193 26153231040599995558278895)
    ·
      refine ⟨39229846560899993337418343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26153231040599995558278895 39229846560899993337418343)
      ·
        refine ⟨58844769841349990006127515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39229846560899993337418343 58844769841349990006127515)
        ·
          refine ⟨88267154762024985009191273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58844769841349990006127515 88267154762024985009191273)
          ·
            refine ⟨66200366071518738756893455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88267154762024985009191273 66200366071518738756893455)
            ·
              refine ⟨99300549107278108135340183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66200366071518738756893455 99300549107278108135340183)
              ·
                refine ⟨148950823660917162203010275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99300549107278108135340183 148950823660917162203010275)
                ·
                  refine ⟨223426235491375743304515413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 148950823660917162203010275 223426235491375743304515413)
                  ·
                    refine ⟨1309138098582279745924895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 223426235491375743304515413 1309138098582279745924895)
                    ·
                      rfl

theorem cell22_3824306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3824306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824306 prefixEnd_3824306 := by exact prefixLift 3824306
  have htrace : WordTrace (prefixWord ++ tailWord_3824306) baseStart_3824306 baseEnd_3824306 := by
    simpa [prefixWord, tailWord_3824306, baseEnd_3824306] using wordTrace_append hprefix tailTrace_3824306
  have hstable : (prefixWord ++ tailWord_3824306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824306).length < 2 ^ (prefixWord ++ tailWord_3824306).sum := by decide
  have hdescent : baseEnd_3824306 < baseStart_3824306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824391 : List Nat := [1, 1, 4, 4, 1, 3, 2, 2, 1, 3]
def baseStart_3824391 : Nat := 118140960795 + 3824391 * 2 ^ 59
def prefixEnd_3824391 : Nat := 4983230072969 + 3 ^ 40 * 3824391 * 2
def baseEnd_3824391 : Nat := 1309167195819367857549635

theorem tailTrace_3824391 : CollatzResearch.WordTrace tailWord_3824391 prefixEnd_3824391 1309167195819367857549635 := by
  unfold tailWord_3824391
  simp only [CollatzResearch.WordTrace]
  refine ⟨139486999087892035827665027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92991332725261357218443351 139486999087892035827665027)
  ·
    refine ⟨209230498631838053741497541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139486999087892035827665027 209230498631838053741497541)
    ·
      refine ⟨39230718493469635076530789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 209230498631838053741497541 39230718493469635076530789)
      ·
        refine ⟨7355759717525556576849523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39230718493469635076530789 7355759717525556576849523)
        ·
          refine ⟨11033639576288334865274285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7355759717525556576849523 11033639576288334865274285)
          ·
            refine ⟨4137614841108125574477857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11033639576288334865274285 4137614841108125574477857)
            ·
              refine ⟨3103211130831094180858393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4137614841108125574477857 3103211130831094180858393)
              ·
                refine ⟨2327408348123320635643795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3103211130831094180858393 2327408348123320635643795)
                ·
                  refine ⟨3491112522184980953465693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327408348123320635643795 3491112522184980953465693)
                  ·
                    refine ⟨1309167195819367857549635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491112522184980953465693 1309167195819367857549635)
                    ·
                      rfl

theorem cell22_3824391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_3824391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824391 prefixEnd_3824391 := by exact prefixLift 3824391
  have htrace : WordTrace (prefixWord ++ tailWord_3824391) baseStart_3824391 baseEnd_3824391 := by
    simpa [prefixWord, tailWord_3824391, baseEnd_3824391] using wordTrace_append hprefix tailTrace_3824391
  have hstable : (prefixWord ++ tailWord_3824391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824391).length < 2 ^ (prefixWord ++ tailWord_3824391).sum := by decide
  have hdescent : baseEnd_3824391 < baseStart_3824391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824398 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 6]
def baseStart_3824398 : Nat := 118140960795 + 3824398 * 2 ^ 59
def prefixEnd_3824398 : Nat := 4983230072969 + 3 ^ 40 * 3824398 * 2
def baseEnd_3824398 : Nat := 436389864020807390874871

theorem tailTrace_3824398 : CollatzResearch.WordTrace tailWord_3824398 prefixEnd_3824398 436389864020807390874871 := by
  unfold tailWord_3824398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17435906799858334502896231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 92991502932577784015446565 17435906799858334502896231)
  ·
    refine ⟨26153860199787501754344347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17435906799858334502896231 26153860199787501754344347)
    ·
      refine ⟨39230790299681252631516521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26153860199787501754344347 39230790299681252631516521)
      ·
        refine ⟨29423092724760939473637391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39230790299681252631516521 29423092724760939473637391)
        ·
          refine ⟨44134639087141409210456087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29423092724760939473637391 44134639087141409210456087)
          ·
            refine ⟨66201958630712113815684131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44134639087141409210456087 66201958630712113815684131)
            ·
              refine ⟨99302937946068170723526197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66201958630712113815684131 99302937946068170723526197)
              ·
                refine ⟨9309650432443891005330581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99302937946068170723526197 9309650432443891005330581)
                ·
                  refine ⟨436389864020807390874871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9309650432443891005330581 436389864020807390874871)
                  ·
                    rfl

theorem cell22_3824398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_3824398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824398 prefixEnd_3824398 := by exact prefixLift 3824398
  have htrace : WordTrace (prefixWord ++ tailWord_3824398) baseStart_3824398 baseEnd_3824398 := by
    simpa [prefixWord, tailWord_3824398, baseEnd_3824398] using wordTrace_append hprefix tailTrace_3824398
  have hstable : (prefixWord ++ tailWord_3824398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824398).length < 2 ^ (prefixWord ++ tailWord_3824398).sum := by decide
  have hdescent : baseEnd_3824398 < baseStart_3824398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824402 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3824402 : Nat := 118140960795 + 3824402 * 2 ^ 59
def prefixEnd_3824402 : Nat := 4983230072969 + 3 ^ 40 * 3824402 * 2
def baseEnd_3824402 : Nat := 1309170961344167495524601

theorem tailTrace_3824402 : CollatzResearch.WordTrace tailWord_3824402 prefixEnd_3824402 1309170961344167495524601 := by
  unfold tailWord_3824402
  simp only [CollatzResearch.WordTrace]
  refine ⟨34871850072713046176578865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92991600193901456470876973 34871850072713046176578865)
  ·
    refine ⟨26153887554534784632434149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34871850072713046176578865 26153887554534784632434149)
    ·
      refine ⟨4903853916475272118581403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26153887554534784632434149 4903853916475272118581403)
      ·
        refine ⟨7355780874712908177872105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4903853916475272118581403 7355780874712908177872105)
        ·
          refine ⟨5516835656034681133404079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7355780874712908177872105 5516835656034681133404079)
          ·
            refine ⟨8275253484052021700106119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5516835656034681133404079 8275253484052021700106119)
            ·
              refine ⟨12412880226078032550159179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275253484052021700106119 12412880226078032550159179)
              ·
                refine ⟨18619320339117048825238769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412880226078032550159179 18619320339117048825238769)
                ·
                  refine ⟨13964490254337786618929077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18619320339117048825238769 13964490254337786618929077)
                  ·
                    refine ⟨1309170961344167495524601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13964490254337786618929077 1309170961344167495524601)
                    ·
                      rfl

theorem cell22_3824402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3824402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824402 prefixEnd_3824402 := by exact prefixLift 3824402
  have htrace : WordTrace (prefixWord ++ tailWord_3824402) baseStart_3824402 baseEnd_3824402 := by
    simpa [prefixWord, tailWord_3824402, baseEnd_3824402] using wordTrace_append hprefix tailTrace_3824402
  have hstable : (prefixWord ++ tailWord_3824402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824402).length < 2 ^ (prefixWord ++ tailWord_3824402).sum := by decide
  have hdescent : baseEnd_3824402 < baseStart_3824402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824428 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 6]
def baseStart_3824428 : Nat := 118140960795 + 3824428 * 2 ^ 59
def prefixEnd_3824428 : Nat := 4983230072969 + 3 ^ 40 * 3824428 * 2
def baseEnd_3824428 : Nat := 1309179861675512094374521

theorem tailTrace_3824428 : CollatzResearch.WordTrace tailWord_3824428 prefixEnd_3824428 1309179861675512094374521 := by
  unfold tailWord_3824428
  simp only [CollatzResearch.WordTrace]
  refine ⟨69744174294378995573380969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 92992232392505327431174625 69744174294378995573380969)
  ·
    refine ⟨52308130720784246680035727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69744174294378995573380969 52308130720784246680035727)
    ·
      refine ⟨78462196081176370020053591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52308130720784246680035727 78462196081176370020053591)
      ·
        refine ⟨117693294121764555030080387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78462196081176370020053591 117693294121764555030080387)
        ·
          refine ⟨176539941182646832545120581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117693294121764555030080387 176539941182646832545120581)
          ·
            refine ⟨33101238971746281102210109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 176539941182646832545120581 33101238971746281102210109)
            ·
              refine ⟨12412964614404855413328791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33101238971746281102210109 12412964614404855413328791)
              ·
                refine ⟨18619446921607283119993187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12412964614404855413328791 18619446921607283119993187)
                ·
                  refine ⟨27929170382410924679989781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18619446921607283119993187 27929170382410924679989781)
                  ·
                    refine ⟨1309179861675512094374521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27929170382410924679989781 1309179861675512094374521)
                    ·
                      rfl

theorem cell22_3824428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_3824428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824428 prefixEnd_3824428 := by exact prefixLift 3824428
  have htrace : WordTrace (prefixWord ++ tailWord_3824428) baseStart_3824428 baseEnd_3824428 := by
    simpa [prefixWord, tailWord_3824428, baseEnd_3824428] using wordTrace_append hprefix tailTrace_3824428
  have hstable : (prefixWord ++ tailWord_3824428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824428).length < 2 ^ (prefixWord ++ tailWord_3824428).sum := by decide
  have hdescent : baseEnd_3824428 < baseStart_3824428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824447 : List Nat := [1, 1, 2, 2, 5, 1, 3, 2, 2, 3]
def baseStart_3824447 : Nat := 118140960795 + 3824447 * 2 ^ 59
def prefixEnd_3824447 : Nat := 4983230072969 + 3 ^ 40 * 3824447 * 2
def baseEnd_3824447 : Nat := 1309186365763802378149463

theorem tailTrace_3824447 : CollatzResearch.WordTrace tailWord_3824447 prefixEnd_3824447 1309186365763802378149463 := by
  unfold tailWord_3824447
  simp only [CollatzResearch.WordTrace]
  refine ⟨139489041575689157391703595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92992694383792771594469063 139489041575689157391703595)
  ·
    refine ⟨209233562363533736087555393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139489041575689157391703595 209233562363533736087555393)
    ·
      refine ⟨156925171772650302065666545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209233562363533736087555393 156925171772650302065666545)
      ·
        refine ⟨117693878829487726549249909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156925171772650302065666545 117693878829487726549249909)
        ·
          refine ⟨11033801140264474363992179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 117693878829487726549249909 11033801140264474363992179)
          ·
            refine ⟨16550701710396711545988269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11033801140264474363992179 16550701710396711545988269)
            ·
              refine ⟨6206513141398766829745601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16550701710396711545988269 6206513141398766829745601)
              ·
                refine ⟨4654884856049075122309201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6206513141398766829745601 4654884856049075122309201)
                ·
                  refine ⟨3491163642036806341731901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4654884856049075122309201 3491163642036806341731901)
                  ·
                    refine ⟨1309186365763802378149463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491163642036806341731901 1309186365763802378149463)
                    ·
                      rfl

theorem cell22_3824447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 2, 2, 3].length) (baseStart_3824447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824447 prefixEnd_3824447 := by exact prefixLift 3824447
  have htrace : WordTrace (prefixWord ++ tailWord_3824447) baseStart_3824447 baseEnd_3824447 := by
    simpa [prefixWord, tailWord_3824447, baseEnd_3824447] using wordTrace_append hprefix tailTrace_3824447
  have hstable : (prefixWord ++ tailWord_3824447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824447).length < 2 ^ (prefixWord ++ tailWord_3824447).sum := by decide
  have hdescent : baseEnd_3824447 < baseStart_3824447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824503 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 4, 5]
def baseStart_3824503 : Nat := 118140960795 + 3824503 * 2 ^ 59
def prefixEnd_3824503 : Nat := 4983230072969 + 3 ^ 40 * 3824503 * 2
def baseEnd_3824503 : Nat := 1309205535708236898749291

theorem tailTrace_3824503 : CollatzResearch.WordTrace tailWord_3824503 prefixEnd_3824503 1309205535708236898749291 := by
  unfold tailWord_3824503
  simp only [CollatzResearch.WordTrace]
  refine ⟨139491084063486278955742163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994056042324185970494775 139491084063486278955742163)
  ·
    refine ⟨209236626095229418433613245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139491084063486278955742163 209236626095229418433613245)
    ·
      refine ⟨78463734785711031912604967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209236626095229418433613245 78463734785711031912604967)
      ·
        refine ⟨117695602178566547868907451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78463734785711031912604967 117695602178566547868907451)
        ·
          refine ⟨176543403267849821803361177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117695602178566547868907451 176543403267849821803361177)
          ·
            refine ⟨132407552450887366352520883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176543403267849821803361177 132407552450887366352520883)
            ·
              refine ⟨198611328676331049528781325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132407552450887366352520883 198611328676331049528781325)
              ·
                refine ⟨74479248253624143573292997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 198611328676331049528781325 74479248253624143573292997)
                ·
                  refine ⟨13964859047554526919992437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74479248253624143573292997 13964859047554526919992437)
                  ·
                    refine ⟨1309205535708236898749291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13964859047554526919992437 1309205535708236898749291)
                    ·
                      rfl

theorem cell22_3824503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_3824503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824503 prefixEnd_3824503 := by exact prefixLift 3824503
  have htrace : WordTrace (prefixWord ++ tailWord_3824503) baseStart_3824503 baseEnd_3824503 := by
    simpa [prefixWord, tailWord_3824503, baseEnd_3824503] using wordTrace_append hprefix tailTrace_3824503
  have hstable : (prefixWord ++ tailWord_3824503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824503).length < 2 ^ (prefixWord ++ tailWord_3824503).sum := by decide
  have hdescent : baseEnd_3824503 < baseStart_3824503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824522 : List Nat := [3, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_3824522 : Nat := 118140960795 + 3824522 * 2 ^ 59
def prefixEnd_3824522 : Nat := 4983230072969 + 3 ^ 40 * 3824522 * 2
def baseEnd_3824522 : Nat := 436404013265509060841411

theorem tailTrace_3824522 : CollatzResearch.WordTrace tailWord_3824522 prefixEnd_3824522 436404013265509060841411 := by
  unfold tailWord_3824522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34872944262604361300170955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 92994518033611630133789213 34872944262604361300170955)
  ·
    refine ⟨52309416393906541950256433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34872944262604361300170955 52309416393906541950256433)
    ·
      refine ⟨39232062295429906462692325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52309416393906541950256433 39232062295429906462692325)
      ·
        refine ⟨7356011680393107461754811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39232062295429906462692325 7356011680393107461754811)
        ·
          refine ⟨11034017520589661192632217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356011680393107461754811 11034017520589661192632217)
          ·
            refine ⟨8275513140442245894474163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11034017520589661192632217 8275513140442245894474163)
            ·
              refine ⟨12413269710663368841711245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275513140442245894474163 12413269710663368841711245)
              ·
                refine ⟨4654976141498763315641717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12413269710663368841711245 4654976141498763315641717)
                ·
                  refine ⟨436404013265509060841411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4654976141498763315641717 436404013265509060841411)
                  ·
                    rfl

theorem cell22_3824522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_3824522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824522 prefixEnd_3824522 := by exact prefixLift 3824522
  have htrace : WordTrace (prefixWord ++ tailWord_3824522) baseStart_3824522 baseEnd_3824522 := by
    simpa [prefixWord, tailWord_3824522, baseEnd_3824522] using wordTrace_append hprefix tailTrace_3824522
  have hstable : (prefixWord ++ tailWord_3824522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824522).length < 2 ^ (prefixWord ++ tailWord_3824522).sum := by decide
  have hdescent : baseEnd_3824522 < baseStart_3824522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824535 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 3, 4]
def baseStart_3824535 : Nat := 118140960795 + 3824535 * 2 ^ 59
def prefixEnd_3824535 : Nat := 4983230072969 + 3 ^ 40 * 3824535 * 2
def baseEnd_3824535 : Nat := 1309216489962199481949193

theorem tailTrace_3824535 : CollatzResearch.WordTrace tailWord_3824535 prefixEnd_3824535 1309216489962199481949193 := by
  unfold tailWord_3824535
  simp only [CollatzResearch.WordTrace]
  refine ⟨139492251199370348420907059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92994834132913565613938039 139492251199370348420907059)
  ·
    refine ⟨209238376799055522631360589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139492251199370348420907059 209238376799055522631360589)
    ·
      refine ⟨78464391299645820986760221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209238376799055522631360589 78464391299645820986760221)
      ·
        refine ⟨29424146737367182870035083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78464391299645820986760221 29424146737367182870035083)
        ·
          refine ⟨44136220106050774305052625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29424146737367182870035083 44136220106050774305052625)
          ·
            refine ⟨33102165079538080728789469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44136220106050774305052625 33102165079538080728789469)
            ·
              refine ⟨12413311904826780273296051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33102165079538080728789469 12413311904826780273296051)
              ·
                refine ⟨18619967857240170409944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413311904826780273296051 18619967857240170409944077)
                ·
                  refine ⟨6982487946465063903729029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18619967857240170409944077 6982487946465063903729029)
                  ·
                    refine ⟨1309216489962199481949193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6982487946465063903729029 1309216489962199481949193)
                    ·
                      rfl

theorem cell22_3824535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_3824535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824535 prefixEnd_3824535 := by exact prefixLift 3824535
  have htrace : WordTrace (prefixWord ++ tailWord_3824535) baseStart_3824535 baseEnd_3824535 := by
    simpa [prefixWord, tailWord_3824535, baseEnd_3824535] using wordTrace_append hprefix tailTrace_3824535
  have hstable : (prefixWord ++ tailWord_3824535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824535).length < 2 ^ (prefixWord ++ tailWord_3824535).sum := by decide
  have hdescent : baseEnd_3824535 < baseStart_3824535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824565 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 5]
def baseStart_3824565 : Nat := 118140960795 + 3824565 * 2 ^ 59
def prefixEnd_3824565 : Nat := 4983230072969 + 3 ^ 40 * 3824565 * 2
def baseEnd_3824565 : Nat := 1309226759575289403699101

theorem tailTrace_3824565 : CollatzResearch.WordTrace tailWord_3824565 prefixEnd_3824565 1309226759575289403699101 := by
  unfold tailWord_3824565
  simp only [CollatzResearch.WordTrace]
  refine ⟨139493345389261663544499149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92995563592841109029666099 139493345389261663544499149)
  ·
    refine ⟨52310004520973123829187181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139493345389261663544499149 52310004520973123829187181)
    ·
      refine ⟨19616251695364921435945193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52310004520973123829187181 19616251695364921435945193)
      ·
        refine ⟨14712188771523691076958895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19616251695364921435945193 14712188771523691076958895)
        ·
          refine ⟨22068283157285536615438343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14712188771523691076958895 22068283157285536615438343)
          ·
            refine ⟨33102424735928304923157515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22068283157285536615438343 33102424735928304923157515)
            ·
              refine ⟨49653637103892457384736273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33102424735928304923157515 49653637103892457384736273)
              ·
                refine ⟨37240227827919343038552205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49653637103892457384736273 37240227827919343038552205)
                ·
                  refine ⟨13965085435469753639457077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37240227827919343038552205 13965085435469753639457077)
                  ·
                    refine ⟨1309226759575289403699101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13965085435469753639457077 1309226759575289403699101)
                    ·
                      rfl

theorem cell22_3824565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_3824565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824565 prefixEnd_3824565 := by exact prefixLift 3824565
  have htrace : WordTrace (prefixWord ++ tailWord_3824565) baseStart_3824565 baseEnd_3824565 := by
    simpa [prefixWord, tailWord_3824565, baseEnd_3824565] using wordTrace_append hprefix tailTrace_3824565
  have hstable : (prefixWord ++ tailWord_3824565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824565).length < 2 ^ (prefixWord ++ tailWord_3824565).sum := by decide
  have hdescent : baseEnd_3824565 < baseStart_3824565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824597 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_3824597 : Nat := 118140960795 + 3824597 * 2 ^ 59
def prefixEnd_3824597 : Nat := 4983230072969 + 3 ^ 40 * 3824597 * 2
def baseEnd_3824597 : Nat := 1309237713829251986899003

theorem tailTrace_3824597 : CollatzResearch.WordTrace tailWord_3824597 prefixEnd_3824597 1309237713829251986899003 := by
  unfold tailWord_3824597
  simp only [CollatzResearch.WordTrace]
  refine ⟨139494512525145733009664045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92996341683430488673109363 139494512525145733009664045)
  ·
    refine ⟨52310442196929649878624017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139494512525145733009664045 52310442196929649878624017)
    ·
      refine ⟨39232831647697237408968013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52310442196929649878624017 39232831647697237408968013)
      ·
        refine ⟨14712311867886464028363005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39232831647697237408968013 14712311867886464028363005)
        ·
          refine ⟨5517116950457424010636127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14712311867886464028363005 5517116950457424010636127)
          ·
            refine ⟨8275675425686136015954191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5517116950457424010636127 8275675425686136015954191)
            ·
              refine ⟨12413513138529204023931287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8275675425686136015954191 12413513138529204023931287)
              ·
                refine ⟨18620269707793806035896931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12413513138529204023931287 18620269707793806035896931)
                ·
                  refine ⟨27930404561690709053845397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18620269707793806035896931 27930404561690709053845397)
                  ·
                    refine ⟨1309237713829251986899003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27930404561690709053845397 1309237713829251986899003)
                    ·
                      rfl

theorem cell22_3824597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_3824597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824597 prefixEnd_3824597 := by exact prefixLift 3824597
  have htrace : WordTrace (prefixWord ++ tailWord_3824597) baseStart_3824597 baseEnd_3824597 := by
    simpa [prefixWord, tailWord_3824597, baseEnd_3824597] using wordTrace_append hprefix tailTrace_3824597
  have hstable : (prefixWord ++ tailWord_3824597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824597).length < 2 ^ (prefixWord ++ tailWord_3824597).sum := by decide
  have hdescent : baseEnd_3824597 < baseStart_3824597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824661 : List Nat := [1, 3, 2, 1, 4, 1, 3, 3, 1, 3]
def baseStart_3824661 : Nat := 118140960795 + 3824661 * 2 ^ 59
def prefixEnd_3824661 : Nat := 4983230072969 + 3 ^ 40 * 3824661 * 2
def baseEnd_3824661 : Nat := 1309259622337177153298807

theorem tailTrace_3824661 : CollatzResearch.WordTrace tailWord_3824661 prefixEnd_3824661 1309259622337177153298807 := by
  unfold tailWord_3824661
  simp only [CollatzResearch.WordTrace]
  refine ⟨139496846796913871939993837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 92997897864609247959995891 139496846796913871939993837)
  ·
    refine ⟨52311317548842701977497689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139496846796913871939993837 52311317548842701977497689)
    ·
      refine ⟨39233488161632026483123267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52311317548842701977497689 39233488161632026483123267)
      ·
        refine ⟨58850232242448039724684901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39233488161632026483123267 58850232242448039724684901)
        ·
          refine ⟨11034418545459007448378419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58850232242448039724684901 11034418545459007448378419)
          ·
            refine ⟨16551627818188511172567629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11034418545459007448378419 16551627818188511172567629)
            ·
              refine ⟨6206860431820691689712861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16551627818188511172567629 6206860431820691689712861)
              ·
                refine ⟨2327572661932759383642323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6206860431820691689712861 2327572661932759383642323)
                ·
                  refine ⟨3491358992899139075463485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327572661932759383642323 3491358992899139075463485)
                  ·
                    refine ⟨1309259622337177153298807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491358992899139075463485 1309259622337177153298807)
                    ·
                      rfl

theorem cell22_3824661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_3824661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824661 prefixEnd_3824661 := by exact prefixLift 3824661
  have htrace : WordTrace (prefixWord ++ tailWord_3824661) baseStart_3824661 baseEnd_3824661 := by
    simpa [prefixWord, tailWord_3824661, baseEnd_3824661] using wordTrace_append hprefix tailTrace_3824661
  have hstable : (prefixWord ++ tailWord_3824661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824661).length < 2 ^ (prefixWord ++ tailWord_3824661).sum := by decide
  have hdescent : baseEnd_3824661 < baseStart_3824661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824796 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 3, 3]
def baseStart_3824796 : Nat := 118140960795 + 3824796 * 2 ^ 59
def prefixEnd_3824796 : Nat := 4983230072969 + 3 ^ 40 * 3824796 * 2
def baseEnd_3824796 : Nat := 1309305835596081801173393

theorem tailTrace_3824796 : CollatzResearch.WordTrace tailWord_3824796 prefixEnd_3824796 1309305835596081801173393 := by
  unfold tailWord_3824796
  simp only [CollatzResearch.WordTrace]
  refine ⟨69750885325712394998079121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93001180434283193330772161 69750885325712394998079121)
  ·
    refine ⟨52313163994284296248559341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69750885325712394998079121 52313163994284296248559341)
    ·
      refine ⟨19617436497856611093209753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52313163994284296248559341 19617436497856611093209753)
      ·
        refine ⟨14713077373392458319907315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19617436497856611093209753 14713077373392458319907315)
        ·
          refine ⟨22069616060088687479860973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14713077373392458319907315 22069616060088687479860973)
          ·
            refine ⟨8276106022533257804947865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22069616060088687479860973 8276106022533257804947865)
            ·
              refine ⟨6207079516899943353710899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276106022533257804947865 6207079516899943353710899)
              ·
                refine ⟨9310619275349915030566349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207079516899943353710899 9310619275349915030566349)
                ·
                  refine ⟨3491482228256218136462381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9310619275349915030566349 3491482228256218136462381)
                  ·
                    refine ⟨1309305835596081801173393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491482228256218136462381 1309305835596081801173393)
                    ·
                      rfl

theorem cell22_3824796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_3824796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824796 prefixEnd_3824796 := by exact prefixLift 3824796
  have htrace : WordTrace (prefixWord ++ tailWord_3824796) baseStart_3824796 baseEnd_3824796 := by
    simpa [prefixWord, tailWord_3824796, baseEnd_3824796] using wordTrace_append hprefix tailTrace_3824796
  have hstable : (prefixWord ++ tailWord_3824796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824796).length < 2 ^ (prefixWord ++ tailWord_3824796).sum := by decide
  have hdescent : baseEnd_3824796 < baseStart_3824796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824830 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 1, 3]
def baseStart_3824830 : Nat := 118140960795 + 3824830 * 2 ^ 59
def prefixEnd_3824830 : Nat := 4983230072969 + 3 ^ 40 * 3824830 * 2
def baseEnd_3824830 : Nat := 1309317474490917045823289

theorem tailTrace_3824830 : CollatzResearch.WordTrace tailWord_3824830 prefixEnd_3824830 1309317474490917045823289 := by
  unfold tailWord_3824830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17437876341662701725361993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93002007155534409201930629 17437876341662701725361993)
  ·
    refine ⟨13078407256247026294021495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17437876341662701725361993 13078407256247026294021495)
    ·
      refine ⟨19617610884370539441032243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13078407256247026294021495 19617610884370539441032243)
      ·
        refine ⟨29426416326555809161548365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19617610884370539441032243 29426416326555809161548365)
        ·
          refine ⟨11034906122458428435580637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29426416326555809161548365 11034906122458428435580637)
          ·
            refine ⟨4138089795921910663342739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11034906122458428435580637 4138089795921910663342739)
            ·
              refine ⟨6207134693882865995014109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138089795921910663342739 6207134693882865995014109)
              ·
                refine ⟨2327675510206074748130291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6207134693882865995014109 2327675510206074748130291)
                ·
                  refine ⟨3491513265309112122195437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327675510206074748130291 3491513265309112122195437)
                  ·
                    refine ⟨1309317474490917045823289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491513265309112122195437 1309317474490917045823289)
                    ·
                      rfl

theorem cell22_3824830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_3824830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824830 prefixEnd_3824830 := by exact prefixLift 3824830
  have htrace : WordTrace (prefixWord ++ tailWord_3824830) baseStart_3824830 baseEnd_3824830 := by
    simpa [prefixWord, tailWord_3824830, baseEnd_3824830] using wordTrace_append hprefix tailTrace_3824830
  have hstable : (prefixWord ++ tailWord_3824830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824830).length < 2 ^ (prefixWord ++ tailWord_3824830).sum := by decide
  have hdescent : baseEnd_3824830 < baseStart_3824830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824931 : List Nat := [1, 1, 1, 4, 2, 4, 1, 2, 3, 3]
def baseStart_3824931 : Nat := 118140960795 + 3824931 * 2 ^ 59
def prefixEnd_3824931 : Nat := 4983230072969 + 3 ^ 40 * 3824931 * 2
def baseEnd_3824931 : Nat := 1309352048854986449047979

theorem tailTrace_3824931 : CollatzResearch.WordTrace tailWord_3824931 prefixEnd_3824931 1309352048854986449047979 := by
  unfold tailWord_3824931
  simp only [CollatzResearch.WordTrace]
  refine ⟨139506694505935708052322647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93004463003957138701548431 139506694505935708052322647)
  ·
    refine ⟨209260041758903562078483971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139506694505935708052322647 209260041758903562078483971)
    ·
      refine ⟨313890062638355343117725957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209260041758903562078483971 313890062638355343117725957)
      ·
        refine ⟨58854386744691626834573617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313890062638355343117725957 58854386744691626834573617)
        ·
          refine ⟨44140790058518720125930213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58854386744691626834573617 44140790058518720125930213)
          ·
            refine ⟨8276398135972260023611915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44140790058518720125930213 8276398135972260023611915)
            ·
              refine ⟨12414597203958390035417873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276398135972260023611915 12414597203958390035417873)
              ·
                refine ⟨9310947902968792526563405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12414597203958390035417873 9310947902968792526563405)
                ·
                  refine ⟨3491605463613297197461277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9310947902968792526563405 3491605463613297197461277)
                  ·
                    refine ⟨1309352048854986449047979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491605463613297197461277 1309352048854986449047979)
                    ·
                      rfl

theorem cell22_3824931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3, 3].length) (baseStart_3824931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824931 prefixEnd_3824931 := by exact prefixLift 3824931
  have htrace : WordTrace (prefixWord ++ tailWord_3824931) baseStart_3824931 baseEnd_3824931 := by
    simpa [prefixWord, tailWord_3824931, baseEnd_3824931] using wordTrace_append hprefix tailTrace_3824931
  have hstable : (prefixWord ++ tailWord_3824931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824931).length < 2 ^ (prefixWord ++ tailWord_3824931).sum := by decide
  have hdescent : baseEnd_3824931 < baseStart_3824931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824959 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 5]
def baseStart_3824959 : Nat := 118140960795 + 3824959 * 2 ^ 59
def prefixEnd_3824959 : Nat := 4983230072969 + 3 ^ 40 * 3824959 * 2
def baseEnd_3824959 : Nat := 1309361633827203709347893

theorem tailTrace_3824959 : CollatzResearch.WordTrace tailWord_3824959 prefixEnd_3824959 1309361633827203709347893 := by
  unfold tailWord_3824959
  simp only [CollatzResearch.WordTrace]
  refine ⟨139507715749834268834341931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93005143833222845889561287 139507715749834268834341931)
  ·
    refine ⟨209261573624751403251512897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139507715749834268834341931 209261573624751403251512897)
    ·
      refine ⟨156946180218563552438634673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209261573624751403251512897 156946180218563552438634673)
      ·
        refine ⟨117709635163922664328976005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156946180218563552438634673 117709635163922664328976005)
        ·
          refine ⟨22070556593235499561683001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117709635163922664328976005 22070556593235499561683001)
          ·
            refine ⟨16552917444926624671262251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22070556593235499561683001 16552917444926624671262251)
            ·
              refine ⟨24829376167389937006893377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16552917444926624671262251 24829376167389937006893377)
              ·
                refine ⟨18622032125542452755170033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24829376167389937006893377 18622032125542452755170033)
                ·
                  refine ⟨13966524094156839566377525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18622032125542452755170033 13966524094156839566377525)
                  ·
                    refine ⟨1309361633827203709347893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13966524094156839566377525 1309361633827203709347893)
                    ·
                      rfl

theorem cell22_3824959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 5].length) (baseStart_3824959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824959 prefixEnd_3824959 := by exact prefixLift 3824959
  have htrace : WordTrace (prefixWord ++ tailWord_3824959) baseStart_3824959 baseEnd_3824959 := by
    simpa [prefixWord, tailWord_3824959, baseEnd_3824959] using wordTrace_append hprefix tailTrace_3824959
  have hstable : (prefixWord ++ tailWord_3824959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824959).length < 2 ^ (prefixWord ++ tailWord_3824959).sum := by decide
  have hdescent : baseEnd_3824959 < baseStart_3824959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3824961 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 7]
def baseStart_3824961 : Nat := 118140960795 + 3824961 * 2 ^ 59
def prefixEnd_3824961 : Nat := 4983230072969 + 3 ^ 40 * 3824961 * 2
def baseEnd_3824961 : Nat := 436454106156025456932629

theorem tailTrace_3824961 : CollatzResearch.WordTrace tailWord_3824961 prefixEnd_3824961 436454106156025456932629 := by
  unfold tailWord_3824961
  simp only [CollatzResearch.WordTrace]
  refine ⟨139507788695827023175914737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93005192463884682117276491 139507788695827023175914737)
  ·
    refine ⟨104630841521870267381936053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139507788695827023175914737 104630841521870267381936053)
    ·
      refine ⟨9809141392675337567056505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104630841521870267381936053 9809141392675337567056505)
      ·
        refine ⟨7356856044506503175292379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9809141392675337567056505 7356856044506503175292379)
        ·
          refine ⟨11035284066759754762938569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356856044506503175292379 11035284066759754762938569)
          ·
            refine ⟨8276463050069816072203927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11035284066759754762938569 8276463050069816072203927)
            ·
              refine ⟨12414694575104724108305891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8276463050069816072203927 12414694575104724108305891)
              ·
                refine ⟨18622041862657086162458837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12414694575104724108305891 18622041862657086162458837)
                ·
                  refine ⟨436454106156025456932629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18622041862657086162458837 436454106156025456932629)
                  ·
                    rfl

theorem cell22_3824961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_3824961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3824961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3824961 prefixEnd_3824961 := by exact prefixLift 3824961
  have htrace : WordTrace (prefixWord ++ tailWord_3824961) baseStart_3824961 baseEnd_3824961 := by
    simpa [prefixWord, tailWord_3824961, baseEnd_3824961] using wordTrace_append hprefix tailTrace_3824961
  have hstable : (prefixWord ++ tailWord_3824961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3824961).length < 2 ^ (prefixWord ++ tailWord_3824961).sum := by decide
  have hdescent : baseEnd_3824961 < baseStart_3824961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3824961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825021 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 4, 3]
def baseStart_3825021 : Nat := 118140960795 + 3825021 * 2 ^ 59
def prefixEnd_3825021 : Nat := 4983230072969 + 3 ^ 40 * 3825021 * 2
def baseEnd_3825021 : Nat := 1309382857694256214297703

theorem tailTrace_3825021 : CollatzResearch.WordTrace tailWord_3825021 prefixEnd_3825021 1309382857694256214297703 := by
  unfold tailWord_3825021
  simp only [CollatzResearch.WordTrace]
  refine ⟨139509977075609653423098917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93006651383739768948732611 139509977075609653423098917)
  ·
    refine ⟨26158120701676810016831047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139509977075609653423098917 26158120701676810016831047)
    ·
      refine ⟨39237181052515215025246571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26158120701676810016831047 39237181052515215025246571)
      ·
        refine ⟨58855771578772822537869857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39237181052515215025246571 58855771578772822537869857)
        ·
          refine ⟨44141828684079616903402393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58855771578772822537869857 44141828684079616903402393)
          ·
            refine ⟨33106371513059712677551795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44141828684079616903402393 33106371513059712677551795)
            ·
              refine ⟨49659557269589569016327693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33106371513059712677551795 49659557269589569016327693)
              ·
                refine ⟨18622333976096088381122885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49659557269589569016327693 18622333976096088381122885)
                ·
                  refine ⟨3491687620518016571460541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18622333976096088381122885 3491687620518016571460541)
                  ·
                    refine ⟨1309382857694256214297703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491687620518016571460541 1309382857694256214297703)
                    ·
                      rfl

theorem cell22_3825021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_3825021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825021 prefixEnd_3825021 := by exact prefixLift 3825021
  have htrace : WordTrace (prefixWord ++ tailWord_3825021) baseStart_3825021 baseEnd_3825021 := by
    simpa [prefixWord, tailWord_3825021, baseEnd_3825021] using wordTrace_append hprefix tailTrace_3825021
  have hstable : (prefixWord ++ tailWord_3825021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825021).length < 2 ^ (prefixWord ++ tailWord_3825021).sum := by decide
  have hdescent : baseEnd_3825021 < baseStart_3825021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825042 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_3825042 : Nat := 118140960795 + 3825042 * 2 ^ 59
def prefixEnd_3825042 : Nat := 4983230072969 + 3 ^ 40 * 3825042 * 2
def baseEnd_3825042 : Nat := 1309390046423419159522639

theorem tailTrace_3825042 : CollatzResearch.WordTrace tailWord_3825042 prefixEnd_3825042 1309390046423419159522639 := by
  unfold tailWord_3825042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34877685752133393502403345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93007162005689049339742253 34877685752133393502403345)
  ·
    refine ⟨26158264314100045126802509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34877685752133393502403345 26158264314100045126802509)
    ·
      refine ⟨9809349117787516922550941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26158264314100045126802509 9809349117787516922550941)
      ·
        refine ⟨3678505919170318845956603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9809349117787516922550941 3678505919170318845956603)
        ·
          refine ⟨5517758878755478268934905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3678505919170318845956603 5517758878755478268934905)
          ·
            refine ⟨4138319159066608701701179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517758878755478268934905 4138319159066608701701179)
            ·
              refine ⟨6207478738599913052551769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138319159066608701701179 6207478738599913052551769)
              ·
                refine ⟨4655609053949934789413827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207478738599913052551769 4655609053949934789413827)
                ·
                  refine ⟨6983413580924902184120741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4655609053949934789413827 6983413580924902184120741)
                  ·
                    refine ⟨1309390046423419159522639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983413580924902184120741 1309390046423419159522639)
                    ·
                      rfl

theorem cell22_3825042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_3825042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825042 prefixEnd_3825042 := by exact prefixLift 3825042
  have htrace : WordTrace (prefixWord ++ tailWord_3825042) baseStart_3825042 baseEnd_3825042 := by
    simpa [prefixWord, tailWord_3825042, baseEnd_3825042] using wordTrace_append hprefix tailTrace_3825042
  have hstable : (prefixWord ++ tailWord_3825042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825042).length < 2 ^ (prefixWord ++ tailWord_3825042).sum := by decide
  have hdescent : baseEnd_3825042 < baseStart_3825042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825053 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3825053 : Nat := 118140960795 + 3825053 * 2 ^ 59
def prefixEnd_3825053 : Nat := 4983230072969 + 3 ^ 40 * 3825053 * 2
def baseEnd_3825053 : Nat := 1309393811948218797497605

theorem tailTrace_3825053 : CollatzResearch.WordTrace tailWord_3825053 prefixEnd_3825053 1309393811948218797497605 := by
  unfold tailWord_3825053
  simp only [CollatzResearch.WordTrace]
  refine ⟨139511144211493722888263813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93007429474329148592175875 139511144211493722888263813)
  ·
    refine ⟨26158339539655073041549465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139511144211493722888263813 26158339539655073041549465)
    ·
      refine ⟨19618754654741304781162099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26158339539655073041549465 19618754654741304781162099)
      ·
        refine ⟨29428131982111957171743149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19618754654741304781162099 29428131982111957171743149)
        ·
          refine ⟨11035549493291983939403681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29428131982111957171743149 11035549493291983939403681)
          ·
            refine ⟨8276662119968987954552761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11035549493291983939403681 8276662119968987954552761)
            ·
              refine ⟨6207496589976740965914571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276662119968987954552761 6207496589976740965914571)
              ·
                refine ⟨9311244884965111448871857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207496589976740965914571 9311244884965111448871857)
                ·
                  refine ⟨6983433663723833586653893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9311244884965111448871857 6983433663723833586653893)
                  ·
                    refine ⟨1309393811948218797497605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983433663723833586653893 1309393811948218797497605)
                    ·
                      rfl

theorem cell22_3825053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3825053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825053 prefixEnd_3825053 := by exact prefixLift 3825053
  have htrace : WordTrace (prefixWord ++ tailWord_3825053) baseStart_3825053 baseEnd_3825053 := by
    simpa [prefixWord, tailWord_3825053, baseEnd_3825053] using wordTrace_append hprefix tailTrace_3825053
  have hstable : (prefixWord ++ tailWord_3825053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825053).length < 2 ^ (prefixWord ++ tailWord_3825053).sum := by decide
  have hdescent : baseEnd_3825053 < baseStart_3825053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825096 : List Nat := [2, 1, 3, 1, 3, 1, 1, 5, 5]
def baseStart_3825096 : Nat := 118140960795 + 3825096 * 2 ^ 59
def prefixEnd_3825096 : Nat := 4983230072969 + 3 ^ 40 * 3825096 * 2
def baseEnd_3825096 : Nat := 436469510575660339557491

theorem tailTrace_3825096 : CollatzResearch.WordTrace tailWord_3825096 prefixEnd_3825096 436469510575660339557491 := by
  unfold tailWord_3825096
  simp only [CollatzResearch.WordTrace]
  refine ⟨69756356275168970616039571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93008475033558627488052761 69756356275168970616039571)
  ·
    refine ⟨104634534412753455924059357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69756356275168970616039571 104634534412753455924059357)
    ·
      refine ⟨39237950404782545971522259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104634534412753455924059357 39237950404782545971522259)
      ·
        refine ⟨58856925607173818957283389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39237950404782545971522259 58856925607173818957283389)
        ·
          refine ⟨22071347102690182108981271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58856925607173818957283389 22071347102690182108981271)
          ·
            refine ⟨33107020654035273163471907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22071347102690182108981271 33107020654035273163471907)
            ·
              refine ⟨49660530981052909745207861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33107020654035273163471907 49660530981052909745207861)
              ·
                refine ⟨4655674779473710288613237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49660530981052909745207861 4655674779473710288613237)
                ·
                  refine ⟨436469510575660339557491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4655674779473710288613237 436469510575660339557491)
                  ·
                    rfl

theorem cell22_3825096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 5, 5].length) (baseStart_3825096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825096 prefixEnd_3825096 := by exact prefixLift 3825096
  have htrace : WordTrace (prefixWord ++ tailWord_3825096) baseStart_3825096 baseEnd_3825096 := by
    simpa [prefixWord, tailWord_3825096, baseEnd_3825096] using wordTrace_append hprefix tailTrace_3825096
  have hstable : (prefixWord ++ tailWord_3825096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825096).length < 2 ^ (prefixWord ++ tailWord_3825096).sum := by decide
  have hdescent : baseEnd_3825096 < baseStart_3825096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825117 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 1, 3]
def baseStart_3825117 : Nat := 118140960795 + 3825117 * 2 ^ 59
def prefixEnd_3825117 : Nat := 4983230072969 + 3 ^ 40 * 3825117 * 2
def baseEnd_3825117 : Nat := 1309415720456143963897409

theorem tailTrace_3825117 : CollatzResearch.WordTrace tailWord_3825117 prefixEnd_3825117 1309415720456143963897409 := by
  unfold tailWord_3825117
  simp only [CollatzResearch.WordTrace]
  refine ⟨139513478483261861818593605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93008985655507907879062403 139513478483261861818593605)
  ·
    refine ⟨26158777215611599090986301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139513478483261861818593605 26158777215611599090986301)
    ·
      refine ⟨9809541455854349659119863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26158777215611599090986301 9809541455854349659119863)
      ·
        refine ⟨14714312183781524488679795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9809541455854349659119863 14714312183781524488679795)
        ·
          refine ⟨22071468275672286733019693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14714312183781524488679795 22071468275672286733019693)
          ·
            refine ⟨8276800603377107524882385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22071468275672286733019693 8276800603377107524882385)
            ·
              refine ⟨6207600452532830643661789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8276800603377107524882385 6207600452532830643661789)
              ·
                refine ⟨2327850169699811491373171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6207600452532830643661789 2327850169699811491373171)
                ·
                  refine ⟨3491775254549717237059757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327850169699811491373171 3491775254549717237059757)
                  ·
                    refine ⟨1309415720456143963897409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491775254549717237059757 1309415720456143963897409)
                    ·
                      rfl

theorem cell22_3825117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_3825117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825117 prefixEnd_3825117 := by exact prefixLift 3825117
  have htrace : WordTrace (prefixWord ++ tailWord_3825117) baseStart_3825117 baseEnd_3825117 := by
    simpa [prefixWord, tailWord_3825117, baseEnd_3825117] using wordTrace_append hprefix tailTrace_3825117
  have hstable : (prefixWord ++ tailWord_3825117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825117).length < 2 ^ (prefixWord ++ tailWord_3825117).sum := by decide
  have hdescent : baseEnd_3825117 < baseStart_3825117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825130 : List Nat := [3, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_3825130 : Nat := 118140960795 + 3825130 * 2 ^ 59
def prefixEnd_3825130 : Nat := 4983230072969 + 3 ^ 40 * 3825130 * 2
def baseEnd_3825130 : Nat := 436473390207272087774123

theorem tailTrace_3825130 : CollatzResearch.WordTrace tailWord_3825130 prefixEnd_3825130 436473390207272087774123 := by
  unfold tailWord_3825130
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878488158053691259704211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93009301754809843359211229 34878488158053691259704211)
  ·
    refine ⟨52317732237080536889556317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34878488158053691259704211 52317732237080536889556317)
    ·
      refine ⟨19619149588905201333583619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52317732237080536889556317 19619149588905201333583619)
      ·
        refine ⟨29428724383357802000375429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19619149588905201333583619 29428724383357802000375429)
        ·
          refine ⟨5517885821879587875070393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29428724383357802000375429 5517885821879587875070393)
          ·
            refine ⟨4138414366409690906302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5517885821879587875070393 4138414366409690906302795)
            ·
              refine ⟨6207621549614536359454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138414366409690906302795 6207621549614536359454193)
              ·
                refine ⟨4655716162210902269590645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6207621549614536359454193 4655716162210902269590645)
                ·
                  refine ⟨436473390207272087774123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4655716162210902269590645 436473390207272087774123)
                  ·
                    rfl

theorem cell22_3825130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_3825130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825130 prefixEnd_3825130 := by exact prefixLift 3825130
  have htrace : WordTrace (prefixWord ++ tailWord_3825130) baseStart_3825130 baseEnd_3825130 := by
    simpa [prefixWord, tailWord_3825130, baseEnd_3825130] using wordTrace_append hprefix tailTrace_3825130
  have hstable : (prefixWord ++ tailWord_3825130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825130).length < 2 ^ (prefixWord ++ tailWord_3825130).sum := by decide
  have hdescent : baseEnd_3825130 < baseStart_3825130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825171 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 1, 6]
def baseStart_3825171 : Nat := 118140960795 + 3825171 * 2 ^ 59
def prefixEnd_3825171 : Nat := 4983230072969 + 3 ^ 40 * 3825171 * 2
def baseEnd_3825171 : Nat := 1309434205759705823047243

theorem tailTrace_3825171 : CollatzResearch.WordTrace tailWord_3825171 prefixEnd_3825171 1309434205759705823047243 := by
  unfold tailWord_3825171
  simp only [CollatzResearch.WordTrace]
  refine ⟨139515448025066229041059367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93010298683377486027372911 139515448025066229041059367)
  ·
    refine ⟨209273172037599343561589051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139515448025066229041059367 209273172037599343561589051)
    ·
      refine ⟨313909758056399015342383577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209273172037599343561589051 313909758056399015342383577)
      ·
        refine ⟨235432318542299261506787683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 313909758056399015342383577 235432318542299261506787683)
        ·
          refine ⟨353148477813448892260181525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235432318542299261506787683 353148477813448892260181525)
          ·
            refine ⟨16553834897505416824696009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 353148477813448892260181525 16553834897505416824696009)
            ·
              refine ⟨12415376173129062618522007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16553834897505416824696009 12415376173129062618522007)
              ·
                refine ⟨18623064259693593927783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12415376173129062618522007 18623064259693593927783011)
                ·
                  refine ⟨27934596389540390891674517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18623064259693593927783011 27934596389540390891674517)
                  ·
                    refine ⟨1309434205759705823047243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27934596389540390891674517 1309434205759705823047243)
                    ·
                      rfl

theorem cell22_3825171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 1, 6].length) (baseStart_3825171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825171 prefixEnd_3825171 := by exact prefixLift 3825171
  have htrace : WordTrace (prefixWord ++ tailWord_3825171) baseStart_3825171 baseEnd_3825171 := by
    simpa [prefixWord, tailWord_3825171, baseEnd_3825171] using wordTrace_append hprefix tailTrace_3825171
  have hstable : (prefixWord ++ tailWord_3825171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825171).length < 2 ^ (prefixWord ++ tailWord_3825171).sum := by decide
  have hdescent : baseEnd_3825171 < baseStart_3825171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825173 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_3825173 : Nat := 118140960795 + 3825173 * 2 ^ 59
def prefixEnd_3825173 : Nat := 4983230072969 + 3 ^ 40 * 3825173 * 2
def baseEnd_3825173 : Nat := 1309434890400578484497237

theorem tailTrace_3825173 : CollatzResearch.WordTrace tailWord_3825173 prefixEnd_3825173 1309434890400578484497237 := by
  unfold tailWord_3825173
  simp only [CollatzResearch.WordTrace]
  refine ⟨139515520971058983382632173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93010347314039322255088115 139515520971058983382632173)
  ·
    refine ⟨52318320364147118768487065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139515520971058983382632173 52318320364147118768487065)
    ·
      refine ⟨39238740273110339076365299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52318320364147118768487065 39238740273110339076365299)
      ·
        refine ⟨58858110409665508614547949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39238740273110339076365299 58858110409665508614547949)
        ·
          refine ⟨22071791403624565730455481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58858110409665508614547949 22071791403624565730455481)
          ·
            refine ⟨16553843552718424297841611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22071791403624565730455481 16553843552718424297841611)
            ·
              refine ⟨24830765329077636446762417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16553843552718424297841611 24830765329077636446762417)
              ·
                refine ⟨18623073996808227335071813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24830765329077636446762417 18623073996808227335071813)
                ·
                  refine ⟨3491826374401542625325965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18623073996808227335071813 3491826374401542625325965)
                  ·
                    refine ⟨1309434890400578484497237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491826374401542625325965 1309434890400578484497237)
                    ·
                      rfl

theorem cell22_3825173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_3825173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825173 prefixEnd_3825173 := by exact prefixLift 3825173
  have htrace : WordTrace (prefixWord ++ tailWord_3825173) baseStart_3825173 baseEnd_3825173 := by
    simpa [prefixWord, tailWord_3825173, baseEnd_3825173] using wordTrace_append hprefix tailTrace_3825173
  have hstable : (prefixWord ++ tailWord_3825173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825173).length < 2 ^ (prefixWord ++ tailWord_3825173).sum := by decide
  have hdescent : baseEnd_3825173 < baseStart_3825173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825186 : List Nat := [3, 3, 1, 1, 1, 1, 12]
def baseStart_3825186 : Nat := 118140960795 + 3825186 * 2 ^ 59
def prefixEnd_3825186 : Nat := 4983230072969 + 3 ^ 40 * 3825186 * 2
def baseEnd_3825186 : Nat := 48497753354305584589711

theorem tailTrace_3825186 : CollatzResearch.WordTrace tailWord_3825186 prefixEnd_3825186 48497753354305584589711 := by
  unfold tailWord_3825186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34878998780002971650713853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93010663413341257735236941 34878998780002971650713853)
  ·
    refine ⟨13079624542501114369017695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34878998780002971650713853 13079624542501114369017695)
    ·
      refine ⟨19619436813751671553526543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13079624542501114369017695 19619436813751671553526543)
      ·
        refine ⟨29429155220627507330289815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19619436813751671553526543 29429155220627507330289815)
        ·
          refine ⟨44143732830941260995434723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29429155220627507330289815 44143732830941260995434723)
          ·
            refine ⟨66215599246411891493152085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44143732830941260995434723 66215599246411891493152085)
            ·
              refine ⟨48497753354305584589711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66215599246411891493152085 48497753354305584589711)
              ·
                rfl

theorem cell22_3825186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 12].length) (baseStart_3825186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825186 prefixEnd_3825186 := by exact prefixLift 3825186
  have htrace : WordTrace (prefixWord ++ tailWord_3825186) baseStart_3825186 baseEnd_3825186 := by
    simpa [prefixWord, tailWord_3825186, baseEnd_3825186] using wordTrace_append hprefix tailTrace_3825186
  have hstable : (prefixWord ++ tailWord_3825186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825186).length < 2 ^ (prefixWord ++ tailWord_3825186).sum := by decide
  have hdescent : baseEnd_3825186 < baseStart_3825186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825192 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 6]
def baseStart_3825192 : Nat := 118140960795 + 3825192 * 2 ^ 59
def prefixEnd_3825192 : Nat := 4983230072969 + 3 ^ 40 * 3825192 * 2
def baseEnd_3825192 : Nat := 436480464829622922757393

theorem tailTrace_3825192 : CollatzResearch.WordTrace tailWord_3825192 prefixEnd_3825192 436480464829622922757393 := by
  unfold tailWord_3825192
  simp only [CollatzResearch.WordTrace]
  refine ⟨69758106978995074813786915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93010809305326766418382553 69758106978995074813786915)
  ·
    refine ⟨104637160468492612220680373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69758106978995074813786915 104637160468492612220680373)
    ·
      refine ⟨9809733793921182395688785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104637160468492612220680373 9809733793921182395688785)
      ·
        refine ⟨7357300345440886796766589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9809733793921182395688785 7357300345440886796766589)
        ·
          refine ⟨2758987629540332548787471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7357300345440886796766589 2758987629540332548787471)
          ·
            refine ⟨4138481444310498823181207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2758987629540332548787471 4138481444310498823181207)
            ·
              refine ⟨6207722166465748234771811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138481444310498823181207 6207722166465748234771811)
              ·
                refine ⟨9311583249698622352157717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6207722166465748234771811 9311583249698622352157717)
                ·
                  refine ⟨436480464829622922757393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9311583249698622352157717 436480464829622922757393)
                  ·
                    rfl

theorem cell22_3825192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 6].length) (baseStart_3825192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825192 prefixEnd_3825192 := by exact prefixLift 3825192
  have htrace : WordTrace (prefixWord ++ tailWord_3825192) baseStart_3825192 baseEnd_3825192 := by
    simpa [prefixWord, tailWord_3825192, baseEnd_3825192] using wordTrace_append hprefix tailTrace_3825192
  have hstable : (prefixWord ++ tailWord_3825192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825192).length < 2 ^ (prefixWord ++ tailWord_3825192).sum := by decide
  have hdescent : baseEnd_3825192 < baseStart_3825192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825207 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 2, 3]
def baseStart_3825207 : Nat := 118140960795 + 3825207 * 2 ^ 59
def prefixEnd_3825207 : Nat := 4983230072969 + 3 ^ 40 * 3825207 * 2
def baseEnd_3825207 : Nat := 1309446529295413729147133

theorem tailTrace_3825207 : CollatzResearch.WordTrace tailWord_3825207 prefixEnd_3825207 1309446529295413729147133 := by
  unfold tailWord_3825207
  simp only [CollatzResearch.WordTrace]
  refine ⟨139516761052935807189369875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93011174035290538126246583 139516761052935807189369875)
  ·
    refine ⟨209275141579403710784054813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139516761052935807189369875 209275141579403710784054813)
    ·
      refine ⟨78478178092276391544020555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209275141579403710784054813 78478178092276391544020555)
      ·
        refine ⟨117717267138414587316030833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78478178092276391544020555 117717267138414587316030833)
        ·
          refine ⟨88287950353810940487023125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117717267138414587316030833 88287950353810940487023125)
          ·
            refine ⟨4138497672834887835329209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88287950353810940487023125 4138497672834887835329209)
            ·
              refine ⟨3103873254626165876496907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138497672834887835329209 3103873254626165876496907)
              ·
                refine ⟨4655809881939248814745361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3103873254626165876496907 4655809881939248814745361)
                ·
                  refine ⟨3491857411454436611059021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4655809881939248814745361 3491857411454436611059021)
                  ·
                    refine ⟨1309446529295413729147133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491857411454436611059021 1309446529295413729147133)
                    ·
                      rfl

theorem cell22_3825207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_3825207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825207 prefixEnd_3825207 := by exact prefixLift 3825207
  have htrace : WordTrace (prefixWord ++ tailWord_3825207) baseStart_3825207 baseEnd_3825207 := by
    simpa [prefixWord, tailWord_3825207, baseEnd_3825207] using wordTrace_append hprefix tailTrace_3825207
  have hstable : (prefixWord ++ tailWord_3825207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825207).length < 2 ^ (prefixWord ++ tailWord_3825207).sum := by decide
  have hdescent : baseEnd_3825207 < baseStart_3825207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825252 : List Nat := [2, 3, 1, 1, 2, 4, 1, 4, 1, 3]
def baseStart_3825252 : Nat := 118140960795 + 3825252 * 2 ^ 59
def prefixEnd_3825252 : Nat := 4983230072969 + 3 ^ 40 * 3825252 * 2
def baseEnd_3825252 : Nat := 1309461933715048611771995

theorem tailTrace_3825252 : CollatzResearch.WordTrace tailWord_3825252 prefixEnd_3825252 1309461933715048611771995 := by
  unfold tailWord_3825252
  simp only [CollatzResearch.WordTrace]
  refine ⟨69759201168886389937379005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93012268225181853249838673 69759201168886389937379005)
  ·
    refine ⟨26159700438332396226517127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69759201168886389937379005 26159700438332396226517127)
    ·
      refine ⟨39239550657498594339775691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26159700438332396226517127 39239550657498594339775691)
      ·
        refine ⟨58859325986247891509663537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39239550657498594339775691 58859325986247891509663537)
        ·
          refine ⟨44144494489685918632247653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58859325986247891509663537 44144494489685918632247653)
          ·
            refine ⟨8277092716816109743546435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44144494489685918632247653 8277092716816109743546435)
            ·
              refine ⟨12415639075224164615319653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277092716816109743546435 12415639075224164615319653)
              ·
                refine ⟨2327932326604530865372435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12415639075224164615319653 2327932326604530865372435)
                ·
                  refine ⟨3491898489906796298058653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2327932326604530865372435 3491898489906796298058653)
                  ·
                    refine ⟨1309461933715048611771995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3491898489906796298058653 1309461933715048611771995)
                    ·
                      rfl

theorem cell22_3825252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_3825252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825252 prefixEnd_3825252 := by exact prefixLift 3825252
  have htrace : WordTrace (prefixWord ++ tailWord_3825252) baseStart_3825252 baseEnd_3825252 := by
    simpa [prefixWord, tailWord_3825252, baseEnd_3825252] using wordTrace_append hprefix tailTrace_3825252
  have hstable : (prefixWord ++ tailWord_3825252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825252).length < 2 ^ (prefixWord ++ tailWord_3825252).sum := by decide
  have hdescent : baseEnd_3825252 < baseStart_3825252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825310 : List Nat := [4, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3825310 : Nat := 118140960795 + 3825310 * 2 ^ 59
def prefixEnd_3825310 : Nat := 4983230072969 + 3 ^ 40 * 3825310 * 2
def baseEnd_3825310 : Nat := 436493929433451931273939

theorem tailTrace_3825310 : CollatzResearch.WordTrace tailWord_3825310 prefixEnd_3825310 436493929433451931273939 := by
  unfold tailWord_3825310
  simp only [CollatzResearch.WordTrace]
  refine ⟨17440064721445331972546173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93013678514375103853579589 17440064721445331972546173)
  ·
    refine ⟨6540024270541999489704815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17440064721445331972546173 6540024270541999489704815)
    ·
      refine ⟨9810036405812999234557223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6540024270541999489704815 9810036405812999234557223)
      ·
        refine ⟨14715054608719498851835835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9810036405812999234557223 14715054608719498851835835)
        ·
          refine ⟨22072581913079248277753753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14715054608719498851835835 22072581913079248277753753)
          ·
            refine ⟨16554436434809436208315315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22072581913079248277753753 16554436434809436208315315)
            ·
              refine ⟨24831654652214154312472973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16554436434809436208315315 24831654652214154312472973)
              ·
                refine ⟨9311870494580307867177365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24831654652214154312472973 9311870494580307867177365)
                ·
                  refine ⟨436493929433451931273939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9311870494580307867177365 436493929433451931273939)
                  ·
                    rfl

theorem cell22_3825310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3825310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825310 prefixEnd_3825310 := by exact prefixLift 3825310
  have htrace : WordTrace (prefixWord ++ tailWord_3825310) baseStart_3825310 baseEnd_3825310 := by
    simpa [prefixWord, tailWord_3825310, baseEnd_3825310] using wordTrace_append hprefix tailTrace_3825310
  have hstable : (prefixWord ++ tailWord_3825310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825310).length < 2 ^ (prefixWord ++ tailWord_3825310).sum := by decide
  have hdescent : baseEnd_3825310 < baseStart_3825310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825338 : List Nat := [3, 1, 1, 1, 2, 5, 1, 8]
def baseStart_3825338 : Nat := 118140960795 + 3825338 * 2 ^ 59
def prefixEnd_3825338 : Nat := 4983230072969 + 3 ^ 40 * 3825338 * 2
def baseEnd_3825338 : Nat := 145499041474730339346859

theorem tailTrace_3825338 : CollatzResearch.WordTrace tailWord_3825338 prefixEnd_3825338 145499041474730339346859 := by
  unfold tailWord_3825338
  simp only [CollatzResearch.WordTrace]
  refine ⟨34880384753865304140597167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 93014359343640811041592445 34880384753865304140597167)
  ·
    refine ⟨52320577130797956210895751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34880384753865304140597167 52320577130797956210895751)
    ·
      refine ⟨78480865696196934316343627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52320577130797956210895751 78480865696196934316343627)
      ·
        refine ⟨117721298544295401474515441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78480865696196934316343627 117721298544295401474515441)
        ·
          refine ⟨88290973908221551105886581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117721298544295401474515441 88290973908221551105886581)
          ·
            refine ⟨8277278803895770416176867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88290973908221551105886581 8277278803895770416176867)
            ·
              refine ⟨12415918205843655624265301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277278803895770416176867 12415918205843655624265301)
              ·
                refine ⟨145499041474730339346859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12415918205843655624265301 145499041474730339346859)
                ·
                  rfl

theorem cell22_3825338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_3825338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825338 prefixEnd_3825338 := by exact prefixLift 3825338
  have htrace : WordTrace (prefixWord ++ tailWord_3825338) baseStart_3825338 baseEnd_3825338 := by
    simpa [prefixWord, tailWord_3825338, baseEnd_3825338] using wordTrace_append hprefix tailTrace_3825338
  have hstable : (prefixWord ++ tailWord_3825338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825338).length < 2 ^ (prefixWord ++ tailWord_3825338).sum := by decide
  have hdescent : baseEnd_3825338 < baseStart_3825338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825357 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_3825357 : Nat := 118140960795 + 3825357 * 2 ^ 59
def prefixEnd_3825357 : Nat := 4983230072969 + 3 ^ 40 * 3825357 * 2
def baseEnd_3825357 : Nat := 1309497877360863337896673

theorem tailTrace_3825357 : CollatzResearch.WordTrace tailWord_3825357 prefixEnd_3825357 1309497877360863337896673 := by
  unfold tailWord_3825357
  simp only [CollatzResearch.WordTrace]
  refine ⟨139522232002392382807330325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93014821334928255204886883 139522232002392382807330325)
  ·
    refine ⟨6540104625112142944093609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 139522232002392382807330325 6540104625112142944093609)
    ·
      refine ⟨4905078468834107208070207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6540104625112142944093609 4905078468834107208070207)
      ·
        refine ⟨7357617703251160812105311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905078468834107208070207 7357617703251160812105311)
        ·
          refine ⟨11036426554876741218157967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7357617703251160812105311 11036426554876741218157967)
          ·
            refine ⟨16554639832315111827236951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11036426554876741218157967 16554639832315111827236951)
            ·
              refine ⟨24831959748472667740855427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16554639832315111827236951 24831959748472667740855427)
              ·
                refine ⟨37247939622709001611283141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24831959748472667740855427 37247939622709001611283141)
                ·
                  refine ⟨6983988679257937802115589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37247939622709001611283141 6983988679257937802115589)
                  ·
                    refine ⟨1309497877360863337896673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6983988679257937802115589 1309497877360863337896673)
                    ·
                      rfl

theorem cell22_3825357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_3825357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825357 prefixEnd_3825357 := by exact prefixLift 3825357
  have htrace : WordTrace (prefixWord ++ tailWord_3825357) baseStart_3825357 baseEnd_3825357 := by
    simpa [prefixWord, tailWord_3825357, baseEnd_3825357] using wordTrace_append hprefix tailTrace_3825357
  have hstable : (prefixWord ++ tailWord_3825357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825357).length < 2 ^ (prefixWord ++ tailWord_3825357).sum := by decide
  have hdescent : baseEnd_3825357 < baseStart_3825357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825368 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3825368 : Nat := 118140960795 + 3825368 * 2 ^ 59
def prefixEnd_3825368 : Nat := 4983230072969 + 3 ^ 40 * 3825368 * 2
def baseEnd_3825368 : Nat := 1309501642885662975871639

theorem tailTrace_3825368 : CollatzResearch.WordTrace tailWord_3825368 prefixEnd_3825368 1309501642885662975871639 := by
  unfold tailWord_3825368
  simp only [CollatzResearch.WordTrace]
  refine ⟨69761316602676265842990379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93015088803568354457320505 69761316602676265842990379)
  ·
    refine ⟨104641974904014398764485569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69761316602676265842990379 104641974904014398764485569)
    ·
      refine ⟨78481481178010799073364177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104641974904014398764485569 78481481178010799073364177)
      ·
        refine ⟨58861110883508099305023133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78481481178010799073364177 58861110883508099305023133)
        ·
          refine ⟨22072916581315537239383675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58861110883508099305023133 22072916581315537239383675)
          ·
            refine ⟨33109374871973305859075513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22072916581315537239383675 33109374871973305859075513)
            ·
              refine ⟨24832031153979979394306635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33109374871973305859075513 24832031153979979394306635)
              ·
                refine ⟨37248046730969969091459953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24832031153979979394306635 37248046730969969091459953)
                ·
                  refine ⟨27936035048227476818594965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37248046730969969091459953 27936035048227476818594965)
                  ·
                    refine ⟨1309501642885662975871639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27936035048227476818594965 1309501642885662975871639)
                    ·
                      rfl

theorem cell22_3825368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3825368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825368 prefixEnd_3825368 := by exact prefixLift 3825368
  have htrace : WordTrace (prefixWord ++ tailWord_3825368) baseStart_3825368 baseEnd_3825368 := by
    simpa [prefixWord, tailWord_3825368, baseEnd_3825368] using wordTrace_append hprefix tailTrace_3825368
  have hstable : (prefixWord ++ tailWord_3825368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825368).length < 2 ^ (prefixWord ++ tailWord_3825368).sum := by decide
  have hdescent : baseEnd_3825368 < baseStart_3825368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825372 : List Nat := [2, 2, 5, 1, 2, 1, 2, 7]
def baseStart_3825372 : Nat := 118140960795 + 3825372 * 2 ^ 59
def prefixEnd_3825372 : Nat := 4983230072969 + 3 ^ 40 * 3825372 * 2
def baseEnd_3825372 : Nat := 145500334685267588752403

theorem tailTrace_3825372 : CollatzResearch.WordTrace tailWord_3825372 prefixEnd_3825372 145500334685267588752403 := by
  unfold tailWord_3825372
  simp only [CollatzResearch.WordTrace]
  refine ⟨69761389548669020184563185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93015186064892026912750913 69761389548669020184563185)
  ·
    refine ⟨52321042161501765138422389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69761389548669020184563185 52321042161501765138422389)
    ·
      refine ⟨4905097702640790481727099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52321042161501765138422389 4905097702640790481727099)
      ·
        refine ⟨7357646553961185722590649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905097702640790481727099 7357646553961185722590649)
        ·
          refine ⟨5518234915470889291942987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7357646553961185722590649 5518234915470889291942987)
          ·
            refine ⟨8277352373206333937914481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518234915470889291942987 8277352373206333937914481)
            ·
              refine ⟨6208014279904750453435861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8277352373206333937914481 6208014279904750453435861)
              ·
                refine ⟨145500334685267588752403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6208014279904750453435861 145500334685267588752403)
                ·
                  rfl

theorem cell22_3825372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 7].length) (baseStart_3825372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825372 prefixEnd_3825372 := by exact prefixLift 3825372
  have htrace : WordTrace (prefixWord ++ tailWord_3825372) baseStart_3825372 baseEnd_3825372 := by
    simpa [prefixWord, tailWord_3825372, baseEnd_3825372] using wordTrace_append hprefix tailTrace_3825372
  have hstable : (prefixWord ++ tailWord_3825372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825372).length < 2 ^ (prefixWord ++ tailWord_3825372).sum := by decide
  have hdescent : baseEnd_3825372 < baseStart_3825372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825445 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 6]
def baseStart_3825445 : Nat := 118140960795 + 3825445 * 2 ^ 59
def prefixEnd_3825445 : Nat := 4983230072969 + 3 ^ 40 * 3825445 * 2
def baseEnd_3825445 : Nat := 436509333853086813898801

theorem tailTrace_3825445 : CollatzResearch.WordTrace tailWord_3825445 prefixEnd_3825445 436509333853086813898801 := by
  unfold tailWord_3825445
  simp only [CollatzResearch.WordTrace]
  refine ⟨139525441626073573836533789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93016961084049049224355859 139525441626073573836533789)
  ·
    refine ⟨52322040609777590188700171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139525441626073573836533789 52322040609777590188700171)
    ·
      refine ⟨78483060914666385283050257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52322040609777590188700171 78483060914666385283050257)
      ·
        refine ⟨58862295685999788962287693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78483060914666385283050257 58862295685999788962287693)
        ·
          refine ⟨22073360882249920860857885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58862295685999788962287693 22073360882249920860857885)
          ·
            refine ⟨8277510330843720322821707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22073360882249920860857885 8277510330843720322821707)
            ·
              refine ⟨12416265496265580484232561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8277510330843720322821707 12416265496265580484232561)
              ·
                refine ⟨9312199122199185363174421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12416265496265580484232561 9312199122199185363174421)
                ·
                  refine ⟨436509333853086813898801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9312199122199185363174421 436509333853086813898801)
                  ·
                    rfl

theorem cell22_3825445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_3825445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825445 prefixEnd_3825445 := by exact prefixLift 3825445
  have htrace : WordTrace (prefixWord ++ tailWord_3825445) baseStart_3825445 baseEnd_3825445 := by
    simpa [prefixWord, tailWord_3825445, baseEnd_3825445] using wordTrace_append hprefix tailTrace_3825445
  have hstable : (prefixWord ++ tailWord_3825445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825445).length < 2 ^ (prefixWord ++ tailWord_3825445).sum := by decide
  have hdescent : baseEnd_3825445 < baseStart_3825445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825464 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 1, 4]
def baseStart_3825464 : Nat := 118140960795 + 3825464 * 2 ^ 59
def prefixEnd_3825464 : Nat := 4983230072969 + 3 ^ 40 * 3825464 * 2
def baseEnd_3825464 : Nat := 1309534505647550725471345

theorem tailTrace_3825464 : CollatzResearch.WordTrace tailWord_3825464 prefixEnd_3825464 1309534505647550725471345 := by
  unfold tailWord_3825464
  simp only [CollatzResearch.WordTrace]
  refine ⟨69763067306502370040737723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93017423075336493387650297 69763067306502370040737723)
  ·
    refine ⟨104644600959753555061106585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69763067306502370040737723 104644600959753555061106585)
    ·
      refine ⟨78483450719815166295829939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104644600959753555061106585 78483450719815166295829939)
      ·
        refine ⟨117725176079722749443744909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78483450719815166295829939 117725176079722749443744909)
        ·
          refine ⟨44146941029896031041404341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 117725176079722749443744909 44146941029896031041404341)
          ·
            refine ⟨4138775721552752910131657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44146941029896031041404341 4138775721552752910131657)
            ·
              refine ⟨3104081791164564682598743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4138775721552752910131657 3104081791164564682598743)
              ·
                refine ⟨4656122686746847023898115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3104081791164564682598743 4656122686746847023898115)
                ·
                  refine ⟨6984184030120270535847173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656122686746847023898115 6984184030120270535847173)
                  ·
                    refine ⟨1309534505647550725471345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984184030120270535847173 1309534505647550725471345)
                    ·
                      rfl

theorem cell22_3825464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_3825464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825464 prefixEnd_3825464 := by exact prefixLift 3825464
  have htrace : WordTrace (prefixWord ++ tailWord_3825464) baseStart_3825464 baseEnd_3825464 := by
    simpa [prefixWord, tailWord_3825464, baseEnd_3825464] using wordTrace_append hprefix tailTrace_3825464
  have hstable : (prefixWord ++ tailWord_3825464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825464).length < 2 ^ (prefixWord ++ tailWord_3825464).sum := by decide
  have hdescent : baseEnd_3825464 < baseStart_3825464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825535 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 5]
def baseStart_3825535 : Nat := 118140960795 + 3825535 * 2 ^ 59
def prefixEnd_3825535 : Nat := 4983230072969 + 3 ^ 40 * 3825535 * 2
def baseEnd_3825535 : Nat := 436519603466176735648709

theorem tailTrace_3825535 : CollatzResearch.WordTrace tailWord_3825535 prefixEnd_3825535 436519603466176735648709 := by
  unfold tailWord_3825535
  simp only [CollatzResearch.WordTrace]
  refine ⟨139528724195747519207310059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93019149463831679471540039 139528724195747519207310059)
  ·
    refine ⟨209293086293621278810965089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139528724195747519207310059 209293086293621278810965089)
    ·
      refine ⟨156969814720215959108223817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209293086293621278810965089 156969814720215959108223817)
      ·
        refine ⟨117727361040161969331167863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 156969814720215959108223817 117727361040161969331167863)
        ·
          refine ⟨176591041560242953996751795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117727361040161969331167863 176591041560242953996751795)
          ·
            refine ⟨264886562340364430995127693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 176591041560242953996751795 264886562340364430995127693)
            ·
              refine ⟨99332460877636661623172885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 264886562340364430995127693 99332460877636661623172885)
              ·
                refine ⟨4656209103639218513586229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99332460877636661623172885 4656209103639218513586229)
                ·
                  refine ⟨436519603466176735648709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4656209103639218513586229 436519603466176735648709)
                  ·
                    rfl

theorem cell22_3825535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 5].length) (baseStart_3825535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825535 prefixEnd_3825535 := by exact prefixLift 3825535
  have htrace : WordTrace (prefixWord ++ tailWord_3825535) baseStart_3825535 baseEnd_3825535 := by
    simpa [prefixWord, tailWord_3825535, baseEnd_3825535] using wordTrace_append hprefix tailTrace_3825535
  have hstable : (prefixWord ++ tailWord_3825535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825535).length < 2 ^ (prefixWord ++ tailWord_3825535).sum := by decide
  have hdescent : baseEnd_3825535 < baseStart_3825535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825539 : List Nat := [1, 1, 1, 3, 4, 4, 1, 1, 3, 3]
def baseStart_3825539 : Nat := 118140960795 + 3825539 * 2 ^ 59
def prefixEnd_3825539 : Nat := 4983230072969 + 3 ^ 40 * 3825539 * 2
def baseEnd_3825539 : Nat := 1309560179680275529846115

theorem tailTrace_3825539 : CollatzResearch.WordTrace tailWord_3825539 prefixEnd_3825539 1309560179680275529846115 := by
  unfold tailWord_3825539
  simp only [CollatzResearch.WordTrace]
  refine ⟨139528870087733027890455671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93019246725155351926970447 139528870087733027890455671)
  ·
    refine ⟨209293305131599541835683507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139528870087733027890455671 209293305131599541835683507)
    ·
      refine ⟨313939957697399312753525261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209293305131599541835683507 313939957697399312753525261)
      ·
        refine ⟨117727484136524742282571973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 313939957697399312753525261 117727484136524742282571973)
        ·
          refine ⟨22073903275598389177982245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 117727484136524742282571973 22073903275598389177982245)
          ·
            refine ⟨4138856864174697970871671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22073903275598389177982245 4138856864174697970871671)
            ·
              refine ⟨6208285296262046956307507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4138856864174697970871671 6208285296262046956307507)
              ·
                refine ⟨9312427944393070434461261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208285296262046956307507 9312427944393070434461261)
                ·
                  refine ⟨3492160479147401412922973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9312427944393070434461261 3492160479147401412922973)
                  ·
                    refine ⟨1309560179680275529846115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492160479147401412922973 1309560179680275529846115)
                    ·
                      rfl

theorem cell22_3825539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3, 3].length) (baseStart_3825539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825539 prefixEnd_3825539 := by exact prefixLift 3825539
  have htrace : WordTrace (prefixWord ++ tailWord_3825539) baseStart_3825539 baseEnd_3825539 := by
    simpa [prefixWord, tailWord_3825539, baseEnd_3825539] using wordTrace_append hprefix tailTrace_3825539
  have hstable : (prefixWord ++ tailWord_3825539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825539).length < 2 ^ (prefixWord ++ tailWord_3825539).sum := by decide
  have hdescent : baseEnd_3825539 < baseStart_3825539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825612 : List Nat := [2, 2, 1, 4, 1, 2, 1, 3, 1, 5]
def baseStart_3825612 : Nat := 118140960795 + 3825612 * 2 ^ 59
def prefixEnd_3825612 : Nat := 4983230072969 + 3 ^ 40 * 3825612 * 2
def baseEnd_3825612 : Nat := 1309585169072127672770891

theorem tailTrace_3825612 : CollatzResearch.WordTrace tailWord_3825612 prefixEnd_3825612 1309585169072127672770891 := by
  unfold tailWord_3825612
  simp only [CollatzResearch.WordTrace]
  refine ⟨69765766308234280678931545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93021021744312374238575393 69765766308234280678931545)
  ·
    refine ⟨52324324731175710509198659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69765766308234280678931545 52324324731175710509198659)
    ·
      refine ⟨78486487096763565763797989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52324324731175710509198659 78486487096763565763797989)
      ·
        refine ⟨14716216330643168580712123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78486487096763565763797989 14716216330643168580712123)
        ·
          refine ⟨22074324495964752871068185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14716216330643168580712123 22074324495964752871068185)
          ·
            refine ⟨16555743371973564653301139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22074324495964752871068185 16555743371973564653301139)
            ·
              refine ⟨24833615057960346979951709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16555743371973564653301139 24833615057960346979951709)
              ·
                refine ⟨9312605646735130117481891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24833615057960346979951709 9312605646735130117481891)
                ·
                  refine ⟨13968908470102695176222837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9312605646735130117481891 13968908470102695176222837)
                  ·
                    refine ⟨1309585169072127672770891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13968908470102695176222837 1309585169072127672770891)
                    ·
                      rfl

theorem cell22_3825612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 1, 5].length) (baseStart_3825612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825612 prefixEnd_3825612 := by exact prefixLift 3825612
  have htrace : WordTrace (prefixWord ++ tailWord_3825612) baseStart_3825612 baseEnd_3825612 := by
    simpa [prefixWord, tailWord_3825612, baseEnd_3825612] using wordTrace_append hprefix tailTrace_3825612
  have hstable : (prefixWord ++ tailWord_3825612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825612).length < 2 ^ (prefixWord ++ tailWord_3825612).sum := by decide
  have hdescent : baseEnd_3825612 < baseStart_3825612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825646 : List Nat := [4, 1, 2, 1, 3, 1, 3, 2, 2, 3]
def baseStart_3825646 : Nat := 118140960795 + 3825646 * 2 ^ 59
def prefixEnd_3825646 : Nat := 4983230072969 + 3 ^ 40 * 3825646 * 2
def baseEnd_3825646 : Nat := 1309596807966962917420787

theorem tailTrace_3825646 : CollatzResearch.WordTrace tailWord_3825646 prefixEnd_3825646 1309596807966962917420787 := by
  unfold tailWord_3825646
  simp only [CollatzResearch.WordTrace]
  refine ⟨17441596587293173145575099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93021848465563590109733861 17441596587293173145575099)
  ·
    refine ⟨26162394880939759718362649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17441596587293173145575099 26162394880939759718362649)
    ·
      refine ⟨19621796160704819788771987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26162394880939759718362649 19621796160704819788771987)
      ·
        refine ⟨29432694241057229683157981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19621796160704819788771987 29432694241057229683157981)
        ·
          refine ⟨11037260340396461131184243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29432694241057229683157981 11037260340396461131184243)
          ·
            refine ⟨16555890510594691696776365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037260340396461131184243 16555890510594691696776365)
            ·
              refine ⟨6208458941473009386291137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16555890510594691696776365 6208458941473009386291137)
              ·
                refine ⟨4656344206104757039718353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208458941473009386291137 4656344206104757039718353)
                ·
                  refine ⟨3492258154578567779788765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656344206104757039718353 3492258154578567779788765)
                  ·
                    refine ⟨1309596807966962917420787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492258154578567779788765 1309596807966962917420787)
                    ·
                      rfl

theorem cell22_3825646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_3825646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825646 prefixEnd_3825646 := by exact prefixLift 3825646
  have htrace : WordTrace (prefixWord ++ tailWord_3825646) baseStart_3825646 baseEnd_3825646 := by
    simpa [prefixWord, tailWord_3825646, baseEnd_3825646] using wordTrace_append hprefix tailTrace_3825646
  have hstable : (prefixWord ++ tailWord_3825646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825646).length < 2 ^ (prefixWord ++ tailWord_3825646).sum := by decide
  have hdescent : baseEnd_3825646 < baseStart_3825646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825764 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_3825764 : Nat := 118140960795 + 3825764 * 2 ^ 59
def prefixEnd_3825764 : Nat := 4983230072969 + 3 ^ 40 * 3825764 * 2
def baseEnd_3825764 : Nat := 1309637201778449942970425

theorem tailTrace_3825764 : CollatzResearch.WordTrace tailWord_3825764 prefixEnd_3825764 1309637201778449942970425 := by
  unfold tailWord_3825764
  simp only [CollatzResearch.WordTrace]
  refine ⟨69768538255958945658698173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93024717674611927544930897 69768538255958945658698173)
  ·
    refine ⟨26163201845984604622011815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69768538255958945658698173 26163201845984604622011815)
    ·
      refine ⟨39244802768976906933017723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26163201845984604622011815 39244802768976906933017723)
      ·
        refine ⟨58867204153465360399526585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39244802768976906933017723 58867204153465360399526585)
        ·
          refine ⟨44150403115099020299644939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58867204153465360399526585 44150403115099020299644939)
          ·
            refine ⟨66225604672648530449467409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44150403115099020299644939 66225604672648530449467409)
            ·
              refine ⟨49669203504486397837100557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66225604672648530449467409 49669203504486397837100557)
              ·
                refine ⟨18625951314182399188912709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49669203504486397837100557 18625951314182399188912709)
                ·
                  refine ⟨3492365871409199847921133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18625951314182399188912709 3492365871409199847921133)
                  ·
                    refine ⟨1309637201778449942970425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492365871409199847921133 1309637201778449942970425)
                    ·
                      rfl

theorem cell22_3825764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_3825764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825764 prefixEnd_3825764 := by exact prefixLift 3825764
  have htrace : WordTrace (prefixWord ++ tailWord_3825764) baseStart_3825764 baseEnd_3825764 := by
    simpa [prefixWord, tailWord_3825764, baseEnd_3825764] using wordTrace_append hprefix tailTrace_3825764
  have hstable : (prefixWord ++ tailWord_3825764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825764).length < 2 ^ (prefixWord ++ tailWord_3825764).sum := by decide
  have hdescent : baseEnd_3825764 < baseStart_3825764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825815 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 2, 3]
def baseStart_3825815 : Nat := 118140960795 + 3825815 * 2 ^ 59
def prefixEnd_3825815 : Nat := 4983230072969 + 3 ^ 40 * 3825815 * 2
def baseEnd_3825815 : Nat := 1309654660120702809945269

theorem tailTrace_3825815 : CollatzResearch.WordTrace tailWord_3825815 prefixEnd_3825815 1309654660120702809945269 := by
  unfold tailWord_3825815
  simp only [CollatzResearch.WordTrace]
  refine ⟨139538936634733127027502899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93025957756488751351668599 139538936634733127027502899)
  ·
    refine ⟨209308404952099690541254349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139538936634733127027502899 209308404952099690541254349)
    ·
      refine ⟨78490651857037383952970381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209308404952099690541254349 78490651857037383952970381)
      ·
        refine ⟨29433994446389018982363893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78490651857037383952970381 29433994446389018982363893)
        ·
          refine ⟨2759436979348970529596615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29433994446389018982363893 2759436979348970529596615)
          ·
            refine ⟨4139155469023455794394923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759436979348970529596615 4139155469023455794394923)
            ·
              refine ⟨6208733203535183691592385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139155469023455794394923 6208733203535183691592385)
              ·
                refine ⟨4656549902651387768694289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208733203535183691592385 4656549902651387768694289)
                ·
                  refine ⟨3492412426988540826520717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4656549902651387768694289 3492412426988540826520717)
                  ·
                    refine ⟨1309654660120702809945269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492412426988540826520717 1309654660120702809945269)
                    ·
                      rfl

theorem cell22_3825815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_3825815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825815 prefixEnd_3825815 := by exact prefixLift 3825815
  have htrace : WordTrace (prefixWord ++ tailWord_3825815) baseStart_3825815 baseEnd_3825815 := by
    simpa [prefixWord, tailWord_3825815, baseEnd_3825815] using wordTrace_append hprefix tailTrace_3825815
  have hstable : (prefixWord ++ tailWord_3825815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825815).length < 2 ^ (prefixWord ++ tailWord_3825815).sum := by decide
  have hdescent : baseEnd_3825815 < baseStart_3825815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825845 : List Nat := [1, 3, 3, 4, 2, 1, 2, 6]
def baseStart_3825845 : Nat := 118140960795 + 3825845 * 2 ^ 59
def prefixEnd_3825845 : Nat := 4983230072969 + 3 ^ 40 * 3825845 * 2
def baseEnd_3825845 : Nat := 145518325525976970188353

theorem tailTrace_3825845 : CollatzResearch.WordTrace tailWord_3825845 prefixEnd_3825845 145518325525976970188353 := by
  unfold tailWord_3825845
  simp only [CollatzResearch.WordTrace]
  refine ⟨139540030824624442151094989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93026687216416294767396659 139540030824624442151094989)
  ·
    refine ⟨52327511559234165806660621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139540030824624442151094989 52327511559234165806660621)
    ·
      refine ⟨19622816834712812177497733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52327511559234165806660621 19622816834712812177497733)
      ·
        refine ⟨3679278156508652283280825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19622816834712812177497733 3679278156508652283280825)
        ·
          refine ⟨2759458617381489212460619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3679278156508652283280825 2759458617381489212460619)
          ·
            refine ⟨4139187926072233818690929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2759458617381489212460619 4139187926072233818690929)
            ·
              refine ⟨3104390944554175364018197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4139187926072233818690929 3104390944554175364018197)
              ·
                refine ⟨145518325525976970188353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3104390944554175364018197 145518325525976970188353)
                ·
                  rfl

theorem cell22_3825845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 6].length) (baseStart_3825845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825845 prefixEnd_3825845 := by exact prefixLift 3825845
  have htrace : WordTrace (prefixWord ++ tailWord_3825845) baseStart_3825845 baseEnd_3825845 := by
    simpa [prefixWord, tailWord_3825845, baseEnd_3825845] using wordTrace_append hprefix tailTrace_3825845
  have hstable : (prefixWord ++ tailWord_3825845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825845).length < 2 ^ (prefixWord ++ tailWord_3825845).sum := by decide
  have hdescent : baseEnd_3825845 < baseStart_3825845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825860 : List Nat := [2, 3, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_3825860 : Nat := 118140960795 + 3825860 * 2 ^ 59
def prefixEnd_3825860 : Nat := 4983230072969 + 3 ^ 40 * 3825860 * 2
def baseEnd_3825860 : Nat := 1309670064540337692570131

theorem tailTrace_3825860 : CollatzResearch.WordTrace tailWord_3825860 prefixEnd_3825860 1309670064540337692570131 := by
  unfold tailWord_3825860
  simp only [CollatzResearch.WordTrace]
  refine ⟨69770288959785049856445517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93027051946380066475260689 69770288959785049856445517)
  ·
    refine ⟨26163858359919393696167069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69770288959785049856445517 26163858359919393696167069)
    ·
      refine ⟨9811446884969772636062651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26163858359919393696167069 9811446884969772636062651)
      ·
        refine ⟨14717170327454658954093977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811446884969772636062651 14717170327454658954093977)
        ·
          refine ⟨11037877745590994215570483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14717170327454658954093977 11037877745590994215570483)
          ·
            refine ⟨16556816618386491323355725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11037877745590994215570483 16556816618386491323355725)
            ·
              refine ⟨6208806231894934246258397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16556816618386491323355725 6208806231894934246258397)
              ·
                refine ⟨2328302336960600342346899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6208806231894934246258397 2328302336960600342346899)
                ·
                  refine ⟨3492453505440900513520349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328302336960600342346899 3492453505440900513520349)
                  ·
                    refine ⟨1309670064540337692570131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492453505440900513520349 1309670064540337692570131)
                    ·
                      rfl

theorem cell22_3825860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_3825860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825860 prefixEnd_3825860 := by exact prefixLift 3825860
  have htrace : WordTrace (prefixWord ++ tailWord_3825860) baseStart_3825860 baseEnd_3825860 := by
    simpa [prefixWord, tailWord_3825860, baseEnd_3825860] using wordTrace_append hprefix tailTrace_3825860
  have hstable : (prefixWord ++ tailWord_3825860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825860).length < 2 ^ (prefixWord ++ tailWord_3825860).sum := by decide
  have hdescent : baseEnd_3825860 < baseStart_3825860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825877 : List Nat := [1, 3, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_3825877 : Nat := 118140960795 + 3825877 * 2 ^ 59
def prefixEnd_3825877 : Nat := 4983230072969 + 3 ^ 40 * 3825877 * 2
def baseEnd_3825877 : Nat := 1309675883987755314895079

theorem tailTrace_3825877 : CollatzResearch.WordTrace tailWord_3825877 prefixEnd_3825877 1309675883987755314895079 := by
  unfold tailWord_3825877
  simp only [CollatzResearch.WordTrace]
  refine ⟨139541197960508511616259885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93027465307005674410839923 139541197960508511616259885)
  ·
    refine ⟨52327949235190691856097457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139541197960508511616259885 52327949235190691856097457)
    ·
      refine ⟨39245961926393018892073093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52327949235190691856097457 39245961926393018892073093)
      ·
        refine ⟨7358617861198691042263705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39245961926393018892073093 7358617861198691042263705)
        ·
          refine ⟨5518963395899018281697779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7358617861198691042263705 5518963395899018281697779)
          ·
            refine ⟨8278445093848527422546669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5518963395899018281697779 8278445093848527422546669)
            ·
              refine ⟨3104416910193197783455001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8278445093848527422546669 3104416910193197783455001)
              ·
                refine ⟨2328312682644898337591251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3104416910193197783455001 2328312682644898337591251)
                ·
                  refine ⟨3492469023967347506386877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2328312682644898337591251 3492469023967347506386877)
                  ·
                    refine ⟨1309675883987755314895079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3492469023967347506386877 1309675883987755314895079)
                    ·
                      rfl

theorem cell22_3825877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_3825877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825877 prefixEnd_3825877 := by exact prefixLift 3825877
  have htrace : WordTrace (prefixWord ++ tailWord_3825877) baseStart_3825877 baseEnd_3825877 := by
    simpa [prefixWord, tailWord_3825877, baseEnd_3825877] using wordTrace_append hprefix tailTrace_3825877
  have hstable : (prefixWord ++ tailWord_3825877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825877).length < 2 ^ (prefixWord ++ tailWord_3825877).sum := by decide
  have hdescent : baseEnd_3825877 < baseStart_3825877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825899 : List Nat := [1, 1, 1, 1, 2, 5, 2, 3, 1, 5]
def baseStart_3825899 : Nat := 118140960795 + 3825899 * 2 ^ 59
def prefixEnd_3825899 : Nat := 4983230072969 + 3 ^ 40 * 3825899 * 2
def baseEnd_3825899 : Nat := 1309683415037354590845011

theorem tailTrace_3825899 : CollatzResearch.WordTrace tailWord_3825899 prefixEnd_3825899 1309683415037354590845011 := by
  unfold tailWord_3825899
  simp only [CollatzResearch.WordTrace]
  refine ⟨139542000366428809373560751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93028000244285872915707167 139542000366428809373560751)
  ·
    refine ⟨209313000549643214060341127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139542000366428809373560751 209313000549643214060341127)
    ·
      refine ⟨313969500824464821090511691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209313000549643214060341127 313969500824464821090511691)
      ·
        refine ⟨470954251236697231635767537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 313969500824464821090511691 470954251236697231635767537)
        ·
          refine ⟨353215688427522923726825653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 470954251236697231635767537 353215688427522923726825653)
          ·
            refine ⟨33113970790080274099389905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 353215688427522923726825653 33113970790080274099389905)
            ·
              refine ⟨24835478092560205574542429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33113970790080274099389905 24835478092560205574542429)
              ·
                refine ⟨9313304284710077090453411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24835478092560205574542429 9313304284710077090453411)
                ·
                  refine ⟨13969956427065115635680117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313304284710077090453411 13969956427065115635680117)
                  ·
                    refine ⟨1309683415037354590845011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13969956427065115635680117 1309683415037354590845011)
                    ·
                      rfl

theorem cell22_3825899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 5].length) (baseStart_3825899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825899 prefixEnd_3825899 := by exact prefixLift 3825899
  have htrace : WordTrace (prefixWord ++ tailWord_3825899) baseStart_3825899 baseEnd_3825899 := by
    simpa [prefixWord, tailWord_3825899, baseEnd_3825899] using wordTrace_append hprefix tailTrace_3825899
  have hstable : (prefixWord ++ tailWord_3825899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825899).length < 2 ^ (prefixWord ++ tailWord_3825899).sum := by decide
  have hdescent : baseEnd_3825899 < baseStart_3825899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825903 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 1, 4]
def baseStart_3825903 : Nat := 118140960795 + 3825903 * 2 ^ 59
def prefixEnd_3825903 : Nat := 4983230072969 + 3 ^ 40 * 3825903 * 2
def baseEnd_3825903 : Nat := 1309684784319099913744999

theorem tailTrace_3825903 : CollatzResearch.WordTrace tailWord_3825903 prefixEnd_3825903 1309684784319099913744999 := by
  unfold tailWord_3825903
  simp only [CollatzResearch.WordTrace]
  refine ⟨139542146258414318056706363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93028097505609545371137575 139542146258414318056706363)
  ·
    refine ⟨209313219387621477085059545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139542146258414318056706363 209313219387621477085059545)
    ·
      refine ⟨156984914540716107813794659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209313219387621477085059545 156984914540716107813794659)
      ·
        refine ⟨235477371811074161720691989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 156984914540716107813794659 235477371811074161720691989)
        ·
          refine ⟨11038001803644101330657437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 235477371811074161720691989 11038001803644101330657437)
          ·
            refine ⟨4139250676366537998996539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11038001803644101330657437 4139250676366537998996539)
            ·
              refine ⟨6208876014549806998494809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4139250676366537998996539 6208876014549806998494809)
              ·
                refine ⟨4656657010912355248871107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6208876014549806998494809 4656657010912355248871107)
                ·
                  refine ⟨6984985516368532873306661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4656657010912355248871107 6984985516368532873306661)
                  ·
                    refine ⟨1309684784319099913744999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6984985516368532873306661 1309684784319099913744999)
                    ·
                      rfl

theorem cell22_3825903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_3825903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825903 prefixEnd_3825903 := by exact prefixLift 3825903
  have htrace : WordTrace (prefixWord ++ tailWord_3825903) baseStart_3825903 baseEnd_3825903 := by
    simpa [prefixWord, tailWord_3825903, baseEnd_3825903] using wordTrace_append hprefix tailTrace_3825903
  have hstable : (prefixWord ++ tailWord_3825903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825903).length < 2 ^ (prefixWord ++ tailWord_3825903).sum := by decide
  have hdescent : baseEnd_3825903 < baseStart_3825903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825916 : List Nat := [2, 2, 2, 1, 4, 2, 1, 2, 1, 5]
def baseStart_3825916 : Nat := 118140960795 + 3825916 * 2 ^ 59
def prefixEnd_3825916 : Nat := 4983230072969 + 3 ^ 40 * 3825916 * 2
def baseEnd_3825916 : Nat := 1309689234484772213169959

theorem tailTrace_3825916 : CollatzResearch.WordTrace tailWord_3825916 prefixEnd_3825916 1309689234484772213169959 := by
  unfold tailWord_3825916
  simp only [CollatzResearch.WordTrace]
  refine ⟨69771310203683610638464801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 93028413604911480851286401 69771310203683610638464801)
  ·
    refine ⟨52328482652762707978848601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69771310203683610638464801 52328482652762707978848601)
    ·
      refine ⟨39246361989572030984136451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52328482652762707978848601 39246361989572030984136451)
      ·
        refine ⟨58869542984358046476204677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39246361989572030984136451 58869542984358046476204677)
        ·
          refine ⟨11038039309567133714288377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58869542984358046476204677 11038039309567133714288377)
          ·
            refine ⟨8278529482175350285716283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11038039309567133714288377 8278529482175350285716283)
            ·
              refine ⟨12417794223263025428574425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8278529482175350285716283 12417794223263025428574425)
              ·
                refine ⟨9313345667447269071430819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12417794223263025428574425 9313345667447269071430819)
                ·
                  refine ⟨13970018501170903607146229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313345667447269071430819 13970018501170903607146229)
                  ·
                    refine ⟨1309689234484772213169959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13970018501170903607146229 1309689234484772213169959)
                    ·
                      rfl

theorem cell22_3825916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_3825916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825916 prefixEnd_3825916 := by exact prefixLift 3825916
  have htrace : WordTrace (prefixWord ++ tailWord_3825916) baseStart_3825916 baseEnd_3825916 := by
    simpa [prefixWord, tailWord_3825916, baseEnd_3825916] using wordTrace_append hprefix tailTrace_3825916
  have hstable : (prefixWord ++ tailWord_3825916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825916).length < 2 ^ (prefixWord ++ tailWord_3825916).sum := by decide
  have hdescent : baseEnd_3825916 < baseStart_3825916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825918 : List Nat := [4, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3825918 : Nat := 118140960795 + 3825918 * 2 ^ 59
def prefixEnd_3825918 : Nat := 4983230072969 + 3 ^ 40 * 3825918 * 2
def baseEnd_3825918 : Nat := 436563306375214958206651

theorem tailTrace_3825918 : CollatzResearch.WordTrace tailWord_3825918 prefixEnd_3825918 436563306375214958206651 := by
  unfold tailWord_3825918
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442836669169996952312801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93028462235573317079001605 17442836669169996952312801)
  ·
    refine ⟨13082127501877497714234601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17442836669169996952312801 13082127501877497714234601)
    ·
      refine ⟨9811595626408123285675951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13082127501877497714234601 9811595626408123285675951)
      ·
        refine ⟨14717393439612184928513927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9811595626408123285675951 14717393439612184928513927)
        ·
          refine ⟨22076090159418277392770891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14717393439612184928513927 22076090159418277392770891)
          ·
            refine ⟨33114135239127416089156337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22076090159418277392770891 33114135239127416089156337)
            ·
              refine ⟨24835601429345562066867253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33114135239127416089156337 24835601429345562066867253)
              ·
                refine ⟨2328337634001146443768805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24835601429345562066867253 2328337634001146443768805)
                ·
                  refine ⟨436563306375214958206651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2328337634001146443768805 436563306375214958206651)
                  ·
                    rfl

theorem cell22_3825918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3825918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825918 prefixEnd_3825918 := by exact prefixLift 3825918
  have htrace : WordTrace (prefixWord ++ tailWord_3825918) baseStart_3825918 baseEnd_3825918 := by
    simpa [prefixWord, tailWord_3825918, baseEnd_3825918] using wordTrace_append hprefix tailTrace_3825918
  have hstable : (prefixWord ++ tailWord_3825918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825918).length < 2 ^ (prefixWord ++ tailWord_3825918).sum := by decide
  have hdescent : baseEnd_3825918 < baseStart_3825918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3825950 : List Nat := [4, 3, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3825950 : Nat := 118140960795 + 3825950 * 2 ^ 59
def prefixEnd_3825950 : Nat := 4983230072969 + 3 ^ 40 * 3825950 * 2
def baseEnd_3825950 : Nat := 1309700873379607457819855

theorem tailTrace_3825950 : CollatzResearch.WordTrace tailWord_3825950 prefixEnd_3825950 1309700873379607457819855 := by
  unfold tailWord_3825950
  simp only [CollatzResearch.WordTrace]
  refine ⟨17442982561155505635458413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 93029240326162696722444869 17442982561155505635458413)
  ·
    refine ⟨6541118460433314613296905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17442982561155505635458413 6541118460433314613296905)
    ·
      refine ⟨4905838845324985959972679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6541118460433314613296905 4905838845324985959972679)
      ·
        refine ⟨7358758267987478939959019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4905838845324985959972679 7358758267987478939959019)
        ·
          refine ⟨11038137401981218409938529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7358758267987478939959019 11038137401981218409938529)
          ·
            refine ⟨8278603051485913807453897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11038137401981218409938529 8278603051485913807453897)
            ·
              refine ⟨6208952288614435355590423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278603051485913807453897 6208952288614435355590423)
              ·
                refine ⟨9313428432921653033385635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6208952288614435355590423 9313428432921653033385635)
                ·
                  refine ⟨13970142649382479550078453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9313428432921653033385635 13970142649382479550078453)
                  ·
                    refine ⟨1309700873379607457819855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13970142649382479550078453 1309700873379607457819855)
                    ·
                      rfl

theorem cell22_3825950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3825950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3825950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3825950 prefixEnd_3825950 := by exact prefixLift 3825950
  have htrace : WordTrace (prefixWord ++ tailWord_3825950) baseStart_3825950 baseEnd_3825950 := by
    simpa [prefixWord, tailWord_3825950, baseEnd_3825950] using wordTrace_append hprefix tailTrace_3825950
  have hstable : (prefixWord ++ tailWord_3825950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3825950).length < 2 ^ (prefixWord ++ tailWord_3825950).sum := by decide
  have hdescent : baseEnd_3825950 < baseStart_3825950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3825950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3826083 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 2, 4]
def baseStart_3826083 : Nat := 118140960795 + 3826083 * 2 ^ 59
def prefixEnd_3826083 : Nat := 4983230072969 + 3 ^ 40 * 3826083 * 2
def baseEnd_3826083 : Nat := 1309746401997639444244447

theorem tailTrace_3826083 : CollatzResearch.WordTrace tailWord_3826083 prefixEnd_3826083 1309746401997639444244447 := by
  unfold tailWord_3826083
  simp only [CollatzResearch.WordTrace]
  refine ⟨139548711397762208798258903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 93032474265174805865505935 139548711397762208798258903)
  ·
    refine ⟨209323067096643313197388355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139548711397762208798258903 209323067096643313197388355)
    ·
      refine ⟨313984600644964969796082533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209323067096643313197388355 313984600644964969796082533)
      ·
        refine ⟨58872112620930931836765475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 313984600644964969796082533 58872112620930931836765475)
        ·
          refine ⟨88308168931396397755148213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58872112620930931836765475 88308168931396397755148213)
          ·
            refine ⟨8278890837318412289545145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88308168931396397755148213 8278890837318412289545145)
            ·
              refine ⟨6209168127988809217158859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8278890837318412289545145 6209168127988809217158859)
              ·
                refine ⟨9313752191983213825738289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6209168127988809217158859 9313752191983213825738289)
                ·
                  refine ⟨6985314143987410369303717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9313752191983213825738289 6985314143987410369303717)
                  ·
                    refine ⟨1309746401997639444244447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6985314143987410369303717 1309746401997639444244447)
                    ·
                      rfl

theorem cell22_3826083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 2, 4].length) (baseStart_3826083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3826083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3826083 prefixEnd_3826083 := by exact prefixLift 3826083
  have htrace : WordTrace (prefixWord ++ tailWord_3826083) baseStart_3826083 baseEnd_3826083 := by
    simpa [prefixWord, tailWord_3826083, baseEnd_3826083] using wordTrace_append hprefix tailTrace_3826083
  have hstable : (prefixWord ++ tailWord_3826083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3826083).length < 2 ^ (prefixWord ++ tailWord_3826083).sum := by decide
  have hdescent : baseEnd_3826083 < baseStart_3826083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3826083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
