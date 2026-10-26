import V185TrunkScan23Chunk0182

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1083732 : List Nat := [2, 4, 1, 1, 2, 2, 11]
def baseStart_1083732 : Nat := 118140960795 + 1083732 * 2 ^ 59
def prefixEnd_1083732 : Nat := 4983230072969 + 3 ^ 40 * 1083732 * 2
def baseEnd_1083732 : Nat := 6870066872326655892173

theorem tailTrace_1083732 : CollatzResearch.WordTrace tailWord_1083732 prefixEnd_1083732 6870066872326655892173 := by
  unfold tailWord_1083732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19763476654915762767602725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26351302206554350356803633 19763476654915762767602725)
  ·
    refine ⟨3705651872796705518925511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19763476654915762767602725 3705651872796705518925511)
    ·
      refine ⟨5558477809195058278388267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3705651872796705518925511 5558477809195058278388267)
      ·
        refine ⟨8337716713792587417582401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5558477809195058278388267 8337716713792587417582401)
        ·
          refine ⟨6253287535344440563186801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8337716713792587417582401 6253287535344440563186801)
          ·
            refine ⟨4689965651508330422390101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6253287535344440563186801 4689965651508330422390101)
            ·
              refine ⟨6870066872326655892173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 4689965651508330422390101 6870066872326655892173)
              ·
                rfl

theorem cell23_1083732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 11].length) (baseStart_1083732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083732 prefixEnd_1083732 := by exact prefixLift 1083732
  have htrace : WordTrace (prefixWord ++ tailWord_1083732) baseStart_1083732 baseEnd_1083732 := by
    simpa [prefixWord, tailWord_1083732, baseEnd_1083732] using wordTrace_append hprefix tailTrace_1083732
  have hstable : (prefixWord ++ tailWord_1083732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083732).length < 2 ^ (prefixWord ++ tailWord_1083732).sum := by decide
  have hdescent : baseEnd_1083732 < baseStart_1083732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083743 : List Nat := [1, 1, 2, 3, 1, 2, 2, 6, 1, 2, 2]
def baseStart_1083743 : Nat := 118140960795 + 1083743 * 2 ^ 59
def prefixEnd_1083743 : Nat := 4983230072969 + 3 ^ 40 * 1083743 * 2
def baseEnd_1083743 : Nat := 556481064945658584228463

theorem tailTrace_1083743 : CollatzResearch.WordTrace tailWord_1083743 prefixEnd_1083743 556481064945658584228463 := by
  unfold tailWord_1083743
  simp only [CollatzResearch.WordTrace]
  refine ⟨39527354512791674413855883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26351569675194449609237255 39527354512791674413855883)
  ·
    refine ⟨59291031769187511620783825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39527354512791674413855883 59291031769187511620783825)
    ·
      refine ⟨44468273826890633715587869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59291031769187511620783825 44468273826890633715587869)
      ·
        refine ⟨16675602685083987643345451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44468273826890633715587869 16675602685083987643345451)
        ·
          refine ⟨25013404027625981465018177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16675602685083987643345451 25013404027625981465018177)
          ·
            refine ⟨18760053020719486098763633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25013404027625981465018177 18760053020719486098763633)
            ·
              refine ⟨14070039765539614574072725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18760053020719486098763633 14070039765539614574072725)
              ·
                refine ⟨659533114009669433159659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14070039765539614574072725 659533114009669433159659)
                ·
                  refine ⟨989299671014504149739489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659533114009669433159659 989299671014504149739489)
                  ·
                    refine ⟨741974753260878112304617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989299671014504149739489 741974753260878112304617)
                    ·
                      refine ⟨556481064945658584228463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 741974753260878112304617 556481064945658584228463)
                      ·
                        rfl

theorem cell23_1083743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_1083743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083743 prefixEnd_1083743 := by exact prefixLift 1083743
  have htrace : WordTrace (prefixWord ++ tailWord_1083743) baseStart_1083743 baseEnd_1083743 := by
    simpa [prefixWord, tailWord_1083743, baseEnd_1083743] using wordTrace_append hprefix tailTrace_1083743
  have hstable : (prefixWord ++ tailWord_1083743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083743).length < 2 ^ (prefixWord ++ tailWord_1083743).sum := by decide
  have hdescent : baseEnd_1083743 < baseStart_1083743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083759 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_1083759 : Nat := 118140960795 + 1083759 * 2 ^ 59
def prefixEnd_1083759 : Nat := 4983230072969 + 3 ^ 40 * 1083759 * 2
def baseEnd_1083759 : Nat := 556489280636130521628389

theorem tailTrace_1083759 : CollatzResearch.WordTrace tailWord_1083759 prefixEnd_1083759 556489280636130521628389 := by
  unfold tailWord_1083759
  simp only [CollatzResearch.WordTrace]
  refine ⟨39527938080733709146438331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26351958720489139430958887 39527938080733709146438331)
  ·
    refine ⟨59291907121100563719657497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39527938080733709146438331 59291907121100563719657497)
    ·
      refine ⟨44468930340825422789743123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59291907121100563719657497 44468930340825422789743123)
      ·
        refine ⟨66703395511238134184614685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44468930340825422789743123 66703395511238134184614685)
        ·
          refine ⟨25013773316714300319230507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66703395511238134184614685 25013773316714300319230507)
          ·
            refine ⟨37520659975071450478845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25013773316714300319230507 37520659975071450478845761)
            ·
              refine ⟨28140494981303587859134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37520659975071450478845761 28140494981303587859134321)
              ·
                refine ⟨21105371235977690894350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28140494981303587859134321 21105371235977690894350741)
                ·
                  refine ⟨989314276686454260672691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21105371235977690894350741 989314276686454260672691)
                  ·
                    refine ⟨1483971415029681391009037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 989314276686454260672691 1483971415029681391009037)
                    ·
                      refine ⟨556489280636130521628389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1483971415029681391009037 556489280636130521628389)
                      ·
                        rfl

theorem cell23_1083759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_1083759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083759 prefixEnd_1083759 := by exact prefixLift 1083759
  have htrace : WordTrace (prefixWord ++ tailWord_1083759) baseStart_1083759 baseEnd_1083759 := by
    simpa [prefixWord, tailWord_1083759, baseEnd_1083759] using wordTrace_append hprefix tailTrace_1083759
  have hstable : (prefixWord ++ tailWord_1083759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083759).length < 2 ^ (prefixWord ++ tailWord_1083759).sum := by decide
  have hdescent : baseEnd_1083759 < baseStart_1083759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083772 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1083772 : Nat := 118140960795 + 1083772 * 2 ^ 59
def prefixEnd_1083772 : Nat := 4983230072969 + 3 ^ 40 * 1083772 * 2
def baseEnd_1083772 : Nat := 556495955884638970765829

theorem tailTrace_1083772 : CollatzResearch.WordTrace tailWord_1083772 prefixEnd_1083772 556495955884638970765829 := by
  unfold tailWord_1083772
  simp only [CollatzResearch.WordTrace]
  refine ⟨19764206114843306183330785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26352274819791074911107713 19764206114843306183330785)
  ·
    refine ⟨14823154586132479637498089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19764206114843306183330785 14823154586132479637498089)
    ·
      refine ⟨11117365939599359728123567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14823154586132479637498089 11117365939599359728123567)
      ·
        refine ⟨16676048909399039592185351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11117365939599359728123567 16676048909399039592185351)
        ·
          refine ⟨25014073364098559388278027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16676048909399039592185351 25014073364098559388278027)
          ·
            refine ⟨37521110046147839082417041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25014073364098559388278027 37521110046147839082417041)
            ·
              refine ⟨28140832534610879311812781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37521110046147839082417041 28140832534610879311812781)
              ·
                refine ⟨10552812200479079741929793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28140832534610879311812781 10552812200479079741929793)
                ·
                  refine ⟨7914609150359309806447345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10552812200479079741929793 7914609150359309806447345)
                  ·
                    refine ⟨5935956862769482354835509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7914609150359309806447345 5935956862769482354835509)
                    ·
                      refine ⟨556495955884638970765829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5935956862769482354835509 556495955884638970765829)
                      ·
                        rfl

theorem cell23_1083772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1083772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083772 prefixEnd_1083772 := by exact prefixLift 1083772
  have htrace : WordTrace (prefixWord ++ tailWord_1083772) baseStart_1083772 baseEnd_1083772 := by
    simpa [prefixWord, tailWord_1083772, baseEnd_1083772] using wordTrace_append hprefix tailTrace_1083772
  have hstable : (prefixWord ++ tailWord_1083772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083772).length < 2 ^ (prefixWord ++ tailWord_1083772).sum := by decide
  have hdescent : baseEnd_1083772 < baseStart_1083772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083832 : List Nat := [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_1083832 : Nat := 118140960795 + 1083832 * 2 ^ 59
def prefixEnd_1083832 : Nat := 4983230072969 + 3 ^ 40 * 1083832 * 2
def baseEnd_1083832 : Nat := 556526764723908736015553

theorem tailTrace_1083832 : CollatzResearch.WordTrace tailWord_1083832 prefixEnd_1083832 556526764723908736015553 := by
  unfold tailWord_1083832
  simp only [CollatzResearch.WordTrace]
  refine ⟨19765300304734621306922875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26353733739646161742563833 19765300304734621306922875)
  ·
    refine ⟨29647950457101931960384313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19765300304734621306922875 29647950457101931960384313)
    ·
      refine ⟨22235962842826448970288235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29647950457101931960384313 22235962842826448970288235)
      ·
        refine ⟨33353944264239673455432353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22235962842826448970288235 33353944264239673455432353)
        ·
          refine ⟨25015458198179755091574265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33353944264239673455432353 25015458198179755091574265)
          ·
            refine ⟨18761593648634816318680699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25015458198179755091574265 18761593648634816318680699)
            ·
              refine ⟨28142390472952224478021049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18761593648634816318680699 28142390472952224478021049)
              ·
                refine ⟨21106792854714168358515787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28142390472952224478021049 21106792854714168358515787)
                ·
                  refine ⟨31660189282071252537773681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21106792854714168358515787 31660189282071252537773681)
                  ·
                    refine ⟨23745141961553439403330261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31660189282071252537773681 23745141961553439403330261)
                    ·
                      refine ⟨556526764723908736015553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23745141961553439403330261 556526764723908736015553)
                      ·
                        rfl

theorem cell23_1083832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_1083832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083832 prefixEnd_1083832 := by exact prefixLift 1083832
  have htrace : WordTrace (prefixWord ++ tailWord_1083832) baseStart_1083832 baseEnd_1083832 := by
    simpa [prefixWord, tailWord_1083832, baseEnd_1083832] using wordTrace_append hprefix tailTrace_1083832
  have hstable : (prefixWord ++ tailWord_1083832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083832).length < 2 ^ (prefixWord ++ tailWord_1083832).sum := by decide
  have hdescent : baseEnd_1083832 < baseStart_1083832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083849 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 3]
def baseStart_1083849 : Nat := 118140960795 + 1083849 * 2 ^ 59
def prefixEnd_1083849 : Nat := 4983230072969 + 3 ^ 40 * 1083849 * 2
def baseEnd_1083849 : Nat := 556535493895035169502975

theorem tailTrace_1083849 : CollatzResearch.WordTrace tailWord_1083849 prefixEnd_1083849 556535493895035169502975 := by
  unfold tailWord_1083849
  simp only [CollatzResearch.WordTrace]
  refine ⟨39531220650407654517214601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26354147100271769678143067 39531220650407654517214601)
  ·
    refine ⟨29648415487805740887910951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39531220650407654517214601 29648415487805740887910951)
    ·
      refine ⟨44472623231708611331866427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29648415487805740887910951 44472623231708611331866427)
      ·
        refine ⟨66708934847562916997799641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44472623231708611331866427 66708934847562916997799641)
        ·
          refine ⟨50031701135672187748349731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66708934847562916997799641 50031701135672187748349731)
          ·
            refine ⟨75047551703508281622524597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50031701135672187748349731 75047551703508281622524597)
            ·
              refine ⟨7035707972203901402111681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75047551703508281622524597 7035707972203901402111681)
              ·
                refine ⟨5276780979152926051583761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7035707972203901402111681 5276780979152926051583761)
                ·
                  refine ⟨3957585734364694538687821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5276780979152926051583761 3957585734364694538687821)
                  ·
                    refine ⟨1484094650386760452007933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3957585734364694538687821 1484094650386760452007933)
                    ·
                      refine ⟨556535493895035169502975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1484094650386760452007933 556535493895035169502975)
                      ·
                        rfl

theorem cell23_1083849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 3, 3].length) (baseStart_1083849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083849 prefixEnd_1083849 := by exact prefixLift 1083849
  have htrace : WordTrace (prefixWord ++ tailWord_1083849) baseStart_1083849 baseEnd_1083849 := by
    simpa [prefixWord, tailWord_1083849, baseEnd_1083849] using wordTrace_append hprefix tailTrace_1083849
  have hstable : (prefixWord ++ tailWord_1083849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083849).length < 2 ^ (prefixWord ++ tailWord_1083849).sum := by decide
  have hdescent : baseEnd_1083849 < baseStart_1083849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083869 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1083869 : Nat := 118140960795 + 1083869 * 2 ^ 59
def prefixEnd_1083869 : Nat := 4983230072969 + 3 ^ 40 * 1083869 * 2
def baseEnd_1083869 : Nat := 185515254502708363750961

theorem tailTrace_1083869 : CollatzResearch.WordTrace tailWord_1083869 prefixEnd_1083869 185515254502708363750961 := by
  unfold tailWord_1083869
  simp only [CollatzResearch.WordTrace]
  refine ⟨39531950110335197932942661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26354633406890131955295107 39531950110335197932942661)
  ·
    refine ⟨7412240645687849612426749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39531950110335197932942661 7412240645687849612426749)
    ·
      refine ⟨2779590242132943604660031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7412240645687849612426749 2779590242132943604660031)
      ·
        refine ⟨4169385363199415406990047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2779590242132943604660031 4169385363199415406990047)
        ·
          refine ⟨6254078044799123110485071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4169385363199415406990047 6254078044799123110485071)
          ·
            refine ⟨9381117067198684665727607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254078044799123110485071 9381117067198684665727607)
            ·
              refine ⟨14071675600798026998591411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9381117067198684665727607 14071675600798026998591411)
              ·
                refine ⟨21107513401197040497887117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14071675600798026998591411 21107513401197040497887117)
                ·
                  refine ⟨7915317525448890186707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21107513401197040497887117 7915317525448890186707669)
                  ·
                    refine ⟨185515254502708363750961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7915317525448890186707669 185515254502708363750961)
                    ·
                      rfl

theorem cell23_1083869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1083869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083869 prefixEnd_1083869 := by exact prefixLift 1083869
  have htrace : WordTrace (prefixWord ++ tailWord_1083869) baseStart_1083869 baseEnd_1083869 := by
    simpa [prefixWord, tailWord_1083869, baseEnd_1083869] using wordTrace_append hprefix tailTrace_1083869
  have hstable : (prefixWord ++ tailWord_1083869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083869).length < 2 ^ (prefixWord ++ tailWord_1083869).sum := by decide
  have hdescent : baseEnd_1083869 < baseStart_1083869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083889 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 4]
def baseStart_1083889 : Nat := 118140960795 + 1083889 * 2 ^ 59
def prefixEnd_1083889 : Nat := 4983230072969 + 3 ^ 40 * 1083889 * 2
def baseEnd_1083889 : Nat := 556556033121215013002791

theorem tailTrace_1083889 : CollatzResearch.WordTrace tailWord_1083889 prefixEnd_1083889 556556033121215013002791 := by
  unfold tailWord_1083889
  simp only [CollatzResearch.WordTrace]
  refine ⟨39532679570262741348670721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26355119713508494232447147 39532679570262741348670721)
  ·
    refine ⟨29649509677697056011503041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39532679570262741348670721 29649509677697056011503041)
    ·
      refine ⟨22237132258272792008627281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29649509677697056011503041 22237132258272792008627281)
      ·
        refine ⟨16677849193704594006470461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22237132258272792008627281 16677849193704594006470461)
        ·
          refine ⟨6254193447639222752426423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16677849193704594006470461 6254193447639222752426423)
          ·
            refine ⟨9381290171458834128639635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6254193447639222752426423 9381290171458834128639635)
            ·
              refine ⟨14071935257188251192959453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9381290171458834128639635 14071935257188251192959453)
              ·
                refine ⟨5276975721445594197359795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14071935257188251192959453 5276975721445594197359795)
                ·
                  refine ⟨7915463582168391296039693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5276975721445594197359795 7915463582168391296039693)
                  ·
                    refine ⟨2968298843313146736014885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7915463582168391296039693 2968298843313146736014885)
                    ·
                      refine ⟨556556033121215013002791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2968298843313146736014885 556556033121215013002791)
                      ·
                        rfl

theorem cell23_1083889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_1083889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083889 prefixEnd_1083889 := by exact prefixLift 1083889
  have htrace : WordTrace (prefixWord ++ tailWord_1083889) baseStart_1083889 baseEnd_1083889 := by
    simpa [prefixWord, tailWord_1083889, baseEnd_1083889] using wordTrace_append hprefix tailTrace_1083889
  have hstable : (prefixWord ++ tailWord_1083889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083889).length < 2 ^ (prefixWord ++ tailWord_1083889).sum := by decide
  have hdescent : baseEnd_1083889 < baseStart_1083889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083890 : List Nat := [3, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_1083890 : Nat := 118140960795 + 1083890 * 2 ^ 59
def prefixEnd_1083890 : Nat := 4983230072969 + 3 ^ 40 * 1083890 * 2
def baseEnd_1083890 : Nat := 61839616289096612121143

theorem tailTrace_1083890 : CollatzResearch.WordTrace tailWord_1083890 prefixEnd_1083890 61839616289096612121143 := by
  unfold tailWord_1083890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9883179010814779629864281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26355144028839412346304749 9883179010814779629864281)
  ·
    refine ⟨7412384258111084722398211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9883179010814779629864281 7412384258111084722398211)
    ·
      refine ⟨11118576387166627083597317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412384258111084722398211 11118576387166627083597317)
      ·
        refine ⟨2084733072593742578174497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11118576387166627083597317 2084733072593742578174497)
        ·
          refine ⟨1563549804445306933630873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2084733072593742578174497 1563549804445306933630873)
          ·
            refine ⟨1172662353333980200223155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1563549804445306933630873 1172662353333980200223155)
            ·
              refine ⟨1758993530000970300334733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172662353333980200223155 1758993530000970300334733)
              ·
                refine ⟨659622573750363862625525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1758993530000970300334733 659622573750363862625525)
                ·
                  refine ⟨61839616289096612121143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 659622573750363862625525 61839616289096612121143)
                  ·
                    rfl

theorem cell23_1083890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_1083890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083890 prefixEnd_1083890 := by exact prefixLift 1083890
  have htrace : WordTrace (prefixWord ++ tailWord_1083890) baseStart_1083890 baseEnd_1083890 := by
    simpa [prefixWord, tailWord_1083890, baseEnd_1083890] using wordTrace_append hprefix tailTrace_1083890
  have hstable : (prefixWord ++ tailWord_1083890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083890).length < 2 ^ (prefixWord ++ tailWord_1083890).sum := by decide
  have hdescent : baseEnd_1083890 < baseStart_1083890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083929 : List Nat := [1, 2, 1, 2, 1, 1, 2, 7, 6]
def baseStart_1083929 : Nat := 118140960795 + 1083929 * 2 ^ 59
def prefixEnd_1083929 : Nat := 4983230072969 + 3 ^ 40 * 1083929 * 2
def baseEnd_1083929 : Nat := 61841841371932761833623

theorem tailTrace_1083929 : CollatzResearch.WordTrace tailWord_1083929 prefixEnd_1083929 61841841371932761833623 := by
  unfold tailWord_1083929
  simp only [CollatzResearch.WordTrace]
  refine ⟨39534138490117828180126841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26356092326745218786751227 39534138490117828180126841)
  ·
    refine ⟨29650603867588371135095131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39534138490117828180126841 29650603867588371135095131)
    ·
      refine ⟨44475905801382556702642697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29650603867588371135095131 44475905801382556702642697)
      ·
        refine ⟨33356929351036917526982023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44475905801382556702642697 33356929351036917526982023)
        ·
          refine ⟨50035394026555376290473035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33356929351036917526982023 50035394026555376290473035)
          ·
            refine ⟨75053091039833064435709553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50035394026555376290473035 75053091039833064435709553)
            ·
              refine ⟨56289818279874798326782165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75053091039833064435709553 56289818279874798326782165)
              ·
                refine ⟨1319292615934565585783957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 56289818279874798326782165 1319292615934565585783957)
                ·
                  refine ⟨61841841371932761833623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1319292615934565585783957 61841841371932761833623)
                  ·
                    rfl

theorem cell23_1083929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 6].length) (baseStart_1083929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083929 prefixEnd_1083929 := by exact prefixLift 1083929
  have htrace : WordTrace (prefixWord ++ tailWord_1083929) baseStart_1083929 baseEnd_1083929 := by
    simpa [prefixWord, tailWord_1083929, baseEnd_1083929] using wordTrace_append hprefix tailTrace_1083929
  have hstable : (prefixWord ++ tailWord_1083929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083929).length < 2 ^ (prefixWord ++ tailWord_1083929).sum := by decide
  have hdescent : baseEnd_1083929 < baseStart_1083929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1083940 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1083940 : Nat := 118140960795 + 1083940 * 2 ^ 59
def prefixEnd_1083940 : Nat := 4983230072969 + 3 ^ 40 * 1083940 * 2
def baseEnd_1083940 : Nat := 556582220634594313465057

theorem tailTrace_1083940 : CollatzResearch.WordTrace tailWord_1083940 prefixEnd_1083940 556582220634594313465057 := by
  unfold tailWord_1083940
  simp only [CollatzResearch.WordTrace]
  refine ⟨19767269846538988529388637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26356359795385318039184849 19767269846538988529388637)
  ·
    refine ⟨7412726192452120698520739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19767269846538988529388637 7412726192452120698520739)
    ·
      refine ⟨11119089288678181047781109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7412726192452120698520739 11119089288678181047781109)
      ·
        refine ⟨1042414620813579473229479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11119089288678181047781109 1042414620813579473229479)
        ·
          refine ⟨1563621931220369209844219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1042414620813579473229479 1563621931220369209844219)
          ·
            refine ⟨2345432896830553814766329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1563621931220369209844219 2345432896830553814766329)
            ·
              refine ⟨1759074672622915361074747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2345432896830553814766329 1759074672622915361074747)
              ·
                refine ⟨2638612008934373041612121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759074672622915361074747 2638612008934373041612121)
                ·
                  refine ⟨1978959006700779781209091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2638612008934373041612121 1978959006700779781209091)
                  ·
                    refine ⟨2968438510051169671813637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1978959006700779781209091 2968438510051169671813637)
                    ·
                      refine ⟨556582220634594313465057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2968438510051169671813637 556582220634594313465057)
                      ·
                        rfl

theorem cell23_1083940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1083940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1083940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1083940 prefixEnd_1083940 := by exact prefixLift 1083940
  have htrace : WordTrace (prefixWord ++ tailWord_1083940) baseStart_1083940 baseEnd_1083940 := by
    simpa [prefixWord, tailWord_1083940, baseEnd_1083940] using wordTrace_append hprefix tailTrace_1083940
  have hstable : (prefixWord ++ tailWord_1083940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1083940).length < 2 ^ (prefixWord ++ tailWord_1083940).sum := by decide
  have hdescent : baseEnd_1083940 < baseStart_1083940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1083940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084009 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 6]
def baseStart_1084009 : Nat := 118140960795 + 1084009 * 2 ^ 59
def prefixEnd_1084009 : Nat := 4983230072969 + 3 ^ 40 * 1084009 * 2
def baseEnd_1084009 : Nat := 556617650799754543502239

theorem tailTrace_1084009 : CollatzResearch.WordTrace tailWord_1084009 prefixEnd_1084009 556617650799754543502239 := by
  unfold tailWord_1084009
  simp only [CollatzResearch.WordTrace]
  refine ⟨39537056329828001843039081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26358037553218667895359387 39537056329828001843039081)
  ·
    refine ⟨29652792247371001382279311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39537056329828001843039081 29652792247371001382279311)
    ·
      refine ⟨44479188371056502073418967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29652792247371001382279311 44479188371056502073418967)
      ·
        refine ⟨66718782556584753110128451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44479188371056502073418967 66718782556584753110128451)
        ·
          refine ⟨100078173834877129665192677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66718782556584753110128451 100078173834877129665192677)
          ·
            refine ⟨18764657594039461812223627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100078173834877129665192677 18764657594039461812223627)
            ·
              refine ⟨28146986391059192718335441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18764657594039461812223627 28146986391059192718335441)
              ·
                refine ⟨21110239793294394538751581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28146986391059192718335441 21110239793294394538751581)
                ·
                  refine ⟨7916339922485397952031843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21110239793294394538751581 7916339922485397952031843)
                  ·
                    refine ⟨11874509883728096928047765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7916339922485397952031843 11874509883728096928047765)
                    ·
                      refine ⟨556617650799754543502239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11874509883728096928047765 556617650799754543502239)
                      ·
                        rfl

theorem cell23_1084009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 1, 6].length) (baseStart_1084009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084009 prefixEnd_1084009 := by exact prefixLift 1084009
  have htrace : WordTrace (prefixWord ++ tailWord_1084009) baseStart_1084009 baseEnd_1084009 := by
    simpa [prefixWord, tailWord_1084009, baseEnd_1084009] using wordTrace_append hprefix tailTrace_1084009
  have hstable : (prefixWord ++ tailWord_1084009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084009).length < 2 ^ (prefixWord ++ tailWord_1084009).sum := by decide
  have hdescent : baseEnd_1084009 < baseStart_1084009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084023 : List Nat := [1, 1, 3, 1, 1, 3, 5, 2, 2, 4]
def baseStart_1084023 : Nat := 118140960795 + 1084023 * 2 ^ 59
def prefixEnd_1084023 : Nat := 4983230072969 + 3 ^ 40 * 1084023 * 2
def baseEnd_1084023 : Nat := 185541613176305829575725

theorem tailTrace_1084023 : CollatzResearch.WordTrace tailWord_1084023 prefixEnd_1084023 185541613176305829575725 := by
  unfold tailWord_1084023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39537566951777282234048723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26358377967851521489365815 39537566951777282234048723)
  ·
    refine ⟨59306350427665923351073085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39537566951777282234048723 59306350427665923351073085)
    ·
      refine ⟨22239881410374721256652407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59306350427665923351073085 22239881410374721256652407)
      ·
        refine ⟨33359822115562081884978611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22239881410374721256652407 33359822115562081884978611)
        ·
          refine ⟨50039733173343122827467917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33359822115562081884978611 50039733173343122827467917)
          ·
            refine ⟨18764899940003671060300469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50039733173343122827467917 18764899940003671060300469)
            ·
              refine ⟨1759209369375344161903169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18764899940003671060300469 1759209369375344161903169)
              ·
                refine ⟨1319407027031508121427377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1759209369375344161903169 1319407027031508121427377)
                ·
                  refine ⟨989555270273631091070533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1319407027031508121427377 989555270273631091070533)
                  ·
                    refine ⟨185541613176305829575725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989555270273631091070533 185541613176305829575725)
                    ·
                      rfl

theorem cell23_1084023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_1084023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084023 prefixEnd_1084023 := by exact prefixLift 1084023
  have htrace : WordTrace (prefixWord ++ tailWord_1084023) baseStart_1084023 baseEnd_1084023 := by
    simpa [prefixWord, tailWord_1084023, baseEnd_1084023] using wordTrace_append hprefix tailTrace_1084023
  have hstable : (prefixWord ++ tailWord_1084023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084023).length < 2 ^ (prefixWord ++ tailWord_1084023).sum := by decide
  have hdescent : baseEnd_1084023 < baseStart_1084023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084049 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 9]
def baseStart_1084049 : Nat := 118140960795 + 1084049 * 2 ^ 59
def prefixEnd_1084049 : Nat := 4983230072969 + 3 ^ 40 * 1084049 * 2
def baseEnd_1084049 : Nat := 185546063341978129000685

theorem tailTrace_1084049 : CollatzResearch.WordTrace tailWord_1084049 prefixEnd_1084049 185546063341978129000685 := by
  unfold tailWord_1084049
  simp only [CollatzResearch.WordTrace]
  refine ⟨39538515249683088674495201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26359010166455392449663467 39538515249683088674495201)
  ·
    refine ⟨29653886437262316505871401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39538515249683088674495201 29653886437262316505871401)
    ·
      refine ⟨22240414827946737379403551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29653886437262316505871401 22240414827946737379403551)
      ·
        refine ⟨33360622241920106069105327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22240414827946737379403551 33360622241920106069105327)
        ·
          refine ⟨50040933362880159103657991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33360622241920106069105327 50040933362880159103657991)
          ·
            refine ⟨75061400044320238655486987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50040933362880159103657991 75061400044320238655486987)
            ·
              refine ⟨112592100066480357983230481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75061400044320238655486987 112592100066480357983230481)
              ·
                refine ⟨84444075049860268487422861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112592100066480357983230481 84444075049860268487422861)
                ·
                  refine ⟨31666528143697600682783573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84444075049860268487422861 31666528143697600682783573)
                  ·
                    refine ⟨185546063341978129000685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31666528143697600682783573 185546063341978129000685)
                    ·
                      rfl

theorem cell23_1084049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_1084049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084049 prefixEnd_1084049 := by exact prefixLift 1084049
  have htrace : WordTrace (prefixWord ++ tailWord_1084049) baseStart_1084049 baseEnd_1084049 := by
    simpa [prefixWord, tailWord_1084049, baseEnd_1084049] using wordTrace_append hprefix tailTrace_1084049
  have hstable : (prefixWord ++ tailWord_1084049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084049).length < 2 ^ (prefixWord ++ tailWord_1084049).sum := by decide
  have hdescent : baseEnd_1084049 < baseStart_1084049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084050 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_1084050 : Nat := 118140960795 + 1084050 * 2 ^ 59
def prefixEnd_1084050 : Nat := 4983230072969 + 3 ^ 40 * 1084050 * 2
def baseEnd_1084050 : Nat := 556638703506588883089551

theorem tailTrace_1084050 : CollatzResearch.WordTrace tailWord_1084050 prefixEnd_1084050 556638703506588883089551 := by
  unfold tailWord_1084050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9884637930669866461320401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26359034481786310563521069 9884637930669866461320401)
  ·
    refine ⟨7413478448002399845990301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9884637930669866461320401 7413478448002399845990301)
    ·
      refine ⟨2780054418000899942246363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7413478448002399845990301 2780054418000899942246363)
      ·
        refine ⟨4170081627001349913369545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780054418000899942246363 4170081627001349913369545)
        ·
          refine ⟨3127561220251012435027159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4170081627001349913369545 3127561220251012435027159)
          ·
            refine ⟨4691341830376518652540739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3127561220251012435027159 4691341830376518652540739)
            ·
              refine ⟨7037012745564777978811109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4691341830376518652540739 7037012745564777978811109)
              ·
                refine ⟨1319439889793395871027083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7037012745564777978811109 1319439889793395871027083)
                ·
                  refine ⟨1979159834690093806540625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319439889793395871027083 1979159834690093806540625)
                  ·
                    refine ⟨1484369876017570354905469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979159834690093806540625 1484369876017570354905469)
                    ·
                      refine ⟨556638703506588883089551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1484369876017570354905469 556638703506588883089551)
                      ·
                        rfl

theorem cell23_1084050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_1084050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084050 prefixEnd_1084050 := by exact prefixLift 1084050
  have htrace : WordTrace (prefixWord ++ tailWord_1084050) baseStart_1084050 baseEnd_1084050 := by
    simpa [prefixWord, tailWord_1084050, baseEnd_1084050] using wordTrace_append hprefix tailTrace_1084050
  have hstable : (prefixWord ++ tailWord_1084050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084050).length < 2 ^ (prefixWord ++ tailWord_1084050).sum := by decide
  have hdescent : baseEnd_1084050 < baseStart_1084050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084081 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1084081 : Nat := 118140960795 + 1084081 * 2 ^ 59
def prefixEnd_1084081 : Nat := 4983230072969 + 3 ^ 40 * 1084081 * 2
def baseEnd_1084081 : Nat := 556654621406878261801909

theorem tailTrace_1084081 : CollatzResearch.WordTrace tailWord_1084081 prefixEnd_1084081 556654621406878261801909 := by
  unfold tailWord_1084081
  simp only [CollatzResearch.WordTrace]
  refine ⟨39539682385567158139660097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26359788257044772093106731 39539682385567158139660097)
  ·
    refine ⟨29654761789175368604745073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39539682385567158139660097 29654761789175368604745073)
    ·
      refine ⟨22241071341881526453558805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29654761789175368604745073 22241071341881526453558805)
      ·
        refine ⟨1042550219150696552510569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22241071341881526453558805 1042550219150696552510569)
        ·
          refine ⟨781912664363022414382927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042550219150696552510569 781912664363022414382927)
          ·
            refine ⟨1172868996544533621574391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 781912664363022414382927 1172868996544533621574391)
            ·
              refine ⟨1759303494816800432361587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1172868996544533621574391 1759303494816800432361587)
              ·
                refine ⟨2638955242225200648542381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759303494816800432361587 2638955242225200648542381)
                ·
                  refine ⟨989608215834450243203393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2638955242225200648542381 989608215834450243203393)
                  ·
                    refine ⟨742206161875837682402545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989608215834450243203393 742206161875837682402545)
                    ·
                      refine ⟨556654621406878261801909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742206161875837682402545 556654621406878261801909)
                      ·
                        rfl

theorem cell23_1084081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1084081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084081 prefixEnd_1084081 := by exact prefixLift 1084081
  have htrace : WordTrace (prefixWord ++ tailWord_1084081) baseStart_1084081 baseEnd_1084081 := by
    simpa [prefixWord, tailWord_1084081, baseEnd_1084081] using wordTrace_append hprefix tailTrace_1084081
  have hstable : (prefixWord ++ tailWord_1084081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084081).length < 2 ^ (prefixWord ++ tailWord_1084081).sum := by decide
  have hdescent : baseEnd_1084081 < baseStart_1084081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084120 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2]
def baseStart_1084120 : Nat := 118140960795 + 1084120 * 2 ^ 59
def prefixEnd_1084120 : Nat := 4983230072969 + 3 ^ 40 * 1084120 * 2
def baseEnd_1084120 : Nat := 556674647152403609214229

theorem tailTrace_1084120 : CollatzResearch.WordTrace tailWord_1084120 prefixEnd_1084120 556674647152403609214229 := by
  unfold tailWord_1084120
  simp only [CollatzResearch.WordTrace]
  refine ⟨19770552416212933900164907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26360736554950578533553209 19770552416212933900164907)
  ·
    refine ⟨29655828624319400850247361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19770552416212933900164907 29655828624319400850247361)
    ·
      refine ⟨22241871468239550637685521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29655828624319400850247361 22241871468239550637685521)
      ·
        refine ⟨16681403601179662978264141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22241871468239550637685521 16681403601179662978264141)
        ·
          refine ⟨6255526350442373616849053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16681403601179662978264141 6255526350442373616849053)
          ·
            refine ⟨2345822381415890106318395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6255526350442373616849053 2345822381415890106318395)
            ·
              refine ⟨3518733572123835159477593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2345822381415890106318395 3518733572123835159477593)
              ·
                refine ⟨2639050179092876369608195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3518733572123835159477593 2639050179092876369608195)
                ·
                  refine ⟨3958575268639314554412293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639050179092876369608195 3958575268639314554412293)
                  ·
                    refine ⟨742232862869871478952305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958575268639314554412293 742232862869871478952305)
                    ·
                      refine ⟨556674647152403609214229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742232862869871478952305 556674647152403609214229)
                      ·
                        rfl

theorem cell23_1084120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_1084120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084120 prefixEnd_1084120 := by exact prefixLift 1084120
  have htrace : WordTrace (prefixWord ++ tailWord_1084120) baseStart_1084120 baseEnd_1084120 := by
    simpa [prefixWord, tailWord_1084120, baseEnd_1084120] using wordTrace_append hprefix tailTrace_1084120
  have hstable : (prefixWord ++ tailWord_1084120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084120).length < 2 ^ (prefixWord ++ tailWord_1084120).sum := by decide
  have hdescent : baseEnd_1084120 < baseStart_1084120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084163 : List Nat := [1, 1, 1, 3, 2, 2, 1, 1, 4, 5, 2]
def baseStart_1084163 : Nat := 118140960795 + 1084163 * 2 ^ 59
def prefixEnd_1084163 : Nat := 4983230072969 + 3 ^ 40 * 1084163 * 2
def baseEnd_1084163 : Nat := 556696726820546940976531

theorem tailTrace_1084163 : CollatzResearch.WordTrace tailWord_1084163 prefixEnd_1084163 556696726820546940976531 := by
  unfold tailWord_1084163
  simp only [CollatzResearch.WordTrace]
  refine ⟨39542673171270086144145143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26361782114180057429430095 39542673171270086144145143)
  ·
    refine ⟨59314009756905129216217715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39542673171270086144145143 59314009756905129216217715)
    ·
      refine ⟨88971014635357693824326573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59314009756905129216217715 88971014635357693824326573)
      ·
        refine ⟨33364130488259135184122465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88971014635357693824326573 33364130488259135184122465)
        ·
          refine ⟨25023097866194351388091849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33364130488259135184122465 25023097866194351388091849)
          ·
            refine ⟨18767323399645763541068887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25023097866194351388091849 18767323399645763541068887)
            ·
              refine ⟨28150985099468645311603331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18767323399645763541068887 28150985099468645311603331)
              ·
                refine ⟨42226477649202967967404997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28150985099468645311603331 42226477649202967967404997)
                ·
                  refine ⟨7917464559225556493888437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42226477649202967967404997 7917464559225556493888437)
                  ·
                    refine ⟨742262302427395921302041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7917464559225556493888437 742262302427395921302041)
                    ·
                      refine ⟨556696726820546940976531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742262302427395921302041 556696726820546940976531)
                      ·
                        rfl

theorem cell23_1084163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_1084163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084163 prefixEnd_1084163 := by exact prefixLift 1084163
  have htrace : WordTrace (prefixWord ++ tailWord_1084163) baseStart_1084163 baseEnd_1084163 := by
    simpa [prefixWord, tailWord_1084163, baseEnd_1084163] using wordTrace_append hprefix tailTrace_1084163
  have hstable : (prefixWord ++ tailWord_1084163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084163).length < 2 ^ (prefixWord ++ tailWord_1084163).sum := by decide
  have hdescent : baseEnd_1084163 < baseStart_1084163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084193 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 4]
def baseStart_1084193 : Nat := 118140960795 + 1084193 * 2 ^ 59
def prefixEnd_1084193 : Nat := 4983230072969 + 3 ^ 40 * 1084193 * 2
def baseEnd_1084193 : Nat := 556712131240181823601393

theorem tailTrace_1084193 : CollatzResearch.WordTrace tailWord_1084193 prefixEnd_1084193 556712131240181823601393 := by
  unfold tailWord_1084193
  simp only [CollatzResearch.WordTrace]
  refine ⟨39543767361161401267737233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26362511574107600845158155 39543767361161401267737233)
  ·
    refine ⟨29657825520871050950802925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39543767361161401267737233 29657825520871050950802925)
    ·
      refine ⟨11121684570326644106551097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29657825520871050950802925 11121684570326644106551097)
      ·
        refine ⟨8341263427744983079913323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11121684570326644106551097 8341263427744983079913323)
        ·
          refine ⟨12511895141617474619869985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8341263427744983079913323 12511895141617474619869985)
          ·
            refine ⟨9383921356213105964902489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12511895141617474619869985 9383921356213105964902489)
            ·
              refine ⟨7037941017159829473676867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9383921356213105964902489 7037941017159829473676867)
              ·
                refine ⟨10556911525739744210515301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7037941017159829473676867 10556911525739744210515301)
                ·
                  refine ⟨1979420911076202039471619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10556911525739744210515301 1979420911076202039471619)
                  ·
                    refine ⟨2969131366614303059207429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979420911076202039471619 2969131366614303059207429)
                    ·
                      refine ⟨556712131240181823601393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2969131366614303059207429 556712131240181823601393)
                      ·
                        rfl

theorem cell23_1084193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_1084193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084193 prefixEnd_1084193 := by exact prefixLift 1084193
  have htrace : WordTrace (prefixWord ++ tailWord_1084193) baseStart_1084193 baseEnd_1084193 := by
    simpa [prefixWord, tailWord_1084193, baseEnd_1084193] using wordTrace_append hprefix tailTrace_1084193
  have hstable : (prefixWord ++ tailWord_1084193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084193).length < 2 ^ (prefixWord ++ tailWord_1084193).sum := by decide
  have hdescent : baseEnd_1084193 < baseStart_1084193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084203 : List Nat := [1, 1, 1, 1, 2, 1, 2, 7, 3, 4]
def baseStart_1084203 : Nat := 118140960795 + 1084203 * 2 ^ 59
def prefixEnd_1084203 : Nat := 4983230072969 + 3 ^ 40 * 1084203 * 2
def baseEnd_1084203 : Nat := 185572422015575594825449

theorem tailTrace_1084203 : CollatzResearch.WordTrace tailWord_1084203 prefixEnd_1084203 185572422015575594825449 := by
  unfold tailWord_1084203
  simp only [CollatzResearch.WordTrace]
  refine ⟨39544132091125172975601263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26362754727416781983734175 39544132091125172975601263)
  ·
    refine ⟨59316198136687759463401895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39544132091125172975601263 59316198136687759463401895)
    ·
      refine ⟨88974297205031639195102843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59316198136687759463401895 88974297205031639195102843)
      ·
        refine ⟨133461445807547458792654265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88974297205031639195102843 133461445807547458792654265)
        ·
          refine ⟨100096084355660594094490699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133461445807547458792654265 100096084355660594094490699)
          ·
            refine ⟨150144126533490891141736049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100096084355660594094490699 150144126533490891141736049)
            ·
              refine ⟨112608094900118168356302037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150144126533490891141736049 112608094900118168356302037)
              ·
                refine ⟨2639252224221519570850829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112608094900118168356302037 2639252224221519570850829)
                ·
                  refine ⟨989719584083069839069061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2639252224221519570850829 989719584083069839069061)
                  ·
                    refine ⟨185572422015575594825449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 989719584083069839069061 185572422015575594825449)
                    ·
                      rfl

theorem cell23_1084203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 4].length) (baseStart_1084203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084203 prefixEnd_1084203 := by exact prefixLift 1084203
  have htrace : WordTrace (prefixWord ++ tailWord_1084203) baseStart_1084203 baseEnd_1084203 := by
    simpa [prefixWord, tailWord_1084203, baseEnd_1084203] using wordTrace_append hprefix tailTrace_1084203
  have hstable : (prefixWord ++ tailWord_1084203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084203).length < 2 ^ (prefixWord ++ tailWord_1084203).sum := by decide
  have hdescent : baseEnd_1084203 < baseStart_1084203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084210 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_1084210 : Nat := 118140960795 + 1084210 * 2 ^ 59
def prefixEnd_1084210 : Nat := 4983230072969 + 3 ^ 40 * 1084210 * 2
def baseEnd_1084210 : Nat := 556720860411308257088815

theorem tailTrace_1084210 : CollatzResearch.WordTrace tailWord_1084210 prefixEnd_1084210 556720860411308257088815 := by
  unfold tailWord_1084210
  simp only [CollatzResearch.WordTrace]
  refine ⟨9886096850524953292776521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26362924934733208780737389 9886096850524953292776521)
  ·
    refine ⟨7414572637893714969582391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9886096850524953292776521 7414572637893714969582391)
    ·
      refine ⟨11121858956840572454373587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7414572637893714969582391 11121858956840572454373587)
      ·
        refine ⟨16682788435260858681560381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11121858956840572454373587 16682788435260858681560381)
        ·
          refine ⟨6256045663222822005585143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16682788435260858681560381 6256045663222822005585143)
          ·
            refine ⟨9384068494834233008377715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6256045663222822005585143 9384068494834233008377715)
            ·
              refine ⟨14076102742251349512566573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9384068494834233008377715 14076102742251349512566573)
              ·
                refine ⟨5278538528344256067212465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14076102742251349512566573 5278538528344256067212465)
                ·
                  refine ⟨3958903896258192050409349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5278538528344256067212465 3958903896258192050409349)
                  ·
                    refine ⟨742294480548411009451753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3958903896258192050409349 742294480548411009451753)
                    ·
                      refine ⟨556720860411308257088815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742294480548411009451753 556720860411308257088815)
                      ·
                        rfl

theorem cell23_1084210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_1084210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084210 prefixEnd_1084210 := by exact prefixLift 1084210
  have htrace : WordTrace (prefixWord ++ tailWord_1084210) baseStart_1084210 baseEnd_1084210 := by
    simpa [prefixWord, tailWord_1084210, baseEnd_1084210] using wordTrace_append hprefix tailTrace_1084210
  have hstable : (prefixWord ++ tailWord_1084210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084210).length < 2 ^ (prefixWord ++ tailWord_1084210).sum := by decide
  have hdescent : baseEnd_1084210 < baseStart_1084210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084293 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_1084293 : Nat := 118140960795 + 1084293 * 2 ^ 59
def prefixEnd_1084293 : Nat := 4983230072969 + 3 ^ 40 * 1084293 * 2
def baseEnd_1084293 : Nat := 185587826435210477450311

theorem tailTrace_1084293 : CollatzResearch.WordTrace tailWord_1084293 prefixEnd_1084293 185587826435210477450311 := by
  unfold tailWord_1084293
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547414660799118346377533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26364943107199412230918355 39547414660799118346377533)
  ·
    refine ⟨14830280497799669379891575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39547414660799118346377533 14830280497799669379891575)
    ·
      refine ⟨22245420746699504069837363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14830280497799669379891575 22245420746699504069837363)
      ·
        refine ⟨33368131120049256104756045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22245420746699504069837363 33368131120049256104756045)
        ·
          refine ⟨12513049170018471039283517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33368131120049256104756045 12513049170018471039283517)
          ·
            refine ⟨4692393438756926639731319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12513049170018471039283517 4692393438756926639731319)
            ·
              refine ⟨7038590158135389959596979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692393438756926639731319 7038590158135389959596979)
              ·
                refine ⟨10557885237203084939395469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7038590158135389959596979 10557885237203084939395469)
                ·
                  refine ⟨3959206963951156852273301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10557885237203084939395469 3959206963951156852273301)
                  ·
                    refine ⟨185587826435210477450311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3959206963951156852273301 185587826435210477450311)
                    ·
                      rfl

theorem cell23_1084293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_1084293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084293 prefixEnd_1084293 := by exact prefixLift 1084293
  have htrace : WordTrace (prefixWord ++ tailWord_1084293) baseStart_1084293 baseEnd_1084293 := by
    simpa [prefixWord, tailWord_1084293, baseEnd_1084293] using wordTrace_append hprefix tailTrace_1084293
  have hstable : (prefixWord ++ tailWord_1084293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084293).length < 2 ^ (prefixWord ++ tailWord_1084293).sum := by decide
  have hdescent : baseEnd_1084293 < baseStart_1084293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084297 : List Nat := [1, 2, 1, 1, 5, 3, 3, 1, 1, 5]
def baseStart_1084297 : Nat := 118140960795 + 1084297 * 2 ^ 59
def prefixEnd_1084297 : Nat := 4983230072969 + 3 ^ 40 * 1084297 * 2
def baseEnd_1084297 : Nat := 185588511076083138900305

theorem tailTrace_1084297 : CollatzResearch.WordTrace tailWord_1084297 prefixEnd_1084297 185588511076083138900305 := by
  unfold tailWord_1084297
  simp only [CollatzResearch.WordTrace]
  refine ⟨39547560552784627029523145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26365040368523084686348763 39547560552784627029523145)
  ·
    refine ⟨29660670414588470272142359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39547560552784627029523145 29660670414588470272142359)
    ·
      refine ⟨44491005621882705408213539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29660670414588470272142359 44491005621882705408213539)
      ·
        refine ⟨66736508432824058112320309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44491005621882705408213539 66736508432824058112320309)
        ·
          refine ⟨6256547665577255448030029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66736508432824058112320309 6256547665577255448030029)
          ·
            refine ⟨2346205374591470793011261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6256547665577255448030029 2346205374591470793011261)
            ·
              refine ⟨879827015471801547379223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2346205374591470793011261 879827015471801547379223)
              ·
                refine ⟨1319740523207702321068835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879827015471801547379223 1319740523207702321068835)
                ·
                  refine ⟨1979610784811553481603253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319740523207702321068835 1979610784811553481603253)
                  ·
                    refine ⟨185588511076083138900305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1979610784811553481603253 185588511076083138900305)
                    ·
                      rfl

theorem cell23_1084297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 1, 1, 5].length) (baseStart_1084297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084297 prefixEnd_1084297 := by exact prefixLift 1084297
  have htrace : WordTrace (prefixWord ++ tailWord_1084297) baseStart_1084297 baseEnd_1084297 := by
    simpa [prefixWord, tailWord_1084297, baseEnd_1084297] using wordTrace_append hprefix tailTrace_1084297
  have hstable : (prefixWord ++ tailWord_1084297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084297).length < 2 ^ (prefixWord ++ tailWord_1084297).sum := by decide
  have hdescent : baseEnd_1084297 < baseStart_1084297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084300 : List Nat := [2, 2, 1, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_1084300 : Nat := 118140960795 + 1084300 * 2 ^ 59
def prefixEnd_1084300 : Nat := 4983230072969 + 3 ^ 40 * 1084300 * 2
def baseEnd_1084300 : Nat := 556767073670212904963401

theorem tailTrace_1084300 : CollatzResearch.WordTrace tailWord_1084300 prefixEnd_1084300 556767073670212904963401 := by
  unfold tailWord_1084300
  simp only [CollatzResearch.WordTrace]
  refine ⟨19773834985886879270941177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26365113314515839027921569 19773834985886879270941177)
  ·
    refine ⟨14830376239415159453205883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19773834985886879270941177 14830376239415159453205883)
    ·
      refine ⟨22245564359122739179808825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14830376239415159453205883 22245564359122739179808825)
      ·
        refine ⟨16684173269342054384856619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22245564359122739179808825 16684173269342054384856619)
        ·
          refine ⟨25026259904013081577284929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16684173269342054384856619 25026259904013081577284929)
          ·
            refine ⟨18769694928009811182963697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25026259904013081577284929 18769694928009811182963697)
            ·
              refine ⟨14077271196007358387222773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18769694928009811182963697 14077271196007358387222773)
              ·
                refine ⟨1319744174625689848802135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14077271196007358387222773 1319744174625689848802135)
                ·
                  refine ⟨1979616261938534773203203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319744174625689848802135 1979616261938534773203203)
                  ·
                    refine ⟨2969424392907802159804805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1979616261938534773203203 2969424392907802159804805)
                    ·
                      refine ⟨556767073670212904963401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2969424392907802159804805 556767073670212904963401)
                      ·
                        rfl

theorem cell23_1084300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_1084300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084300 prefixEnd_1084300 := by exact prefixLift 1084300
  have htrace : WordTrace (prefixWord ++ tailWord_1084300) baseStart_1084300 baseEnd_1084300 := by
    simpa [prefixWord, tailWord_1084300, baseEnd_1084300] using wordTrace_append hprefix tailTrace_1084300
  have hstable : (prefixWord ++ tailWord_1084300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084300).length < 2 ^ (prefixWord ++ tailWord_1084300).sum := by decide
  have hdescent : baseEnd_1084300 < baseStart_1084300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084313 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 4]
def baseStart_1084313 : Nat := 118140960795 + 1084313 * 2 ^ 59
def prefixEnd_1084313 : Nat := 4983230072969 + 3 ^ 40 * 1084313 * 2
def baseEnd_1084313 : Nat := 556773748918721354100841

theorem tailTrace_1084313 : CollatzResearch.WordTrace tailWord_1084313 prefixEnd_1084313 556773748918721354100841 := by
  unfold tailWord_1084313
  simp only [CollatzResearch.WordTrace]
  refine ⟨39548144120726661762105593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26365429413817774508070395 39548144120726661762105593)
  ·
    refine ⟨29661108090544996321579195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39548144120726661762105593 29661108090544996321579195)
    ·
      refine ⟨44491662135817494482368793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29661108090544996321579195 44491662135817494482368793)
      ·
        refine ⟨33368746601863120861776595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44491662135817494482368793 33368746601863120861776595)
        ·
          refine ⟨50053119902794681292664893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33368746601863120861776595 50053119902794681292664893)
          ·
            refine ⟨18769919963548005484749335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50053119902794681292664893 18769919963548005484749335)
            ·
              refine ⟨28154879945322008227124003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18769919963548005484749335 28154879945322008227124003)
              ·
                refine ⟨42232319917983012340686005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28154879945322008227124003 42232319917983012340686005)
                ·
                  refine ⟨3959279992310907406939313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42232319917983012340686005 3959279992310907406939313)
                  ·
                    refine ⟨2969459994233180555204485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3959279992310907406939313 2969459994233180555204485)
                    ·
                      refine ⟨556773748918721354100841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2969459994233180555204485 556773748918721354100841)
                      ·
                        rfl

theorem cell23_1084313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_1084313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084313 prefixEnd_1084313 := by exact prefixLift 1084313
  have htrace : WordTrace (prefixWord ++ tailWord_1084313) baseStart_1084313 baseEnd_1084313 := by
    simpa [prefixWord, tailWord_1084313, baseEnd_1084313] using wordTrace_append hprefix tailTrace_1084313
  have hstable : (prefixWord ++ tailWord_1084313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084313).length < 2 ^ (prefixWord ++ tailWord_1084313).sum := by decide
  have hdescent : baseEnd_1084313 < baseStart_1084313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084320 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3]
def baseStart_1084320 : Nat := 118140960795 + 1084320 * 2 ^ 59
def prefixEnd_1084320 : Nat := 4983230072969 + 3 ^ 40 * 1084320 * 2
def baseEnd_1084320 : Nat := 556777343283302826713309

theorem tailTrace_1084320 : CollatzResearch.WordTrace tailWord_1084320 prefixEnd_1084320 556777343283302826713309 := by
  unfold tailWord_1084320
  simp only [CollatzResearch.WordTrace]
  refine ⟨19774199715850650978805207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26365599621134201305073609 19774199715850650978805207)
  ·
    refine ⟨29661299573775976468207811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19774199715850650978805207 29661299573775976468207811)
    ·
      refine ⟨44491949360663964702311717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29661299573775976468207811 44491949360663964702311717)
      ·
        refine ⟨8342240505124493381683447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44491949360663964702311717 8342240505124493381683447)
        ·
          refine ⟨12513360757686740072525171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8342240505124493381683447 12513360757686740072525171)
          ·
            refine ⟨18770041136530110108787757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12513360757686740072525171 18770041136530110108787757)
            ·
              refine ⟨7038765426198791290795409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18770041136530110108787757 7038765426198791290795409)
              ·
                refine ⟨5279074069649093468096557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7038765426198791290795409 5279074069649093468096557)
                ·
                  refine ⟨1979652776118410050536209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5279074069649093468096557 1979652776118410050536209)
                  ·
                    refine ⟨1484739582088807537902157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1979652776118410050536209 1484739582088807537902157)
                    ·
                      refine ⟨556777343283302826713309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1484739582088807537902157 556777343283302826713309)
                      ·
                        rfl

theorem cell23_1084320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_1084320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084320 prefixEnd_1084320 := by exact prefixLift 1084320
  have htrace : WordTrace (prefixWord ++ tailWord_1084320) baseStart_1084320 baseEnd_1084320 := by
    simpa [prefixWord, tailWord_1084320, baseEnd_1084320] using wordTrace_append hprefix tailTrace_1084320
  have hstable : (prefixWord ++ tailWord_1084320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084320).length < 2 ^ (prefixWord ++ tailWord_1084320).sum := by decide
  have hdescent : baseEnd_1084320 < baseStart_1084320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084323 : List Nat := [1, 1, 1, 4, 1, 2, 5, 8]
def baseStart_1084323 : Nat := 118140960795 + 1084323 * 2 ^ 59
def prefixEnd_1084323 : Nat := 4983230072969 + 3 ^ 40 * 1084323 * 2
def baseEnd_1084323 : Nat := 20621440137972826480585

theorem tailTrace_1084323 : CollatzResearch.WordTrace tailWord_1084323 prefixEnd_1084323 20621440137972826480585 := by
  unfold tailWord_1084323
  simp only [CollatzResearch.WordTrace]
  refine ⟨39548508850690433469969623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26365672567126955646646415 39548508850690433469969623)
  ·
    refine ⟨59322763276035650204954435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39548508850690433469969623 59322763276035650204954435)
    ·
      refine ⟨88984144914053475307431653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59322763276035650204954435 88984144914053475307431653)
      ·
        refine ⟨16684527171385026620143435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88984144914053475307431653 16684527171385026620143435)
        ·
          refine ⟨25026790757077539930215153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16684527171385026620143435 25026790757077539930215153)
          ·
            refine ⟨18770093067808154947661365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25026790757077539930215153 18770093067808154947661365)
            ·
              refine ⟨1759696225107014526343253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18770093067808154947661365 1759696225107014526343253)
              ·
                refine ⟨20621440137972826480585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1759696225107014526343253 20621440137972826480585)
                ·
                  rfl

theorem cell23_1084323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 8].length) (baseStart_1084323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084323 prefixEnd_1084323 := by exact prefixLift 1084323
  have htrace : WordTrace (prefixWord ++ tailWord_1084323) baseStart_1084323 baseEnd_1084323 := by
    simpa [prefixWord, tailWord_1084323, baseEnd_1084323] using wordTrace_append hprefix tailTrace_1084323
  have hstable : (prefixWord ++ tailWord_1084323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084323).length < 2 ^ (prefixWord ++ tailWord_1084323).sum := by decide
  have hdescent : baseEnd_1084323 < baseStart_1084323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084327 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 1, 6]
def baseStart_1084327 : Nat := 118140960795 + 1084327 * 2 ^ 59
def prefixEnd_1084327 : Nat := 4983230072969 + 3 ^ 40 * 1084327 * 2
def baseEnd_1084327 : Nat := 185593645882628099775259

theorem tailTrace_1084327 : CollatzResearch.WordTrace tailWord_1084327 prefixEnd_1084327 185593645882628099775259 := by
  unfold tailWord_1084327
  simp only [CollatzResearch.WordTrace]
  refine ⟨39548654742675942153115235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26365769828450628102076823 39548654742675942153115235)
  ·
    refine ⟨59322982114013913229672853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39548654742675942153115235 59322982114013913229672853)
    ·
      refine ⟨2780764786594402182640915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59322982114013913229672853 2780764786594402182640915)
      ·
        refine ⟨4171147179891603273961373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2780764786594402182640915 4171147179891603273961373)
        ·
          refine ⟨1564180192459351227735515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4171147179891603273961373 1564180192459351227735515)
          ·
            refine ⟨2346270288689026841603273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564180192459351227735515 2346270288689026841603273)
            ·
              refine ⟨1759702716516770131202455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2346270288689026841603273 1759702716516770131202455)
              ·
                refine ⟨2639554074775155196803683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1759702716516770131202455 2639554074775155196803683)
                ·
                  refine ⟨3959331112162732795205525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2639554074775155196803683 3959331112162732795205525)
                  ·
                    refine ⟨185593645882628099775259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3959331112162732795205525 185593645882628099775259)
                    ·
                      rfl

theorem cell23_1084327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_1084327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084327 prefixEnd_1084327 := by exact prefixLift 1084327
  have htrace : WordTrace (prefixWord ++ tailWord_1084327) baseStart_1084327 baseEnd_1084327 := by
    simpa [prefixWord, tailWord_1084327, baseEnd_1084327] using wordTrace_append hprefix tailTrace_1084327
  have hstable : (prefixWord ++ tailWord_1084327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084327).length < 2 ^ (prefixWord ++ tailWord_1084327).sum := by decide
  have hdescent : baseEnd_1084327 < baseStart_1084327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084367 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_1084367 : Nat := 118140960795 + 1084367 * 2 ^ 59
def prefixEnd_1084367 : Nat := 4983230072969 + 3 ^ 40 * 1084367 * 2
def baseEnd_1084367 : Nat := 556801476874064142825593

theorem tailTrace_1084367 : CollatzResearch.WordTrace tailWord_1084367 prefixEnd_1084367 556801476874064142825593 := by
  unfold tailWord_1084367
  simp only [CollatzResearch.WordTrace]
  refine ⟨39550113662531028984571355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26366742441687352656380903 39550113662531028984571355)
  ·
    refine ⟨59325170493796543476857033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39550113662531028984571355 59325170493796543476857033)
    ·
      refine ⟨44493877870347407607642775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59325170493796543476857033 44493877870347407607642775)
      ·
        refine ⟨66740816805521111411464163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44493877870347407607642775 66740816805521111411464163)
        ·
          refine ⟨100111225208281667117196245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66740816805521111411464163 100111225208281667117196245)
          ·
            refine ⟨2346356840819101573059287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 100111225208281667117196245 2346356840819101573059287)
            ·
              refine ⟨3519535261228652359588931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346356840819101573059287 3519535261228652359588931)
              ·
                refine ⟨5279302891842978539383397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519535261228652359588931 5279302891842978539383397)
                ·
                  refine ⟨989869292220558476134387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5279302891842978539383397 989869292220558476134387)
                  ·
                    refine ⟨1484803938330837714201581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 989869292220558476134387 1484803938330837714201581)
                    ·
                      refine ⟨556801476874064142825593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1484803938330837714201581 556801476874064142825593)
                      ·
                        rfl

theorem cell23_1084367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_1084367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084367 prefixEnd_1084367 := by exact prefixLift 1084367
  have htrace : WordTrace (prefixWord ++ tailWord_1084367) baseStart_1084367 baseEnd_1084367 := by
    simpa [prefixWord, tailWord_1084367, baseEnd_1084367] using wordTrace_append hprefix tailTrace_1084367
  have hstable : (prefixWord ++ tailWord_1084367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084367).length < 2 ^ (prefixWord ++ tailWord_1084367).sum := by decide
  have hdescent : baseEnd_1084367 < baseStart_1084367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084393 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 5]
def baseStart_1084393 : Nat := 118140960795 + 1084393 * 2 ^ 59
def prefixEnd_1084393 : Nat := 4983230072969 + 3 ^ 40 * 1084393 * 2
def baseEnd_1084393 : Nat := 556814827371081041100473

theorem tailTrace_1084393 : CollatzResearch.WordTrace tailWord_1084393 prefixEnd_1084393 556814827371081041100473 := by
  unfold tailWord_1084393
  simp only [CollatzResearch.WordTrace]
  refine ⟨39551061960436835425017833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26367374640291223616678555 39551061960436835425017833)
  ·
    refine ⟨29663296470327626568763375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39551061960436835425017833 29663296470327626568763375)
    ·
      refine ⟨44494944705491439853145063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29663296470327626568763375 44494944705491439853145063)
      ·
        refine ⟨66742417058237159779717595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44494944705491439853145063 66742417058237159779717595)
        ·
          refine ⟨100113625587355739669576393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66742417058237159779717595 100113625587355739669576393)
          ·
            refine ⟨75085219190516804752182295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100113625587355739669576393 75085219190516804752182295)
            ·
              refine ⟨112627828785775207128273443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75085219190516804752182295 112627828785775207128273443)
              ·
                refine ⟨168941743178662810692410165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112627828785775207128273443 168941743178662810692410165)
                ·
                  refine ⟨15838288422999638502413453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 168941743178662810692410165 15838288422999638502413453)
                  ·
                    refine ⟨5939358158624864438405045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15838288422999638502413453 5939358158624864438405045)
                    ·
                      refine ⟨556814827371081041100473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5939358158624864438405045 556814827371081041100473)
                      ·
                        rfl

theorem cell23_1084393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 5].length) (baseStart_1084393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084393 prefixEnd_1084393 := by exact prefixLift 1084393
  have htrace : WordTrace (prefixWord ++ tailWord_1084393) baseStart_1084393 baseEnd_1084393 := by
    simpa [prefixWord, tailWord_1084393, baseEnd_1084393] using wordTrace_append hprefix tailTrace_1084393
  have hstable : (prefixWord ++ tailWord_1084393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084393).length < 2 ^ (prefixWord ++ tailWord_1084393).sum := by decide
  have hdescent : baseEnd_1084393 < baseStart_1084393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084394 : List Nat := [3, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2]
def baseStart_1084394 : Nat := 118140960795 + 1084394 * 2 ^ 59
def prefixEnd_1084394 : Nat := 4983230072969 + 3 ^ 40 * 1084394 * 2
def baseEnd_1084394 : Nat := 556815340851735537187969

theorem tailTrace_1084394 : CollatzResearch.WordTrace tailWord_1084394 prefixEnd_1084394 556815340851735537187969 := by
  unfold tailWord_1084394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887774608358303148951059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26367398955622141730536157 9887774608358303148951059)
  ·
    refine ⟨14831661912537454723426589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9887774608358303148951059 14831661912537454723426589)
    ·
      refine ⟨5561873217201545521284971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14831661912537454723426589 5561873217201545521284971)
      ·
        refine ⟨8342809825802318281927457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5561873217201545521284971 8342809825802318281927457)
        ·
          refine ⟨6257107369351738711445593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8342809825802318281927457 6257107369351738711445593)
          ·
            refine ⟨4692830527013804033584195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257107369351738711445593 4692830527013804033584195)
            ·
              refine ⟨7039245790520706050376293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4692830527013804033584195 7039245790520706050376293)
              ·
                refine ⟨1319858585722632384445555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7039245790520706050376293 1319858585722632384445555)
                ·
                  refine ⟨1979787878583948576668333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1319858585722632384445555 1979787878583948576668333)
                  ·
                    refine ⟨742420454468980716250625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1979787878583948576668333 742420454468980716250625)
                    ·
                      refine ⟨556815340851735537187969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742420454468980716250625 556815340851735537187969)
                      ·
                        rfl

theorem cell23_1084394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_1084394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084394 prefixEnd_1084394 := by exact prefixLift 1084394
  have htrace : WordTrace (prefixWord ++ tailWord_1084394) baseStart_1084394 baseEnd_1084394 := by
    simpa [prefixWord, tailWord_1084394, baseEnd_1084394] using wordTrace_append hprefix tailTrace_1084394
  have hstable : (prefixWord ++ tailWord_1084394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084394).length < 2 ^ (prefixWord ++ tailWord_1084394).sum := by decide
  have hdescent : baseEnd_1084394 < baseStart_1084394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084402 : List Nat := [3, 2, 1, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1084402 : Nat := 118140960795 + 1084402 * 2 ^ 59
def prefixEnd_1084402 : Nat := 4983230072969 + 3 ^ 40 * 1084402 * 2
def baseEnd_1084402 : Nat := 556819448696971505887933

theorem tailTrace_1084402 : CollatzResearch.WordTrace tailWord_1084402 prefixEnd_1084402 556819448696971505887933 := by
  unfold tailWord_1084402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9887847554351057490523865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26367593478269486641396973 9887847554351057490523865)
  ·
    refine ⟨7415885665763293117892899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9887847554351057490523865 7415885665763293117892899)
    ·
      refine ⟨11123828498644939676839349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7415885665763293117892899 11123828498644939676839349)
      ·
        refine ⟨1042858921747963094703689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11123828498644939676839349 1042858921747963094703689)
        ·
          refine ⟨782144191310972321027767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1042858921747963094703689 782144191310972321027767)
          ·
            refine ⟨1173216286966458481541651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782144191310972321027767 1173216286966458481541651)
            ·
              refine ⟨1759824430449687722312477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173216286966458481541651 1759824430449687722312477)
              ·
                refine ⟨659934161418632895867179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1759824430449687722312477 659934161418632895867179)
                ·
                  refine ⟨989901242127949343800769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 659934161418632895867179 989901242127949343800769)
                  ·
                    refine ⟨742425931595962007850577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989901242127949343800769 742425931595962007850577)
                    ·
                      refine ⟨556819448696971505887933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742425931595962007850577 556819448696971505887933)
                      ·
                        rfl

theorem cell23_1084402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1084402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084402 prefixEnd_1084402 := by exact prefixLift 1084402
  have htrace : WordTrace (prefixWord ++ tailWord_1084402) baseStart_1084402 baseEnd_1084402 := by
    simpa [prefixWord, tailWord_1084402, baseEnd_1084402] using wordTrace_append hprefix tailTrace_1084402
  have hstable : (prefixWord ++ tailWord_1084402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084402).length < 2 ^ (prefixWord ++ tailWord_1084402).sum := by decide
  have hdescent : baseEnd_1084402 < baseStart_1084402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084424 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2]
def baseStart_1084424 : Nat := 118140960795 + 1084424 * 2 ^ 59
def prefixEnd_1084424 : Nat := 4983230072969 + 3 ^ 40 * 1084424 * 2
def baseEnd_1084424 : Nat := 556830745271370419812831

theorem tailTrace_1084424 : CollatzResearch.WordTrace tailWord_1084424 prefixEnd_1084424 556830745271370419812831 := by
  unfold tailWord_1084424
  simp only [CollatzResearch.WordTrace]
  refine ⟨19776096311662263859698163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26368128415549685146264217 19776096311662263859698163)
  ·
    refine ⟨29664144467493395789547245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19776096311662263859698163 29664144467493395789547245)
    ·
      refine ⟨11124054175310023421080217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29664144467493395789547245 11124054175310023421080217)
      ·
        refine ⟨8343040631482517565810163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11124054175310023421080217 8343040631482517565810163)
        ·
          refine ⟨12514560947223776348715245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8343040631482517565810163 12514560947223776348715245)
          ·
            refine ⟨4692960355208916130768217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12514560947223776348715245 4692960355208916130768217)
            ·
              refine ⟨3519720266406687098076163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4692960355208916130768217 3519720266406687098076163)
              ·
                refine ⟨5279580399610030647114245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3519720266406687098076163 5279580399610030647114245)
                ·
                  refine ⟨989921324926880746333921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5279580399610030647114245 989921324926880746333921)
                  ·
                    refine ⟨742440993695160559750441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989921324926880746333921 742440993695160559750441)
                    ·
                      refine ⟨556830745271370419812831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742440993695160559750441 556830745271370419812831)
                      ·
                        rfl

theorem cell23_1084424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_1084424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084424 prefixEnd_1084424 := by exact prefixLift 1084424
  have htrace : WordTrace (prefixWord ++ tailWord_1084424) baseStart_1084424 baseEnd_1084424 := by
    simpa [prefixWord, tailWord_1084424, baseEnd_1084424] using wordTrace_append hprefix tailTrace_1084424
  have hstable : (prefixWord ++ tailWord_1084424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084424).length < 2 ^ (prefixWord ++ tailWord_1084424).sum := by decide
  have hdescent : baseEnd_1084424 < baseStart_1084424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084441 : List Nat := [1, 2, 1, 2, 1, 1, 8, 1, 2, 2, 2]
def baseStart_1084441 : Nat := 118140960795 + 1084441 * 2 ^ 59
def prefixEnd_1084441 : Nat := 4983230072969 + 3 ^ 40 * 1084441 * 2
def baseEnd_1084441 : Nat := 556839474442496853300253

theorem tailTrace_1084441 : CollatzResearch.WordTrace tailWord_1084441 prefixEnd_1084441 556839474442496853300253 := by
  unfold tailWord_1084441
  simp only [CollatzResearch.WordTrace]
  refine ⟨39552812664262939622765177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26368541776175293081843451 39552812664262939622765177)
  ·
    refine ⟨29664609498197204717073883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39552812664262939622765177 29664609498197204717073883)
    ·
      refine ⟨44496914247295807075610825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29664609498197204717073883 44496914247295807075610825)
      ·
        refine ⟨33372685685471855306708119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44496914247295807075610825 33372685685471855306708119)
        ·
          refine ⟨50059028528207782960062179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33372685685471855306708119 50059028528207782960062179)
          ·
            refine ⟨75088542792311674440093269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50059028528207782960062179 75088542792311674440093269)
            ·
              refine ⟨879943860847402434844843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 75088542792311674440093269 879943860847402434844843)
              ·
                refine ⟨1319915791271103652267265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 879943860847402434844843 1319915791271103652267265)
                ·
                  refine ⟨989936843453327739200449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1319915791271103652267265 989936843453327739200449)
                  ·
                    refine ⟨742452632589995804400337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 989936843453327739200449 742452632589995804400337)
                    ·
                      refine ⟨556839474442496853300253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742452632589995804400337 556839474442496853300253)
                      ·
                        rfl

theorem cell23_1084441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_1084441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084441 prefixEnd_1084441 := by exact prefixLift 1084441
  have htrace : WordTrace (prefixWord ++ tailWord_1084441) baseStart_1084441 baseEnd_1084441 := by
    simpa [prefixWord, tailWord_1084441, baseEnd_1084441] using wordTrace_append hprefix tailTrace_1084441
  have hstable : (prefixWord ++ tailWord_1084441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084441).length < 2 ^ (prefixWord ++ tailWord_1084441).sum := by decide
  have hdescent : baseEnd_1084441 < baseStart_1084441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084477 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1084477 : Nat := 118140960795 + 1084477 * 2 ^ 59
def prefixEnd_1084477 : Nat := 4983230072969 + 3 ^ 40 * 1084477 * 2
def baseEnd_1084477 : Nat := 185619319915352904150029

theorem tailTrace_1084477 : CollatzResearch.WordTrace tailWord_1084477 prefixEnd_1084477 185619319915352904150029 := by
  unfold tailWord_1084477
  simp only [CollatzResearch.WordTrace]
  refine ⟨39554125692132517771075685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26369417128088345180717123 39554125692132517771075685)
  ·
    refine ⟨7416398567274847082076691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39554125692132517771075685 7416398567274847082076691)
    ·
      refine ⟨11124597850912270623115037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7416398567274847082076691 11124597850912270623115037)
      ·
        refine ⟨4171724194092101483668139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11124597850912270623115037 4171724194092101483668139)
        ·
          refine ⟨6257586291138152225502209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171724194092101483668139 6257586291138152225502209)
          ·
            refine ⟨4693189718353614169126657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6257586291138152225502209 4693189718353614169126657)
            ·
              refine ⟨3519892288765210626844993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4693189718353614169126657 3519892288765210626844993)
              ·
                refine ⟨2639919216573907970133745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3519892288765210626844993 2639919216573907970133745)
                ·
                  refine ⟨1979939412430430977600309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2639919216573907970133745 1979939412430430977600309)
                  ·
                    refine ⟨185619319915352904150029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1979939412430430977600309 185619319915352904150029)
                    ·
                      rfl

theorem cell23_1084477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1084477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084477 prefixEnd_1084477 := by exact prefixLift 1084477
  have htrace : WordTrace (prefixWord ++ tailWord_1084477) baseStart_1084477 baseEnd_1084477 := by
    simpa [prefixWord, tailWord_1084477, baseEnd_1084477] using wordTrace_append hprefix tailTrace_1084477
  have hstable : (prefixWord ++ tailWord_1084477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084477).length < 2 ^ (prefixWord ++ tailWord_1084477).sum := by decide
  have hdescent : baseEnd_1084477 < baseStart_1084477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084497 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 1, 6, 2]
def baseStart_1084497 : Nat := 118140960795 + 1084497 * 2 ^ 59
def prefixEnd_1084497 : Nat := 4983230072969 + 3 ^ 40 * 1084497 * 2
def baseEnd_1084497 : Nat := 556868229359148634199995

theorem tailTrace_1084497 : CollatzResearch.WordTrace tailWord_1084497 prefixEnd_1084497 556868229359148634199995 := by
  unfold tailWord_1084497
  simp only [CollatzResearch.WordTrace]
  refine ⟨39554855152060061186803745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26369903434706707457869163 39554855152060061186803745)
  ·
    refine ⟨29666141364045045890102809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39554855152060061186803745 29666141364045045890102809)
    ·
      refine ⟨22249606023033784417577107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29666141364045045890102809 22249606023033784417577107)
      ·
        refine ⟨33374409034550676626365661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22249606023033784417577107 33374409034550676626365661)
        ·
          refine ⟨12515403387956503734887123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33374409034550676626365661 12515403387956503734887123)
          ·
            refine ⟨18773105081934755602330685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12515403387956503734887123 18773105081934755602330685)
            ·
              refine ⟨7039914405725533350874007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18773105081934755602330685 7039914405725533350874007)
              ·
                refine ⟨10559871608588300026311011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7039914405725533350874007 10559871608588300026311011)
                ·
                  refine ⟨15839807412882450039466517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10559871608588300026311011 15839807412882450039466517)
                  ·
                    refine ⟨742490972478864845599993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15839807412882450039466517 742490972478864845599993)
                    ·
                      refine ⟨556868229359148634199995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742490972478864845599993 556868229359148634199995)
                      ·
                        rfl

theorem cell23_1084497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 6, 2].length) (baseStart_1084497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084497 prefixEnd_1084497 := by exact prefixLift 1084497
  have htrace : WordTrace (prefixWord ++ tailWord_1084497) baseStart_1084497 baseEnd_1084497 := by
    simpa [prefixWord, tailWord_1084497, baseEnd_1084497] using wordTrace_append hprefix tailTrace_1084497
  have hstable : (prefixWord ++ tailWord_1084497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084497).length < 2 ^ (prefixWord ++ tailWord_1084497).sum := by decide
  have hdescent : baseEnd_1084497 < baseStart_1084497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084514 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1084514 : Nat := 118140960795 + 1084514 * 2 ^ 59
def prefixEnd_1084514 : Nat := 4983230072969 + 3 ^ 40 * 1084514 * 2
def baseEnd_1084514 : Nat := 556876958530275067687417

theorem tailTrace_1084514 : CollatzResearch.WordTrace tailWord_1084514 prefixEnd_1084514 556876958530275067687417 := by
  unfold tailWord_1084514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9888868798249618272543149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26370316795332315393448397 9888868798249618272543149)
  ·
    refine ⟨3708325799343606852203681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9888868798249618272543149 3708325799343606852203681)
    ·
      refine ⟨2781244349507705139152761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3708325799343606852203681 2781244349507705139152761)
      ·
        refine ⟨2085933262130778854364571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2781244349507705139152761 2085933262130778854364571)
        ·
          refine ⟨3128899893196168281546857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2085933262130778854364571 3128899893196168281546857)
          ·
            refine ⟨2346674919897126211160143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3128899893196168281546857 2346674919897126211160143)
            ·
              refine ⟨3520012379845689316740215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346674919897126211160143 3520012379845689316740215)
              ·
                refine ⟨5280018569768533975110323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520012379845689316740215 5280018569768533975110323)
                ·
                  refine ⟨7920027854652800962665485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5280018569768533975110323 7920027854652800962665485)
                  ·
                    refine ⟨2970010445494800360999557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7920027854652800962665485 2970010445494800360999557)
                    ·
                      refine ⟨556876958530275067687417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2970010445494800360999557 556876958530275067687417)
                      ·
                        rfl

theorem cell23_1084514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1084514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084514 prefixEnd_1084514 := by exact prefixLift 1084514
  have htrace : WordTrace (prefixWord ++ tailWord_1084514) baseStart_1084514 baseEnd_1084514 := by
    simpa [prefixWord, tailWord_1084514, baseEnd_1084514] using wordTrace_append hprefix tailTrace_1084514
  have hstable : (prefixWord ++ tailWord_1084514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084514).length < 2 ^ (prefixWord ++ tailWord_1084514).sum := by decide
  have hdescent : baseEnd_1084514 < baseStart_1084514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084517 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1084517 : Nat := 118140960795 + 1084517 * 2 ^ 59
def prefixEnd_1084517 : Nat := 4983230072969 + 3 ^ 40 * 1084517 * 2
def baseEnd_1084517 : Nat := 556878498972238555949903

theorem tailTrace_1084517 : CollatzResearch.WordTrace tailWord_1084517 prefixEnd_1084517 556878498972238555949903 := by
  unfold tailWord_1084517
  simp only [CollatzResearch.WordTrace]
  refine ⟨39555584611987604602531805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26370389741325069735021203 39555584611987604602531805)
  ·
    refine ⟨14833344229495351725949427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39555584611987604602531805 14833344229495351725949427)
    ·
      refine ⟨22250016344243027588924141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14833344229495351725949427 22250016344243027588924141)
      ·
        refine ⟨8343756129091135345846553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22250016344243027588924141 8343756129091135345846553)
        ·
          refine ⟨6257817096818351509384915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8343756129091135345846553 6257817096818351509384915)
          ·
            refine ⟨9386725645227527264077373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257817096818351509384915 9386725645227527264077373)
            ·
              refine ⟨3520022116960322724029015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9386725645227527264077373 3520022116960322724029015)
              ·
                refine ⟨5280033175440484086043523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520022116960322724029015 5280033175440484086043523)
                ·
                  refine ⟨7920049763160726129065285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5280033175440484086043523 7920049763160726129065285)
                  ·
                    refine ⟨1485009330592636149199741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7920049763160726129065285 1485009330592636149199741)
                    ·
                      refine ⟨556878498972238555949903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485009330592636149199741 556878498972238555949903)
                      ·
                        rfl

theorem cell23_1084517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1084517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084517 prefixEnd_1084517 := by exact prefixLift 1084517
  have htrace : WordTrace (prefixWord ++ tailWord_1084517) baseStart_1084517 baseEnd_1084517 := by
    simpa [prefixWord, tailWord_1084517, baseEnd_1084517] using wordTrace_append hprefix tailTrace_1084517
  have hstable : (prefixWord ++ tailWord_1084517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084517).length < 2 ^ (prefixWord ++ tailWord_1084517).sum := by decide
  have hdescent : baseEnd_1084517 < baseStart_1084517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084534 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1084534 : Nat := 118140960795 + 1084534 * 2 ^ 59
def prefixEnd_1084534 : Nat := 4983230072969 + 3 ^ 40 * 1084534 * 2
def baseEnd_1084534 : Nat := 556887228143364989437325

theorem tailTrace_1084534 : CollatzResearch.WordTrace tailWord_1084534 prefixEnd_1084534 556887228143364989437325 := by
  unfold tailWord_1084534
  simp only [CollatzResearch.WordTrace]
  refine ⟨2472262790807876031618791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26370803101950677670600437 2472262790807876031618791)
  ·
    refine ⟨3708394186211814047428187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2472262790807876031618791 3708394186211814047428187)
    ·
      refine ⟨5562591279317721071142281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3708394186211814047428187 5562591279317721071142281)
      ·
        refine ⟨4171943459488290803356711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5562591279317721071142281 4171943459488290803356711)
        ·
          refine ⟨6257915189232436205035067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4171943459488290803356711 6257915189232436205035067)
          ·
            refine ⟨9386872783848654307552601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6257915189232436205035067 9386872783848654307552601)
            ·
              refine ⟨7040154587886490730664451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9386872783848654307552601 7040154587886490730664451)
              ·
                refine ⟨10560231881829736095996677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7040154587886490730664451 10560231881829736095996677)
                ·
                  refine ⟨1980043477843075517999377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10560231881829736095996677 1980043477843075517999377)
                  ·
                    refine ⟨1485032608382306638499533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980043477843075517999377 1485032608382306638499533)
                    ·
                      refine ⟨556887228143364989437325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485032608382306638499533 556887228143364989437325)
                      ·
                        rfl

theorem cell23_1084534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1084534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084534 prefixEnd_1084534 := by exact prefixLift 1084534
  have htrace : WordTrace (prefixWord ++ tailWord_1084534) baseStart_1084534 baseEnd_1084534 := by
    simpa [prefixWord, tailWord_1084534, baseEnd_1084534] using wordTrace_append hprefix tailTrace_1084534
  have hstable : (prefixWord ++ tailWord_1084534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084534).length < 2 ^ (prefixWord ++ tailWord_1084534).sum := by decide
  have hdescent : baseEnd_1084534 < baseStart_1084534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084537 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 8]
def baseStart_1084537 : Nat := 118140960795 + 1084537 * 2 ^ 59
def prefixEnd_1084537 : Nat := 4983230072969 + 3 ^ 40 * 1084537 * 2
def baseEnd_1084537 : Nat := 61876529842814275299979

theorem tailTrace_1084537 : CollatzResearch.WordTrace tailWord_1084537 prefixEnd_1084537 61876529842814275299979 := by
  unfold tailWord_1084537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39556314071915148018259865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26370876047943432012173243 39556314071915148018259865)
  ·
    refine ⟨29667235553936361013694899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39556314071915148018259865 29667235553936361013694899)
    ·
      refine ⟨44500853330904541520542349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29667235553936361013694899 44500853330904541520542349)
      ·
        refine ⟨16687819999089203070203381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44500853330904541520542349 16687819999089203070203381)
        ·
          refine ⟨1564483124914612787831567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16687819999089203070203381 1564483124914612787831567)
          ·
            refine ⟨2346724687371919181747351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564483124914612787831567 2346724687371919181747351)
            ·
              refine ⟨3520087031057878772621027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346724687371919181747351 3520087031057878772621027)
              ·
                refine ⟨5280130546586818158931541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3520087031057878772621027 5280130546586818158931541)
                ·
                  refine ⟨61876529842814275299979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5280130546586818158931541 61876529842814275299979)
                  ·
                    rfl

theorem cell23_1084537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 8].length) (baseStart_1084537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084537 prefixEnd_1084537 := by exact prefixLift 1084537
  have htrace : WordTrace (prefixWord ++ tailWord_1084537) baseStart_1084537 baseEnd_1084537 := by
    simpa [prefixWord, tailWord_1084537, baseEnd_1084537] using wordTrace_append hprefix tailTrace_1084537
  have hstable : (prefixWord ++ tailWord_1084537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084537).length < 2 ^ (prefixWord ++ tailWord_1084537).sum := by decide
  have hdescent : baseEnd_1084537 < baseStart_1084537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084540 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_1084540 : Nat := 118140960795 + 1084540 * 2 ^ 59
def prefixEnd_1084540 : Nat := 4983230072969 + 3 ^ 40 * 1084540 * 2
def baseEnd_1084540 : Nat := 556890309027291965962297

theorem tailTrace_1084540 : CollatzResearch.WordTrace tailWord_1084540 prefixEnd_1084540 556890309027291965962297 := by
  unfold tailWord_1084540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19778211745452139765309537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26370948993936186353746049 19778211745452139765309537)
  ·
    refine ⟨14833658809089104823982153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19778211745452139765309537 14833658809089104823982153)
    ·
      refine ⟨11125244106816828617986615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14833658809089104823982153 11125244106816828617986615)
      ·
        refine ⟨16687866160225242926979923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11125244106816828617986615 16687866160225242926979923)
        ·
          refine ⟨25031799240337864390469885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16687866160225242926979923 25031799240337864390469885)
          ·
            refine ⟨9386924715126699146426207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25031799240337864390469885 9386924715126699146426207)
            ·
              refine ⟨14080387072690048719639311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9386924715126699146426207 14080387072690048719639311)
              ·
                refine ⟨21120580609035073079458967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14080387072690048719639311 21120580609035073079458967)
                ·
                  refine ⟨31680870913552609619188451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21120580609035073079458967 31680870913552609619188451)
                  ·
                    refine ⟨47521306370328914428782677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31680870913552609619188451 47521306370328914428782677)
                    ·
                      refine ⟨556890309027291965962297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47521306370328914428782677 556890309027291965962297)
                      ·
                        rfl

theorem cell23_1084540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_1084540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084540 prefixEnd_1084540 := by exact prefixLift 1084540
  have htrace : WordTrace (prefixWord ++ tailWord_1084540) baseStart_1084540 baseEnd_1084540 := by
    simpa [prefixWord, tailWord_1084540, baseEnd_1084540] using wordTrace_append hprefix tailTrace_1084540
  have hstable : (prefixWord ++ tailWord_1084540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084540).length < 2 ^ (prefixWord ++ tailWord_1084540).sum := by decide
  have hdescent : baseEnd_1084540 < baseStart_1084540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084554 : List Nat := [3, 1, 2, 3, 1, 1, 5, 1, 6]
def baseStart_1084554 : Nat := 118140960795 + 1084554 * 2 ^ 59
def prefixEnd_1084554 : Nat := 4983230072969 + 3 ^ 40 * 1084554 * 2
def baseEnd_1084554 : Nat := 61877499750717212354137

theorem tailTrace_1084554 : CollatzResearch.WordTrace tailWord_1084554 prefixEnd_1084554 61877499750717212354137 := by
  unfold tailWord_1084554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9889233528213389980407179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26371289408569039947752477 9889233528213389980407179)
  ·
    refine ⟨14833850292320084970610769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9889233528213389980407179 14833850292320084970610769)
    ·
      refine ⟨11125387719240063727958077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14833850292320084970610769 11125387719240063727958077)
      ·
        refine ⟨4172020394715023897984279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11125387719240063727958077 4172020394715023897984279)
        ·
          refine ⟨6258030592072535846976419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172020394715023897984279 6258030592072535846976419)
          ·
            refine ⟨9387045888108803770464629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6258030592072535846976419 9387045888108803770464629)
            ·
              refine ⟨880035552010200353481059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9387045888108803770464629 880035552010200353481059)
              ·
                refine ⟨1320053328015300530221589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880035552010200353481059 1320053328015300530221589)
                ·
                  refine ⟨61877499750717212354137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1320053328015300530221589 61877499750717212354137)
                  ·
                    rfl

theorem cell23_1084554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 6].length) (baseStart_1084554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084554 prefixEnd_1084554 := by exact prefixLift 1084554
  have htrace : WordTrace (prefixWord ++ tailWord_1084554) baseStart_1084554 baseEnd_1084554 := by
    simpa [prefixWord, tailWord_1084554, baseEnd_1084554] using wordTrace_append hprefix tailTrace_1084554
  have hstable : (prefixWord ++ tailWord_1084554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084554).length < 2 ^ (prefixWord ++ tailWord_1084554).sum := by decide
  have hdescent : baseEnd_1084554 < baseStart_1084554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084575 : List Nat := [1, 1, 2, 6, 3, 1, 1, 3, 1, 4]
def baseStart_1084575 : Nat := 118140960795 + 1084575 * 2 ^ 59
def prefixEnd_1084575 : Nat := 4983230072969 + 3 ^ 40 * 1084575 * 2
def baseEnd_1084575 : Nat := 185636093616733109674879

theorem tailTrace_1084575 : CollatzResearch.WordTrace tailWord_1084575 prefixEnd_1084575 185636093616733109674879 := by
  unfold tailWord_1084575
  simp only [CollatzResearch.WordTrace]
  refine ⟨39557700045777480508143179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26371800030518320338762119 39557700045777480508143179)
  ·
    refine ⟨59336550068666220762214769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39557700045777480508143179 59336550068666220762214769)
    ·
      refine ⟨44502412551499665571661077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59336550068666220762214769 44502412551499665571661077)
      ·
        refine ⟨2086050588351546823671613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44502412551499665571661077 2086050588351546823671613)
        ·
          refine ⟨782268970631830058876855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2086050588351546823671613 782268970631830058876855)
          ·
            refine ⟨1173403455947745088315283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 782268970631830058876855 1173403455947745088315283)
            ·
              refine ⟨1760105183921617632472925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1173403455947745088315283 1760105183921617632472925)
              ·
                refine ⟨660039443970606612177347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1760105183921617632472925 660039443970606612177347)
                ·
                  refine ⟨990059165955909918266021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660039443970606612177347 990059165955909918266021)
                  ·
                    refine ⟨185636093616733109674879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990059165955909918266021 185636093616733109674879)
                    ·
                      rfl

theorem cell23_1084575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_1084575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084575 prefixEnd_1084575 := by exact prefixLift 1084575
  have htrace : WordTrace (prefixWord ++ tailWord_1084575) baseStart_1084575 baseEnd_1084575 := by
    simpa [prefixWord, tailWord_1084575, baseEnd_1084575] using wordTrace_append hprefix tailTrace_1084575
  have hstable : (prefixWord ++ tailWord_1084575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084575).length < 2 ^ (prefixWord ++ tailWord_1084575).sum := by decide
  have hdescent : baseEnd_1084575 < baseStart_1084575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084607 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_1084607 : Nat := 118140960795 + 1084607 * 2 ^ 59
def prefixEnd_1084607 : Nat := 4983230072969 + 3 ^ 40 * 1084607 * 2
def baseEnd_1084607 : Nat := 556924712231143203824489

theorem tailTrace_1084607 : CollatzResearch.WordTrace tailWord_1084607 prefixEnd_1084607 556924712231143203824489 := by
  unfold tailWord_1084607
  simp only [CollatzResearch.WordTrace]
  refine ⟨39558867181661549973308075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26372578121107699982205383 39558867181661549973308075)
  ·
    refine ⟨59338300772492324959962113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39558867181661549973308075 59338300772492324959962113)
    ·
      refine ⟨44503725579369243719971585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59338300772492324959962113 44503725579369243719971585)
      ·
        refine ⟨33377794184526932789978689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44503725579369243719971585 33377794184526932789978689)
        ·
          refine ⟨25033345638395199592484017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33377794184526932789978689 25033345638395199592484017)
          ·
            refine ⟨18775009228796399694363013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25033345638395199592484017 18775009228796399694363013)
            ·
              refine ⟨3520314230399324942693065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18775009228796399694363013 3520314230399324942693065)
              ·
                refine ⟨2640235672799493707019799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3520314230399324942693065 2640235672799493707019799)
                ·
                  refine ⟨3960353509199240560529699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2640235672799493707019799 3960353509199240560529699)
                  ·
                    refine ⟨5940530263798860840794549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3960353509199240560529699 5940530263798860840794549)
                    ·
                      refine ⟨556924712231143203824489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5940530263798860840794549 556924712231143203824489)
                      ·
                        rfl

theorem cell23_1084607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_1084607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084607 prefixEnd_1084607 := by exact prefixLift 1084607
  have htrace : WordTrace (prefixWord ++ tailWord_1084607) baseStart_1084607 baseEnd_1084607 := by
    simpa [prefixWord, tailWord_1084607, baseEnd_1084607] using wordTrace_append hprefix tailTrace_1084607
  have hstable : (prefixWord ++ tailWord_1084607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084607).length < 2 ^ (prefixWord ++ tailWord_1084607).sum := by decide
  have hdescent : baseEnd_1084607 < baseStart_1084607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084655 : List Nat := [1, 1, 2, 1, 7, 1, 1, 4, 1, 2, 2]
def baseStart_1084655 : Nat := 118140960795 + 1084655 * 2 ^ 59
def prefixEnd_1084655 : Nat := 4983230072969 + 3 ^ 40 * 1084655 * 2
def baseEnd_1084655 : Nat := 556949359302559016024269

theorem tailTrace_1084655 : CollatzResearch.WordTrace tailWord_1084655 prefixEnd_1084655 556949359302559016024269 := by
  unfold tailWord_1084655
  simp only [CollatzResearch.WordTrace]
  refine ⟨39560617885487654171055419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26373745256991769447370279 39560617885487654171055419)
  ·
    refine ⟨59340926828231481256583129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39560617885487654171055419 59340926828231481256583129)
    ·
      refine ⟨44505695121173610942437347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59340926828231481256583129 44505695121173610942437347)
      ·
        refine ⟨66758542681760416413656021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44505695121173610942437347 66758542681760416413656021)
        ·
          refine ⟨1564653344103759759695063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 66758542681760416413656021 1564653344103759759695063)
          ·
            refine ⟨2346980016155639639542595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1564653344103759759695063 2346980016155639639542595)
            ·
              refine ⟨3520470024233459459313893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2346980016155639639542595 3520470024233459459313893)
              ·
                refine ⟨660088129543773648621355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3520470024233459459313893 660088129543773648621355)
                ·
                  refine ⟨990132194315660472932033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660088129543773648621355 990132194315660472932033)
                  ·
                    refine ⟨742599145736745354699025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990132194315660472932033 742599145736745354699025)
                    ·
                      refine ⟨556949359302559016024269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742599145736745354699025 556949359302559016024269)
                      ·
                        rfl

theorem cell23_1084655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 2, 2].length) (baseStart_1084655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084655 prefixEnd_1084655 := by exact prefixLift 1084655
  have htrace : WordTrace (prefixWord ++ tailWord_1084655) baseStart_1084655 baseEnd_1084655 := by
    simpa [prefixWord, tailWord_1084655, baseEnd_1084655] using wordTrace_append hprefix tailTrace_1084655
  have hstable : (prefixWord ++ tailWord_1084655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084655).length < 2 ^ (prefixWord ++ tailWord_1084655).sum := by decide
  have hdescent : baseEnd_1084655 < baseStart_1084655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084671 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_1084671 : Nat := 118140960795 + 1084671 * 2 ^ 59
def prefixEnd_1084671 : Nat := 4983230072969 + 3 ^ 40 * 1084671 * 2
def baseEnd_1084671 : Nat := 556957574993030953424195

theorem tailTrace_1084671 : CollatzResearch.WordTrace tailWord_1084671 prefixEnd_1084671 556957574993030953424195 := by
  unfold tailWord_1084671
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561201453429688903637867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26374134302286459269091911 39561201453429688903637867)
  ·
    refine ⟨59341802180144533355456801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39561201453429688903637867 59341802180144533355456801)
    ·
      refine ⟨44506351635108400016592601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59341802180144533355456801 44506351635108400016592601)
      ·
        refine ⟨33379763726331300012444451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44506351635108400016592601 33379763726331300012444451)
        ·
          refine ⟨50069645589496950018666677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33379763726331300012444451 50069645589496950018666677)
          ·
            refine ⟨4694029274015339064250001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50069645589496950018666677 4694029274015339064250001)
            ·
              refine ⟨3520521955511504298187501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4694029274015339064250001 3520521955511504298187501)
              ·
                refine ⟨1320195733316814111820313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3520521955511504298187501 1320195733316814111820313)
                ·
                  refine ⟨990146799987610583865235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320195733316814111820313 990146799987610583865235)
                  ·
                    refine ⟨1485220199981415875797853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 990146799987610583865235 1485220199981415875797853)
                    ·
                      refine ⟨556957574993030953424195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485220199981415875797853 556957574993030953424195)
                      ·
                        rfl

theorem cell23_1084671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_1084671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084671 prefixEnd_1084671 := by exact prefixLift 1084671
  have htrace : WordTrace (prefixWord ++ tailWord_1084671) baseStart_1084671 baseEnd_1084671 := by
    simpa [prefixWord, tailWord_1084671, baseEnd_1084671] using wordTrace_append hprefix tailTrace_1084671
  have hstable : (prefixWord ++ tailWord_1084671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084671).length < 2 ^ (prefixWord ++ tailWord_1084671).sum := by decide
  have hdescent : baseEnd_1084671 < baseStart_1084671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084677 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 4]
def baseStart_1084677 : Nat := 118140960795 + 1084677 * 2 ^ 59
def prefixEnd_1084677 : Nat := 4983230072969 + 3 ^ 40 * 1084677 * 2
def baseEnd_1084677 : Nat := 556960655876957929949167

theorem tailTrace_1084677 : CollatzResearch.WordTrace tailWord_1084677 prefixEnd_1084677 556960655876957929949167 := by
  unfold tailWord_1084677
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561420291407951928356285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26374280194271967952237523 39561420291407951928356285)
  ·
    refine ⟨14835532609277981973133607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39561420291407951928356285 14835532609277981973133607)
    ·
      refine ⟨22253298913916972959700411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835532609277981973133607 22253298913916972959700411)
      ·
        refine ⟨33379948370875459439550617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22253298913916972959700411 33379948370875459439550617)
        ·
          refine ⟨25034961278156594579662963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33379948370875459439550617 25034961278156594579662963)
          ·
            refine ⟨37552441917234891869494445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25034961278156594579662963 37552441917234891869494445)
            ·
              refine ⟨14082165718963084451060417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37552441917234891869494445 14082165718963084451060417)
              ·
                refine ⟨10561624289222313338295313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14082165718963084451060417 10561624289222313338295313)
                ·
                  refine ⟨7921218216916735003721485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10561624289222313338295313 7921218216916735003721485)
                  ·
                    refine ⟨2970456831343775626395557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7921218216916735003721485 2970456831343775626395557)
                    ·
                      refine ⟨556960655876957929949167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2970456831343775626395557 556960655876957929949167)
                      ·
                        rfl

theorem cell23_1084677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_1084677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084677 prefixEnd_1084677 := by exact prefixLift 1084677
  have htrace : WordTrace (prefixWord ++ tailWord_1084677) baseStart_1084677 baseEnd_1084677 := by
    simpa [prefixWord, tailWord_1084677, baseEnd_1084677] using wordTrace_append hprefix tailTrace_1084677
  have hstable : (prefixWord ++ tailWord_1084677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084677).length < 2 ^ (prefixWord ++ tailWord_1084677).sum := by decide
  have hdescent : baseEnd_1084677 < baseStart_1084677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084681 : List Nat := [1, 2, 1, 1, 3, 3, 2, 4, 1, 3, 2]
def baseStart_1084681 : Nat := 118140960795 + 1084681 * 2 ^ 59
def prefixEnd_1084681 : Nat := 4983230072969 + 3 ^ 40 * 1084681 * 2
def baseEnd_1084681 : Nat := 556962709799575914299149

theorem tailTrace_1084681 : CollatzResearch.WordTrace tailWord_1084681 prefixEnd_1084681 556962709799575914299149 := by
  unfold tailWord_1084681
  simp only [CollatzResearch.WordTrace]
  refine ⟨39561566183393460611501897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26374377455595640407667931 39561566183393460611501897)
  ·
    refine ⟨29671174637545095458626423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39561566183393460611501897 29671174637545095458626423)
    ·
      refine ⟨44506761956317643187939635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29671174637545095458626423 44506761956317643187939635)
      ·
        refine ⟨66760142934476464781909453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44506761956317643187939635 66760142934476464781909453)
        ·
          refine ⟨25035053600428674293216045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66760142934476464781909453 25035053600428674293216045)
          ·
            refine ⟨9388145100160752859956017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25035053600428674293216045 9388145100160752859956017)
            ·
              refine ⟨7041108825120564644967013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9388145100160752859956017 7041108825120564644967013)
              ·
                refine ⟨1320207904710105870931315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7041108825120564644967013 1320207904710105870931315)
                ·
                  refine ⟨1980311857065158806396973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320207904710105870931315 1980311857065158806396973)
                  ·
                    refine ⟨742616946399434552398865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980311857065158806396973 742616946399434552398865)
                    ·
                      refine ⟨556962709799575914299149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742616946399434552398865 556962709799575914299149)
                      ·
                        rfl

theorem cell23_1084681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 3, 2].length) (baseStart_1084681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084681 prefixEnd_1084681 := by exact prefixLift 1084681
  have htrace : WordTrace (prefixWord ++ tailWord_1084681) baseStart_1084681 baseEnd_1084681 := by
    simpa [prefixWord, tailWord_1084681, baseEnd_1084681] using wordTrace_append hprefix tailTrace_1084681
  have hstable : (prefixWord ++ tailWord_1084681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084681).length < 2 ^ (prefixWord ++ tailWord_1084681).sum := by decide
  have hdescent : baseEnd_1084681 < baseStart_1084681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084698 : List Nat := [3, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2]
def baseStart_1084698 : Nat := 118140960795 + 1084698 * 2 ^ 59
def prefixEnd_1084698 : Nat := 4983230072969 + 3 ^ 40 * 1084698 * 2
def baseEnd_1084698 : Nat := 556971438970702347786571

theorem tailTrace_1084698 : CollatzResearch.WordTrace tailWord_1084698 prefixEnd_1084698 556971438970702347786571 := by
  unfold tailWord_1084698
  simp only [CollatzResearch.WordTrace]
  refine ⟨9890546556082968128717687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26374790816221248343247165 9890546556082968128717687)
  ·
    refine ⟨14835819834124452193076531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9890546556082968128717687 14835819834124452193076531)
    ·
      refine ⟨22253729751186678289614797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14835819834124452193076531 22253729751186678289614797)
      ·
        refine ⟨8345148656695004358605549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22253729751186678289614797 8345148656695004358605549)
        ·
          refine ⟨3129430746260626634477081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8345148656695004358605549 3129430746260626634477081)
          ·
            refine ⟨2347073059695469975857811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129430746260626634477081 2347073059695469975857811)
            ·
              refine ⟨3520609589543204963786717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347073059695469975857811 3520609589543204963786717)
              ·
                refine ⟨1320228596078701861420019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3520609589543204963786717 1320228596078701861420019)
                ·
                  refine ⟨1980342894118052792130029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320228596078701861420019 1980342894118052792130029)
                  ·
                    refine ⟨742628585294269797048761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980342894118052792130029 742628585294269797048761)
                    ·
                      refine ⟨556971438970702347786571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742628585294269797048761 556971438970702347786571)
                      ·
                        rfl

theorem cell23_1084698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_1084698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084698 prefixEnd_1084698 := by exact prefixLift 1084698
  have htrace : WordTrace (prefixWord ++ tailWord_1084698) baseStart_1084698 baseEnd_1084698 := by
    simpa [prefixWord, tailWord_1084698, baseEnd_1084698] using wordTrace_append hprefix tailTrace_1084698
  have hstable : (prefixWord ++ tailWord_1084698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084698).length < 2 ^ (prefixWord ++ tailWord_1084698).sum := by decide
  have hdescent : baseEnd_1084698 < baseStart_1084698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084734 : List Nat := [4, 2, 1, 2, 1, 1, 1, 4, 7]
def baseStart_1084734 : Nat := 118140960795 + 1084734 * 2 ^ 59
def prefixEnd_1084734 : Nat := 4983230072969 + 3 ^ 40 * 1084734 * 2
def baseEnd_1084734 : Nat := 61887769363807134104045

theorem tailTrace_1084734 : CollatzResearch.WordTrace tailWord_1084734 prefixEnd_1084734 61887769363807134104045 := by
  unfold tailWord_1084734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4945437406525181332897657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26375666168134300442120837 4945437406525181332897657)
  ·
    refine ⟨3709078054893885999673243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4945437406525181332897657 3709078054893885999673243)
    ·
      refine ⟨5563617082340828999509865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709078054893885999673243 5563617082340828999509865)
      ·
        refine ⟨4172712811755621749632399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5563617082340828999509865 4172712811755621749632399)
        ·
          refine ⟨6259069217633432624448599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4172712811755621749632399 6259069217633432624448599)
          ·
            refine ⟨9388603826450148936672899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259069217633432624448599 9388603826450148936672899)
            ·
              refine ⟨14082905739675223405009349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9388603826450148936672899 14082905739675223405009349)
              ·
                refine ⟨2640544826189104388439253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14082905739675223405009349 2640544826189104388439253)
                ·
                  refine ⟨61887769363807134104045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2640544826189104388439253 61887769363807134104045)
                  ·
                    rfl

theorem cell23_1084734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_1084734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084734 prefixEnd_1084734 := by exact prefixLift 1084734
  have htrace : WordTrace (prefixWord ++ tailWord_1084734) baseStart_1084734 baseEnd_1084734 := by
    simpa [prefixWord, tailWord_1084734, baseEnd_1084734] using wordTrace_append hprefix tailTrace_1084734
  have hstable : (prefixWord ++ tailWord_1084734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084734).length < 2 ^ (prefixWord ++ tailWord_1084734).sum := by decide
  have hdescent : baseEnd_1084734 < baseStart_1084734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084768 : List Nat := [2, 1, 1, 3, 4, 2, 3, 2, 5]
def baseStart_1084768 : Nat := 118140960795 + 1084768 * 2 ^ 59
def prefixEnd_1084768 : Nat := 4983230072969 + 3 ^ 40 * 1084768 * 2
def baseEnd_1084768 : Nat := 61889709179613008212361

theorem tailTrace_1084768 : CollatzResearch.WordTrace tailWord_1084768 prefixEnd_1084768 61889709179613008212361 := by
  unfold tailWord_1084768
  simp only [CollatzResearch.WordTrace]
  refine ⟨19782369667039137234959479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26376492889385516313279305 19782369667039137234959479)
  ·
    refine ⟨29673554500558705852439219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19782369667039137234959479 29673554500558705852439219)
    ·
      refine ⟨44510331750838058778658829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29673554500558705852439219 44510331750838058778658829)
      ·
        refine ⟨16691374406564272041997061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44510331750838058778658829 16691374406564272041997061)
        ·
          refine ⟨3129632701230801007874449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16691374406564272041997061 3129632701230801007874449)
          ·
            refine ⟨2347224525923100755905837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3129632701230801007874449 2347224525923100755905837)
            ·
              refine ⟨880209197221162783464689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2347224525923100755905837 880209197221162783464689)
              ·
                refine ⟨660156897915872087598517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 880209197221162783464689 660156897915872087598517)
                ·
                  refine ⟨61889709179613008212361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 660156897915872087598517 61889709179613008212361)
                  ·
                    rfl

theorem cell23_1084768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 2, 5].length) (baseStart_1084768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084768 prefixEnd_1084768 := by exact prefixLift 1084768
  have htrace : WordTrace (prefixWord ++ tailWord_1084768) baseStart_1084768 baseEnd_1084768 := by
    simpa [prefixWord, tailWord_1084768, baseEnd_1084768] using wordTrace_append hprefix tailTrace_1084768
  have hstable : (prefixWord ++ tailWord_1084768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084768).length < 2 ^ (prefixWord ++ tailWord_1084768).sum := by decide
  have hdescent : baseEnd_1084768 < baseStart_1084768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084777 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 8]
def baseStart_1084777 : Nat := 118140960795 + 1084777 * 2 ^ 59
def prefixEnd_1084777 : Nat := 4983230072969 + 3 ^ 40 * 1084777 * 2
def baseEnd_1084777 : Nat := 185670667980802512899569

theorem tailTrace_1084777 : CollatzResearch.WordTrace tailWord_1084777 prefixEnd_1084777 185670667980802512899569 := by
  unfold tailWord_1084777
  simp only [CollatzResearch.WordTrace]
  refine ⟨39565067591045669006996585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26376711727363779337997723 39565067591045669006996585)
  ·
    refine ⟨29673800693284251755247439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39565067591045669006996585 29673800693284251755247439)
    ·
      refine ⟨44510701039926377632871159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29673800693284251755247439 44510701039926377632871159)
      ·
        refine ⟨66766051559889566449306739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44510701039926377632871159 66766051559889566449306739)
        ·
          refine ⟨100149077339834349673960109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66766051559889566449306739 100149077339834349673960109)
          ·
            refine ⟨37555904002437881127735041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100149077339834349673960109 37555904002437881127735041)
            ·
              refine ⟨28166928001828410845801281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37555904002437881127735041 28166928001828410845801281)
              ·
                refine ⟨21125196001371308134350961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28166928001828410845801281 21125196001371308134350961)
                ·
                  refine ⟨15843897001028481100763221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21125196001371308134350961 15843897001028481100763221)
                  ·
                    refine ⟨185670667980802512899569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15843897001028481100763221 185670667980802512899569)
                    ·
                      rfl

theorem cell23_1084777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 8].length) (baseStart_1084777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084777 prefixEnd_1084777 := by exact prefixLift 1084777
  have htrace : WordTrace (prefixWord ++ tailWord_1084777) baseStart_1084777 baseEnd_1084777 := by
    simpa [prefixWord, tailWord_1084777, baseEnd_1084777] using wordTrace_append hprefix tailTrace_1084777
  have hstable : (prefixWord ++ tailWord_1084777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084777).length < 2 ^ (prefixWord ++ tailWord_1084777).sum := by decide
  have hdescent : baseEnd_1084777 < baseStart_1084777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084784 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4]
def baseStart_1084784 : Nat := 118140960795 + 1084784 * 2 ^ 59
def prefixEnd_1084784 : Nat := 4983230072969 + 3 ^ 40 * 1084784 * 2
def baseEnd_1084784 : Nat := 557015598306989011311175

theorem tailTrace_1084784 : CollatzResearch.WordTrace tailWord_1084784 prefixEnd_1084784 557015598306989011311175 := by
  unfold tailWord_1084784
  simp only [CollatzResearch.WordTrace]
  refine ⟨19782661451010154601250703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26376881934680206135000937 19782661451010154601250703)
  ·
    refine ⟨29673992176515231901876055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19782661451010154601250703 29673992176515231901876055)
    ·
      refine ⟨44510988264772847852814083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29673992176515231901876055 44510988264772847852814083)
      ·
        refine ⟨66766482397159271779221125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44510988264772847852814083 66766482397159271779221125)
        ·
          refine ⟨12518715449467363458603961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66766482397159271779221125 12518715449467363458603961)
          ·
            refine ⟨9389036587100522593952971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12518715449467363458603961 9389036587100522593952971)
            ·
              refine ⟨14083554880650783890929457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9389036587100522593952971 14083554880650783890929457)
              ·
                refine ⟨10562666160488087918197093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14083554880650783890929457 10562666160488087918197093)
                ·
                  refine ⟨1980499905091516484661955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10562666160488087918197093 1980499905091516484661955)
                  ·
                    refine ⟨2970749857637274726992933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1980499905091516484661955 2970749857637274726992933)
                    ·
                      refine ⟨557015598306989011311175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2970749857637274726992933 557015598306989011311175)
                      ·
                        rfl

theorem cell23_1084784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4].length) (baseStart_1084784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084784 prefixEnd_1084784 := by exact prefixLift 1084784
  have htrace : WordTrace (prefixWord ++ tailWord_1084784) baseStart_1084784 baseEnd_1084784 := by
    simpa [prefixWord, tailWord_1084784, baseEnd_1084784] using wordTrace_append hprefix tailTrace_1084784
  have hstable : (prefixWord ++ tailWord_1084784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084784).length < 2 ^ (prefixWord ++ tailWord_1084784).sum := by decide
  have hdescent : baseEnd_1084784 < baseStart_1084784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084821 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 3]
def baseStart_1084821 : Nat := 118140960795 + 1084821 * 2 ^ 59
def prefixEnd_1084821 : Nat := 4983230072969 + 3 ^ 40 * 1084821 * 2
def baseEnd_1084821 : Nat := 557034597091205366548505

theorem tailTrace_1084821 : CollatzResearch.WordTrace tailWord_1084821 prefixEnd_1084821 557034597091205366548505 := by
  unfold tailWord_1084821
  simp only [CollatzResearch.WordTrace]
  refine ⟨39566672402886264521598317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26377781601924176347732211 39566672402886264521598317)
  ·
    refine ⟨14837502151082349195599369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39566672402886264521598317 14837502151082349195599369)
    ·
      refine ⟨11128126613311761896699527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14837502151082349195599369 11128126613311761896699527)
      ·
        refine ⟨16692189919967642845049291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128126613311761896699527 16692189919967642845049291)
        ·
          refine ⟨25038284879951464267573937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692189919967642845049291 25038284879951464267573937)
          ·
            refine ⟨18778713659963598200680453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25038284879951464267573937 18778713659963598200680453)
            ·
              refine ⟨3521008811243174662627585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18778713659963598200680453 3521008811243174662627585)
              ·
                refine ⟨2640756608432380996970689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521008811243174662627585 2640756608432380996970689)
                ·
                  refine ⟨1980567456324285747728017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640756608432380996970689 1980567456324285747728017)
                  ·
                    refine ⟨1485425592243214310796013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980567456324285747728017 1485425592243214310796013)
                    ·
                      refine ⟨557034597091205366548505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485425592243214310796013 557034597091205366548505)
                      ·
                        rfl

theorem cell23_1084821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 2, 3].length) (baseStart_1084821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084821 prefixEnd_1084821 := by exact prefixLift 1084821
  have htrace : WordTrace (prefixWord ++ tailWord_1084821) baseStart_1084821 baseEnd_1084821 := by
    simpa [prefixWord, tailWord_1084821, baseEnd_1084821] using wordTrace_append hprefix tailTrace_1084821
  have hstable : (prefixWord ++ tailWord_1084821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084821).length < 2 ^ (prefixWord ++ tailWord_1084821).sum := by decide
  have hdescent : baseEnd_1084821 < baseStart_1084821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084871 : List Nat := [1, 1, 4, 1, 1, 3, 3, 3, 1, 5]
def baseStart_1084871 : Nat := 118140960795 + 1084871 * 2 ^ 59
def prefixEnd_1084871 : Nat := 4983230072969 + 3 ^ 40 * 1084871 * 2
def baseEnd_1084871 : Nat := 185686757041310056974425

theorem tailTrace_1084871 : CollatzResearch.WordTrace tailWord_1084871 prefixEnd_1084871 185686757041310056974425 := by
  unfold tailWord_1084871
  simp only [CollatzResearch.WordTrace]
  refine ⟨39568496052705123060918467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26378997368470082040612311 39568496052705123060918467)
  ·
    refine ⟨59352744079057684591377701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39568496052705123060918467 59352744079057684591377701)
    ·
      refine ⟨11128639514823315860883319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59352744079057684591377701 11128639514823315860883319)
      ·
        refine ⟨16692959272234973791324979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128639514823315860883319 16692959272234973791324979)
        ·
          refine ⟨25039438908352460686987469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16692959272234973791324979 25039438908352460686987469)
          ·
            refine ⟨9389789590632172757620301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25039438908352460686987469 9389789590632172757620301)
            ·
              refine ⟨3521171096487064784107613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9389789590632172757620301 3521171096487064784107613)
              ·
                refine ⟨1320439161182649294040355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3521171096487064784107613 1320439161182649294040355)
                ·
                  refine ⟨1980658741773973941060533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1320439161182649294040355 1980658741773973941060533)
                  ·
                    refine ⟨185686757041310056974425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1980658741773973941060533 185686757041310056974425)
                    ·
                      rfl

theorem cell23_1084871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_1084871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084871 prefixEnd_1084871 := by exact prefixLift 1084871
  have htrace : WordTrace (prefixWord ++ tailWord_1084871) baseStart_1084871 baseEnd_1084871 := by
    simpa [prefixWord, tailWord_1084871, baseEnd_1084871] using wordTrace_append hprefix tailTrace_1084871
  have hstable : (prefixWord ++ tailWord_1084871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084871).length < 2 ^ (prefixWord ++ tailWord_1084871).sum := by decide
  have hdescent : baseEnd_1084871 < baseStart_1084871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084878 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_1084878 : Nat := 118140960795 + 1084878 * 2 ^ 59
def prefixEnd_1084878 : Nat := 4983230072969 + 3 ^ 40 * 1084878 * 2
def baseEnd_1084878 : Nat := 557063865488511643535743

theorem tailTrace_1084878 : CollatzResearch.WordTrace tailWord_1084878 prefixEnd_1084878 557063865488511643535743 := by
  unfold tailWord_1084878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4946093920459970407052911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26379167575786508837615525 4946093920459970407052911)
  ·
    refine ⟨7419140880689955610579367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4946093920459970407052911 7419140880689955610579367)
    ·
      refine ⟨11128711321034933415869051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7419140880689955610579367 11128711321034933415869051)
      ·
        refine ⟨16693066981552400123803577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11128711321034933415869051 16693066981552400123803577)
        ·
          refine ⟨12519800236164300092852683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16693066981552400123803577 12519800236164300092852683)
          ·
            refine ⟨18779700354246450139279025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12519800236164300092852683 18779700354246450139279025)
            ·
              refine ⟨14084775265684837604459269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18779700354246450139279025 14084775265684837604459269)
              ·
                refine ⟨2640895362315907050836113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14084775265684837604459269 2640895362315907050836113)
                ·
                  refine ⟨1980671521736930288127085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2640895362315907050836113 1980671521736930288127085)
                  ·
                    refine ⟨742751820651348858047657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1980671521736930288127085 742751820651348858047657)
                    ·
                      refine ⟨557063865488511643535743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742751820651348858047657 557063865488511643535743)
                      ·
                        rfl

theorem cell23_1084878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_1084878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084878 prefixEnd_1084878 := by exact prefixLift 1084878
  have htrace : WordTrace (prefixWord ++ tailWord_1084878) baseStart_1084878 baseEnd_1084878 := by
    simpa [prefixWord, tailWord_1084878, baseEnd_1084878] using wordTrace_append hprefix tailTrace_1084878
  have hstable : (prefixWord ++ tailWord_1084878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084878).length < 2 ^ (prefixWord ++ tailWord_1084878).sum := by decide
  have hdescent : baseEnd_1084878 < baseStart_1084878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084885 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1084885 : Nat := 118140960795 + 1084885 * 2 ^ 59
def prefixEnd_1084885 : Nat := 4983230072969 + 3 ^ 40 * 1084885 * 2
def baseEnd_1084885 : Nat := 557067459853093116148211

theorem tailTrace_1084885 : CollatzResearch.WordTrace tailWord_1084885 prefixEnd_1084885 557067459853093116148211 := by
  unfold tailWord_1084885
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569006674654403451928109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26379337783102935634618739 39569006674654403451928109)
  ·
    refine ⟨14838377502995401294473041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39569006674654403451928109 14838377502995401294473041)
    ·
      refine ⟨11128783127246550970854781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14838377502995401294473041 11128783127246550970854781)
      ·
        refine ⟨4173293672717456614070543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11128783127246550970854781 4173293672717456614070543)
        ·
          refine ⟨6259940509076184921105815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4173293672717456614070543 6259940509076184921105815)
          ·
            refine ⟨9389910763614277381658723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6259940509076184921105815 9389910763614277381658723)
            ·
              refine ⟨14084866145421416072488085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9389910763614277381658723 14084866145421416072488085)
              ·
                refine ⟨660228100566628878397879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14084866145421416072488085 660228100566628878397879)
                ·
                  refine ⟨990342150849943317596819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660228100566628878397879 990342150849943317596819)
                  ·
                    refine ⟨1485513226274914976395229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 990342150849943317596819 1485513226274914976395229)
                    ·
                      refine ⟨557067459853093116148211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485513226274914976395229 557067459853093116148211)
                      ·
                        rfl

theorem cell23_1084885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1084885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084885 prefixEnd_1084885 := by exact prefixLift 1084885
  have htrace : WordTrace (prefixWord ++ tailWord_1084885) baseStart_1084885 baseEnd_1084885 := by
    simpa [prefixWord, tailWord_1084885, baseEnd_1084885] using wordTrace_append hprefix tailTrace_1084885
  have hstable : (prefixWord ++ tailWord_1084885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084885).length < 2 ^ (prefixWord ++ tailWord_1084885).sum := by decide
  have hdescent : baseEnd_1084885 < baseStart_1084885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084908 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 5, 2, 2]
def baseStart_1084908 : Nat := 118140960795 + 1084908 * 2 ^ 59
def prefixEnd_1084908 : Nat := 4983230072969 + 3 ^ 40 * 1084908 * 2
def baseEnd_1084908 : Nat := 557079269908146526160605

theorem tailTrace_1084908 : CollatzResearch.WordTrace tailWord_1084908 prefixEnd_1084908 557079269908146526160605 := by
  unfold tailWord_1084908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19784922776785539190007689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26379897035714052253343585 19784922776785539190007689)
  ·
    refine ⟨14838692082589154392505767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19784922776785539190007689 14838692082589154392505767)
    ·
      refine ⟨22258038123883731588758651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14838692082589154392505767 22258038123883731588758651)
      ·
        refine ⟨33387057185825597383137977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22258038123883731588758651 33387057185825597383137977)
        ·
          refine ⟨25040292889369198037353483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33387057185825597383137977 25040292889369198037353483)
          ·
            refine ⟨37560439334053797056030225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25040292889369198037353483 37560439334053797056030225)
            ·
              refine ⟨28170329500540347792022669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37560439334053797056030225 28170329500540347792022669)
              ·
                refine ⟨10563873562702630422008501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28170329500540347792022669 10563873562702630422008501)
                ·
                  refine ⟨990363146503371602063297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10563873562702630422008501 990363146503371602063297)
                  ·
                    refine ⟨742772359877528701547473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990363146503371602063297 742772359877528701547473)
                    ·
                      refine ⟨557079269908146526160605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742772359877528701547473 557079269908146526160605)
                      ·
                        rfl

theorem cell23_1084908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 2, 2].length) (baseStart_1084908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084908 prefixEnd_1084908 := by exact prefixLift 1084908
  have htrace : WordTrace (prefixWord ++ tailWord_1084908) baseStart_1084908 baseEnd_1084908 := by
    simpa [prefixWord, tailWord_1084908, baseEnd_1084908] using wordTrace_append hprefix tailTrace_1084908
  have hstable : (prefixWord ++ tailWord_1084908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084908).length < 2 ^ (prefixWord ++ tailWord_1084908).sum := by decide
  have hdescent : baseEnd_1084908 < baseStart_1084908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084911 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_1084911 : Nat := 118140960795 + 1084911 * 2 ^ 59
def prefixEnd_1084911 : Nat := 4983230072969 + 3 ^ 40 * 1084911 * 2
def baseEnd_1084911 : Nat := 557080810350110014423091

theorem tailTrace_1084911 : CollatzResearch.WordTrace tailWord_1084911 prefixEnd_1084911 557080810350110014423091 := by
  unfold tailWord_1084911
  simp only [CollatzResearch.WordTrace]
  refine ⟨39569954972560209892374587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26379969981706806594916391 39569954972560209892374587)
  ·
    refine ⟨59354932458840314838561881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39569954972560209892374587 59354932458840314838561881)
    ·
      refine ⟨44516199344130236128921411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59354932458840314838561881 44516199344130236128921411)
      ·
        refine ⟨66774299016195354193382117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44516199344130236128921411 66774299016195354193382117)
        ·
          refine ⟨12520181065536628911259147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66774299016195354193382117 12520181065536628911259147)
          ·
            refine ⟨18780271598304943366888721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12520181065536628911259147 18780271598304943366888721)
            ·
              refine ⟨14085203698728707525166541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18780271598304943366888721 14085203698728707525166541)
              ·
                refine ⟨5281951387023265321937453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14085203698728707525166541 5281951387023265321937453)
                ·
                  refine ⟨1980731770133724495726545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5281951387023265321937453 1980731770133724495726545)
                  ·
                    refine ⟨1485548827600293371794909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1980731770133724495726545 1485548827600293371794909)
                    ·
                      refine ⟨557080810350110014423091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1485548827600293371794909 557080810350110014423091)
                      ·
                        rfl

theorem cell23_1084911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_1084911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084911 prefixEnd_1084911 := by exact prefixLift 1084911
  have htrace : WordTrace (prefixWord ++ tailWord_1084911) baseStart_1084911 baseEnd_1084911 := by
    simpa [prefixWord, tailWord_1084911, baseEnd_1084911] using wordTrace_append hprefix tailTrace_1084911
  have hstable : (prefixWord ++ tailWord_1084911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084911).length < 2 ^ (prefixWord ++ tailWord_1084911).sum := by decide
  have hdescent : baseEnd_1084911 < baseStart_1084911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084918 : List Nat := [5, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1084918 : Nat := 118140960795 + 1084918 * 2 ^ 59
def prefixEnd_1084918 : Nat := 4983230072969 + 3 ^ 40 * 1084918 * 2
def baseEnd_1084918 : Nat := 185694801571563829011853

theorem tailTrace_1084918 : CollatzResearch.WordTrace tailWord_1084918 prefixEnd_1084918 185694801571563829011853 := by
  unfold tailWord_1084918
  simp only [CollatzResearch.WordTrace]
  refine ⟨2473138142720928130492463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26380140189023233391919605 2473138142720928130492463)
  ·
    refine ⟨3709707214081392195738695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2473138142720928130492463 3709707214081392195738695)
    ·
      refine ⟨5564560821122088293608043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3709707214081392195738695 5564560821122088293608043)
      ·
        refine ⟨8346841231683132440412065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5564560821122088293608043 8346841231683132440412065)
        ·
          refine ⟨6260130923762349330309049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8346841231683132440412065 6260130923762349330309049)
          ·
            refine ⟨4695098192821761997731787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6260130923762349330309049 4695098192821761997731787)
            ·
              refine ⟨7042647289232642996597681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4695098192821761997731787 7042647289232642996597681)
              ·
                refine ⟨5281985466924482247448261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7042647289232642996597681 5281985466924482247448261)
                ·
                  refine ⟨990372275048340421396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5281985466924482247448261 990372275048340421396549)
                  ·
                    refine ⟨185694801571563829011853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990372275048340421396549 185694801571563829011853)
                    ·
                      rfl

theorem cell23_1084918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1084918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084918 prefixEnd_1084918 := by exact prefixLift 1084918
  have htrace : WordTrace (prefixWord ++ tailWord_1084918) baseStart_1084918 baseEnd_1084918 := by
    simpa [prefixWord, tailWord_1084918, baseEnd_1084918] using wordTrace_append hprefix tailTrace_1084918
  have hstable : (prefixWord ++ tailWord_1084918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084918).length < 2 ^ (prefixWord ++ tailWord_1084918).sum := by decide
  have hdescent : baseEnd_1084918 < baseStart_1084918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1084952 : List Nat := [2, 1, 2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_1084952 : Nat := 118140960795 + 1084952 * 2 ^ 59
def prefixEnd_1084952 : Nat := 4983230072969 + 3 ^ 40 * 1084952 * 2
def baseEnd_1084952 : Nat := 185700621018981451336801

theorem tailTrace_1084952 : CollatzResearch.WordTrace tailWord_1084952 prefixEnd_1084952 185700621018981451336801 := by
  unfold tailWord_1084952
  simp only [CollatzResearch.WordTrace]
  refine ⟨19785725182705836947308555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26380966910274449263078073 19785725182705836947308555)
  ·
    refine ⟨29678587774058755420962833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19785725182705836947308555 29678587774058755420962833)
    ·
      refine ⟨22258940830544066565722125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29678587774058755420962833 22258940830544066565722125)
      ·
        refine ⟨8347102811454024962145797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22258940830544066565722125 8347102811454024962145797)
        ·
          refine ⟨1565081777147629680402337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8347102811454024962145797 1565081777147629680402337)
          ·
            refine ⟨1173811332860722260301753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1565081777147629680402337 1173811332860722260301753)
            ·
              refine ⟨880358499645541695226315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1173811332860722260301753 880358499645541695226315)
              ·
                refine ⟨1320537749468312542839473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880358499645541695226315 1320537749468312542839473)
                ·
                  refine ⟨990403312101234407129605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1320537749468312542839473 990403312101234407129605)
                  ·
                    refine ⟨185700621018981451336801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990403312101234407129605 185700621018981451336801)
                    ·
                      rfl

theorem cell23_1084952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_1084952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1084952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1084952 prefixEnd_1084952 := by exact prefixLift 1084952
  have htrace : WordTrace (prefixWord ++ tailWord_1084952) baseStart_1084952 baseEnd_1084952 := by
    simpa [prefixWord, tailWord_1084952, baseEnd_1084952] using wordTrace_append hprefix tailTrace_1084952
  have hstable : (prefixWord ++ tailWord_1084952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1084952).length < 2 ^ (prefixWord ++ tailWord_1084952).sum := by decide
  have hdescent : baseEnd_1084952 < baseStart_1084952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1084952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085015 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_1085015 : Nat := 118140960795 + 1085015 * 2 ^ 59
def prefixEnd_1085015 : Nat := 4983230072969 + 3 ^ 40 * 1085015 * 2
def baseEnd_1085015 : Nat := 557134212338177607522613

theorem tailTrace_1085015 : CollatzResearch.WordTrace tailWord_1085015 prefixEnd_1085015 557134212338177607522613 := by
  unfold tailWord_1085015
  simp only [CollatzResearch.WordTrace]
  refine ⟨39573748164183435654160499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26382498776122290436106999 39573748164183435654160499)
  ·
    refine ⟨59360622246275153481240749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39573748164183435654160499 59360622246275153481240749)
    ·
      refine ⟨22260233342353182555465281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59360622246275153481240749 22260233342353182555465281)
      ·
        refine ⟨16695175006764886916598961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22260233342353182555465281 16695175006764886916598961)
        ·
          refine ⟨12521381255073665187449221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16695175006764886916598961 12521381255073665187449221)
          ·
            refine ⟨2347758985326312222646729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12521381255073665187449221 2347758985326312222646729)
            ·
              refine ⟨1760819238994734166985047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2347758985326312222646729 1760819238994734166985047)
              ·
                refine ⟨2641228858492101250477571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1760819238994734166985047 2641228858492101250477571)
                ·
                  refine ⟨3961843287738151875716357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641228858492101250477571 3961843287738151875716357)
                  ·
                    refine ⟨742845616450903476696817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3961843287738151875716357 742845616450903476696817)
                    ·
                      refine ⟨557134212338177607522613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742845616450903476696817 557134212338177607522613)
                      ·
                        rfl

theorem cell23_1085015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_1085015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085015 prefixEnd_1085015 := by exact prefixLift 1085015
  have htrace : WordTrace (prefixWord ++ tailWord_1085015) baseStart_1085015 baseEnd_1085015 := by
    simpa [prefixWord, tailWord_1085015, baseEnd_1085015] using wordTrace_append hprefix tailTrace_1085015
  have hstable : (prefixWord ++ tailWord_1085015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085015).length < 2 ^ (prefixWord ++ tailWord_1085015).sum := by decide
  have hdescent : baseEnd_1085015 < baseStart_1085015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085051 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 4, 5]
def baseStart_1085051 : Nat := 118140960795 + 1085051 * 2 ^ 59
def prefixEnd_1085051 : Nat := 4983230072969 + 3 ^ 40 * 1085051 * 2
def baseEnd_1085051 : Nat := 185717565880579822224149

theorem tailTrace_1085051 : CollatzResearch.WordTrace tailWord_1085051 prefixEnd_1085051 185717565880579822224149 := by
  unfold tailWord_1085051
  simp only [CollatzResearch.WordTrace]
  refine ⟨39575061192053013802471007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26383374128035342534980671 39575061192053013802471007)
  ·
    refine ⟨59362591788079520703706511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39575061192053013802471007 59362591788079520703706511)
    ·
      refine ⟨89043887682119281055559767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59362591788079520703706511 89043887682119281055559767)
      ·
        refine ⟨133565831523178921583339651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89043887682119281055559767 133565831523178921583339651)
        ·
          refine ⟨200348747284768382375009477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133565831523178921583339651 200348747284768382375009477)
          ·
            refine ⟨37565390115894071695314277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200348747284768382375009477 37565390115894071695314277)
            ·
              refine ⟨7043510646730138442871427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37565390115894071695314277 7043510646730138442871427)
              ·
                refine ⟨10565265970095207664307141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043510646730138442871427 10565265970095207664307141)
                ·
                  refine ⟨1980987369392851437057589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10565265970095207664307141 1980987369392851437057589)
                  ·
                    refine ⟨185717565880579822224149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1980987369392851437057589 185717565880579822224149)
                    ·
                      rfl

theorem cell23_1085051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 5].length) (baseStart_1085051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085051 prefixEnd_1085051 := by exact prefixLift 1085051
  have htrace : WordTrace (prefixWord ++ tailWord_1085051) baseStart_1085051 baseEnd_1085051 := by
    simpa [prefixWord, tailWord_1085051, baseEnd_1085051] using wordTrace_append hprefix tailTrace_1085051
  have hstable : (prefixWord ++ tailWord_1085051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085051).length < 2 ^ (prefixWord ++ tailWord_1085051).sum := by decide
  have hdescent : baseEnd_1085051 < baseStart_1085051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085061 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1085061 : Nat := 118140960795 + 1085061 * 2 ^ 59
def prefixEnd_1085061 : Nat := 4983230072969 + 3 ^ 40 * 1085061 * 2
def baseEnd_1085061 : Nat := 557157832448284427547401

theorem tailTrace_1085061 : CollatzResearch.WordTrace tailWord_1085061 prefixEnd_1085061 557157832448284427547401 := by
  unfold tailWord_1085061
  simp only [CollatzResearch.WordTrace]
  refine ⟨39575425922016785510335037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26383617281344523673556691 39575425922016785510335037)
  ·
    refine ⟨14840784720756294566375639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39575425922016785510335037 14840784720756294566375639)
    ·
      refine ⟨22261177081134441849563459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14840784720756294566375639 22261177081134441849563459)
      ·
        refine ⟨33391765621701662774345189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22261177081134441849563459 33391765621701662774345189)
        ·
          refine ⟨6260956054069061770189723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33391765621701662774345189 6260956054069061770189723)
          ·
            refine ⟨9391434081103592655284585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6260956054069061770189723 9391434081103592655284585)
            ·
              refine ⟨7043575560827694491463439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9391434081103592655284585 7043575560827694491463439)
              ·
                refine ⟨10565363341241541737195159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7043575560827694491463439 10565363341241541737195159)
                ·
                  refine ⟨15848045011862312605792739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10565363341241541737195159 15848045011862312605792739)
                  ·
                    refine ⟨23772067517793468908689109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15848045011862312605792739 23772067517793468908689109)
                    ·
                      refine ⟨557157832448284427547401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23772067517793468908689109 557157832448284427547401)
                      ·
                        rfl

theorem cell23_1085061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1085061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085061 prefixEnd_1085061 := by exact prefixLift 1085061
  have htrace : WordTrace (prefixWord ++ tailWord_1085061) baseStart_1085061 baseEnd_1085061 := by
    simpa [prefixWord, tailWord_1085061, baseEnd_1085061] using wordTrace_append hprefix tailTrace_1085061
  have hstable : (prefixWord ++ tailWord_1085061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085061).length < 2 ^ (prefixWord ++ tailWord_1085061).sum := by decide
  have hdescent : baseEnd_1085061 < baseStart_1085061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085088 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4]
def baseStart_1085088 : Nat := 118140960795 + 1085088 * 2 ^ 59
def prefixEnd_1085088 : Nat := 4983230072969 + 3 ^ 40 * 1085088 * 2
def baseEnd_1085088 : Nat := 557171696425955821909777

theorem tailTrace_1085088 : CollatzResearch.WordTrace tailWord_1085088 prefixEnd_1085088 557171696425955821909777 := by
  unfold tailWord_1085088
  simp only [CollatzResearch.WordTrace]
  refine ⟨19788205346459484560783959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26384273795279312747711945 19788205346459484560783959)
  ·
    refine ⟨29682308019689226841175939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19788205346459484560783959 29682308019689226841175939)
    ·
      refine ⟨44523462029533840261763909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29682308019689226841175939 44523462029533840261763909)
      ·
        refine ⟨8348149130537595049080733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44523462029533840261763909 8348149130537595049080733)
        ·
          refine ⟨3130555923951598143405275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8348149130537595049080733 3130555923951598143405275)
          ·
            refine ⟨4695833885927397215107913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3130555923951598143405275 4695833885927397215107913)
            ·
              refine ⟨3521875414445547911330935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4695833885927397215107913 3521875414445547911330935)
              ·
                refine ⟨5282813121668321866996403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3521875414445547911330935 5282813121668321866996403)
                ·
                  refine ⟨7924219682502482800494605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5282813121668321866996403 7924219682502482800494605)
                  ·
                    refine ⟨2971582380938431050185477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7924219682502482800494605 2971582380938431050185477)
                    ·
                      refine ⟨557171696425955821909777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2971582380938431050185477 557171696425955821909777)
                      ·
                        rfl

theorem cell23_1085088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_1085088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085088 prefixEnd_1085088 := by exact prefixLift 1085088
  have htrace : WordTrace (prefixWord ++ tailWord_1085088) baseStart_1085088 baseEnd_1085088 := by
    simpa [prefixWord, tailWord_1085088, baseEnd_1085088] using wordTrace_append hprefix tailTrace_1085088
  have hstable : (prefixWord ++ tailWord_1085088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085088).length < 2 ^ (prefixWord ++ tailWord_1085088).sum := by decide
  have hdescent : baseEnd_1085088 < baseStart_1085088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085102 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1085102 : Nat := 118140960795 + 1085102 * 2 ^ 59
def prefixEnd_1085102 : Nat := 4983230072969 + 3 ^ 40 * 1085102 * 2
def baseEnd_1085102 : Nat := 185726295051706255711571

theorem tailTrace_1085102 : CollatzResearch.WordTrace tailWord_1085102 prefixEnd_1085102 185726295051706255711571 := by
  unfold tailWord_1085102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4947115164358531189072195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26384614209912166341718373 4947115164358531189072195)
  ·
    refine ⟨7420672746537796783608293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4947115164358531189072195 7420672746537796783608293)
    ·
      refine ⟨1391376139975836896926555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7420672746537796783608293 1391376139975836896926555)
      ·
        refine ⟨2087064209963755345389833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391376139975836896926555 2087064209963755345389833)
        ·
          refine ⟨1565298157472816509042375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2087064209963755345389833 1565298157472816509042375)
          ·
            refine ⟨2347947236209224763563563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565298157472816509042375 2347947236209224763563563)
            ·
              refine ⟨3521920854313837145345345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2347947236209224763563563 3521920854313837145345345)
              ·
                refine ⟨2641440640735377859009009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3521920854313837145345345 2641440640735377859009009)
                ·
                  refine ⟨1981080480551533394256757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641440640735377859009009 1981080480551533394256757)
                  ·
                    refine ⟨185726295051706255711571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1981080480551533394256757 185726295051706255711571)
                    ·
                      rfl

theorem cell23_1085102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1085102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085102 prefixEnd_1085102 := by exact prefixLift 1085102
  have htrace : WordTrace (prefixWord ++ tailWord_1085102) baseStart_1085102 baseEnd_1085102 := by
    simpa [prefixWord, tailWord_1085102, baseEnd_1085102] using wordTrace_append hprefix tailTrace_1085102
  have hstable : (prefixWord ++ tailWord_1085102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085102).length < 2 ^ (prefixWord ++ tailWord_1085102).sum := by decide
  have hdescent : baseEnd_1085102 < baseStart_1085102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085115 : List Nat := [1, 1, 1, 1, 1, 2, 3, 8, 1, 4]
def baseStart_1085115 : Nat := 118140960795 + 1085115 * 2 ^ 59
def prefixEnd_1085115 : Nat := 4983230072969 + 3 ^ 40 * 1085115 * 2
def baseEnd_1085115 : Nat := 185728520134542405424051

theorem tailTrace_1085115 : CollatzResearch.WordTrace tailWord_1085115 prefixEnd_1085115 185728520134542405424051 := by
  unfold tailWord_1085115
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577395463821152732800799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26384930309214101821867199 39577395463821152732800799)
  ·
    refine ⟨59366093195731729099201199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39577395463821152732800799 59366093195731729099201199)
    ·
      refine ⟨89049139793597593648801799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59366093195731729099201199 89049139793597593648801799)
      ·
        refine ⟨133573709690396390473202699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89049139793597593648801799 133573709690396390473202699)
        ·
          refine ⟨200360564535594585709804049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133573709690396390473202699 200360564535594585709804049)
          ·
            refine ⟨150270423401695939282353037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200360564535594585709804049 150270423401695939282353037)
            ·
              refine ⟨56351408775635977230882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150270423401695939282353037 56351408775635977230882389)
              ·
                refine ⟨660368071589484108174403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 56351408775635977230882389 660368071589484108174403)
                ·
                  refine ⟨990552107384226162261605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660368071589484108174403 990552107384226162261605)
                  ·
                    refine ⟨185728520134542405424051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 990552107384226162261605 185728520134542405424051)
                    ·
                      rfl

theorem cell23_1085115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 4].length) (baseStart_1085115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085115 prefixEnd_1085115 := by exact prefixLift 1085115
  have htrace : WordTrace (prefixWord ++ tailWord_1085115) baseStart_1085115 baseEnd_1085115 := by
    simpa [prefixWord, tailWord_1085115, baseEnd_1085115] using wordTrace_append hprefix tailTrace_1085115
  have hstable : (prefixWord ++ tailWord_1085115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085115).length < 2 ^ (prefixWord ++ tailWord_1085115).sum := by decide
  have hdescent : baseEnd_1085115 < baseStart_1085115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085128 : List Nat := [2, 1, 3, 1, 2, 2, 3, 3, 6]
def baseStart_1085128 : Nat := 118140960795 + 1085128 * 2 ^ 59
def prefixEnd_1085128 : Nat := 4983230072969 + 3 ^ 40 * 1085128 * 2
def baseEnd_1085128 : Nat := 61910248405792851712177

theorem tailTrace_1085128 : CollatzResearch.WordTrace tailWord_1085128 prefixEnd_1085128 61910248405792851712177 := by
  unfold tailWord_1085128
  simp only [CollatzResearch.WordTrace]
  refine ⟨19788934806387027976512019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26385246408516037302016025 19788934806387027976512019)
  ·
    refine ⟨29683402209580541964768029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19788934806387027976512019 29683402209580541964768029)
    ·
      refine ⟨11131275828592703236788011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29683402209580541964768029 11131275828592703236788011)
      ·
        refine ⟨16696913742889054855182017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11131275828592703236788011 16696913742889054855182017)
        ·
          refine ⟨12522685307166791141386513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16696913742889054855182017 12522685307166791141386513)
          ·
            refine ⟨9392013980375093356039885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12522685307166791141386513 9392013980375093356039885)
            ·
              refine ⟨3522005242640660008514957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9392013980375093356039885 3522005242640660008514957)
              ·
                refine ⟨1320751965990247503193109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3522005242640660008514957 1320751965990247503193109)
                ·
                  refine ⟨61910248405792851712177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1320751965990247503193109 61910248405792851712177)
                  ·
                    rfl

theorem cell23_1085128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 3, 6].length) (baseStart_1085128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085128 prefixEnd_1085128 := by exact prefixLift 1085128
  have htrace : WordTrace (prefixWord ++ tailWord_1085128) baseStart_1085128 baseEnd_1085128 := by
    simpa [prefixWord, tailWord_1085128, baseEnd_1085128] using wordTrace_append hprefix tailTrace_1085128
  have hstable : (prefixWord ++ tailWord_1085128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085128).length < 2 ^ (prefixWord ++ tailWord_1085128).sum := by decide
  have hdescent : baseEnd_1085128 < baseStart_1085128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085131 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6]
def baseStart_1085131 : Nat := 118140960795 + 1085131 * 2 ^ 59
def prefixEnd_1085131 : Nat := 4983230072969 + 3 ^ 40 * 1085131 * 2
def baseEnd_1085131 : Nat := 557193776094099153672079

theorem tailTrace_1085131 : CollatzResearch.WordTrace tailWord_1085131 prefixEnd_1085131 557193776094099153672079 := by
  unfold tailWord_1085131
  simp only [CollatzResearch.WordTrace]
  refine ⟨39577979031763187465383247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26385319354508791643588831 39577979031763187465383247)
  ·
    refine ⟨59366968547644781198074871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39577979031763187465383247 59366968547644781198074871)
    ·
      refine ⟨89050452821467171797112307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59366968547644781198074871 89050452821467171797112307)
      ·
        refine ⟨133575679232200757695668461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89050452821467171797112307 133575679232200757695668461)
        ·
          refine ⟨50090879712075284135875673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133575679232200757695668461 50090879712075284135875673)
          ·
            refine ⟨37568159784056463101906755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50090879712075284135875673 37568159784056463101906755)
            ·
              refine ⟨56352239676084694652860133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37568159784056463101906755 56352239676084694652860133)
              ·
                refine ⟨10566044939265880247411275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56352239676084694652860133 10566044939265880247411275)
                ·
                  refine ⟨15849067408898820371116913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10566044939265880247411275 15849067408898820371116913)
                  ·
                    refine ⟨11886800556674115278337685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15849067408898820371116913 11886800556674115278337685)
                    ·
                      refine ⟨557193776094099153672079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11886800556674115278337685 557193776094099153672079)
                      ·
                        rfl

theorem cell23_1085131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_1085131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085131 prefixEnd_1085131 := by exact prefixLift 1085131
  have htrace : WordTrace (prefixWord ++ tailWord_1085131) baseStart_1085131 baseEnd_1085131 := by
    simpa [prefixWord, tailWord_1085131, baseEnd_1085131] using wordTrace_append hprefix tailTrace_1085131
  have hstable : (prefixWord ++ tailWord_1085131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085131).length < 2 ^ (prefixWord ++ tailWord_1085131).sum := by decide
  have hdescent : baseEnd_1085131 < baseStart_1085131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085190 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1085190 : Nat := 118140960795 + 1085190 * 2 ^ 59
def prefixEnd_1085190 : Nat := 4983230072969 + 3 ^ 40 * 1085190 * 2
def baseEnd_1085190 : Nat := 557224071452714422834309

theorem tailTrace_1085190 : CollatzResearch.WordTrace tailWord_1085190 prefixEnd_1085190 557224071452714422834309 := by
  unfold tailWord_1085190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1236879091829670016930657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26386753959032960361187349 1236879091829670016930657)
  ·
    refine ⟨927659318872252512697993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1236879091829670016930657 927659318872252512697993)
    ·
      refine ⟨695744489154189384523495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927659318872252512697993 695744489154189384523495)
      ·
        refine ⟨1043616733731284076785243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 695744489154189384523495 1043616733731284076785243)
        ·
          refine ⟨1565425100596926115177865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1043616733731284076785243 1565425100596926115177865)
          ·
            refine ⟨1174068825447694586383399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1565425100596926115177865 1174068825447694586383399)
            ·
              refine ⟨1761103238171541879575099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174068825447694586383399 1761103238171541879575099)
              ·
                refine ⟨2641654857257312819362649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761103238171541879575099 2641654857257312819362649)
                ·
                  refine ⟨1981241142942984614521987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2641654857257312819362649 1981241142942984614521987)
                  ·
                    refine ⟨2971861714414476921782981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1981241142942984614521987 2971861714414476921782981)
                    ·
                      refine ⟨557224071452714422834309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2971861714414476921782981 557224071452714422834309)
                      ·
                        rfl

theorem cell23_1085190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1085190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085190 prefixEnd_1085190 := by exact prefixLift 1085190
  have htrace : WordTrace (prefixWord ++ tailWord_1085190) baseStart_1085190 baseEnd_1085190 := by
    simpa [prefixWord, tailWord_1085190, baseEnd_1085190] using wordTrace_append hprefix tailTrace_1085190
  have hstable : (prefixWord ++ tailWord_1085190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085190).length < 2 ^ (prefixWord ++ tailWord_1085190).sum := by decide
  have hdescent : baseEnd_1085190 < baseStart_1085190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085212 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_1085212 : Nat := 118140960795 + 1085212 * 2 ^ 59
def prefixEnd_1085212 : Nat := 4983230072969 + 3 ^ 40 * 1085212 * 2
def baseEnd_1085212 : Nat := 557235368027113336759207

theorem tailTrace_1085212 : CollatzResearch.WordTrace tailWord_1085212 prefixEnd_1085212 557235368027113336759207 := by
  unfold tailWord_1085212
  simp only [CollatzResearch.WordTrace]
  refine ⟨19790466672234869149540945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26387288896313158866054593 19790466672234869149540945)
  ·
    refine ⟨14842850004176151862155709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19790466672234869149540945 14842850004176151862155709)
    ·
      refine ⟨5566068751566056948308391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14842850004176151862155709 5566068751566056948308391)
      ·
        refine ⟨8349103127349085422462587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566068751566056948308391 8349103127349085422462587)
        ·
          refine ⟨12523654691023628133693881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8349103127349085422462587 12523654691023628133693881)
          ·
            refine ⟨9392741018267721100270411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12523654691023628133693881 9392741018267721100270411)
            ·
              refine ⟨14089111527401581650405617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9392741018267721100270411 14089111527401581650405617)
              ·
                refine ⟨10566833645551186237804213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14089111527401581650405617 10566833645551186237804213)
                ·
                  refine ⟨990640654270423709794145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10566833645551186237804213 990640654270423709794145)
                  ·
                    refine ⟨742980490702817782345609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990640654270423709794145 742980490702817782345609)
                    ·
                      refine ⟨557235368027113336759207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 742980490702817782345609 557235368027113336759207)
                      ·
                        rfl

theorem cell23_1085212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_1085212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085212 prefixEnd_1085212 := by exact prefixLift 1085212
  have htrace : WordTrace (prefixWord ++ tailWord_1085212) baseStart_1085212 baseEnd_1085212 := by
    simpa [prefixWord, tailWord_1085212, baseEnd_1085212] using wordTrace_append hprefix tailTrace_1085212
  have hstable : (prefixWord ++ tailWord_1085212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085212).length < 2 ^ (prefixWord ++ tailWord_1085212).sum := by decide
  have hdescent : baseEnd_1085212 < baseStart_1085212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085218 : List Nat := [3, 3, 1, 1, 2, 1, 12]
def baseStart_1085218 : Nat := 118140960795 + 1085218 * 2 ^ 59
def prefixEnd_1085218 : Nat := 4983230072969 + 3 ^ 40 * 1085218 * 2
def baseEnd_1085218 : Nat := 6879487023593090287459

theorem tailTrace_1085218 : CollatzResearch.WordTrace tailWord_1085218 prefixEnd_1085218 6879487023593090287459 := by
  unfold tailWord_1085218
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895288045612000330950077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26387434788298667549200205 9895288045612000330950077)
  ·
    refine ⟨3710733017104500124106279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9895288045612000330950077 3710733017104500124106279)
    ·
      refine ⟨5566099525656750186159419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3710733017104500124106279 5566099525656750186159419)
      ·
        refine ⟨8349149288485125279239129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566099525656750186159419 8349149288485125279239129)
        ·
          refine ⟨6261861966363843959429347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8349149288485125279239129 6261861966363843959429347)
          ·
            refine ⟨9392792949545765939144021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6261861966363843959429347 9392792949545765939144021)
            ·
              refine ⟨6879487023593090287459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 9392792949545765939144021 6879487023593090287459)
              ·
                rfl

theorem cell23_1085218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 12].length) (baseStart_1085218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085218 prefixEnd_1085218 := by exact prefixLift 1085218
  have htrace : WordTrace (prefixWord ++ tailWord_1085218) baseStart_1085218 baseEnd_1085218 := by
    simpa [prefixWord, tailWord_1085218, baseEnd_1085218] using wordTrace_append hprefix tailTrace_1085218
  have hstable : (prefixWord ++ tailWord_1085218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085218).length < 2 ^ (prefixWord ++ tailWord_1085218).sum := by decide
  have hdescent : baseEnd_1085218 < baseStart_1085218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085242 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4]
def baseStart_1085242 : Nat := 118140960795 + 1085242 * 2 ^ 59
def prefixEnd_1085242 : Nat := 4983230072969 + 3 ^ 40 * 1085242 * 2
def baseEnd_1085242 : Nat := 557250772446748219384069

theorem tailTrace_1085242 : CollatzResearch.WordTrace tailWord_1085242 prefixEnd_1085242 557250772446748219384069 := by
  unfold tailWord_1085242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895506883590263355668495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26388018356240702281782653 9895506883590263355668495)
  ·
    refine ⟨14843260325385395033502743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9895506883590263355668495 14843260325385395033502743)
    ·
      refine ⟨22264890488078092550254115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14843260325385395033502743 22264890488078092550254115)
      ·
        refine ⟨33397335732117138825381173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22264890488078092550254115 33397335732117138825381173)
        ·
          refine ⟨3131000224885981764879485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33397335732117138825381173 3131000224885981764879485)
          ·
            refine ⟨1174125084332243161829807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3131000224885981764879485 1174125084332243161829807)
            ·
              refine ⟨1761187626498364742744711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174125084332243161829807 1761187626498364742744711)
              ·
                refine ⟨2641781439747547114117067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761187626498364742744711 2641781439747547114117067)
                ·
                  refine ⟨3962672159621320671175601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641781439747547114117067 3962672159621320671175601)
                  ·
                    refine ⟨2972004119715990503381701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3962672159621320671175601 2972004119715990503381701)
                    ·
                      refine ⟨557250772446748219384069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2972004119715990503381701 557250772446748219384069)
                      ·
                        rfl

theorem cell23_1085242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 1, 2, 4].length) (baseStart_1085242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085242 prefixEnd_1085242 := by exact prefixLift 1085242
  have htrace : WordTrace (prefixWord ++ tailWord_1085242) baseStart_1085242 baseEnd_1085242 := by
    simpa [prefixWord, tailWord_1085242, baseEnd_1085242] using wordTrace_append hprefix tailTrace_1085242
  have hstable : (prefixWord ++ tailWord_1085242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085242).length < 2 ^ (prefixWord ++ tailWord_1085242).sum := by decide
  have hdescent : baseEnd_1085242 < baseStart_1085242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085258 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1085258 : Nat := 118140960795 + 1085258 * 2 ^ 59
def prefixEnd_1085258 : Nat := 4983230072969 + 3 ^ 40 * 1085258 * 2
def baseEnd_1085258 : Nat := 557258988137220156783995

theorem tailTrace_1085258 : CollatzResearch.WordTrace tailWord_1085258 prefixEnd_1085258 557258988137220156783995 := by
  unfold tailWord_1085258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9895652775575772038814107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26388407401535392103504285 9895652775575772038814107)
  ·
    refine ⟨14843479163363658058221161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9895652775575772038814107 14843479163363658058221161)
    ·
      refine ⟨11132609372522743543665871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14843479163363658058221161 11132609372522743543665871)
      ·
        refine ⟨16698914058784115315498807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11132609372522743543665871 16698914058784115315498807)
        ·
          refine ⟨25048371088176172973248211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16698914058784115315498807 25048371088176172973248211)
          ·
            refine ⟨37572556632264259459872317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25048371088176172973248211 37572556632264259459872317)
            ·
              refine ⟨14089708737099097297452119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37572556632264259459872317 14089708737099097297452119)
              ·
                refine ⟨21134563105648645946178179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14089708737099097297452119 21134563105648645946178179)
                ·
                  refine ⟨31701844658472968919267269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21134563105648645946178179 31701844658472968919267269)
                  ·
                    refine ⟨5944095873463681672362613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31701844658472968919267269 5944095873463681672362613)
                    ·
                      refine ⟨557258988137220156783995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5944095873463681672362613 557258988137220156783995)
                      ·
                        rfl

theorem cell23_1085258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1085258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085258 prefixEnd_1085258 := by exact prefixLift 1085258
  have htrace : WordTrace (prefixWord ++ tailWord_1085258) baseStart_1085258 baseEnd_1085258 := by
    simpa [prefixWord, tailWord_1085258, baseEnd_1085258] using wordTrace_append hprefix tailTrace_1085258
  have hstable : (prefixWord ++ tailWord_1085258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085258).length < 2 ^ (prefixWord ++ tailWord_1085258).sum := by decide
  have hdescent : baseEnd_1085258 < baseStart_1085258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085319 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_1085319 : Nat := 118140960795 + 1085319 * 2 ^ 59
def prefixEnd_1085319 : Nat := 4983230072969 + 3 ^ 40 * 1085319 * 2
def baseEnd_1085319 : Nat := 557290310457144418121215

theorem tailTrace_1085319 : CollatzResearch.WordTrace tailWord_1085319 prefixEnd_1085319 557290310457144418121215 := by
  unfold tailWord_1085319
  simp only [CollatzResearch.WordTrace]
  refine ⟨39584835955082095573227011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26389890636721397048818007 39584835955082095573227011)
  ·
    refine ⟨59377253932623143359840517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39584835955082095573227011 59377253932623143359840517)
    ·
      refine ⟨11133235112366839379970097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59377253932623143359840517 11133235112366839379970097)
      ·
        refine ⟨8349926334275129534977573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11133235112366839379970097 8349926334275129534977573)
        ·
          refine ⟨1565611187676586787808295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8349926334275129534977573 1565611187676586787808295)
          ·
            refine ⟨2348416781514880181712443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565611187676586787808295 2348416781514880181712443)
            ·
              refine ⟨3522625172272320272568665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2348416781514880181712443 3522625172272320272568665)
              ·
                refine ⟨2641968879204240204426499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3522625172272320272568665 2641968879204240204426499)
                ·
                  refine ⟨3962953318806360306639749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2641968879204240204426499 3962953318806360306639749)
                  ·
                    refine ⟨743053747276192557494953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3962953318806360306639749 743053747276192557494953)
                    ·
                      refine ⟨557290310457144418121215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743053747276192557494953 557290310457144418121215)
                      ·
                        rfl

theorem cell23_1085319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_1085319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085319 prefixEnd_1085319 := by exact prefixLift 1085319
  have htrace : WordTrace (prefixWord ++ tailWord_1085319) baseStart_1085319 baseEnd_1085319 := by
    simpa [prefixWord, tailWord_1085319, baseEnd_1085319] using wordTrace_append hprefix tailTrace_1085319
  have hstable : (prefixWord ++ tailWord_1085319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085319).length < 2 ^ (prefixWord ++ tailWord_1085319).sum := by decide
  have hdescent : baseEnd_1085319 < baseStart_1085319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085375 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_1085375 : Nat := 118140960795 + 1085375 * 2 ^ 59
def prefixEnd_1085375 : Nat := 4983230072969 + 3 ^ 40 * 1085375 * 2
def baseEnd_1085375 : Nat := 557319065373796199020957

theorem tailTrace_1085375 : CollatzResearch.WordTrace tailWord_1085375 prefixEnd_1085375 557319065373796199020957 := by
  unfold tailWord_1085375
  simp only [CollatzResearch.WordTrace]
  refine ⟨39586878442879217137265579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26391252295252811424843719 39586878442879217137265579)
  ·
    refine ⟨59380317664318825705898369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39586878442879217137265579 59380317664318825705898369)
    ·
      refine ⟨44535238248239119279423777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59380317664318825705898369 44535238248239119279423777)
      ·
        refine ⟨33401428686179339459567833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44535238248239119279423777 33401428686179339459567833)
        ·
          refine ⟨25051071514634504594675875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33401428686179339459567833 25051071514634504594675875)
          ·
            refine ⟨37576607271951756892013813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25051071514634504594675875 37576607271951756892013813)
            ·
              refine ⟨3522806931745477208626295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37576607271951756892013813 3522806931745477208626295)
              ·
                refine ⟨5284210397618215812939443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3522806931745477208626295 5284210397618215812939443)
                ·
                  refine ⟨7926315596427323719409165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5284210397618215812939443 7926315596427323719409165)
                  ·
                    refine ⟨2972368348660246394778437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7926315596427323719409165 2972368348660246394778437)
                    ·
                      refine ⟨557319065373796199020957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2972368348660246394778437 557319065373796199020957)
                      ·
                        rfl

theorem cell23_1085375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_1085375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085375 prefixEnd_1085375 := by exact prefixLift 1085375
  have htrace : WordTrace (prefixWord ++ tailWord_1085375) baseStart_1085375 baseEnd_1085375 := by
    simpa [prefixWord, tailWord_1085375, baseEnd_1085375] using wordTrace_append hprefix tailTrace_1085375
  have hstable : (prefixWord ++ tailWord_1085375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085375).length < 2 ^ (prefixWord ++ tailWord_1085375).sum := by decide
  have hdescent : baseEnd_1085375 < baseStart_1085375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085392 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2]
def baseStart_1085392 : Nat := 118140960795 + 1085392 * 2 ^ 59
def prefixEnd_1085392 : Nat := 4983230072969 + 3 ^ 40 * 1085392 * 2
def baseEnd_1085392 : Nat := 557327794544922632508379

theorem tailTrace_1085392 : CollatzResearch.WordTrace tailWord_1085392 prefixEnd_1085392 557327794544922632508379 := by
  unfold tailWord_1085392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19793749241908814520317215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26391665655878419360422953 19793749241908814520317215)
  ·
    refine ⟨29690623862863221780475823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19793749241908814520317215 29690623862863221780475823)
    ·
      refine ⟨44535935794294832670713735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29690623862863221780475823 44535935794294832670713735)
      ·
        refine ⟨66803903691442249006070603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44535935794294832670713735 66803903691442249006070603)
        ·
          refine ⟨100205855537163373509105905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66803903691442249006070603 100205855537163373509105905)
          ·
            refine ⟨75154391652872530131829429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100205855537163373509105905 75154391652872530131829429)
            ·
              refine ⟨7045724217456799699859009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75154391652872530131829429 7045724217456799699859009)
              ·
                refine ⟨5284293163092599774894257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7045724217456799699859009 5284293163092599774894257)
                ·
                  refine ⟨3963219872319449831170693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5284293163092599774894257 3963219872319449831170693)
                  ·
                    refine ⟨743103726059896843344505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3963219872319449831170693 743103726059896843344505)
                    ·
                      refine ⟨557327794544922632508379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743103726059896843344505 557327794544922632508379)
                      ·
                        rfl

theorem cell23_1085392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 2, 4, 2].length) (baseStart_1085392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085392 prefixEnd_1085392 := by exact prefixLift 1085392
  have htrace : WordTrace (prefixWord ++ tailWord_1085392) baseStart_1085392 baseEnd_1085392 := by
    simpa [prefixWord, tailWord_1085392, baseEnd_1085392] using wordTrace_append hprefix tailTrace_1085392
  have hstable : (prefixWord ++ tailWord_1085392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085392).length < 2 ^ (prefixWord ++ tailWord_1085392).sum := by decide
  have hdescent : baseEnd_1085392 < baseStart_1085392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085459 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 3]
def baseStart_1085459 : Nat := 118140960795 + 1085459 * 2 ^ 59
def prefixEnd_1085459 : Nat := 4983230072969 + 3 ^ 40 * 1085459 * 2
def baseEnd_1085459 : Nat := 557362197748773870370571

theorem tailTrace_1085459 : CollatzResearch.WordTrace tailWord_1085459 prefixEnd_1085459 557362197748773870370571 := by
  unfold tailWord_1085459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39589942174574899483323431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26393294783049932988882287 39589942174574899483323431)
  ·
    refine ⟨59384913261862349224985147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39589942174574899483323431 59384913261862349224985147)
    ·
      refine ⟨89077369892793523837477721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59384913261862349224985147 89077369892793523837477721)
      ·
        refine ⟨66808027419595142878108291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89077369892793523837477721 66808027419595142878108291)
        ·
          refine ⟨100212041129392714317162437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66808027419595142878108291 100212041129392714317162437)
          ·
            refine ⟨18789757711761133934467957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100212041129392714317162437 18789757711761133934467957)
            ·
              refine ⟨1761539785477606306356371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18789757711761133934467957 1761539785477606306356371)
              ·
                refine ⟨2642309678216409459534557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1761539785477606306356371 2642309678216409459534557)
                ·
                  refine ⟨990866129331153547325459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2642309678216409459534557 990866129331153547325459)
                  ·
                    refine ⟨1486299193996730320988189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 990866129331153547325459 1486299193996730320988189)
                    ·
                      refine ⟨557362197748773870370571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486299193996730320988189 557362197748773870370571)
                      ·
                        rfl

theorem cell23_1085459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_1085459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085459 prefixEnd_1085459 := by exact prefixLift 1085459
  have htrace : WordTrace (prefixWord ++ tailWord_1085459) baseStart_1085459 baseEnd_1085459 := by
    simpa [prefixWord, tailWord_1085459, baseEnd_1085459] using wordTrace_append hprefix tailTrace_1085459
  have hstable : (prefixWord ++ tailWord_1085459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085459).length < 2 ^ (prefixWord ++ tailWord_1085459).sum := by decide
  have hdescent : baseEnd_1085459 < baseStart_1085459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085465 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 4]
def baseStart_1085465 : Nat := 118140960795 + 1085465 * 2 ^ 59
def prefixEnd_1085465 : Nat := 4983230072969 + 3 ^ 40 * 1085465 * 2
def baseEnd_1085465 : Nat := 557365278632700846895543

theorem tailTrace_1085465 : CollatzResearch.WordTrace tailWord_1085465 prefixEnd_1085465 557365278632700846895543 := by
  unfold tailWord_1085465
  simp only [CollatzResearch.WordTrace]
  refine ⟨39590161012553162508041849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26393440675035441672027899 39590161012553162508041849)
  ·
    refine ⟨29692620759414871881031387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39590161012553162508041849 29692620759414871881031387)
    ·
      refine ⟨44538931139122307821547081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29692620759414871881031387 44538931139122307821547081)
      ·
        refine ⟨33404198354341730866160311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44538931139122307821547081 33404198354341730866160311)
        ·
          refine ⟨50106297531512596299240467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33404198354341730866160311 50106297531512596299240467)
          ·
            refine ⟨75159446297268894448860701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50106297531512596299240467 75159446297268894448860701)
            ·
              refine ⟨28184792361475835418322763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75159446297268894448860701 28184792361475835418322763)
              ·
                refine ⟨42277188542213753127484145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28184792361475835418322763 42277188542213753127484145)
                ·
                  refine ⟨31707891406660314845613109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42277188542213753127484145 31707891406660314845613109)
                  ·
                    refine ⟨2972614819374404516776229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31707891406660314845613109 2972614819374404516776229)
                    ·
                      refine ⟨557365278632700846895543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2972614819374404516776229 557365278632700846895543)
                      ·
                        rfl

theorem cell23_1085465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_1085465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085465 prefixEnd_1085465 := by exact prefixLift 1085465
  have htrace : WordTrace (prefixWord ++ tailWord_1085465) baseStart_1085465 baseEnd_1085465 := by
    simpa [prefixWord, tailWord_1085465, baseEnd_1085465] using wordTrace_append hprefix tailTrace_1085465
  have hstable : (prefixWord ++ tailWord_1085465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085465).length < 2 ^ (prefixWord ++ tailWord_1085465).sum := by decide
  have hdescent : baseEnd_1085465 < baseStart_1085465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085486 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_1085486 : Nat := 118140960795 + 1085486 * 2 ^ 59
def prefixEnd_1085486 : Nat := 4983230072969 + 3 ^ 40 * 1085486 * 2
def baseEnd_1085486 : Nat := 557376061726445264732947

theorem tailTrace_1085486 : CollatzResearch.WordTrace tailWord_1085486 prefixEnd_1085486 557376061726445264732947 := by
  unfold tailWord_1085486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948865868184635386819539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26393951296984722063037541 4948865868184635386819539)
  ·
    refine ⟨7423298802276953080229309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4948865868184635386819539 7423298802276953080229309)
    ·
      refine ⟨2783737050853857405085991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7423298802276953080229309 2783737050853857405085991)
      ·
        refine ⟨4175605576280786107628987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783737050853857405085991 4175605576280786107628987)
        ·
          refine ⟨6263408364421179161443481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175605576280786107628987 6263408364421179161443481)
          ·
            refine ⟨4697556273315884371082611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6263408364421179161443481 4697556273315884371082611)
            ·
              refine ⟨7046334409973826556623917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697556273315884371082611 7046334409973826556623917)
              ·
                refine ⟨2642375403740184958733969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7046334409973826556623917 2642375403740184958733969)
                ·
                  refine ⟨1981781552805138719050477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2642375403740184958733969 1981781552805138719050477)
                  ·
                    refine ⟨743168082301927019643929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1981781552805138719050477 743168082301927019643929)
                    ·
                      refine ⟨557376061726445264732947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743168082301927019643929 557376061726445264732947)
                      ·
                        rfl

theorem cell23_1085486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_1085486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085486 prefixEnd_1085486 := by exact prefixLift 1085486
  have htrace : WordTrace (prefixWord ++ tailWord_1085486) baseStart_1085486 baseEnd_1085486 := by
    simpa [prefixWord, tailWord_1085486, baseEnd_1085486] using wordTrace_append hprefix tailTrace_1085486
  have hstable : (prefixWord ++ tailWord_1085486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085486).length < 2 ^ (prefixWord ++ tailWord_1085486).sum := by decide
  have hdescent : baseEnd_1085486 < baseStart_1085486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085496 : List Nat := [2, 1, 2, 1, 6, 1, 3, 1, 1, 5]
def baseStart_1085496 : Nat := 118140960795 + 1085496 * 2 ^ 59
def prefixEnd_1085496 : Nat := 4983230072969 + 3 ^ 40 * 1085496 * 2
def baseEnd_1085496 : Nat := 185793732177663408535967

theorem tailTrace_1085496 : CollatzResearch.WordTrace tailWord_1085496 prefixEnd_1085496 185793732177663408535967 := by
  unfold tailWord_1085496
  simp only [CollatzResearch.WordTrace]
  refine ⟨19795645837720427401210171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26394194450293903201613561 19795645837720427401210171)
  ·
    refine ⟨29693468756580641101815257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19795645837720427401210171 29693468756580641101815257)
    ·
      refine ⟨22270101567435480826361443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29693468756580641101815257 22270101567435480826361443)
      ·
        refine ⟨33405152351153221239542165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22270101567435480826361443 33405152351153221239542165)
        ·
          refine ⟨1565866516460307245603539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33405152351153221239542165 1565866516460307245603539)
          ·
            refine ⟨2348799774690460868405309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1565866516460307245603539 2348799774690460868405309)
            ·
              refine ⟨880799915508922825651991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2348799774690460868405309 880799915508922825651991)
              ·
                refine ⟨1321199873263384238477987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880799915508922825651991 1321199873263384238477987)
                ·
                  refine ⟨1981799809895076357716981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1321199873263384238477987 1981799809895076357716981)
                  ·
                    refine ⟨185793732177663408535967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1981799809895076357716981 185793732177663408535967)
                    ·
                      rfl

theorem cell23_1085496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_1085496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085496 prefixEnd_1085496 := by exact prefixLift 1085496
  have htrace : WordTrace (prefixWord ++ tailWord_1085496) baseStart_1085496 baseEnd_1085496 := by
    simpa [prefixWord, tailWord_1085496, baseEnd_1085496] using wordTrace_append hprefix tailTrace_1085496
  have hstable : (prefixWord ++ tailWord_1085496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085496).length < 2 ^ (prefixWord ++ tailWord_1085496).sum := by decide
  have hdescent : baseEnd_1085496 < baseStart_1085496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085499 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 5, 2, 2]
def baseStart_1085499 : Nat := 118140960795 + 1085499 * 2 ^ 59
def prefixEnd_1085499 : Nat := 4983230072969 + 3 ^ 40 * 1085499 * 2
def baseEnd_1085499 : Nat := 557382736974953713870387

theorem tailTrace_1085499 : CollatzResearch.WordTrace tailWord_1085499 prefixEnd_1085499 557382736974953713870387 := by
  unfold tailWord_1085499
  simp only [CollatzResearch.WordTrace]
  refine ⟨39591401094429986314779551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26394267396286657543186367 39591401094429986314779551)
  ·
    refine ⟨59387101641644979472169327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39591401094429986314779551 59387101641644979472169327)
    ·
      refine ⟨89080652462467469208253991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59387101641644979472169327 89080652462467469208253991)
      ·
        refine ⟨133620978693701203812380987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89080652462467469208253991 133620978693701203812380987)
        ·
          refine ⟨200431468040551805718571481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133620978693701203812380987 200431468040551805718571481)
          ·
            refine ⟨150323601030413854288928611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200431468040551805718571481 150323601030413854288928611)
            ·
              refine ⟨225485401545620781433392917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150323601030413854288928611 225485401545620781433392917)
              ·
                refine ⟨10569628197450974129690293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225485401545620781433392917 10569628197450974129690293)
                ·
                  refine ⟨990902643511028824658465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10569628197450974129690293 990902643511028824658465)
                  ·
                    refine ⟨743176982633271618493849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990902643511028824658465 743176982633271618493849)
                    ·
                      refine ⟨557382736974953713870387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743176982633271618493849 557382736974953713870387)
                      ·
                        rfl

theorem cell23_1085499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 5, 2, 2].length) (baseStart_1085499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085499 prefixEnd_1085499 := by exact prefixLift 1085499
  have htrace : WordTrace (prefixWord ++ tailWord_1085499) baseStart_1085499 baseEnd_1085499 := by
    simpa [prefixWord, tailWord_1085499, baseEnd_1085499] using wordTrace_append hprefix tailTrace_1085499
  have hstable : (prefixWord ++ tailWord_1085499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085499).length < 2 ^ (prefixWord ++ tailWord_1085499).sum := by decide
  have hdescent : baseEnd_1085499 < baseStart_1085499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085510 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_1085510 : Nat := 118140960795 + 1085510 * 2 ^ 59
def prefixEnd_1085510 : Nat := 4983230072969 + 3 ^ 40 * 1085510 * 2
def baseEnd_1085510 : Nat := 557388385262153170832837

theorem tailTrace_1085510 : CollatzResearch.WordTrace tailWord_1085510 prefixEnd_1085510 557388385262153170832837 := by
  unfold tailWord_1085510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1237243821793441724794687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26394534864926756795619989 1237243821793441724794687)
  ·
    refine ⟨1855865732690162587192031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1237243821793441724794687 1855865732690162587192031)
    ·
      refine ⟨2783798599035243880788047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1855865732690162587192031 2783798599035243880788047)
      ·
        refine ⟨4175697898552865821182071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2783798599035243880788047 4175697898552865821182071)
        ·
          refine ⟨6263546847829298731773107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175697898552865821182071 6263546847829298731773107)
          ·
            refine ⟨9395320271743948097659661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263546847829298731773107 9395320271743948097659661)
            ·
              refine ⟨3523245101903980536622373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9395320271743948097659661 3523245101903980536622373)
              ·
                refine ⟨660608456606996350616695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3523245101903980536622373 660608456606996350616695)
                ·
                  refine ⟨990912684910494525925043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660608456606996350616695 990912684910494525925043)
                  ·
                    refine ⟨1486369027365741788887565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 990912684910494525925043 1486369027365741788887565)
                    ·
                      refine ⟨557388385262153170832837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486369027365741788887565 557388385262153170832837)
                      ·
                        rfl

theorem cell23_1085510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_1085510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085510 prefixEnd_1085510 := by exact prefixLift 1085510
  have htrace : WordTrace (prefixWord ++ tailWord_1085510) baseStart_1085510 baseEnd_1085510 := by
    simpa [prefixWord, tailWord_1085510, baseEnd_1085510] using wordTrace_append hprefix tailTrace_1085510
  have hstable : (prefixWord ++ tailWord_1085510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085510).length < 2 ^ (prefixWord ++ tailWord_1085510).sum := by decide
  have hdescent : baseEnd_1085510 < baseStart_1085510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085526 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1085526 : Nat := 118140960795 + 1085526 * 2 ^ 59
def prefixEnd_1085526 : Nat := 4983230072969 + 3 ^ 40 * 1085526 * 2
def baseEnd_1085526 : Nat := 185798866984208369410921

theorem tailTrace_1085526 : CollatzResearch.WordTrace tailWord_1085526 prefixEnd_1085526 185798866984208369410921 := by
  unfold tailWord_1085526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474524116583260620375777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26394923910221446617341621 2474524116583260620375777)
  ·
    refine ⟨1855893087437445465281833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2474524116583260620375777 1855893087437445465281833)
    ·
      refine ⟨1391919815578084098961375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1855893087437445465281833 1391919815578084098961375)
      ·
        refine ⟨2087879723367126148442063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391919815578084098961375 2087879723367126148442063)
        ·
          refine ⟨3131819585050689222663095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087879723367126148442063 3131819585050689222663095)
          ·
            refine ⟨4697729377576033833994643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131819585050689222663095 4697729377576033833994643)
            ·
              refine ⟨7046594066364050750991965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697729377576033833994643 7046594066364050750991965)
              ·
                refine ⟨2642472774886519031621987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7046594066364050750991965 2642472774886519031621987)
                ·
                  refine ⟨3963709162329778547432981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642472774886519031621987 3963709162329778547432981)
                  ·
                    refine ⟨185798866984208369410921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3963709162329778547432981 185798866984208369410921)
                    ·
                      rfl

theorem cell23_1085526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1085526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085526 prefixEnd_1085526 := by exact prefixLift 1085526
  have htrace : WordTrace (prefixWord ++ tailWord_1085526) baseStart_1085526 baseEnd_1085526 := by
    simpa [prefixWord, tailWord_1085526, baseEnd_1085526] using wordTrace_append hprefix tailTrace_1085526
  have hstable : (prefixWord ++ tailWord_1085526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085526).length < 2 ^ (prefixWord ++ tailWord_1085526).sum := by decide
  have hdescent : baseEnd_1085526 < baseStart_1085526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085533 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_1085533 : Nat := 118140960795 + 1085533 * 2 ^ 59
def prefixEnd_1085533 : Nat := 4983230072969 + 3 ^ 40 * 1085533 * 2
def baseEnd_1085533 : Nat := 557400195317206580845231

theorem tailTrace_1085533 : CollatzResearch.WordTrace tailWord_1085533 prefixEnd_1085533 557400195317206580845231 := by
  unfold tailWord_1085533
  simp only [CollatzResearch.WordTrace]
  refine ⟨39592641176306810121517253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26395094117537873414344835 39592641176306810121517253)
  ·
    refine ⟨7423620220557526897784485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39592641176306810121517253 7423620220557526897784485)
    ·
      refine ⟨1391928791354536293334591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7423620220557526897784485 1391928791354536293334591)
      ·
        refine ⟨2087893187031804440001887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1391928791354536293334591 2087893187031804440001887)
        ·
          refine ⟨3131839780547706660002831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2087893187031804440001887 3131839780547706660002831)
          ·
            refine ⟨4697759670821559990004247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3131839780547706660002831 4697759670821559990004247)
            ·
              refine ⟨7046639506232339985006371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4697759670821559990004247 7046639506232339985006371)
              ·
                refine ⟨10569959259348509977509557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7046639506232339985006371 10569959259348509977509557)
                ·
                  refine ⟨990933680563922810391521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10569959259348509977509557 990933680563922810391521)
                  ·
                    refine ⟨743200260422942107793641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990933680563922810391521 743200260422942107793641)
                    ·
                      refine ⟨557400195317206580845231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743200260422942107793641 557400195317206580845231)
                      ·
                        rfl

theorem cell23_1085533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_1085533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085533 prefixEnd_1085533 := by exact prefixLift 1085533
  have htrace : WordTrace (prefixWord ++ tailWord_1085533) baseStart_1085533 baseEnd_1085533 := by
    simpa [prefixWord, tailWord_1085533, baseEnd_1085533] using wordTrace_append hprefix tailTrace_1085533
  have hstable : (prefixWord ++ tailWord_1085533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085533).length < 2 ^ (prefixWord ++ tailWord_1085533).sum := by decide
  have hdescent : baseEnd_1085533 < baseStart_1085533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085549 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_1085549 : Nat := 118140960795 + 1085549 * 2 ^ 59
def prefixEnd_1085549 : Nat := 4983230072969 + 3 ^ 40 * 1085549 * 2
def baseEnd_1085549 : Nat := 557408411007678518245157

theorem tailTrace_1085549 : CollatzResearch.WordTrace tailWord_1085549 prefixEnd_1085549 557408411007678518245157 := by
  unfold tailWord_1085549
  simp only [CollatzResearch.WordTrace]
  refine ⟨39593224744248844854099701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26395483162832563236066467 39593224744248844854099701)
  ·
    refine ⟨3711864819773329205071847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39593224744248844854099701 3711864819773329205071847)
    ·
      refine ⟨5567797229659993807607771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711864819773329205071847 5567797229659993807607771)
      ·
        refine ⟨8351695844489990711411657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5567797229659993807607771 8351695844489990711411657)
        ·
          refine ⟨6263771883367493033558743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8351695844489990711411657 6263771883367493033558743)
          ·
            refine ⟨9395657825051239550338115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263771883367493033558743 9395657825051239550338115)
            ·
              refine ⟨14093486737576859325507173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9395657825051239550338115 14093486737576859325507173)
              ·
                refine ⟨2642528763295661123532595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14093486737576859325507173 2642528763295661123532595)
                ·
                  refine ⟨3963793144943491685298893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2642528763295661123532595 3963793144943491685298893)
                  ·
                    refine ⟨1486422429353809381987085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3963793144943491685298893 1486422429353809381987085)
                    ·
                      refine ⟨557408411007678518245157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486422429353809381987085 557408411007678518245157)
                      ·
                        rfl

theorem cell23_1085549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_1085549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085549 prefixEnd_1085549 := by exact prefixLift 1085549
  have htrace : WordTrace (prefixWord ++ tailWord_1085549) baseStart_1085549 baseEnd_1085549 := by
    simpa [prefixWord, tailWord_1085549, baseEnd_1085549] using wordTrace_append hprefix tailTrace_1085549
  have hstable : (prefixWord ++ tailWord_1085549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085549).length < 2 ^ (prefixWord ++ tailWord_1085549).sum := by decide
  have hdescent : baseEnd_1085549 < baseStart_1085549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085550 : List Nat := [4, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_1085550 : Nat := 118140960795 + 1085550 * 2 ^ 59
def prefixEnd_1085550 : Nat := 4983230072969 + 3 ^ 40 * 1085550 * 2
def baseEnd_1085550 : Nat := 557408924488333014332653

theorem tailTrace_1085550 : CollatzResearch.WordTrace tailWord_1085550 prefixEnd_1085550 557408924488333014332653 := by
  unfold tailWord_1085550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4949157652155652753110763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26395507478163481349924069 4949157652155652753110763)
  ·
    refine ⟨7423736478233479129666145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4949157652155652753110763 7423736478233479129666145)
    ·
      refine ⟨5567802358675109347249609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7423736478233479129666145 5567802358675109347249609)
      ·
        refine ⟨4175851769006332010437207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5567802358675109347249609 4175851769006332010437207)
        ·
          refine ⟨6263777653509498015655811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4175851769006332010437207 6263777653509498015655811)
          ·
            refine ⟨9395666480264247023483717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6263777653509498015655811 9395666480264247023483717)
            ·
              refine ⟨1761687465049546316903197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9395666480264247023483717 1761687465049546316903197)
              ·
                refine ⟨660632799393579868838699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1761687465049546316903197 660632799393579868838699)
                ·
                  refine ⟨990949199090369803258049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660632799393579868838699 990949199090369803258049)
                  ·
                    refine ⟨743211899317777352443537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 990949199090369803258049 743211899317777352443537)
                    ·
                      refine ⟨557408924488333014332653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743211899317777352443537 557408924488333014332653)
                      ·
                        rfl

theorem cell23_1085550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_1085550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085550 prefixEnd_1085550 := by exact prefixLift 1085550
  have htrace : WordTrace (prefixWord ++ tailWord_1085550) baseStart_1085550 baseEnd_1085550 := by
    simpa [prefixWord, tailWord_1085550, baseEnd_1085550] using wordTrace_append hprefix tailTrace_1085550
  have hstable : (prefixWord ++ tailWord_1085550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085550).length < 2 ^ (prefixWord ++ tailWord_1085550).sum := by decide
  have hdescent : baseEnd_1085550 < baseStart_1085550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085590 : List Nat := [5, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1085590 : Nat := 118140960795 + 1085590 * 2 ^ 59
def prefixEnd_1085590 : Nat := 4983230072969 + 3 ^ 40 * 1085590 * 2
def baseEnd_1085590 : Nat := 20645535693130105845647

theorem tailTrace_1085590 : CollatzResearch.WordTrace tailWord_1085590 prefixEnd_1085590 20645535693130105845647 := by
  unfold tailWord_1085590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474670008568769303521389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26396480091400205904228149 2474670008568769303521389)
  ·
    refine ⟨928001253213288488820521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2474670008568769303521389 928001253213288488820521)
    ·
      refine ⟨696000939909966366615391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 928001253213288488820521 696000939909966366615391)
      ·
        refine ⟨1044001409864949549923087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 696000939909966366615391 1044001409864949549923087)
        ·
          refine ⟨1566002114797424324884631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044001409864949549923087 1566002114797424324884631)
          ·
            refine ⟨2349003172196136487326947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566002114797424324884631 2349003172196136487326947)
            ·
              refine ⟨3523504758294204730990421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349003172196136487326947 3523504758294204730990421)
              ·
                refine ⟨20645535693130105845647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3523504758294204730990421 20645535693130105845647)
                ·
                  rfl

theorem cell23_1085590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1085590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085590 prefixEnd_1085590 := by exact prefixLift 1085590
  have htrace : WordTrace (prefixWord ++ tailWord_1085590) baseStart_1085590 baseEnd_1085590 := by
    simpa [prefixWord, tailWord_1085590, baseEnd_1085590] using wordTrace_append hprefix tailTrace_1085590
  have hstable : (prefixWord ++ tailWord_1085590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085590).length < 2 ^ (prefixWord ++ tailWord_1085590).sum := by decide
  have hdescent : baseEnd_1085590 < baseStart_1085590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085634 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1085634 : Nat := 118140960795 + 1085634 * 2 ^ 59
def prefixEnd_1085634 : Nat := 4983230072969 + 3 ^ 40 * 1085634 * 2
def baseEnd_1085634 : Nat := 557452056863310685682267

theorem tailTrace_1085634 : CollatzResearch.WordTrace tailWord_1085634 prefixEnd_1085634 557452056863310685682267 := by
  unfold tailWord_1085634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9899081237235226092735989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26397549965960602913962637 9899081237235226092735989)
  ·
    refine ⟨928038865990802446193999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9899081237235226092735989 928038865990802446193999)
    ·
      refine ⟨1392058298986203669290999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928038865990802446193999 1392058298986203669290999)
      ·
        refine ⟨2088087448479305503936499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392058298986203669290999 2088087448479305503936499)
        ·
          refine ⟨3132131172718958255904749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088087448479305503936499 3132131172718958255904749)
          ·
            refine ⟨1174549189769609345964281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3132131172718958255904749 1174549189769609345964281)
            ·
              refine ⟨880911892327207009473211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1174549189769609345964281 880911892327207009473211)
              ·
                refine ⟨1321367838490810514209817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 880911892327207009473211 1321367838490810514209817)
                ·
                  refine ⟨991025878868107885657363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1321367838490810514209817 991025878868107885657363)
                  ·
                    refine ⟨1486538818302161828486045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 991025878868107885657363 1486538818302161828486045)
                    ·
                      refine ⟨557452056863310685682267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486538818302161828486045 557452056863310685682267)
                      ·
                        rfl

theorem cell23_1085634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1085634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085634 prefixEnd_1085634 := by exact prefixLift 1085634
  have htrace : WordTrace (prefixWord ++ tailWord_1085634) baseStart_1085634 baseEnd_1085634 := by
    simpa [prefixWord, tailWord_1085634, baseEnd_1085634] using wordTrace_append hprefix tailTrace_1085634
  have hstable : (prefixWord ++ tailWord_1085634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085634).length < 2 ^ (prefixWord ++ tailWord_1085634).sum := by decide
  have hdescent : baseEnd_1085634 < baseStart_1085634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085669 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1085669 : Nat := 118140960795 + 1085669 * 2 ^ 59
def prefixEnd_1085669 : Nat := 4983230072969 + 3 ^ 40 * 1085669 * 2
def baseEnd_1085669 : Nat := 557470028686218048744605

theorem tailTrace_1085669 : CollatzResearch.WordTrace tailWord_1085669 prefixEnd_1085669 557470028686218048744605 := by
  unfold tailWord_1085669
  simp only [CollatzResearch.WordTrace]
  refine ⟨39597601503814105348468061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26398401002542736898978707 39597601503814105348468061)
  ·
    refine ⟨14849100563930289505675523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39597601503814105348468061 14849100563930289505675523)
    ·
      refine ⟨22273650845895434258513285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14849100563930289505675523 22273650845895434258513285)
      ·
        refine ⟨4176309533605393923471241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22273650845895434258513285 4176309533605393923471241)
        ·
          refine ⟨3132232150204045442603431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4176309533605393923471241 3132232150204045442603431)
          ·
            refine ⟨4698348225306068163905147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132232150204045442603431 4698348225306068163905147)
            ·
              refine ⟨7047522337959102245857721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4698348225306068163905147 7047522337959102245857721)
              ·
                refine ⟨5285641753469326684393291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047522337959102245857721 5285641753469326684393291)
                ·
                  refine ⟨7928462630203990026589937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285641753469326684393291 7928462630203990026589937)
                  ·
                    refine ⟨5946346972652992519942453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7928462630203990026589937 5946346972652992519942453)
                    ·
                      refine ⟨557470028686218048744605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5946346972652992519942453 557470028686218048744605)
                      ·
                        rfl

theorem cell23_1085669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1085669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085669 prefixEnd_1085669 := by exact prefixLift 1085669
  have htrace : WordTrace (prefixWord ++ tailWord_1085669) baseStart_1085669 baseEnd_1085669 := by
    simpa [prefixWord, tailWord_1085669, baseEnd_1085669] using wordTrace_append hprefix tailTrace_1085669
  have hstable : (prefixWord ++ tailWord_1085669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085669).length < 2 ^ (prefixWord ++ tailWord_1085669).sum := by decide
  have hdescent : baseEnd_1085669 < baseStart_1085669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085699 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3]
def baseStart_1085699 : Nat := 118140960795 + 1085699 * 2 ^ 59
def prefixEnd_1085699 : Nat := 4983230072969 + 3 ^ 40 * 1085699 * 2
def baseEnd_1085699 : Nat := 557485433105852931369467

theorem tailTrace_1085699 : CollatzResearch.WordTrace tailWord_1085699 prefixEnd_1085699 557485433105852931369467 := by
  unfold tailWord_1085699
  simp only [CollatzResearch.WordTrace]
  refine ⟨39598695693705420472060151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26399130462470280314706767 39598695693705420472060151)
  ·
    refine ⟨59398043540558130708090227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39598695693705420472060151 59398043540558130708090227)
    ·
      refine ⟨89097065310837196062135341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59398043540558130708090227 89097065310837196062135341)
      ·
        refine ⟨33411399491563948523300753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89097065310837196062135341 33411399491563948523300753)
        ·
          refine ⟨25058549618672961392475565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33411399491563948523300753 25058549618672961392475565)
          ·
            refine ⟨9396956107002360522178337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25058549618672961392475565 9396956107002360522178337)
            ·
              refine ⟨7047717080251770391633753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9396956107002360522178337 7047717080251770391633753)
              ·
                refine ⟨5285787810188827793725315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7047717080251770391633753 5285787810188827793725315)
                ·
                  refine ⟨7928681715283241690587973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5285787810188827793725315 7928681715283241690587973)
                  ·
                    refine ⟨1486627821615607816985245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7928681715283241690587973 1486627821615607816985245)
                    ·
                      refine ⟨557485433105852931369467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486627821615607816985245 557485433105852931369467)
                      ·
                        rfl

theorem cell23_1085699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_1085699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085699 prefixEnd_1085699 := by exact prefixLift 1085699
  have htrace : WordTrace (prefixWord ++ tailWord_1085699) baseStart_1085699 baseEnd_1085699 := by
    simpa [prefixWord, tailWord_1085699, baseEnd_1085699] using wordTrace_append hprefix tailTrace_1085699
  have hstable : (prefixWord ++ tailWord_1085699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085699).length < 2 ^ (prefixWord ++ tailWord_1085699).sum := by decide
  have hdescent : baseEnd_1085699 < baseStart_1085699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085736 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 8]
def baseStart_1085736 : Nat := 118140960795 + 1085736 * 2 ^ 59
def prefixEnd_1085736 : Nat := 4983230072969 + 3 ^ 40 * 1085736 * 2
def baseEnd_1085736 : Nat := 61944936876674365178533

theorem tailTrace_1085736 : CollatzResearch.WordTrace tailWord_1085736 prefixEnd_1085736 61944936876674365178533 := by
  unfold tailWord_1085736
  simp only [CollatzResearch.WordTrace]
  refine ⟨19800022597285687895578531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26400030129714250527438041 19800022597285687895578531)
  ·
    refine ⟨29700033895928531843367797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19800022597285687895578531 29700033895928531843367797)
    ·
      refine ⟨2784378177743299860315731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 29700033895928531843367797 2784378177743299860315731)
      ·
        refine ⟨4176567266614949790473597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2784378177743299860315731 4176567266614949790473597)
        ·
          refine ⟨1566212724980606171427599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4176567266614949790473597 1566212724980606171427599)
          ·
            refine ⟨2349319087470909257141399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1566212724980606171427599 2349319087470909257141399)
            ·
              refine ⟨3523978631206363885712099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349319087470909257141399 3523978631206363885712099)
              ·
                refine ⟨5285967946809545828568149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3523978631206363885712099 5285967946809545828568149)
                ·
                  refine ⟨61944936876674365178533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5285967946809545828568149 61944936876674365178533)
                  ·
                    rfl

theorem cell23_1085736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 8].length) (baseStart_1085736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085736 prefixEnd_1085736 := by exact prefixLift 1085736
  have htrace : WordTrace (prefixWord ++ tailWord_1085736) baseStart_1085736 baseEnd_1085736 := by
    simpa [prefixWord, tailWord_1085736, baseEnd_1085736] using wordTrace_append hprefix tailTrace_1085736
  have hstable : (prefixWord ++ tailWord_1085736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085736).length < 2 ^ (prefixWord ++ tailWord_1085736).sum := by decide
  have hdescent : baseEnd_1085736 < baseStart_1085736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085753 : List Nat := [1, 2, 1, 6, 1, 2, 3, 1, 6]
def baseStart_1085753 : Nat := 118140960795 + 1085753 * 2 ^ 59
def prefixEnd_1085753 : Nat := 4983230072969 + 3 ^ 40 * 1085753 * 2
def baseEnd_1085753 : Nat := 61945906784577302232691

theorem tailTrace_1085753 : CollatzResearch.WordTrace tailWord_1085753 prefixEnd_1085753 61945906784577302232691 := by
  unfold tailWord_1085753
  simp only [CollatzResearch.WordTrace]
  refine ⟨39600665235509787694525913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26400443490339858463017275 39600665235509787694525913)
  ·
    refine ⟨29700498926632340770894435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39600665235509787694525913 29700498926632340770894435)
    ·
      refine ⟨44550748389948511156341653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29700498926632340770894435 44550748389948511156341653)
      ·
        refine ⟨2088316330778836460453515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44550748389948511156341653 2088316330778836460453515)
        ·
          refine ⟨3132474496168254690680273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088316330778836460453515 3132474496168254690680273)
          ·
            refine ⟨2349355872126191018010205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3132474496168254690680273 2349355872126191018010205)
            ·
              refine ⟨881008452047321631753827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2349355872126191018010205 881008452047321631753827)
              ·
                refine ⟨1321512678070982447630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881008452047321631753827 1321512678070982447630741)
                ·
                  refine ⟨61945906784577302232691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1321512678070982447630741 61945906784577302232691)
                  ·
                    rfl

theorem cell23_1085753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 6].length) (baseStart_1085753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085753 prefixEnd_1085753 := by exact prefixLift 1085753
  have htrace : WordTrace (prefixWord ++ tailWord_1085753) baseStart_1085753 baseEnd_1085753 := by
    simpa [prefixWord, tailWord_1085753, baseEnd_1085753] using wordTrace_append hprefix tailTrace_1085753
  have hstable : (prefixWord ++ tailWord_1085753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085753).length < 2 ^ (prefixWord ++ tailWord_1085753).sum := by decide
  have hdescent : baseEnd_1085753 < baseStart_1085753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085756 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_1085756 : Nat := 118140960795 + 1085756 * 2 ^ 59
def prefixEnd_1085756 : Nat := 4983230072969 + 3 ^ 40 * 1085756 * 2
def baseEnd_1085756 : Nat := 557514701503159208356705

theorem tailTrace_1085756 : CollatzResearch.WordTrace tailWord_1085756 prefixEnd_1085756 557514701503159208356705 := by
  unfold tailWord_1085756
  simp only [CollatzResearch.WordTrace]
  refine ⟨19800387327249459603442561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26400516436332612804590081 19800387327249459603442561)
  ·
    refine ⟨14850290495437094702581921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19800387327249459603442561 14850290495437094702581921)
    ·
      refine ⟨11137717871577821026936441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14850290495437094702581921 11137717871577821026936441)
      ·
        refine ⟨8353288403683365770202331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11137717871577821026936441 8353288403683365770202331)
        ·
          refine ⟨12529932605525048655303497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353288403683365770202331 12529932605525048655303497)
          ·
            refine ⟨9397449454143786491477623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12529932605525048655303497 9397449454143786491477623)
            ·
              refine ⟨14096174181215679737216435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397449454143786491477623 14096174181215679737216435)
              ·
                refine ⟨21144261271823519605824653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14096174181215679737216435 21144261271823519605824653)
                ·
                  refine ⟨7929097976933819852184245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21144261271823519605824653 7929097976933819852184245)
                  ·
                    refine ⟨743352935337545611142273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7929097976933819852184245 743352935337545611142273)
                    ·
                      refine ⟨557514701503159208356705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743352935337545611142273 557514701503159208356705)
                      ·
                        rfl

theorem cell23_1085756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_1085756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085756 prefixEnd_1085756 := by exact prefixLift 1085756
  have htrace : WordTrace (prefixWord ++ tailWord_1085756) baseStart_1085756 baseEnd_1085756 := by
    simpa [prefixWord, tailWord_1085756, baseEnd_1085756] using wordTrace_append hprefix tailTrace_1085756
  have hstable : (prefixWord ++ tailWord_1085756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085756).length < 2 ^ (prefixWord ++ tailWord_1085756).sum := by decide
  have hdescent : baseEnd_1085756 < baseStart_1085756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085796 : List Nat := [2, 3, 1, 1, 3, 1, 1, 3, 4, 4]
def baseStart_1085796 : Nat := 118140960795 + 1085796 * 2 ^ 59
def prefixEnd_1085796 : Nat := 4983230072969 + 3 ^ 40 * 1085796 * 2
def baseEnd_1085796 : Nat := 185845080243113017285507

theorem tailTrace_1085796 : CollatzResearch.WordTrace tailWord_1085796 prefixEnd_1085796 185845080243113017285507 := by
  unfold tailWord_1085796
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801116787177003019170621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26401489049569337358894161 19801116787177003019170621)
  ·
    refine ⟨7425418795191376132188983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19801116787177003019170621 7425418795191376132188983)
    ·
      refine ⟨11138128192787064198283475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7425418795191376132188983 11138128192787064198283475)
      ·
        refine ⟨16707192289180596297425213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11138128192787064198283475 16707192289180596297425213)
        ·
          refine ⟨6265197108442723611534455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16707192289180596297425213 6265197108442723611534455)
          ·
            refine ⟨9397795662664085417301683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6265197108442723611534455 9397795662664085417301683)
            ·
              refine ⟨14096693493996128125952525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9397795662664085417301683 14096693493996128125952525)
              ·
                refine ⟨5286260060248548047232197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14096693493996128125952525 5286260060248548047232197)
                ·
                  refine ⟨991173761296602758856037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5286260060248548047232197 991173761296602758856037)
                  ·
                    refine ⟨185845080243113017285507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991173761296602758856037 185845080243113017285507)
                    ·
                      rfl

theorem cell23_1085796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_1085796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085796 prefixEnd_1085796 := by exact prefixLift 1085796
  have htrace : WordTrace (prefixWord ++ tailWord_1085796) baseStart_1085796 baseEnd_1085796 := by
    simpa [prefixWord, tailWord_1085796, baseEnd_1085796] using wordTrace_append hprefix tailTrace_1085796
  have hstable : (prefixWord ++ tailWord_1085796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085796).length < 2 ^ (prefixWord ++ tailWord_1085796).sum := by decide
  have hdescent : baseEnd_1085796 < baseStart_1085796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085797 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 1, 1, 3]
def baseStart_1085797 : Nat := 118140960795 + 1085797 * 2 ^ 59
def prefixEnd_1085797 : Nat := 4983230072969 + 3 ^ 40 * 1085797 * 2
def baseEnd_1085797 : Nat := 557535754209993547944017

theorem tailTrace_1085797 : CollatzResearch.WordTrace tailWord_1085797 prefixEnd_1085797 557535754209993547944017 := by
  unfold tailWord_1085797
  simp only [CollatzResearch.WordTrace]
  refine ⟨39602270047350383209127645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26401513364900255472751763 39602270047350383209127645)
  ·
    refine ⟨14850851267756393703422867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39602270047350383209127645 14850851267756393703422867)
    ·
      refine ⟨22276276901634590555134301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14850851267756393703422867 22276276901634590555134301)
      ·
        refine ⟨8353603838112971458175363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22276276901634590555134301 8353603838112971458175363)
        ·
          refine ⟨12530405757169457187263045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8353603838112971458175363 12530405757169457187263045)
          ·
            refine ⟨2349451079469273222611821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12530405757169457187263045 2349451079469273222611821)
            ·
              refine ⟨881044154800977458479433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2349451079469273222611821 881044154800977458479433)
              ·
                refine ⟨660783116100733093859575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881044154800977458479433 660783116100733093859575)
                ·
                  refine ⟨991174674151099640789363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660783116100733093859575 991174674151099640789363)
                  ·
                    refine ⟨1486762011226649461184045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 991174674151099640789363 1486762011226649461184045)
                    ·
                      refine ⟨557535754209993547944017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486762011226649461184045 557535754209993547944017)
                      ·
                        rfl

theorem cell23_1085797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_1085797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085797 prefixEnd_1085797 := by exact prefixLift 1085797
  have htrace : WordTrace (prefixWord ++ tailWord_1085797) baseStart_1085797 baseEnd_1085797 := by
    simpa [prefixWord, tailWord_1085797, baseEnd_1085797] using wordTrace_append hprefix tailTrace_1085797
  have hstable : (prefixWord ++ tailWord_1085797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085797).length < 2 ^ (prefixWord ++ tailWord_1085797).sum := by decide
  have hdescent : baseEnd_1085797 < baseStart_1085797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085836 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 3, 3, 3]
def baseStart_1085836 : Nat := 118140960795 + 1085836 * 2 ^ 59
def prefixEnd_1085836 : Nat := 4983230072969 + 3 ^ 40 * 1085836 * 2
def baseEnd_1085836 : Nat := 557555779955518895356337

theorem tailTrace_1085836 : CollatzResearch.WordTrace tailWord_1085836 prefixEnd_1085836 557555779955518895356337 := by
  unfold tailWord_1085836
  simp only [CollatzResearch.WordTrace]
  refine ⟨19801846247104546434898681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26402461662806061913198241 19801846247104546434898681)
  ·
    refine ⟨14851384685328409826174011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19801846247104546434898681 14851384685328409826174011)
    ·
      refine ⟨22277077027992614739261017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14851384685328409826174011 22277077027992614739261017)
      ·
        refine ⟨16707807770994461054445763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22277077027992614739261017 16707807770994461054445763)
        ·
          refine ⟨25061711656491691581668645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16707807770994461054445763 25061711656491691581668645)
          ·
            refine ⟨4699070935592192171562871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25061711656491691581668645 4699070935592192171562871)
            ·
              refine ⟨7048606403388288257344307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699070935592192171562871 7048606403388288257344307)
              ·
                refine ⟨10572909605082432386016461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7048606403388288257344307 10572909605082432386016461)
                ·
                  refine ⟨3964841101905912144756173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10572909605082432386016461 3964841101905912144756173)
                  ·
                    refine ⟨1486815413214717054283565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3964841101905912144756173 1486815413214717054283565)
                    ·
                      refine ⟨557555779955518895356337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1486815413214717054283565 557555779955518895356337)
                      ·
                        rfl

theorem cell23_1085836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_1085836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085836 prefixEnd_1085836 := by exact prefixLift 1085836
  have htrace : WordTrace (prefixWord ++ tailWord_1085836) baseStart_1085836 baseEnd_1085836 := by
    simpa [prefixWord, tailWord_1085836, baseEnd_1085836] using wordTrace_append hprefix tailTrace_1085836
  have hstable : (prefixWord ++ tailWord_1085836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085836).length < 2 ^ (prefixWord ++ tailWord_1085836).sum := by decide
  have hdescent : baseEnd_1085836 < baseStart_1085836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085899 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 11]
def baseStart_1085899 : Nat := 118140960795 + 1085899 * 2 ^ 59
def prefixEnd_1085899 : Nat := 4983230072969 + 3 ^ 40 * 1085899 * 2
def baseEnd_1085899 : Nat := 61954236581861349874283

theorem tailTrace_1085899 : CollatzResearch.WordTrace tailWord_1085899 prefixEnd_1085899 61954236581861349874283 := by
  unfold tailWord_1085899
  simp only [CollatzResearch.WordTrace]
  refine ⟨39605990292980854629340751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26403993528653903086227167 39605990292980854629340751)
  ·
    refine ⟨59408985439471281944011127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39605990292980854629340751 59408985439471281944011127)
    ·
      refine ⟨89113478159206922916016691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59408985439471281944011127 89113478159206922916016691)
      ·
        refine ⟨133670217238810384374025037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89113478159206922916016691 133670217238810384374025037)
        ·
          refine ⟨50126331464553894140259389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133670217238810384374025037 50126331464553894140259389)
          ·
            refine ⟨18797374299207710302597271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50126331464553894140259389 18797374299207710302597271)
            ·
              refine ⟨28196061448811565453895907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18797374299207710302597271 28196061448811565453895907)
              ·
                refine ⟨42294092173217348180843861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28196061448811565453895907 42294092173217348180843861)
                ·
                  refine ⟨61954236581861349874283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 42294092173217348180843861 61954236581861349874283)
                  ·
                    rfl

theorem cell23_1085899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 11].length) (baseStart_1085899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085899 prefixEnd_1085899 := by exact prefixLift 1085899
  have htrace : WordTrace (prefixWord ++ tailWord_1085899) baseStart_1085899 baseEnd_1085899 := by
    simpa [prefixWord, tailWord_1085899, baseEnd_1085899] using wordTrace_append hprefix tailTrace_1085899
  have hstable : (prefixWord ++ tailWord_1085899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085899).length < 2 ^ (prefixWord ++ tailWord_1085899).sum := by decide
  have hdescent : baseEnd_1085899 < baseStart_1085899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085933 : List Nat := [1, 5, 1, 3, 1, 1, 2, 2, 7]
def baseStart_1085933 : Nat := 118140960795 + 1085933 * 2 ^ 59
def prefixEnd_1085933 : Nat := 4983230072969 + 3 ^ 40 * 1085933 * 2
def baseEnd_1085933 : Nat := 61956176397667223982599

theorem tailTrace_1085933 : CollatzResearch.WordTrace tailWord_1085933 prefixEnd_1085933 61956176397667223982599 := by
  unfold tailWord_1085933
  simp only [CollatzResearch.WordTrace]
  refine ⟨39607230374857678436078453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26404820249905118957385635 39607230374857678436078453)
  ·
    refine ⟨3713177847642907353382355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39607230374857678436078453 3713177847642907353382355)
    ·
      refine ⟨5569766771464361030073533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3713177847642907353382355 5569766771464361030073533)
      ·
        refine ⟨2088662539299135386277575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5569766771464361030073533 2088662539299135386277575)
        ·
          refine ⟨3132993808948703079416363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2088662539299135386277575 3132993808948703079416363)
          ·
            refine ⟨4699490713423054619124545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3132993808948703079416363 4699490713423054619124545)
            ·
              refine ⟨3524618035067290964343409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4699490713423054619124545 3524618035067290964343409)
              ·
                refine ⟨2643463526300468223257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524618035067290964343409 2643463526300468223257557)
                ·
                  refine ⟨61956176397667223982599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2643463526300468223257557 61956176397667223982599)
                  ·
                    rfl

theorem cell23_1085933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_1085933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085933 prefixEnd_1085933 := by exact prefixLift 1085933
  have htrace : WordTrace (prefixWord ++ tailWord_1085933) baseStart_1085933 baseEnd_1085933 := by
    simpa [prefixWord, tailWord_1085933, baseEnd_1085933] using wordTrace_append hprefix tailTrace_1085933
  have hstable : (prefixWord ++ tailWord_1085933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085933).length < 2 ^ (prefixWord ++ tailWord_1085933).sum := by decide
  have hdescent : baseEnd_1085933 < baseStart_1085933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085963 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 2, 5]
def baseStart_1085963 : Nat := 118140960795 + 1085963 * 2 ^ 59
def prefixEnd_1085963 : Nat := 4983230072969 + 3 ^ 40 * 1085963 * 2
def baseEnd_1085963 : Nat := 185873663999546632822751

theorem tailTrace_1085963 : CollatzResearch.WordTrace tailWord_1085963 prefixEnd_1085963 185873663999546632822751 := by
  unfold tailWord_1085963
  simp only [CollatzResearch.WordTrace]
  refine ⟨39608324564748993559670543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26405549709832662373113695 39608324564748993559670543)
  ·
    refine ⟨59412486847123490339505815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39608324564748993559670543 59412486847123490339505815)
    ·
      refine ⟨89118730270685235509258723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59412486847123490339505815 89118730270685235509258723)
      ·
        refine ⟨133678095406027853263888085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89118730270685235509258723 133678095406027853263888085)
        ·
          refine ⟨3133080361078777810872377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 133678095406027853263888085 3133080361078777810872377)
          ·
            refine ⟨2349810270809083358154283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3133080361078777810872377 2349810270809083358154283)
            ·
              refine ⟨3524715406213625037231425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2349810270809083358154283 3524715406213625037231425)
              ·
                refine ⟨2643536554660218777923569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3524715406213625037231425 2643536554660218777923569)
                ·
                  refine ⟨1982652415995164083442677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2643536554660218777923569 1982652415995164083442677)
                  ·
                    refine ⟨185873663999546632822751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1982652415995164083442677 185873663999546632822751)
                    ·
                      rfl

theorem cell23_1085963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 5].length) (baseStart_1085963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085963 prefixEnd_1085963 := by exact prefixLift 1085963
  have htrace : WordTrace (prefixWord ++ tailWord_1085963) baseStart_1085963 baseEnd_1085963 := by
    simpa [prefixWord, tailWord_1085963, baseEnd_1085963] using wordTrace_append hprefix tailTrace_1085963
  have hstable : (prefixWord ++ tailWord_1085963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085963).length < 2 ^ (prefixWord ++ tailWord_1085963).sum := by decide
  have hdescent : baseEnd_1085963 < baseStart_1085963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085983 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 1, 6, 2]
def baseStart_1085983 : Nat := 118140960795 + 1085983 * 2 ^ 59
def prefixEnd_1085983 : Nat := 4983230072969 + 3 ^ 40 * 1085983 * 2
def baseEnd_1085983 : Nat := 557631261611729820218161

theorem tailTrace_1085983 : CollatzResearch.WordTrace tailWord_1085983 prefixEnd_1085983 557631261611729820218161 := by
  unfold tailWord_1085983
  simp only [CollatzResearch.WordTrace]
  refine ⟨39609054024676536975398603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26406036016451024650265735 39609054024676536975398603)
  ·
    refine ⟨59413581037014805463097905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39609054024676536975398603 59413581037014805463097905)
    ·
      refine ⟨44560185777761104097323429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59413581037014805463097905 44560185777761104097323429)
      ·
        refine ⟨8355034833330207018248143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44560185777761104097323429 8355034833330207018248143)
        ·
          refine ⟨12532552249995310527372215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8355034833330207018248143 12532552249995310527372215)
          ·
            refine ⟨18798828374992965791058323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12532552249995310527372215 18798828374992965791058323)
            ·
              refine ⟨28198242562489448686587485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18798828374992965791058323 28198242562489448686587485)
              ·
                refine ⟨10574340960933543257470307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28198242562489448686587485 10574340960933543257470307)
                ·
                  refine ⟨15861511441400314886205461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10574340960933543257470307 15861511441400314886205461)
                  ·
                    refine ⟨743508348815639760290881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15861511441400314886205461 743508348815639760290881)
                    ·
                      refine ⟨557631261611729820218161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743508348815639760290881 557631261611729820218161)
                      ·
                        rfl

theorem cell23_1085983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_1085983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085983 prefixEnd_1085983 := by exact prefixLift 1085983
  have htrace : WordTrace (prefixWord ++ tailWord_1085983) baseStart_1085983 baseEnd_1085983 := by
    simpa [prefixWord, tailWord_1085983, baseEnd_1085983] using wordTrace_append hprefix tailTrace_1085983
  have hstable : (prefixWord ++ tailWord_1085983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085983).length < 2 ^ (prefixWord ++ tailWord_1085983).sum := by decide
  have hdescent : baseEnd_1085983 < baseStart_1085983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1085996 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 4]
def baseStart_1085996 : Nat := 118140960795 + 1085996 * 2 ^ 59
def prefixEnd_1085996 : Nat := 4983230072969 + 3 ^ 40 * 1085996 * 2
def baseEnd_1085996 : Nat := 557637936860238269355601

theorem tailTrace_1085996 : CollatzResearch.WordTrace tailWord_1085996 prefixEnd_1085996 557637936860238269355601 := by
  unfold tailWord_1085996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19804764086814720097810921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26406352115752960130414561 19804764086814720097810921)
  ·
    refine ⟨14853573065111040073358191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19804764086814720097810921 14853573065111040073358191)
    ·
      refine ⟨22280359597666560110037287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14853573065111040073358191 22280359597666560110037287)
      ·
        refine ⟨33420539396499840165055931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22280359597666560110037287 33420539396499840165055931)
        ·
          refine ⟨50130809094749760247583897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33420539396499840165055931 50130809094749760247583897)
          ·
            refine ⟨37598106821062320185687923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50130809094749760247583897 37598106821062320185687923)
            ·
              refine ⟨56397160231593480278531885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37598106821062320185687923 56397160231593480278531885)
              ·
                refine ⟨21148935086847555104449457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56397160231593480278531885 21148935086847555104449457)
                ·
                  refine ⟨15861701315135666328337093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21148935086847555104449457 15861701315135666328337093)
                  ·
                    refine ⟨2974068996587937436563205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15861701315135666328337093 2974068996587937436563205)
                    ·
                      refine ⟨557637936860238269355601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2974068996587937436563205 557637936860238269355601)
                      ·
                        rfl

theorem cell23_1085996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_1085996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1085996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1085996 prefixEnd_1085996 := by exact prefixLift 1085996
  have htrace : WordTrace (prefixWord ++ tailWord_1085996) baseStart_1085996 baseEnd_1085996 := by
    simpa [prefixWord, tailWord_1085996, baseEnd_1085996] using wordTrace_append hprefix tailTrace_1085996
  have hstable : (prefixWord ++ tailWord_1085996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1085996).length < 2 ^ (prefixWord ++ tailWord_1085996).sum := by decide
  have hdescent : baseEnd_1085996 < baseStart_1085996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1085996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086023 : List Nat := [1, 1, 4, 1, 4, 1, 1, 4, 6]
def baseStart_1086023 : Nat := 118140960795 + 1086023 * 2 ^ 59
def prefixEnd_1086023 : Nat := 4983230072969 + 3 ^ 40 * 1086023 * 2
def baseEnd_1086023 : Nat := 61961311204212184857553

theorem tailTrace_1086023 : CollatzResearch.WordTrace tailWord_1086023 prefixEnd_1086023 61961311204212184857553 := by
  unfold tailWord_1086023
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610512944531623806854723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26407008629687749204569815 39610512944531623806854723)
  ·
    refine ⟨59415769416797435710282085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39610512944531623806854723 59415769416797435710282085)
    ·
      refine ⟨11140456765649519195677891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59415769416797435710282085 11140456765649519195677891)
      ·
        refine ⟨16710685148474278793516837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11140456765649519195677891 16710685148474278793516837)
        ·
          refine ⟨3133253465338927273784407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16710685148474278793516837 3133253465338927273784407)
          ·
            refine ⟨4699880198008390910676611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133253465338927273784407 4699880198008390910676611)
            ·
              refine ⟨7049820297012586366014917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4699880198008390910676611 7049820297012586366014917)
              ·
                refine ⟨1321841305689859943627797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7049820297012586366014917 1321841305689859943627797)
                ·
                  refine ⟨61961311204212184857553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1321841305689859943627797 61961311204212184857553)
                  ·
                    rfl

theorem cell23_1086023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 6].length) (baseStart_1086023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086023 prefixEnd_1086023 := by exact prefixLift 1086023
  have htrace : WordTrace (prefixWord ++ tailWord_1086023) baseStart_1086023 baseEnd_1086023 := by
    simpa [prefixWord, tailWord_1086023, baseEnd_1086023] using wordTrace_append hprefix tailTrace_1086023
  have hstable : (prefixWord ++ tailWord_1086023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086023).length < 2 ^ (prefixWord ++ tailWord_1086023).sum := by decide
  have hdescent : baseEnd_1086023 < baseStart_1086023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086027 : List Nat := [1, 1, 1, 1, 3, 1, 8, 2, 1, 4]
def baseStart_1086027 : Nat := 118140960795 + 1086027 * 2 ^ 59
def prefixEnd_1086027 : Nat := 4983230072969 + 3 ^ 40 * 1086027 * 2
def baseEnd_1086027 : Nat := 185884618253509216022653

theorem tailTrace_1086027 : CollatzResearch.WordTrace tailWord_1086027 prefixEnd_1086027 185884618253509216022653 := by
  unfold tailWord_1086027
  simp only [CollatzResearch.WordTrace]
  refine ⟨39610658836517132490000335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26407105891011421660000223 39610658836517132490000335)
  ·
    refine ⟨59415988254775698735000503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39610658836517132490000335 59415988254775698735000503)
    ·
      refine ⟨89123982382163548102500755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59415988254775698735000503 89123982382163548102500755)
      ·
        refine ⟨133685973573245322153751133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89123982382163548102500755 133685973573245322153751133)
        ·
          refine ⟨50132240089966995807656675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133685973573245322153751133 50132240089966995807656675)
          ·
            refine ⟨75198360134950493711485013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50132240089966995807656675 75198360134950493711485013)
            ·
              refine ⟨881230782831451098181465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 75198360134950493711485013 881230782831451098181465)
              ·
                refine ⟨660923087123588323636099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 881230782831451098181465 660923087123588323636099)
                ·
                  refine ⟨991384630685382485454149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660923087123588323636099 991384630685382485454149)
                  ·
                    refine ⟨185884618253509216022653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991384630685382485454149 185884618253509216022653)
                    ·
                      rfl

theorem cell23_1086027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 4].length) (baseStart_1086027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086027 prefixEnd_1086027 := by exact prefixLift 1086027
  have htrace : WordTrace (prefixWord ++ tailWord_1086027) baseStart_1086027 baseEnd_1086027 := by
    simpa [prefixWord, tailWord_1086027, baseEnd_1086027] using wordTrace_append hprefix tailTrace_1086027
  have hstable : (prefixWord ++ tailWord_1086027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086027).length < 2 ^ (prefixWord ++ tailWord_1086027).sum := by decide
  have hdescent : baseEnd_1086027 < baseStart_1086027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086084 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_1086084 : Nat := 118140960795 + 1086084 * 2 ^ 59
def prefixEnd_1086084 : Nat := 4983230072969 + 3 ^ 40 * 1086084 * 2
def baseEnd_1086084 : Nat := 557683123157833925055197

theorem tailTrace_1086084 : CollatzResearch.WordTrace tailWord_1086084 prefixEnd_1086084 557683123157833925055197 := by
  unfold tailWord_1086084
  simp only [CollatzResearch.WordTrace]
  refine ⟨19806368898655315612412653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26408491864873754149883537 19806368898655315612412653)
  ·
    refine ⟨7427388336995743354654745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19806368898655315612412653 7427388336995743354654745)
    ·
      refine ⟨5570541252746807515991059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7427388336995743354654745 5570541252746807515991059)
      ·
        refine ⟨8355811879120211273986589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5570541252746807515991059 8355811879120211273986589)
        ·
          refine ⟨3133429454670079227744971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8355811879120211273986589 3133429454670079227744971)
          ·
            refine ⟨4700144182005118841617457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133429454670079227744971 4700144182005118841617457)
            ·
              refine ⟨3525108136503839131213093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700144182005118841617457 3525108136503839131213093)
              ·
                refine ⟨660957775594469837102455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3525108136503839131213093 660957775594469837102455)
                ·
                  refine ⟨991436663391704755653683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 660957775594469837102455 991436663391704755653683)
                  ·
                    refine ⟨1487154995087557133480525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 991436663391704755653683 1487154995087557133480525)
                    ·
                      refine ⟨557683123157833925055197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1487154995087557133480525 557683123157833925055197)
                      ·
                        rfl

theorem cell23_1086084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_1086084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086084 prefixEnd_1086084 := by exact prefixLift 1086084
  have htrace : WordTrace (prefixWord ++ tailWord_1086084) baseStart_1086084 baseEnd_1086084 := by
    simpa [prefixWord, tailWord_1086084, baseEnd_1086084] using wordTrace_append hprefix tailTrace_1086084
  have hstable : (prefixWord ++ tailWord_1086084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086084).length < 2 ^ (prefixWord ++ tailWord_1086084).sum := by decide
  have hdescent : baseEnd_1086084 < baseStart_1086084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086103 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1086103 : Nat := 118140960795 + 1086103 * 2 ^ 59
def prefixEnd_1086103 : Nat := 4983230072969 + 3 ^ 40 * 1086103 * 2
def baseEnd_1086103 : Nat := 557692879290269350717609

theorem tailTrace_1086103 : CollatzResearch.WordTrace tailWord_1086103 prefixEnd_1086103 557692879290269350717609 := by
  unfold tailWord_1086103
  simp only [CollatzResearch.WordTrace]
  refine ⟨39613430784241797469766963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26408953856161198313177975 39613430784241797469766963)
  ·
    refine ⟨59420146176362696204650445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39613430784241797469766963 59420146176362696204650445)
    ·
      refine ⟨22282554816136011076743917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59420146176362696204650445 22282554816136011076743917)
      ·
        refine ⟨8355958056051004153778969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22282554816136011076743917 8355958056051004153778969)
        ·
          refine ⟨6266968542038253115334227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8355958056051004153778969 6266968542038253115334227)
          ·
            refine ⟨9400452813057379673001341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6266968542038253115334227 9400452813057379673001341)
            ·
              refine ⟨3525169804896517377375503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9400452813057379673001341 3525169804896517377375503)
              ·
                refine ⟨5287754707344776066063255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525169804896517377375503 5287754707344776066063255)
                ·
                  refine ⟨7931632061017164099094883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5287754707344776066063255 7931632061017164099094883)
                  ·
                    refine ⟨11897448091525746148642325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7931632061017164099094883 11897448091525746148642325)
                    ·
                      refine ⟨557692879290269350717609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11897448091525746148642325 557692879290269350717609)
                      ·
                        rfl

theorem cell23_1086103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1086103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086103 prefixEnd_1086103 := by exact prefixLift 1086103
  have htrace : WordTrace (prefixWord ++ tailWord_1086103) baseStart_1086103 baseEnd_1086103 := by
    simpa [prefixWord, tailWord_1086103, baseEnd_1086103] using wordTrace_append hprefix tailTrace_1086103
  have hstable : (prefixWord ++ tailWord_1086103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086103).length < 2 ^ (prefixWord ++ tailWord_1086103).sum := by decide
  have hdescent : baseEnd_1086103 < baseStart_1086103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086110 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1086110 : Nat := 118140960795 + 1086110 * 2 ^ 59
def prefixEnd_1086110 : Nat := 4983230072969 + 3 ^ 40 * 1086110 * 2
def baseEnd_1086110 : Nat := 557696473654850823330077

theorem tailTrace_1086110 : CollatzResearch.WordTrace tailWord_1086110 prefixEnd_1086110 557696473654850823330077 := by
  unfold tailWord_1086110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4951710761902054708158973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26409124063477625110181189 4951710761902054708158973)
  ·
    refine ⟨1856891535713270515559615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4951710761902054708158973 1856891535713270515559615)
    ·
      refine ⟨2785337303569905773339423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1856891535713270515559615 2785337303569905773339423)
      ·
        refine ⟨4178005955354858660009135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2785337303569905773339423 4178005955354858660009135)
        ·
          refine ⟨6267008933032287990013703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4178005955354858660009135 6267008933032287990013703)
          ·
            refine ⟨9400513399548431985020555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6267008933032287990013703 9400513399548431985020555)
            ·
              refine ⟨14100770099322647977530833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9400513399548431985020555 14100770099322647977530833)
              ·
                refine ⟨10575577574491985983148125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14100770099322647977530833 10575577574491985983148125)
                ·
                  refine ⟨3965841590434494743680547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10575577574491985983148125 3965841590434494743680547)
                  ·
                    refine ⟨5948762385651742115520821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3965841590434494743680547 5948762385651742115520821)
                    ·
                      refine ⟨557696473654850823330077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5948762385651742115520821 557696473654850823330077)
                      ·
                        rfl

theorem cell23_1086110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1086110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086110 prefixEnd_1086110 := by exact prefixLift 1086110
  have htrace : WordTrace (prefixWord ++ tailWord_1086110) baseStart_1086110 baseEnd_1086110 := by
    simpa [prefixWord, tailWord_1086110, baseEnd_1086110] using wordTrace_append hprefix tailTrace_1086110
  have hstable : (prefixWord ++ tailWord_1086110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086110).length < 2 ^ (prefixWord ++ tailWord_1086110).sum := by decide
  have hdescent : baseEnd_1086110 < baseStart_1086110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086167 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_1086167 : Nat := 118140960795 + 1086167 * 2 ^ 59
def prefixEnd_1086167 : Nat := 4983230072969 + 3 ^ 40 * 1086167 * 2
def baseEnd_1086167 : Nat := 557725742052157100317315

theorem tailTrace_1086167 : CollatzResearch.WordTrace tailWord_1086167 prefixEnd_1086167 557725742052157100317315 := by
  unfold tailWord_1086167
  simp only [CollatzResearch.WordTrace]
  refine ⟨39615765056009936400096755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26410510037339957600064503 39615765056009936400096755)
  ·
    refine ⟨59423647584014904600145133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39615765056009936400096755 59423647584014904600145133)
    ·
      refine ⟨22283867844005589225054425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59423647584014904600145133 22283867844005589225054425)
      ·
        refine ⟨16712900883004191918790819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22283867844005589225054425 16712900883004191918790819)
        ·
          refine ⟨25069351324506287878186229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16712900883004191918790819 25069351324506287878186229)
          ·
            refine ⟨2350251686672464488579959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25069351324506287878186229 2350251686672464488579959)
            ·
              refine ⟨3525377530008696732869939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350251686672464488579959 3525377530008696732869939)
              ·
                refine ⟨5288066295013045099304909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3525377530008696732869939 5288066295013045099304909)
                ·
                  refine ⟨1983024860629891912239341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5288066295013045099304909 1983024860629891912239341)
                  ·
                    refine ⟨743634322736209467089753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983024860629891912239341 743634322736209467089753)
                    ·
                      refine ⟨557725742052157100317315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743634322736209467089753 557725742052157100317315)
                      ·
                        rfl

theorem cell23_1086167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_1086167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086167 prefixEnd_1086167 := by exact prefixLift 1086167
  have htrace : WordTrace (prefixWord ++ tailWord_1086167) baseStart_1086167 baseEnd_1086167 := by
    simpa [prefixWord, tailWord_1086167, baseEnd_1086167] using wordTrace_append hprefix tailTrace_1086167
  have hstable : (prefixWord ++ tailWord_1086167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086167).length < 2 ^ (prefixWord ++ tailWord_1086167).sum := by decide
  have hdescent : baseEnd_1086167 < baseStart_1086167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086254 : List Nat := [4, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_1086254 : Nat := 118140960795 + 1086254 * 2 ^ 59
def prefixEnd_1086254 : Nat := 4983230072969 + 3 ^ 40 * 1086254 * 2
def baseEnd_1086254 : Nat := 61974490541010917769935

theorem tailTrace_1086254 : CollatzResearch.WordTrace tailWord_1086254 prefixEnd_1086254 61974490541010917769935 := by
  unfold tailWord_1086254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4952367275836843782314227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26412625471129833505675877 4952367275836843782314227)
  ·
    refine ⟨7428550913755265673471341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4952367275836843782314227 7428550913755265673471341)
    ·
      refine ⟨2785706592658224627551753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7428550913755265673471341 2785706592658224627551753)
      ·
        refine ⟨2089279944493668470663815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2785706592658224627551753 2089279944493668470663815)
        ·
          refine ⟨3133919916740502705995723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089279944493668470663815 3133919916740502705995723)
          ·
            refine ⟨4700879875110754058993585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3133919916740502705995723 4700879875110754058993585)
            ·
              refine ⟨3525659906333065544245189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4700879875110754058993585 3525659906333065544245189)
              ·
                refine ⟨661061232437449789545973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3525659906333065544245189 661061232437449789545973)
                ·
                  refine ⟨61974490541010917769935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661061232437449789545973 61974490541010917769935)
                  ·
                    rfl

theorem cell23_1086254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_1086254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086254 prefixEnd_1086254 := by exact prefixLift 1086254
  have htrace : WordTrace (prefixWord ++ tailWord_1086254) baseStart_1086254 baseEnd_1086254 := by
    simpa [prefixWord, tailWord_1086254, baseEnd_1086254] using wordTrace_append hprefix tailTrace_1086254
  have hstable : (prefixWord ++ tailWord_1086254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086254).length < 2 ^ (prefixWord ++ tailWord_1086254).sum := by decide
  have hdescent : baseEnd_1086254 < baseStart_1086254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086307 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1086307 : Nat := 118140960795 + 1086307 * 2 ^ 59
def prefixEnd_1086307 : Nat := 4983230072969 + 3 ^ 40 * 1086307 * 2
def baseEnd_1086307 : Nat := 557797629343786552566671

theorem tailTrace_1086307 : CollatzResearch.WordTrace tailWord_1086307 prefixEnd_1086307 557797629343786552566671 := by
  unfold tailWord_1086307
  simp only [CollatzResearch.WordTrace]
  refine ⟨39620871275502740310193175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26413914183668493540128783 39620871275502740310193175)
  ·
    refine ⟨59431306913254110465289763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39620871275502740310193175 59431306913254110465289763)
    ·
      refine ⟨89146960369881165697934645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59431306913254110465289763 89146960369881165697934645)
      ·
        refine ⟨8357527534676359284181373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89146960369881165697934645 8357527534676359284181373)
        ·
          refine ⟨3134072825503634731568015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8357527534676359284181373 3134072825503634731568015)
          ·
            refine ⟨4701109238255452097352023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134072825503634731568015 4701109238255452097352023)
            ·
              refine ⟨7051663857383178146028035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4701109238255452097352023 7051663857383178146028035)
              ·
                refine ⟨10577495786074767219042053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7051663857383178146028035 10577495786074767219042053)
                ·
                  refine ⟨1983280459889018853570385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10577495786074767219042053 1983280459889018853570385)
                  ·
                    refine ⟨1487460344916764140177789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983280459889018853570385 1487460344916764140177789)
                    ·
                      refine ⟨557797629343786552566671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1487460344916764140177789 557797629343786552566671)
                      ·
                        rfl

theorem cell23_1086307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1086307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086307 prefixEnd_1086307 := by exact prefixLift 1086307
  have htrace : WordTrace (prefixWord ++ tailWord_1086307) baseStart_1086307 baseEnd_1086307 := by
    simpa [prefixWord, tailWord_1086307, baseEnd_1086307] using wordTrace_append hprefix tailTrace_1086307
  have hstable : (prefixWord ++ tailWord_1086307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086307).length < 2 ^ (prefixWord ++ tailWord_1086307).sum := by decide
  have hdescent : baseEnd_1086307 < baseStart_1086307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086338 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_1086338 : Nat := 118140960795 + 1086338 * 2 ^ 59
def prefixEnd_1086338 : Nat := 4983230072969 + 3 ^ 40 * 1086338 * 2
def baseEnd_1086338 : Nat := 557813547244075931279029

theorem tailTrace_1086338 : CollatzResearch.WordTrace tailWord_1086338 prefixEnd_1086338 557813547244075931279029 := by
  unfold tailWord_1086338
  simp only [CollatzResearch.WordTrace]
  refine ⟨9905500484597608151142917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26414667958926955069714445 9905500484597608151142917)
  ·
    refine ⟨1857281340862051528339297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9905500484597608151142917 1857281340862051528339297)
    ·
      refine ⟨1392961005646538646254473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857281340862051528339297 1392961005646538646254473)
      ·
        refine ⟨1044720754234903984690855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1392961005646538646254473 1044720754234903984690855)
        ·
          refine ⟨1567081131352355977036283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1044720754234903984690855 1567081131352355977036283)
          ·
            refine ⟨2350621697028533965554425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567081131352355977036283 2350621697028533965554425)
            ·
              refine ⟨1762966272771400474165819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2350621697028533965554425 1762966272771400474165819)
              ·
                refine ⟨2644449409157100711248729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1762966272771400474165819 2644449409157100711248729)
                ·
                  refine ⟨1983337056867825533436547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644449409157100711248729 1983337056867825533436547)
                  ·
                    refine ⟨2975005585301738300154821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983337056867825533436547 2975005585301738300154821)
                    ·
                      refine ⟨557813547244075931279029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2975005585301738300154821 557813547244075931279029)
                      ·
                        rfl

theorem cell23_1086338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_1086338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086338 prefixEnd_1086338 := by exact prefixLift 1086338
  have htrace : WordTrace (prefixWord ++ tailWord_1086338) baseStart_1086338 baseEnd_1086338 := by
    simpa [prefixWord, tailWord_1086338, baseEnd_1086338] using wordTrace_append hprefix tailTrace_1086338
  have hstable : (prefixWord ++ tailWord_1086338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086338).length < 2 ^ (prefixWord ++ tailWord_1086338).sum := by decide
  have hdescent : baseEnd_1086338 < baseStart_1086338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086347 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 5, 2]
def baseStart_1086347 : Nat := 118140960795 + 1086347 * 2 ^ 59
def prefixEnd_1086347 : Nat := 4983230072969 + 3 ^ 40 * 1086347 * 2
def baseEnd_1086347 : Nat := 557818168569966396066487

theorem tailTrace_1086347 : CollatzResearch.WordTrace tailWord_1086347 prefixEnd_1086347 557818168569966396066487 := by
  unfold tailWord_1086347
  simp only [CollatzResearch.WordTrace]
  refine ⟨39622330195357827141649295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26414886796905218094432863 39622330195357827141649295)
  ·
    refine ⟨59433495293036740712473943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39622330195357827141649295 59433495293036740712473943)
    ·
      refine ⟨89150242939555111068710915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59433495293036740712473943 89150242939555111068710915)
      ·
        refine ⟨133725364409332666603066373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89150242939555111068710915 133725364409332666603066373)
        ·
          refine ⟨25073505826749874988074945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133725364409332666603066373 25073505826749874988074945)
          ·
            refine ⟨18805129370062406241056209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25073505826749874988074945 18805129370062406241056209)
            ·
              refine ⟨14103847027546804680792157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18805129370062406241056209 14103847027546804680792157)
              ·
                refine ⟨5288942635330051755297059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14103847027546804680792157 5288942635330051755297059)
                ·
                  refine ⟨7933413952995077632945589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5288942635330051755297059 7933413952995077632945589)
                  ·
                    refine ⟨743757558093288528088649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7933413952995077632945589 743757558093288528088649)
                    ·
                      refine ⟨557818168569966396066487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743757558093288528088649 557818168569966396066487)
                      ·
                        rfl

theorem cell23_1086347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5, 2].length) (baseStart_1086347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086347 prefixEnd_1086347 := by exact prefixLift 1086347
  have htrace : WordTrace (prefixWord ++ tailWord_1086347) baseStart_1086347 baseEnd_1086347 := by
    simpa [prefixWord, tailWord_1086347, baseEnd_1086347] using wordTrace_append hprefix tailTrace_1086347
  have hstable : (prefixWord ++ tailWord_1086347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086347).length < 2 ^ (prefixWord ++ tailWord_1086347).sum := by decide
  have hdescent : baseEnd_1086347 < baseStart_1086347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086358 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_1086358 : Nat := 118140960795 + 1086358 * 2 ^ 59
def prefixEnd_1086358 : Nat := 4983230072969 + 3 ^ 40 * 1086358 * 2
def baseEnd_1086358 : Nat := 557823816857165853028937

theorem tailTrace_1086358 : CollatzResearch.WordTrace tailWord_1086358 prefixEnd_1086358 557823816857165853028937 := by
  unfold tailWord_1086358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476420712394873501268733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26415154265545317346866485 2476420712394873501268733)
  ·
    refine ⟨928657767148077562975775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2476420712394873501268733 928657767148077562975775)
    ·
      refine ⟨1392986650722116344463663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928657767148077562975775 1392986650722116344463663)
      ·
        refine ⟨2089479976083174516695495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1392986650722116344463663 2089479976083174516695495)
        ·
          refine ⟨3134219964124761775043243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089479976083174516695495 3134219964124761775043243)
          ·
            refine ⟨4701329946187142662564865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3134219964124761775043243 4701329946187142662564865)
            ·
              refine ⟨3525997459640356996923649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4701329946187142662564865 3525997459640356996923649)
              ·
                refine ⟨2644498094730267747692737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3525997459640356996923649 2644498094730267747692737)
                ·
                  refine ⟨1983373571047700810769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2644498094730267747692737 1983373571047700810769553)
                  ·
                    refine ⟨1487530178285775608077165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1983373571047700810769553 1487530178285775608077165)
                    ·
                      refine ⟨557823816857165853028937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1487530178285775608077165 557823816857165853028937)
                      ·
                        rfl

theorem cell23_1086358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_1086358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086358 prefixEnd_1086358 := by exact prefixLift 1086358
  have htrace : WordTrace (prefixWord ++ tailWord_1086358) baseStart_1086358 baseEnd_1086358 := by
    simpa [prefixWord, tailWord_1086358, baseEnd_1086358] using wordTrace_append hprefix tailTrace_1086358
  have hstable : (prefixWord ++ tailWord_1086358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086358).length < 2 ^ (prefixWord ++ tailWord_1086358).sum := by decide
  have hdescent : baseEnd_1086358 < baseStart_1086358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086388 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_1086388 : Nat := 118140960795 + 1086388 * 2 ^ 59
def prefixEnd_1086388 : Nat := 4983230072969 + 3 ^ 40 * 1086388 * 2
def baseEnd_1086388 : Nat := 557839221276800735653799

theorem tailTrace_1086388 : CollatzResearch.WordTrace tailWord_1086388 prefixEnd_1086388 557839221276800735653799 := by
  unfold tailWord_1086388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19811912794104645571945909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26415883725472860762594545 19811912794104645571945909)
  ·
    refine ⟨1857366824447310522369929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19811912794104645571945909 1857366824447310522369929)
    ·
      refine ⟨1393025118335482891777447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1857366824447310522369929 1393025118335482891777447)
      ·
        refine ⟨2089537677503224337666171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393025118335482891777447 2089537677503224337666171)
        ·
          refine ⟨3134306516254836506499257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089537677503224337666171 3134306516254836506499257)
          ·
            refine ⟨2350729887191127379874443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134306516254836506499257 2350729887191127379874443)
            ·
              refine ⟨3526094830786691069811665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2350729887191127379874443 3526094830786691069811665)
              ·
                refine ⟨2644571123090018302358749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526094830786691069811665 2644571123090018302358749)
                ·
                  refine ⟨991714171158756863384531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2644571123090018302358749 991714171158756863384531)
                  ·
                    refine ⟨1487571256738135295076797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 991714171158756863384531 1487571256738135295076797)
                    ·
                      refine ⟨557839221276800735653799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1487571256738135295076797 557839221276800735653799)
                      ·
                        rfl

theorem cell23_1086388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_1086388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086388 prefixEnd_1086388 := by exact prefixLift 1086388
  have htrace : WordTrace (prefixWord ++ tailWord_1086388) baseStart_1086388 baseEnd_1086388 := by
    simpa [prefixWord, tailWord_1086388, baseEnd_1086388] using wordTrace_append hprefix tailTrace_1086388
  have hstable : (prefixWord ++ tailWord_1086388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086388).length < 2 ^ (prefixWord ++ tailWord_1086388).sum := by decide
  have hdescent : baseEnd_1086388 < baseStart_1086388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086407 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_1086407 : Nat := 118140960795 + 1086407 * 2 ^ 59
def prefixEnd_1086407 : Nat := 4983230072969 + 3 ^ 40 * 1086407 * 2
def baseEnd_1086407 : Nat := 557848977409236161316211

theorem tailTrace_1086407 : CollatzResearch.WordTrace tailWord_1086407 prefixEnd_1086407 557848977409236161316211 := by
  unfold tailWord_1086407
  simp only [CollatzResearch.WordTrace]
  refine ⟨39624518575140457388833475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26416345716760304925888983 39624518575140457388833475)
  ·
    refine ⟨59436777862710686083250213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39624518575140457388833475 59436777862710686083250213)
    ·
      refine ⟨11144395849258253640609415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59436777862710686083250213 11144395849258253640609415)
      ·
        refine ⟨16716593773887380460914123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11144395849258253640609415 16716593773887380460914123)
        ·
          refine ⟨25074890660831070691371185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16716593773887380460914123 25074890660831070691371185)
          ·
            refine ⟨18806167995623303018528389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25074890660831070691371185 18806167995623303018528389)
            ·
              refine ⟨3526156499179369315974073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18806167995623303018528389 3526156499179369315974073)
              ·
                refine ⟨2644617374384526986980555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526156499179369315974073 2644617374384526986980555)
                ·
                  refine ⟨3966926061576790480470833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644617374384526986980555 3966926061576790480470833)
                  ·
                    refine ⟨2975194546182592860353125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3966926061576790480470833 2975194546182592860353125)
                    ·
                      refine ⟨557848977409236161316211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2975194546182592860353125 557848977409236161316211)
                      ·
                        rfl

theorem cell23_1086407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_1086407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086407 prefixEnd_1086407 := by exact prefixLift 1086407
  have htrace : WordTrace (prefixWord ++ tailWord_1086407) baseStart_1086407 baseEnd_1086407 := by
    simpa [prefixWord, tailWord_1086407, baseEnd_1086407] using wordTrace_append hprefix tailTrace_1086407
  have hstable : (prefixWord ++ tailWord_1086407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086407).length < 2 ^ (prefixWord ++ tailWord_1086407).sum := by decide
  have hdescent : baseEnd_1086407 < baseStart_1086407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086408 : List Nat := [2, 1, 3, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1086408 : Nat := 118140960795 + 1086408 * 2 ^ 59
def prefixEnd_1086408 : Nat := 4983230072969 + 3 ^ 40 * 1086408 * 2
def baseEnd_1086408 : Nat := 185949830296630219134569

theorem tailTrace_1086408 : CollatzResearch.WordTrace tailWord_1086408 prefixEnd_1086408 185949830296630219134569 := by
  unfold tailWord_1086408
  simp only [CollatzResearch.WordTrace]
  refine ⟨19812277524068417279809939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26416370032091223039746585 19812277524068417279809939)
  ·
    refine ⟨29718416286102625919714909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19812277524068417279809939 29718416286102625919714909)
    ·
      refine ⟨11144406107288484719893091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29718416286102625919714909 11144406107288484719893091)
      ·
        refine ⟨16716609160932727079839637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11144406107288484719893091 16716609160932727079839637)
        ·
          refine ⟨783591054418721581867483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16716609160932727079839637 783591054418721581867483)
          ·
            refine ⟨1175386581628082372801225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 783591054418721581867483 1175386581628082372801225)
            ·
              refine ⟨881539936221061779600919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175386581628082372801225 881539936221061779600919)
              ·
                refine ⟨1322309904331592669401379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881539936221061779600919 1322309904331592669401379)
                ·
                  refine ⟨1983464856497389004102069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322309904331592669401379 1983464856497389004102069)
                  ·
                    refine ⟨185949830296630219134569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1983464856497389004102069 185949830296630219134569)
                    ·
                      rfl

theorem cell23_1086408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1086408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086408 prefixEnd_1086408 := by exact prefixLift 1086408
  have htrace : WordTrace (prefixWord ++ tailWord_1086408) baseStart_1086408 baseEnd_1086408 := by
    simpa [prefixWord, tailWord_1086408, baseEnd_1086408] using wordTrace_append hprefix tailTrace_1086408
  have hstable : (prefixWord ++ tailWord_1086408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086408).length < 2 ^ (prefixWord ++ tailWord_1086408).sum := by decide
  have hdescent : baseEnd_1086408 < baseStart_1086408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086411 : List Nat := [1, 1, 1, 1, 3, 7, 2, 1, 1, 1, 4]
def baseStart_1086411 : Nat := 118140960795 + 1086411 * 2 ^ 59
def prefixEnd_1086411 : Nat := 4983230072969 + 3 ^ 40 * 1086411 * 2
def baseEnd_1086411 : Nat := 557851031331854145666193

theorem tailTrace_1086411 : CollatzResearch.WordTrace tailWord_1086411 prefixEnd_1086411 557851031331854145666193 := by
  unfold tailWord_1086411
  simp only [CollatzResearch.WordTrace]
  refine ⟨39624664467125966071979087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26416442978083977381319391 39624664467125966071979087)
  ·
    refine ⟨59436996700688949107968631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39624664467125966071979087 59436996700688949107968631)
    ·
      refine ⟨89155495051033423661952947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59436996700688949107968631 89155495051033423661952947)
      ·
        refine ⟨133733242576550135492929421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89155495051033423661952947 133733242576550135492929421)
        ·
          refine ⟨50149965966206300809848533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 133733242576550135492929421 50149965966206300809848533)
          ·
            refine ⟨1175389827332960175230825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 50149965966206300809848533 1175389827332960175230825)
            ·
              refine ⟨881542370499720131423119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175389827332960175230825 881542370499720131423119)
              ·
                refine ⟨1322313555749580197134679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881542370499720131423119 1322313555749580197134679)
                ·
                  refine ⟨1983470333624370295702019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322313555749580197134679 1983470333624370295702019)
                  ·
                    refine ⟨2975205500436555443553029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1983470333624370295702019 2975205500436555443553029)
                    ·
                      refine ⟨557851031331854145666193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2975205500436555443553029 557851031331854145666193)
                      ·
                        rfl

theorem cell23_1086411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 2, 1, 1, 1, 4].length) (baseStart_1086411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086411 prefixEnd_1086411 := by exact prefixLift 1086411
  have htrace : WordTrace (prefixWord ++ tailWord_1086411) baseStart_1086411 baseEnd_1086411 := by
    simpa [prefixWord, tailWord_1086411, baseEnd_1086411] using wordTrace_append hprefix tailTrace_1086411
  have hstable : (prefixWord ++ tailWord_1086411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086411).length < 2 ^ (prefixWord ++ tailWord_1086411).sum := by decide
  have hdescent : baseEnd_1086411 < baseStart_1086411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086471 : List Nat := [1, 1, 4, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1086471 : Nat := 118140960795 + 1086471 * 2 ^ 59
def prefixEnd_1086471 : Nat := 4983230072969 + 3 ^ 40 * 1086471 * 2
def baseEnd_1086471 : Nat := 557881840171123910915917

theorem tailTrace_1086471 : CollatzResearch.WordTrace tailWord_1086471 prefixEnd_1086471 557881840171123910915917 := by
  unfold tailWord_1086471
  simp only [CollatzResearch.WordTrace]
  refine ⟨39626852846908596319163267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26417901897939064212775511 39626852846908596319163267)
  ·
    refine ⟨59440279270362894478744901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39626852846908596319163267 59440279270362894478744901)
    ·
      refine ⟨11145052363193042714764669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59440279270362894478744901 11145052363193042714764669)
      ·
        refine ⟨4179394636197391018036751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11145052363193042714764669 4179394636197391018036751)
        ·
          refine ⟨6269091954296086527055127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179394636197391018036751 6269091954296086527055127)
          ·
            refine ⟨9403637931444129790582691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269091954296086527055127 9403637931444129790582691)
            ·
              refine ⟨14105456897166194685874037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9403637931444129790582691 14105456897166194685874037)
              ·
                refine ⟨1322386584109330751800691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14105456897166194685874037 1322386584109330751800691)
                ·
                  refine ⟨1983579876163996127701037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322386584109330751800691 1983579876163996127701037)
                  ·
                    refine ⟨743842453561498547887889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1983579876163996127701037 743842453561498547887889)
                    ·
                      refine ⟨557881840171123910915917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743842453561498547887889 557881840171123910915917)
                      ·
                        rfl

theorem cell23_1086471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1086471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086471 prefixEnd_1086471 := by exact prefixLift 1086471
  have htrace : WordTrace (prefixWord ++ tailWord_1086471) baseStart_1086471 baseEnd_1086471 := by
    simpa [prefixWord, tailWord_1086471, baseEnd_1086471] using wordTrace_append hprefix tailTrace_1086471
  have hstable : (prefixWord ++ tailWord_1086471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086471).length < 2 ^ (prefixWord ++ tailWord_1086471).sum := by decide
  have hdescent : baseEnd_1086471 < baseStart_1086471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086518 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2]
def baseStart_1086518 : Nat := 118140960795 + 1086518 * 2 ^ 59
def prefixEnd_1086518 : Nat := 4983230072969 + 3 ^ 40 * 1086518 * 2
def baseEnd_1086518 : Nat := 557905973761885227028201

theorem tailTrace_1086518 : CollatzResearch.WordTrace tailWord_1086518 prefixEnd_1086518 557905973761885227028201 := by
  unfold tailWord_1086518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2476785442358645209132763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26419044718492215564082805 2476785442358645209132763)
  ·
    refine ⟨3715178163537967813699145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2476785442358645209132763 3715178163537967813699145)
    ·
      refine ⟨2786383622653475860274359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715178163537967813699145 2786383622653475860274359)
      ·
        refine ⟨4179575433980213790411539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786383622653475860274359 4179575433980213790411539)
        ·
          refine ⟨6269363150970320685617309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4179575433980213790411539 6269363150970320685617309)
          ·
            refine ⟨2351011181613870257106491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6269363150970320685617309 2351011181613870257106491)
            ·
              refine ⟨3526516772420805385659737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351011181613870257106491 3526516772420805385659737)
              ·
                refine ⟨2644887579315604039244803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526516772420805385659737 2644887579315604039244803)
                ·
                  refine ⟨3967331368973406058867205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2644887579315604039244803 3967331368973406058867205)
                  ·
                    refine ⟨743874631682513636037601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3967331368973406058867205 743874631682513636037601)
                    ·
                      refine ⟨557905973761885227028201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 743874631682513636037601 557905973761885227028201)
                      ·
                        rfl

theorem cell23_1086518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_1086518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086518 prefixEnd_1086518 := by exact prefixLift 1086518
  have htrace : WordTrace (prefixWord ++ tailWord_1086518) baseStart_1086518 baseEnd_1086518 := by
    simpa [prefixWord, tailWord_1086518, baseEnd_1086518] using wordTrace_append hprefix tailTrace_1086518
  have hstable : (prefixWord ++ tailWord_1086518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086518).length < 2 ^ (prefixWord ++ tailWord_1086518).sum := by decide
  have hdescent : baseEnd_1086518 < baseStart_1086518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086537 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_1086537 : Nat := 118140960795 + 1086537 * 2 ^ 59
def prefixEnd_1086537 : Nat := 4983230072969 + 3 ^ 40 * 1086537 * 2
def baseEnd_1086537 : Nat := 185971909964773550896871

theorem tailTrace_1086537 : CollatzResearch.WordTrace tailWord_1086537 prefixEnd_1086537 185971909964773550896871 := by
  unfold tailWord_1086537
  simp only [CollatzResearch.WordTrace]
  refine ⟨39629260064669489591065865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26419506709779659727377243 39629260064669489591065865)
  ·
    refine ⟨29721945048502117193299399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39629260064669489591065865 29721945048502117193299399)
    ·
      refine ⟨44582917572753175789949099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29721945048502117193299399 44582917572753175789949099)
      ·
        refine ⟨66874376359129763684923649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44582917572753175789949099 66874376359129763684923649)
        ·
          refine ⟨50155782269347322763692737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66874376359129763684923649 50155782269347322763692737)
          ·
            refine ⟨37616836702010492072769553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50155782269347322763692737 37616836702010492072769553)
            ·
              refine ⟨28212627526507869054577165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37616836702010492072769553 28212627526507869054577165)
              ·
                refine ⟨10579735322440450895466437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28212627526507869054577165 10579735322440450895466437)
                ·
                  refine ⟨1983700372957584542899957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10579735322440450895466437 1983700372957584542899957)
                  ·
                    refine ⟨185971909964773550896871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1983700372957584542899957 185971909964773550896871)
                    ·
                      rfl

theorem cell23_1086537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_1086537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086537 prefixEnd_1086537 := by exact prefixLift 1086537
  have htrace : WordTrace (prefixWord ++ tailWord_1086537) baseStart_1086537 baseEnd_1086537 := by
    simpa [prefixWord, tailWord_1086537, baseEnd_1086537] using wordTrace_append hprefix tailTrace_1086537
  have hstable : (prefixWord ++ tailWord_1086537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086537).length < 2 ^ (prefixWord ++ tailWord_1086537).sum := by decide
  have hdescent : baseEnd_1086537 < baseStart_1086537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086558 : List Nat := [4, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1086558 : Nat := 118140960795 + 1086558 * 2 ^ 59
def prefixEnd_1086558 : Nat := 4983230072969 + 3 ^ 40 * 1086558 * 2
def baseEnd_1086558 : Nat := 61991834776451674503113

theorem tailTrace_1086558 : CollatzResearch.WordTrace tailWord_1086558 prefixEnd_1086558 61991834776451674503113 := by
  unfold tailWord_1086558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953753249699176272197541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26420017331728940118386885 4953753249699176272197541)
  ·
    refine ⟨928828734318595551037039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4953753249699176272197541 928828734318595551037039)
    ·
      refine ⟨1393243101477893326555559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928828734318595551037039 1393243101477893326555559)
      ·
        refine ⟨2089864652216839989833339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393243101477893326555559 2089864652216839989833339)
        ·
          refine ⟨3134796978325259984750009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2089864652216839989833339 3134796978325259984750009)
          ·
            refine ⟨2351097733743944988562507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3134796978325259984750009 2351097733743944988562507)
            ·
              refine ⟨3526646600615917482843761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351097733743944988562507 3526646600615917482843761)
              ·
                refine ⟨2644984950461938112132821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3526646600615917482843761 2644984950461938112132821)
                ·
                  refine ⟨61991834776451674503113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2644984950461938112132821 61991834776451674503113)
                  ·
                    rfl

theorem cell23_1086558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1086558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086558 prefixEnd_1086558 := by exact prefixLift 1086558
  have htrace : WordTrace (prefixWord ++ tailWord_1086558) baseStart_1086558 baseEnd_1086558 := by
    simpa [prefixWord, tailWord_1086558, baseEnd_1086558] using wordTrace_append hprefix tailTrace_1086558
  have hstable : (prefixWord ++ tailWord_1086558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086558).length < 2 ^ (prefixWord ++ tailWord_1086558).sum := by decide
  have hdescent : baseEnd_1086558 < baseStart_1086558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086577 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1086577 : Nat := 118140960795 + 1086577 * 2 ^ 59
def prefixEnd_1086577 : Nat := 4983230072969 + 3 ^ 40 * 1086577 * 2
def baseEnd_1086577 : Nat := 557936269120500496190429

theorem tailTrace_1086577 : CollatzResearch.WordTrace tailWord_1086577 prefixEnd_1086577 557936269120500496190429 := by
  unfold tailWord_1086577
  simp only [CollatzResearch.WordTrace]
  refine ⟨39630718984524576422521985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26420479323016384281681323 39630718984524576422521985)
  ·
    refine ⟨29723039238393432316891489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39630718984524576422521985 29723039238393432316891489)
    ·
      refine ⟨22292279428795074237668617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29723039238393432316891489 22292279428795074237668617)
      ·
        refine ⟨16719209571596305678251463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22292279428795074237668617 16719209571596305678251463)
        ·
          refine ⟨25078814357394458517377195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16719209571596305678251463 25078814357394458517377195)
          ·
            refine ⟨37618221536091687776065793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25078814357394458517377195 37618221536091687776065793)
            ·
              refine ⟨28213666152068765832049345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37618221536091687776065793 28213666152068765832049345)
              ·
                refine ⟨21160249614051574374037009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28213666152068765832049345 21160249614051574374037009)
                ·
                  refine ⟨15870187210538680780527757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21160249614051574374037009 15870187210538680780527757)
                  ·
                    refine ⟨5951320203952005292697909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15870187210538680780527757 5951320203952005292697909)
                    ·
                      refine ⟨557936269120500496190429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5951320203952005292697909 557936269120500496190429)
                      ·
                        rfl

theorem cell23_1086577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1086577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086577 prefixEnd_1086577 := by exact prefixLift 1086577
  have htrace : WordTrace (prefixWord ++ tailWord_1086577) baseStart_1086577 baseEnd_1086577 := by
    simpa [prefixWord, tailWord_1086577, baseEnd_1086577] using wordTrace_append hprefix tailTrace_1086577
  have hstable : (prefixWord ++ tailWord_1086577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086577).length < 2 ^ (prefixWord ++ tailWord_1086577).sum := by decide
  have hdescent : baseEnd_1086577 < baseStart_1086577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086587 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4]
def baseStart_1086587 : Nat := 118140960795 + 1086587 * 2 ^ 59
def prefixEnd_1086587 : Nat := 4983230072969 + 3 ^ 40 * 1086587 * 2
def baseEnd_1086587 : Nat := 557941403927045457065383

theorem tailTrace_1086587 : CollatzResearch.WordTrace tailWord_1086587 prefixEnd_1086587 557941403927045457065383 := by
  unfold tailWord_1086587
  simp only [CollatzResearch.WordTrace]
  refine ⟨39631083714488348130386015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26420722476325565420257343 39631083714488348130386015)
  ·
    refine ⟨59446625571732522195579023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39631083714488348130386015 59446625571732522195579023)
    ·
      refine ⟨89169938357598783293368535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59446625571732522195579023 89169938357598783293368535)
      ·
        refine ⟨133754907536398174940052803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89169938357598783293368535 133754907536398174940052803)
        ·
          refine ⟨200632361304597262410079205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133754907536398174940052803 200632361304597262410079205)
          ·
            refine ⟨37618567744611986701889851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 200632361304597262410079205 37618567744611986701889851)
            ·
              refine ⟨56427851616917980052834777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37618567744611986701889851 56427851616917980052834777)
              ·
                refine ⟨42320888712688485039626083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56427851616917980052834777 42320888712688485039626083)
                ·
                  refine ⟨63481333069032727559439125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42320888712688485039626083 63481333069032727559439125)
                  ·
                    refine ⟨2975687487610909104348709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63481333069032727559439125 2975687487610909104348709)
                    ·
                      refine ⟨557941403927045457065383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2975687487610909104348709 557941403927045457065383)
                      ·
                        rfl

theorem cell23_1086587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 6, 4].length) (baseStart_1086587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086587 prefixEnd_1086587 := by exact prefixLift 1086587
  have htrace : WordTrace (prefixWord ++ tailWord_1086587) baseStart_1086587 baseEnd_1086587 := by
    simpa [prefixWord, tailWord_1086587, baseEnd_1086587] using wordTrace_append hprefix tailTrace_1086587
  have hstable : (prefixWord ++ tailWord_1086587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086587).length < 2 ^ (prefixWord ++ tailWord_1086587).sum := by decide
  have hdescent : baseEnd_1086587 < baseStart_1086587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086601 : List Nat := [1, 2, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_1086601 : Nat := 118140960795 + 1086601 * 2 ^ 59
def prefixEnd_1086601 : Nat := 4983230072969 + 3 ^ 40 * 1086601 * 2
def baseEnd_1086601 : Nat := 185982864218736134096773

theorem tailTrace_1086601 : CollatzResearch.WordTrace tailWord_1086601 prefixEnd_1086601 185982864218736134096773 := by
  unfold tailWord_1086601
  simp only [CollatzResearch.WordTrace]
  refine ⟨39631594336437628521395657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26421062890958419014263771 39631594336437628521395657)
  ·
    refine ⟨29723695752328221391046743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39631594336437628521395657 29723695752328221391046743)
    ·
      refine ⟨44585543628492332086570115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29723695752328221391046743 44585543628492332086570115)
      ·
        refine ⟨66878315442738498129855173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44585543628492332086570115 66878315442738498129855173)
        ·
          refine ⟨12539684145513468399347845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66878315442738498129855173 12539684145513468399347845)
          ·
            refine ⟨2351190777283775324877721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12539684145513468399347845 2351190777283775324877721)
            ·
              refine ⟨1763393082962831493658291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351190777283775324877721 1763393082962831493658291)
              ·
                refine ⟨2645089624444247240487437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763393082962831493658291 2645089624444247240487437)
                ·
                  refine ⟨991908609166592715182789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645089624444247240487437 991908609166592715182789)
                  ·
                    refine ⟨185982864218736134096773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 991908609166592715182789 185982864218736134096773)
                    ·
                      rfl

theorem cell23_1086601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_1086601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086601 prefixEnd_1086601 := by exact prefixLift 1086601
  have htrace : WordTrace (prefixWord ++ tailWord_1086601) baseStart_1086601 baseEnd_1086601 := by
    simpa [prefixWord, tailWord_1086601, baseEnd_1086601] using wordTrace_append hprefix tailTrace_1086601
  have hstable : (prefixWord ++ tailWord_1086601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086601).length < 2 ^ (prefixWord ++ tailWord_1086601).sum := by decide
  have hdescent : baseEnd_1086601 < baseStart_1086601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086624 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3]
def baseStart_1086624 : Nat := 118140960795 + 1086624 * 2 ^ 59
def prefixEnd_1086624 : Nat := 4983230072969 + 3 ^ 40 * 1086624 * 2
def baseEnd_1086624 : Nat := 557960402711261812302713

theorem tailTrace_1086624 : CollatzResearch.WordTrace tailWord_1086624 prefixEnd_1086624 557960402711261812302713 := by
  unfold tailWord_1086624
  simp only [CollatzResearch.WordTrace]
  refine ⟨19816216607677151724741463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26421622143569535632988617 19816216607677151724741463)
  ·
    refine ⟨29724324911515727587112195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19816216607677151724741463 29724324911515727587112195)
    ·
      refine ⟨44586487367273591380668293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29724324911515727587112195 44586487367273591380668293)
      ·
        refine ⟨8359966381363798383875305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44586487367273591380668293 8359966381363798383875305)
        ·
          refine ⟨6269974786022848787906479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8359966381363798383875305 6269974786022848787906479)
          ·
            refine ⟨9404962179034273181859719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6269974786022848787906479 9404962179034273181859719)
            ·
              refine ⟨14107443268551409772789579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9404962179034273181859719 14107443268551409772789579)
              ·
                refine ⟨21161164902827114659184369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14107443268551409772789579 21161164902827114659184369)
                ·
                  refine ⟨15870873677120335994388277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21161164902827114659184369 15870873677120335994388277)
                  ·
                    refine ⟨1487894407230031499473901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15870873677120335994388277 1487894407230031499473901)
                    ·
                      refine ⟨557960402711261812302713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1487894407230031499473901 557960402711261812302713)
                      ·
                        rfl

theorem cell23_1086624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_1086624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086624 prefixEnd_1086624 := by exact prefixLift 1086624
  have htrace : WordTrace (prefixWord ++ tailWord_1086624) baseStart_1086624 baseEnd_1086624 := by
    simpa [prefixWord, tailWord_1086624, baseEnd_1086624] using wordTrace_append hprefix tailTrace_1086624
  have hstable : (prefixWord ++ tailWord_1086624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086624).length < 2 ^ (prefixWord ++ tailWord_1086624).sum := by decide
  have hdescent : baseEnd_1086624 < baseStart_1086624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086627 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 9]
def baseStart_1086627 : Nat := 118140960795 + 1086627 * 2 ^ 59
def prefixEnd_1086627 : Nat := 4983230072969 + 3 ^ 40 * 1086627 * 2
def baseEnd_1086627 : Nat := 185987314384408433521733

theorem tailTrace_1086627 : CollatzResearch.WordTrace tailWord_1086627 prefixEnd_1086627 185987314384408433521733 := by
  unfold tailWord_1086627
  simp only [CollatzResearch.WordTrace]
  refine ⟨39632542634343434961842135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26421695089562289974561423 39632542634343434961842135)
  ·
    refine ⟨59448813951515152442763203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39632542634343434961842135 59448813951515152442763203)
    ·
      refine ⟨89173220927272728664144805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59448813951515152442763203 89173220927272728664144805)
      ·
        refine ⟨16719978923863636624527151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89173220927272728664144805 16719978923863636624527151)
        ·
          refine ⟨25079968385795454936790727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16719978923863636624527151 25079968385795454936790727)
          ·
            refine ⟨37619952578693182405186091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25079968385795454936790727 37619952578693182405186091)
            ·
              refine ⟨56429928868039773607779137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37619952578693182405186091 56429928868039773607779137)
              ·
                refine ⟨42322446651029830205834353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56429928868039773607779137 42322446651029830205834353)
                ·
                  refine ⟨31741834988272372654375765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42322446651029830205834353 31741834988272372654375765)
                  ·
                    refine ⟨185987314384408433521733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 31741834988272372654375765 185987314384408433521733)
                    ·
                      rfl

theorem cell23_1086627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 9].length) (baseStart_1086627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086627 prefixEnd_1086627 := by exact prefixLift 1086627
  have htrace : WordTrace (prefixWord ++ tailWord_1086627) baseStart_1086627 baseEnd_1086627 := by
    simpa [prefixWord, tailWord_1086627, baseEnd_1086627] using wordTrace_append hprefix tailTrace_1086627
  have hstable : (prefixWord ++ tailWord_1086627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086627).length < 2 ^ (prefixWord ++ tailWord_1086627).sum := by decide
  have hdescent : baseEnd_1086627 < baseStart_1086627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086695 : List Nat := [1, 1, 5, 3, 2, 1, 3, 1, 1, 5]
def baseStart_1086695 : Nat := 118140960795 + 1086695 * 2 ^ 59
def prefixEnd_1086695 : Nat := 4983230072969 + 3 ^ 40 * 1086695 * 2
def baseEnd_1086695 : Nat := 185998953279243678171629

theorem tailTrace_1086695 : CollatzResearch.WordTrace tailWord_1086695 prefixEnd_1086695 185998953279243678171629 := by
  unfold tailWord_1086695
  simp only [CollatzResearch.WordTrace]
  refine ⟨39635022798097082575317539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26423348532064721716878359 39635022798097082575317539)
  ·
    refine ⟨59452534197145623862976309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39635022798097082575317539 59452534197145623862976309)
    ·
      refine ⟨5573675080982402237154029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59452534197145623862976309 5573675080982402237154029)
      ·
        refine ⟨2090128155368400838932761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5573675080982402237154029 2090128155368400838932761)
        ·
          refine ⟨1567596116526300629199571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2090128155368400838932761 1567596116526300629199571)
          ·
            refine ⟨2351394174789450943799357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567596116526300629199571 2351394174789450943799357)
            ·
              refine ⟨881772815546044103924759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2351394174789450943799357 881772815546044103924759)
              ·
                refine ⟨1322659223319066155887139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881772815546044103924759 1322659223319066155887139)
                ·
                  refine ⟨1983988834978599233830709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322659223319066155887139 1983988834978599233830709)
                  ·
                    refine ⟨185998953279243678171629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1983988834978599233830709 185998953279243678171629)
                    ·
                      rfl

theorem cell23_1086695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_1086695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086695 prefixEnd_1086695 := by exact prefixLift 1086695
  have htrace : WordTrace (prefixWord ++ tailWord_1086695) baseStart_1086695 baseEnd_1086695 := by
    simpa [prefixWord, tailWord_1086695, baseEnd_1086695] using wordTrace_append hprefix tailTrace_1086695
  have hstable : (prefixWord ++ tailWord_1086695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086695).length < 2 ^ (prefixWord ++ tailWord_1086695).sum := by decide
  have hdescent : baseEnd_1086695 < baseStart_1086695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086718 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_1086718 : Nat := 118140960795 + 1086718 * 2 ^ 59
def prefixEnd_1086718 : Nat := 4983230072969 + 3 ^ 40 * 1086718 * 2
def baseEnd_1086718 : Nat := 558008669892784444527281

theorem tailTrace_1086718 : CollatzResearch.WordTrace tailWord_1086718 prefixEnd_1086718 558008669892784444527281 := by
  unfold tailWord_1086718
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954482709626719687925601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26423907784675838335603205 4954482709626719687925601)
  ·
    refine ⟨3715862032220039765944201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4954482709626719687925601 3715862032220039765944201)
    ·
      refine ⟨2786896524165029824458151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3715862032220039765944201 2786896524165029824458151)
      ·
        refine ⟨4180344786247544736687227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2786896524165029824458151 4180344786247544736687227)
        ·
          refine ⟨6270517179371317105030841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180344786247544736687227 6270517179371317105030841)
          ·
            refine ⟨4702887884528487828773131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6270517179371317105030841 4702887884528487828773131)
            ·
              refine ⟨7054331826792731743159697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702887884528487828773131 7054331826792731743159697)
              ·
                refine ⟨5290748870094548807369773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054331826792731743159697 5290748870094548807369773)
                ·
                  refine ⟨1984030826285455802763665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5290748870094548807369773 1984030826285455802763665)
                  ·
                    refine ⟨1488023119714091852072749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984030826285455802763665 1488023119714091852072749)
                    ·
                      refine ⟨558008669892784444527281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488023119714091852072749 558008669892784444527281)
                      ·
                        rfl

theorem cell23_1086718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_1086718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086718 prefixEnd_1086718 := by exact prefixLift 1086718
  have htrace : WordTrace (prefixWord ++ tailWord_1086718) baseStart_1086718 baseEnd_1086718 := by
    simpa [prefixWord, tailWord_1086718, baseEnd_1086718] using wordTrace_append hprefix tailTrace_1086718
  have hstable : (prefixWord ++ tailWord_1086718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086718).length < 2 ^ (prefixWord ++ tailWord_1086718).sum := by decide
  have hdescent : baseEnd_1086718 < baseStart_1086718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086721 : List Nat := [1, 2, 4, 1, 1, 5, 1, 8]
def baseStart_1086721 : Nat := 118140960795 + 1086721 * 2 ^ 59
def prefixEnd_1086721 : Nat := 4983230072969 + 3 ^ 40 * 1086721 * 2
def baseEnd_1086721 : Nat := 20667044827212886399621

theorem tailTrace_1086721 : CollatzResearch.WordTrace tailWord_1086721 prefixEnd_1086721 20667044827212886399621 := by
  unfold tailWord_1086721
  simp only [CollatzResearch.WordTrace]
  refine ⟨39635971096002889015764017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26423980730668592677176011 39635971096002889015764017)
  ·
    refine ⟨29726978322002166761823013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39635971096002889015764017 29726978322002166761823013)
    ·
      refine ⟨5573808435375406267841815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29726978322002166761823013 5573808435375406267841815)
      ·
        refine ⟨8360712653063109401762723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5573808435375406267841815 8360712653063109401762723)
        ·
          refine ⟨12541068979594664102644085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8360712653063109401762723 12541068979594664102644085)
          ·
            refine ⟨1175725216836999759622883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12541068979594664102644085 1175725216836999759622883)
            ·
              refine ⟨1763587825255499639434325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175725216836999759622883 1763587825255499639434325)
              ·
                refine ⟨20667044827212886399621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1763587825255499639434325 20667044827212886399621)
                ·
                  rfl

theorem cell23_1086721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 8].length) (baseStart_1086721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086721 prefixEnd_1086721 := by exact prefixLift 1086721
  have htrace : WordTrace (prefixWord ++ tailWord_1086721) baseStart_1086721 baseEnd_1086721 := by
    simpa [prefixWord, tailWord_1086721, baseEnd_1086721] using wordTrace_append hprefix tailTrace_1086721
  have hstable : (prefixWord ++ tailWord_1086721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086721).length < 2 ^ (prefixWord ++ tailWord_1086721).sum := by decide
  have hdescent : baseEnd_1086721 < baseStart_1086721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086728 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4]
def baseStart_1086728 : Nat := 118140960795 + 1086728 * 2 ^ 59
def prefixEnd_1086728 : Nat := 4983230072969 + 3 ^ 40 * 1086728 * 2
def baseEnd_1086728 : Nat := 558013804699329405402235

theorem tailTrace_1086728 : CollatzResearch.WordTrace tailWord_1086728 prefixEnd_1086728 558013804699329405402235 := by
  unfold tailWord_1086728
  simp only [CollatzResearch.WordTrace]
  refine ⟨19818113203488764605634419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26424150937985019474179225 19818113203488764605634419)
  ·
    refine ⟨29727169805233146908451629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19818113203488764605634419 29727169805233146908451629)
    ·
      refine ⟨11147688676962430090669361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29727169805233146908451629 11147688676962430090669361)
      ·
        refine ⟨8360766507721822568002021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11147688676962430090669361 8360766507721822568002021)
        ·
          refine ⟨1567643720197841731500379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8360766507721822568002021 1567643720197841731500379)
          ·
            refine ⟨2351465580296762597250569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567643720197841731500379 2351465580296762597250569)
            ·
              refine ⟨1763599185222571947937927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351465580296762597250569 1763599185222571947937927)
              ·
                refine ⟨2645398777833857921906891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763599185222571947937927 2645398777833857921906891)
                ·
                  refine ⟨3968098166750786882860337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645398777833857921906891 3968098166750786882860337)
                  ·
                    refine ⟨2976073625063090162145253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3968098166750786882860337 2976073625063090162145253)
                    ·
                      refine ⟨558013804699329405402235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2976073625063090162145253 558013804699329405402235)
                      ·
                        rfl

theorem cell23_1086728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_1086728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086728 prefixEnd_1086728 := by exact prefixLift 1086728
  have htrace : WordTrace (prefixWord ++ tailWord_1086728) baseStart_1086728 baseEnd_1086728 := by
    simpa [prefixWord, tailWord_1086728, baseEnd_1086728] using wordTrace_append hprefix tailTrace_1086728
  have hstable : (prefixWord ++ tailWord_1086728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086728).length < 2 ^ (prefixWord ++ tailWord_1086728).sum := by decide
  have hdescent : baseEnd_1086728 < baseStart_1086728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086731 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3]
def baseStart_1086731 : Nat := 118140960795 + 1086731 * 2 ^ 59
def prefixEnd_1086731 : Nat := 4983230072969 + 3 ^ 40 * 1086731 * 2
def baseEnd_1086731 : Nat := 558015345141292893664721

theorem tailTrace_1086731 : CollatzResearch.WordTrace tailWord_1086731 prefixEnd_1086731 558015345141292893664721 := by
  unfold tailWord_1086731
  simp only [CollatzResearch.WordTrace]
  refine ⟨39636335825966660723628047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26424223883977773815752031 39636335825966660723628047)
  ·
    refine ⟨59454503738949991085442071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39636335825966660723628047 59454503738949991085442071)
    ·
      refine ⟨89181755608424986628163107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59454503738949991085442071 89181755608424986628163107)
      ·
        refine ⟨133772633412637479942244661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89181755608424986628163107 133772633412637479942244661)
        ·
          refine ⟨12541184382434763744585437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 133772633412637479942244661 12541184382434763744585437)
          ·
            refine ⟨4702944143413036404219539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12541184382434763744585437 4702944143413036404219539)
            ·
              refine ⟨7054416215119554606329309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4702944143413036404219539 7054416215119554606329309)
              ·
                refine ⟨2645406080669832977373491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7054416215119554606329309 2645406080669832977373491)
                ·
                  refine ⟨3968109121004749466060237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2645406080669832977373491 3968109121004749466060237)
                  ·
                    refine ⟨1488040920376781049772589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3968109121004749466060237 1488040920376781049772589)
                    ·
                      refine ⟨558015345141292893664721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488040920376781049772589 558015345141292893664721)
                      ·
                        rfl

theorem cell23_1086731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 3, 3].length) (baseStart_1086731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086731 prefixEnd_1086731 := by exact prefixLift 1086731
  have htrace : WordTrace (prefixWord ++ tailWord_1086731) baseStart_1086731 baseEnd_1086731 := by
    simpa [prefixWord, tailWord_1086731, baseEnd_1086731] using wordTrace_append hprefix tailTrace_1086731
  have hstable : (prefixWord ++ tailWord_1086731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086731).length < 2 ^ (prefixWord ++ tailWord_1086731).sum := by decide
  have hdescent : baseEnd_1086731 < baseStart_1086731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086749 : List Nat := [1, 4, 2, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1086749 : Nat := 118140960795 + 1086749 * 2 ^ 59
def prefixEnd_1086749 : Nat := 4983230072969 + 3 ^ 40 * 1086749 * 2
def baseEnd_1086749 : Nat := 558024587793073823239639

theorem tailTrace_1086749 : CollatzResearch.WordTrace tailWord_1086749 prefixEnd_1086749 558024587793073823239639 := by
  unfold tailWord_1086749
  simp only [CollatzResearch.WordTrace]
  refine ⟨39636992339901449797783301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26424661559934299865188867 39636992339901449797783301)
  ·
    refine ⟨7431936063731521837084369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39636992339901449797783301 7431936063731521837084369)
    ·
      refine ⟨5573952047798641377813277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7431936063731521837084369 5573952047798641377813277)
      ·
        refine ⟨2090232017924490516679979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5573952047798641377813277 2090232017924490516679979)
        ·
          refine ⟨3135348026886735775019969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090232017924490516679979 3135348026886735775019969)
          ·
            refine ⟨2351511020165051831264977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3135348026886735775019969 2351511020165051831264977)
            ·
              refine ⟨1763633265123788873448733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351511020165051831264977 1763633265123788873448733)
              ·
                refine ⟨661362474421420827543275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763633265123788873448733 661362474421420827543275)
                ·
                  refine ⟨992043711632131241314913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661362474421420827543275 992043711632131241314913)
                  ·
                    refine ⟨744032783724098430986185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992043711632131241314913 744032783724098430986185)
                    ·
                      refine ⟨558024587793073823239639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744032783724098430986185 558024587793073823239639)
                      ·
                        rfl

theorem cell23_1086749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1086749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086749 prefixEnd_1086749 := by exact prefixLift 1086749
  have htrace : WordTrace (prefixWord ++ tailWord_1086749) baseStart_1086749 baseEnd_1086749 := by
    simpa [prefixWord, tailWord_1086749, baseEnd_1086749] using wordTrace_append hprefix tailTrace_1086749
  have hstable : (prefixWord ++ tailWord_1086749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086749).length < 2 ^ (prefixWord ++ tailWord_1086749).sum := by decide
  have hdescent : baseEnd_1086749 < baseStart_1086749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086752 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1086752 : Nat := 118140960795 + 1086752 * 2 ^ 59
def prefixEnd_1086752 : Nat := 4983230072969 + 3 ^ 40 * 1086752 * 2
def baseEnd_1086752 : Nat := 558026128235037311502125

theorem tailTrace_1086752 : CollatzResearch.WordTrace tailWord_1086752 prefixEnd_1086752 558026128235037311502125 := by
  unfold tailWord_1086752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19818550879445290655071255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26424734505927054206761673 19818550879445290655071255)
  ·
    refine ⟨29727826319167935982606883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19818550879445290655071255 29727826319167935982606883)
    ·
      refine ⟨44591739478751903973910325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29727826319167935982606883 44591739478751903973910325)
      ·
        refine ⟨4180475576132990997554093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44591739478751903973910325 4180475576132990997554093)
        ·
          refine ⟨1567678341049871624082785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4180475576132990997554093 1567678341049871624082785)
          ·
            refine ⟨1175758755787403718062089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1567678341049871624082785 1175758755787403718062089)
            ·
              refine ⟨881819066840552788546567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1175758755787403718062089 881819066840552788546567)
              ·
                refine ⟨1322728600260829182819851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881819066840552788546567 1322728600260829182819851)
                ·
                  refine ⟨1984092900391243774229777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1322728600260829182819851 1984092900391243774229777)
                  ·
                    refine ⟨1488069675293432830672333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984092900391243774229777 1488069675293432830672333)
                    ·
                      refine ⟨558026128235037311502125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488069675293432830672333 558026128235037311502125)
                      ·
                        rfl

theorem cell23_1086752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1086752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086752 prefixEnd_1086752 := by exact prefixLift 1086752
  have htrace : WordTrace (prefixWord ++ tailWord_1086752) baseStart_1086752 baseEnd_1086752 := by
    simpa [prefixWord, tailWord_1086752, baseEnd_1086752] using wordTrace_append hprefix tailTrace_1086752
  have hstable : (prefixWord ++ tailWord_1086752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086752).length < 2 ^ (prefixWord ++ tailWord_1086752).sum := by decide
  have hdescent : baseEnd_1086752 < baseStart_1086752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086782 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_1086782 : Nat := 118140960795 + 1086782 * 2 ^ 59
def prefixEnd_1086782 : Nat := 4983230072969 + 3 ^ 40 * 1086782 * 2
def baseEnd_1086782 : Nat := 558041532654672194126987

theorem tailTrace_1086782 : CollatzResearch.WordTrace tailWord_1086782 prefixEnd_1086782 558041532654672194126987 := by
  unfold tailWord_1086782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4954774493597737054216825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26425463965854597622489733 4954774493597737054216825)
  ·
    refine ⟨3716080870198302790662619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4954774493597737054216825 3716080870198302790662619)
    ·
      refine ⟨5574121305297454185993929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3716080870198302790662619 5574121305297454185993929)
      ·
        refine ⟨4180590978973090639495447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5574121305297454185993929 4180590978973090639495447)
        ·
          refine ⟨6270886468459635959243171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4180590978973090639495447 6270886468459635959243171)
          ·
            refine ⟨9406329702689453938864757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6270886468459635959243171 9406329702689453938864757)
            ·
              refine ⟨881843409627136306768571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9406329702689453938864757 881843409627136306768571)
              ·
                refine ⟨1322765114440704460152857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 881843409627136306768571 1322765114440704460152857)
                ·
                  refine ⟨992073835830528345114643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1322765114440704460152857 992073835830528345114643)
                  ·
                    refine ⟨1488110753745792517671965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992073835830528345114643 1488110753745792517671965)
                    ·
                      refine ⟨558041532654672194126987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488110753745792517671965 558041532654672194126987)
                      ·
                        rfl

theorem cell23_1086782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_1086782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086782 prefixEnd_1086782 := by exact prefixLift 1086782
  have htrace : WordTrace (prefixWord ++ tailWord_1086782) baseStart_1086782 baseEnd_1086782 := by
    simpa [prefixWord, tailWord_1086782, baseEnd_1086782] using wordTrace_append hprefix tailTrace_1086782
  have hstable : (prefixWord ++ tailWord_1086782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086782).length < 2 ^ (prefixWord ++ tailWord_1086782).sum := by decide
  have hdescent : baseEnd_1086782 < baseStart_1086782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086805 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1086805 : Nat := 118140960795 + 1086805 * 2 ^ 59
def prefixEnd_1086805 : Nat := 4983230072969 + 3 ^ 40 * 1086805 * 2
def baseEnd_1086805 : Nat := 558053342709725604139381

theorem tailTrace_1086805 : CollatzResearch.WordTrace tailWord_1086805 prefixEnd_1086805 558053342709725604139381 := by
  unfold tailWord_1086805
  simp only [CollatzResearch.WordTrace]
  refine ⟨39639034827698571361821869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26426023218465714241214579 39639034827698571361821869)
  ·
    refine ⟨14864638060386964260683201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39639034827698571361821869 14864638060386964260683201)
    ·
      refine ⟨11148478545290223195512401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14864638060386964260683201 11148478545290223195512401)
      ·
        refine ⟨8361358908967667396634301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11148478545290223195512401 8361358908967667396634301)
        ·
          refine ⟨3135509590862875273737863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8361358908967667396634301 3135509590862875273737863)
          ·
            refine ⟨4703264386294312910606795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135509590862875273737863 4703264386294312910606795)
            ·
              refine ⟨7054896579441469365910193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703264386294312910606795 7054896579441469365910193)
              ·
                refine ⟨5291172434581102024432645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7054896579441469365910193 5291172434581102024432645)
                ·
                  refine ⟨992094831483956629581121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5291172434581102024432645 992094831483956629581121)
                  ·
                    refine ⟨744071123612967472185841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992094831483956629581121 744071123612967472185841)
                    ·
                      refine ⟨558053342709725604139381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744071123612967472185841 558053342709725604139381)
                      ·
                        rfl

theorem cell23_1086805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1086805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086805 prefixEnd_1086805 := by exact prefixLift 1086805
  have htrace : WordTrace (prefixWord ++ tailWord_1086805) baseStart_1086805 baseEnd_1086805 := by
    simpa [prefixWord, tailWord_1086805, baseEnd_1086805] using wordTrace_append hprefix tailTrace_1086805
  have hstable : (prefixWord ++ tailWord_1086805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086805).length < 2 ^ (prefixWord ++ tailWord_1086805).sum := by decide
  have hdescent : baseEnd_1086805 < baseStart_1086805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086828 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 7]
def baseStart_1086828 : Nat := 118140960795 + 1086828 * 2 ^ 59
def prefixEnd_1086828 : Nat := 4983230072969 + 3 ^ 40 * 1086828 * 2
def baseEnd_1086828 : Nat := 62007239196086557127975

theorem tailTrace_1086828 : CollatzResearch.WordTrace tailWord_1086828 prefixEnd_1086828 62007239196086557127975 := by
  unfold tailWord_1086828
  simp only [CollatzResearch.WordTrace]
  refine ⟨19819936853307623144954569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26426582471076830859939425 19819936853307623144954569)
  ·
    refine ⟨14864952639980717358715927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19819936853307623144954569 14864952639980717358715927)
    ·
      refine ⟨22297428959971076038073891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14864952639980717358715927 22297428959971076038073891)
      ·
        refine ⟨33446143439956614057110837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22297428959971076038073891 33446143439956614057110837)
        ·
          refine ⟨3135575947495932567854141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33446143439956614057110837 3135575947495932567854141)
          ·
            refine ⟨1175840980310974712945303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3135575947495932567854141 1175840980310974712945303)
            ·
              refine ⟨1763761470466462069417955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1175840980310974712945303 1763761470466462069417955)
              ·
                refine ⟨2645642205699693104126933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1763761470466462069417955 2645642205699693104126933)
                ·
                  refine ⟨62007239196086557127975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2645642205699693104126933 62007239196086557127975)
                  ·
                    rfl

theorem cell23_1086828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 7].length) (baseStart_1086828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086828 prefixEnd_1086828 := by exact prefixLift 1086828
  have htrace : WordTrace (prefixWord ++ tailWord_1086828) baseStart_1086828 baseEnd_1086828 := by
    simpa [prefixWord, tailWord_1086828, baseEnd_1086828] using wordTrace_append hprefix tailTrace_1086828
  have hstable : (prefixWord ++ tailWord_1086828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086828).length < 2 ^ (prefixWord ++ tailWord_1086828).sum := by decide
  have hdescent : baseEnd_1086828 < baseStart_1086828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086868 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1086868 : Nat := 118140960795 + 1086868 * 2 ^ 59
def prefixEnd_1086868 : Nat := 4983230072969 + 3 ^ 40 * 1086868 * 2
def baseEnd_1086868 : Nat := 558085691990958857651591

theorem tailTrace_1086868 : CollatzResearch.WordTrace tailWord_1086868 prefixEnd_1086868 558085691990958857651591 := by
  unfold tailWord_1086868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19820666313235166560682629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26427555084313555414243505 19820666313235166560682629)
  ·
    refine ⟨3716374933731593730127993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19820666313235166560682629 3716374933731593730127993)
    ·
      refine ⟨2787281200298695297595995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3716374933731593730127993 2787281200298695297595995)
      ·
        refine ⟨4180921800448042946393993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787281200298695297595995 4180921800448042946393993)
        ·
          refine ⟨3135691350336032209795495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4180921800448042946393993 3135691350336032209795495)
          ·
            refine ⟨4703537025504048314693243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135691350336032209795495 4703537025504048314693243)
            ·
              refine ⟨7055305538256072472039865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703537025504048314693243 7055305538256072472039865)
              ·
                refine ⟨5291479153692054354029899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7055305538256072472039865 5291479153692054354029899)
                ·
                  refine ⟨7937218730538081531044849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5291479153692054354029899 7937218730538081531044849)
                  ·
                    refine ⟨5952914047903561148283637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7937218730538081531044849 5952914047903561148283637)
                    ·
                      refine ⟨558085691990958857651591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5952914047903561148283637 558085691990958857651591)
                      ·
                        rfl

theorem cell23_1086868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1086868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086868 prefixEnd_1086868 := by exact prefixLift 1086868
  have htrace : WordTrace (prefixWord ++ tailWord_1086868) baseStart_1086868 baseEnd_1086868 := by
    simpa [prefixWord, tailWord_1086868, baseEnd_1086868] using wordTrace_append hprefix tailTrace_1086868
  have hstable : (prefixWord ++ tailWord_1086868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086868).length < 2 ^ (prefixWord ++ tailWord_1086868).sum := by decide
  have hdescent : baseEnd_1086868 < baseStart_1086868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086905 : List Nat := [1, 2, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_1086905 : Nat := 118140960795 + 1086905 * 2 ^ 59
def prefixEnd_1086905 : Nat := 4983230072969 + 3 ^ 40 * 1086905 * 2
def baseEnd_1086905 : Nat := 186034896925058404296307

theorem tailTrace_1086905 : CollatzResearch.WordTrace tailWord_1086905 prefixEnd_1086905 186034896925058404296307 := by
  unfold tailWord_1086905
  simp only [CollatzResearch.WordTrace]
  refine ⟨39642682127336288440462169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26428454751557525626974779 39642682127336288440462169)
  ·
    refine ⟨29732011595502216330346627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39642682127336288440462169 29732011595502216330346627)
    ·
      refine ⟨44598017393253324495519941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29732011595502216330346627 44598017393253324495519941)
      ·
        refine ⟨8362128261234998342909989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44598017393253324495519941 8362128261234998342909989)
        ·
          refine ⟨1567899048981562189295623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8362128261234998342909989 1567899048981562189295623)
          ·
            refine ⟨2351848573472343283943435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1567899048981562189295623 2351848573472343283943435)
            ·
              refine ⟨3527772860208514925915153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2351848573472343283943435 3527772860208514925915153)
              ·
                refine ⟨2645829645156386194436365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3527772860208514925915153 2645829645156386194436365)
                ·
                  refine ⟨992186116933644822913637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645829645156386194436365 992186116933644822913637)
                  ·
                    refine ⟨186034896925058404296307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 992186116933644822913637 186034896925058404296307)
                    ·
                      rfl

theorem cell23_1086905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_1086905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086905 prefixEnd_1086905 := by exact prefixLift 1086905
  have htrace : WordTrace (prefixWord ++ tailWord_1086905) baseStart_1086905 baseEnd_1086905 := by
    simpa [prefixWord, tailWord_1086905, baseEnd_1086905] using wordTrace_append hprefix tailTrace_1086905
  have hstable : (prefixWord ++ tailWord_1086905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086905).length < 2 ^ (prefixWord ++ tailWord_1086905).sum := by decide
  have hdescent : baseEnd_1086905 < baseStart_1086905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086922 : List Nat := [3, 1, 2, 1, 2, 4, 2, 3, 1, 4]
def baseStart_1086922 : Nat := 118140960795 + 1086922 * 2 ^ 59
def prefixEnd_1086922 : Nat := 4983230072969 + 3 ^ 40 * 1086922 * 2
def baseEnd_1086922 : Nat := 186037806648767215458781

theorem tailTrace_1086922 : CollatzResearch.WordTrace tailWord_1086922 prefixEnd_1086922 186037806648767215458781 := by
  unfold tailWord_1086922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9910825542068675085957755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26428868112183133562554013 9910825542068675085957755)
  ·
    refine ⟨14866238313103012628936633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9910825542068675085957755 14866238313103012628936633)
    ·
      refine ⟨11149678734827259471702475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14866238313103012628936633 11149678734827259471702475)
      ·
        refine ⟨16724518102240889207553713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11149678734827259471702475 16724518102240889207553713)
        ·
          refine ⟨12543388576680666905665285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16724518102240889207553713 12543388576680666905665285)
          ·
            refine ⟨2351885358127625044812241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12543388576680666905665285 2351885358127625044812241)
            ·
              refine ⟨1763914018595718783609181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2351885358127625044812241 1763914018595718783609181)
              ·
                refine ⟨661467756973394543853443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1763914018595718783609181 661467756973394543853443)
                ·
                  refine ⟨992201635460091815780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661467756973394543853443 992201635460091815780165)
                  ·
                    refine ⟨186037806648767215458781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 992201635460091815780165 186037806648767215458781)
                    ·
                      rfl

theorem cell23_1086922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_1086922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086922 prefixEnd_1086922 := by exact prefixLift 1086922
  have htrace : WordTrace (prefixWord ++ tailWord_1086922) baseStart_1086922 baseEnd_1086922 := by
    simpa [prefixWord, tailWord_1086922, baseEnd_1086922] using wordTrace_append hprefix tailTrace_1086922
  have hstable : (prefixWord ++ tailWord_1086922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086922).length < 2 ^ (prefixWord ++ tailWord_1086922).sum := by decide
  have hdescent : baseEnd_1086922 < baseStart_1086922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086945 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_1086945 : Nat := 118140960795 + 1086945 * 2 ^ 59
def prefixEnd_1086945 : Nat := 4983230072969 + 3 ^ 40 * 1086945 * 2
def baseEnd_1086945 : Nat := 558125230001355056388737

theorem tailTrace_1086945 : CollatzResearch.WordTrace tailWord_1086945 prefixEnd_1086945 558125230001355056388737 := by
  unfold tailWord_1086945
  simp only [CollatzResearch.WordTrace]
  refine ⟨39644141047191375271918289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26429427364794250181278859 39644141047191375271918289)
  ·
    refine ⟨29733105785393531453938717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39644141047191375271918289 29733105785393531453938717)
    ·
      refine ⟨11149914669522574295227019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29733105785393531453938717 11149914669522574295227019)
      ·
        refine ⟨16724872004283861442840529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11149914669522574295227019 16724872004283861442840529)
        ·
          refine ⟨12543654003212896082130397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16724872004283861442840529 12543654003212896082130397)
          ·
            refine ⟨4703870251204836030798899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12543654003212896082130397 4703870251204836030798899)
            ·
              refine ⟨7055805376807254046198349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4703870251204836030798899 7055805376807254046198349)
              ·
                refine ⟨2645927016302720267324381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7055805376807254046198349 2645927016302720267324381)
                ·
                  refine ⟨992222631113520100246643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645927016302720267324381 992222631113520100246643)
                  ·
                    refine ⟨1488333946670280150369965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992222631113520100246643 1488333946670280150369965)
                    ·
                      refine ⟨558125230001355056388737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488333946670280150369965 558125230001355056388737)
                      ·
                        rfl

theorem cell23_1086945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_1086945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086945 prefixEnd_1086945 := by exact prefixLift 1086945
  have htrace : WordTrace (prefixWord ++ tailWord_1086945) baseStart_1086945 baseEnd_1086945 := by
    simpa [prefixWord, tailWord_1086945, baseEnd_1086945] using wordTrace_append hprefix tailTrace_1086945
  have hstable : (prefixWord ++ tailWord_1086945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086945).length < 2 ^ (prefixWord ++ tailWord_1086945).sum := by decide
  have hdescent : baseEnd_1086945 < baseStart_1086945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086962 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1086962 : Nat := 118140960795 + 1086962 * 2 ^ 59
def prefixEnd_1086962 : Nat := 4983230072969 + 3 ^ 40 * 1086962 * 2
def baseEnd_1086962 : Nat := 558133959172481489876159

theorem tailTrace_1086962 : CollatzResearch.WordTrace tailWord_1086962 prefixEnd_1086962 558133959172481489876159 := by
  unfold tailWord_1086962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9911190272032446793821785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26429840725419858116858093 9911190272032446793821785)
  ·
    refine ⟨7433392704024335095366339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9911190272032446793821785 7433392704024335095366339)
    ·
      refine ⟨11150089056036502643049509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7433392704024335095366339 11150089056036502643049509)
      ·
        refine ⟨2090641698006844245571783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11150089056036502643049509 2090641698006844245571783)
        ·
          refine ⟨3135962547010266368357675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090641698006844245571783 3135962547010266368357675)
          ·
            refine ⟨4703943820515399552536513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3135962547010266368357675 4703943820515399552536513)
            ·
              refine ⟨3527957865386549664402385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4703943820515399552536513 3527957865386549664402385)
              ·
                refine ⟨2645968399039912248301789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3527957865386549664402385 2645968399039912248301789)
                ·
                  refine ⟨992238149639967093113171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2645968399039912248301789 992238149639967093113171)
                  ·
                    refine ⟨1488357224459950639669757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992238149639967093113171 1488357224459950639669757)
                    ·
                      refine ⟨558133959172481489876159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488357224459950639669757 558133959172481489876159)
                      ·
                        rfl

theorem cell23_1086962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1086962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086962 prefixEnd_1086962 := by exact prefixLift 1086962
  have htrace : WordTrace (prefixWord ++ tailWord_1086962) baseStart_1086962 baseEnd_1086962 := by
    simpa [prefixWord, tailWord_1086962, baseEnd_1086962] using wordTrace_append hprefix tailTrace_1086962
  have hstable : (prefixWord ++ tailWord_1086962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086962).length < 2 ^ (prefixWord ++ tailWord_1086962).sum := by decide
  have hdescent : baseEnd_1086962 < baseStart_1086962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1086996 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_1086996 : Nat := 118140960795 + 1086996 * 2 ^ 59
def prefixEnd_1086996 : Nat := 4983230072969 + 3 ^ 40 * 1086996 * 2
def baseEnd_1086996 : Nat := 558151417514734356851003

theorem tailTrace_1086996 : CollatzResearch.WordTrace tailWord_1086996 prefixEnd_1086996 558151417514734356851003 := by
  unfold tailWord_1086996
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823000585003305491012421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26430667446671073988016561 19823000585003305491012421)
  ·
    refine ⟨3716812609688119779564829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19823000585003305491012421 3716812609688119779564829)
    ·
      refine ⟨1393804728633044917336811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3716812609688119779564829 1393804728633044917336811)
      ·
        refine ⟨2090707092949567376005217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393804728633044917336811 2090707092949567376005217)
        ·
          refine ⟨1568030319712175532003913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2090707092949567376005217 1568030319712175532003913)
          ·
            refine ⟨1176022739784131649002935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568030319712175532003913 1176022739784131649002935)
            ·
              refine ⟨1764034109676197473504403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176022739784131649002935 1764034109676197473504403)
              ·
                refine ⟨2646051164514296210256605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764034109676197473504403 2646051164514296210256605)
                ·
                  refine ⟨992269186692861078846227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2646051164514296210256605 992269186692861078846227)
                  ·
                    refine ⟨1488403780039291618269341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992269186692861078846227 1488403780039291618269341)
                    ·
                      refine ⟨558151417514734356851003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488403780039291618269341 558151417514734356851003)
                      ·
                        rfl

theorem cell23_1086996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_1086996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1086996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1086996 prefixEnd_1086996 := by exact prefixLift 1086996
  have htrace : WordTrace (prefixWord ++ tailWord_1086996) baseStart_1086996 baseEnd_1086996 := by
    simpa [prefixWord, tailWord_1086996, baseEnd_1086996] using wordTrace_append hprefix tailTrace_1086996
  have hstable : (prefixWord ++ tailWord_1086996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1086996).length < 2 ^ (prefixWord ++ tailWord_1086996).sum := by decide
  have hdescent : baseEnd_1086996 < baseStart_1086996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1086996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087001 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_1087001 : Nat := 118140960795 + 1087001 * 2 ^ 59
def prefixEnd_1087001 : Nat := 4983230072969 + 3 ^ 40 * 1087001 * 2
def baseEnd_1087001 : Nat := 558153984918006837288479

theorem tailTrace_1087001 : CollatzResearch.WordTrace tailWord_1087001 prefixEnd_1087001 558153984918006837288479 := by
  unfold tailWord_1087001
  simp only [CollatzResearch.WordTrace]
  refine ⟨39646183534988496835956857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26430789023325664557304571 39646183534988496835956857)
  ·
    refine ⟨29734637651241372626967643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39646183534988496835956857 29734637651241372626967643)
    ·
      refine ⟨44601956476862058940451465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29734637651241372626967643 44601956476862058940451465)
      ·
        refine ⟨33451467357646544205338599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44601956476862058940451465 33451467357646544205338599)
        ·
          refine ⟨50177201036469816308007899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33451467357646544205338599 50177201036469816308007899)
          ·
            refine ⟨75265801554704724462011849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50177201036469816308007899 75265801554704724462011849)
            ·
              refine ⟨56449351166028543346508887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75265801554704724462011849 56449351166028543346508887)
              ·
                refine ⟨84674026749042815019763331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56449351166028543346508887 84674026749042815019763331)
                ·
                  refine ⟨127011040123564222529644997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84674026749042815019763331 127011040123564222529644997)
                  ·
                    refine ⟨23814570023168291724308437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127011040123564222529644997 23814570023168291724308437)
                    ·
                      refine ⟨558153984918006837288479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23814570023168291724308437 558153984918006837288479)
                      ·
                        rfl

theorem cell23_1087001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_1087001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087001 prefixEnd_1087001 := by exact prefixLift 1087001
  have htrace : WordTrace (prefixWord ++ tailWord_1087001) baseStart_1087001 baseEnd_1087001 := by
    simpa [prefixWord, tailWord_1087001, baseEnd_1087001] using wordTrace_append hprefix tailTrace_1087001
  have hstable : (prefixWord ++ tailWord_1087001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087001).length < 2 ^ (prefixWord ++ tailWord_1087001).sum := by decide
  have hdescent : baseEnd_1087001 < baseStart_1087001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087005 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1087005 : Nat := 118140960795 + 1087005 * 2 ^ 59
def prefixEnd_1087005 : Nat := 4983230072969 + 3 ^ 40 * 1087005 * 2
def baseEnd_1087005 : Nat := 558156038840624821638461

theorem tailTrace_1087005 : CollatzResearch.WordTrace tailWord_1087005 prefixEnd_1087005 558156038840624821638461 := by
  unfold tailWord_1087005
  simp only [CollatzResearch.WordTrace]
  refine ⟨39646329426974005519102469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26430886284649337012734979 39646329426974005519102469)
  ·
    refine ⟨7433686767557626034831713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39646329426974005519102469 7433686767557626034831713)
    ·
      refine ⟨5575265075668219526123785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7433686767557626034831713 5575265075668219526123785)
      ·
        refine ⟨4181448806751164644592839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575265075668219526123785 4181448806751164644592839)
        ·
          refine ⟨6272173210126746966889259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181448806751164644592839 6272173210126746966889259)
          ·
            refine ⟨9408259815190120450333889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6272173210126746966889259 9408259815190120450333889)
            ·
              refine ⟨7056194861392590337750417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9408259815190120450333889 7056194861392590337750417)
              ·
                refine ⟨5292146146044442753312813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7056194861392590337750417 5292146146044442753312813)
                ·
                  refine ⟨1984554804766666032492305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5292146146044442753312813 1984554804766666032492305)
                  ·
                    refine ⟨1488416103574999524369229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984554804766666032492305 1488416103574999524369229)
                    ·
                      refine ⟨558156038840624821638461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488416103574999524369229 558156038840624821638461)
                      ·
                        rfl

theorem cell23_1087005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1087005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087005 prefixEnd_1087005 := by exact prefixLift 1087005
  have htrace : WordTrace (prefixWord ++ tailWord_1087005) baseStart_1087005 baseEnd_1087005 := by
    simpa [prefixWord, tailWord_1087005, baseEnd_1087005] using wordTrace_append hprefix tailTrace_1087005
  have hstable : (prefixWord ++ tailWord_1087005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087005).length < 2 ^ (prefixWord ++ tailWord_1087005).sum := by decide
  have hdescent : baseEnd_1087005 < baseStart_1087005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087008 : List Nat := [2, 1, 1, 6, 1, 1, 1, 10]
def baseStart_1087008 : Nat := 118140960795 + 1087008 * 2 ^ 59
def prefixEnd_1087008 : Nat := 4983230072969 + 3 ^ 40 * 1087008 * 2
def baseEnd_1087008 : Nat := 20672502936392159625961

theorem tailTrace_1087008 : CollatzResearch.WordTrace tailWord_1087008 prefixEnd_1087008 20672502936392159625961 := by
  unfold tailWord_1087008
  simp only [CollatzResearch.WordTrace]
  refine ⟨19823219422981568515730839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26430959230642091354307785 19823219422981568515730839)
  ·
    refine ⟨29734829134472352773596259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19823219422981568515730839 29734829134472352773596259)
    ·
      refine ⟨44602243701708529160394389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29734829134472352773596259 44602243701708529160394389)
      ·
        refine ⟨2090730173517587304393487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44602243701708529160394389 2090730173517587304393487)
        ·
          refine ⟨3136095260276380956590231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2090730173517587304393487 3136095260276380956590231)
          ·
            refine ⟨4704142890414571434885347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3136095260276380956590231 4704142890414571434885347)
            ·
              refine ⟨7056214335621857152328021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704142890414571434885347 7056214335621857152328021)
              ·
                refine ⟨20672502936392159625961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7056214335621857152328021 20672502936392159625961)
                ·
                  rfl

theorem cell23_1087008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 10].length) (baseStart_1087008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087008 prefixEnd_1087008 := by exact prefixLift 1087008
  have htrace : WordTrace (prefixWord ++ tailWord_1087008) baseStart_1087008 baseEnd_1087008 := by
    simpa [prefixWord, tailWord_1087008, baseEnd_1087008] using wordTrace_append hprefix tailTrace_1087008
  have hstable : (prefixWord ++ tailWord_1087008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087008).length < 2 ^ (prefixWord ++ tailWord_1087008).sum := by decide
  have hdescent : baseEnd_1087008 < baseStart_1087008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087022 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_1087022 : Nat := 118140960795 + 1087022 * 2 ^ 59
def prefixEnd_1087022 : Nat := 4983230072969 + 3 ^ 40 * 1087022 * 2
def baseEnd_1087022 : Nat := 558164768011751255125883

theorem tailTrace_1087022 : CollatzResearch.WordTrace tailWord_1087022 prefixEnd_1087022 558164768011751255125883 := by
  unfold tailWord_1087022
  simp only [CollatzResearch.WordTrace]
  refine ⟨4955868683489052177808915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26431299645274944948314213 4955868683489052177808915)
  ·
    refine ⟨7433803025233578266713373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4955868683489052177808915 7433803025233578266713373)
    ·
      refine ⟨2787676134462591850017515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7433803025233578266713373 2787676134462591850017515)
      ·
        refine ⟨4181514201693887775026273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787676134462591850017515 4181514201693887775026273)
        ·
          refine ⟨3136135651270415831269705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4181514201693887775026273 3136135651270415831269705)
          ·
            refine ⟨2352101738452811873452279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3136135651270415831269705 2352101738452811873452279)
            ·
              refine ⟨3528152607679217810178419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352101738452811873452279 3528152607679217810178419)
              ·
                refine ⟨5292228911518826715267629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3528152607679217810178419 5292228911518826715267629)
                ·
                  refine ⟨1984585841819560018225361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5292228911518826715267629 1984585841819560018225361)
                  ·
                    refine ⟨1488439381364670013669021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1984585841819560018225361 1488439381364670013669021)
                    ·
                      refine ⟨558164768011751255125883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488439381364670013669021 558164768011751255125883)
                      ·
                        rfl

theorem cell23_1087022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_1087022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087022 prefixEnd_1087022 := by exact prefixLift 1087022
  have htrace : WordTrace (prefixWord ++ tailWord_1087022) baseStart_1087022 baseEnd_1087022 := by
    simpa [prefixWord, tailWord_1087022, baseEnd_1087022] using wordTrace_append hprefix tailTrace_1087022
  have hstable : (prefixWord ++ tailWord_1087022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087022).length < 2 ^ (prefixWord ++ tailWord_1087022).sum := by decide
  have hdescent : baseEnd_1087022 < baseStart_1087022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087046 : List Nat := [6, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1087046 : Nat := 118140960795 + 1087046 * 2 ^ 59
def prefixEnd_1087046 : Nat := 4983230072969 + 3 ^ 40 * 1087046 * 2
def baseEnd_1087046 : Nat := 186059030515819720408591

theorem tailTrace_1087046 : CollatzResearch.WordTrace tailWord_1087046 prefixEnd_1087046 186059030515819720408591 := by
  unfold tailWord_1087046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238994525619545922542031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26431883213216979680896661 1238994525619545922542031)
  ·
    refine ⟨1858491788429318883813047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238994525619545922542031 1858491788429318883813047)
    ·
      refine ⟨2787737682643978325719571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858491788429318883813047 2787737682643978325719571)
      ·
        refine ⟨4181606523965967488579357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787737682643978325719571 4181606523965967488579357)
        ·
          refine ⟨1568102446487237808217259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4181606523965967488579357 1568102446487237808217259)
          ·
            refine ⟨2352153669730856712325889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568102446487237808217259 2352153669730856712325889)
            ·
              refine ⟨1764115252298142534244417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352153669730856712325889 1764115252298142534244417)
              ·
                refine ⟨1323086439223606900683313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1764115252298142534244417 1323086439223606900683313)
                ·
                  refine ⟨992314829417705175512485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323086439223606900683313 992314829417705175512485)
                  ·
                    refine ⟨186059030515819720408591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 992314829417705175512485 186059030515819720408591)
                    ·
                      rfl

theorem cell23_1087046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1087046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087046 prefixEnd_1087046 := by exact prefixLift 1087046
  have htrace : WordTrace (prefixWord ++ tailWord_1087046) baseStart_1087046 baseEnd_1087046 := by
    simpa [prefixWord, tailWord_1087046, baseEnd_1087046] using wordTrace_append hprefix tailTrace_1087046
  have hstable : (prefixWord ++ tailWord_1087046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087046).length < 2 ^ (prefixWord ++ tailWord_1087046).sum := by decide
  have hdescent : baseEnd_1087046 < baseStart_1087046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087052 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1087052 : Nat := 118140960795 + 1087052 * 2 ^ 59
def prefixEnd_1087052 : Nat := 4983230072969 + 3 ^ 40 * 1087052 * 2
def baseEnd_1087052 : Nat := 558180172431386137750745

theorem tailTrace_1087052 : CollatzResearch.WordTrace tailWord_1087052 prefixEnd_1087052 558180172431386137750745 := by
  unfold tailWord_1087052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19824021828901866273031705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26432029105202488364042273 19824021828901866273031705)
  ·
    refine ⟨14868016371676399704773779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19824021828901866273031705 14868016371676399704773779)
    ·
      refine ⟨22302024557514599557160669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14868016371676399704773779 22302024557514599557160669)
      ·
        refine ⟨8363259209067974833935251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22302024557514599557160669 8363259209067974833935251)
        ·
          refine ⟨12544888813601962250902877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8363259209067974833935251 12544888813601962250902877)
          ·
            refine ⟨4704333305100735844088579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12544888813601962250902877 4704333305100735844088579)
            ·
              refine ⟨7056499957651103766132869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704333305100735844088579 7056499957651103766132869)
              ·
                refine ⟨1323093742059581956149913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7056499957651103766132869 1323093742059581956149913)
                ·
                  refine ⟨992320306544686467112435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323093742059581956149913 992320306544686467112435)
                  ·
                    refine ⟨1488480459817029700668653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992320306544686467112435 1488480459817029700668653)
                    ·
                      refine ⟨558180172431386137750745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488480459817029700668653 558180172431386137750745)
                      ·
                        rfl

theorem cell23_1087052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1087052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087052 prefixEnd_1087052 := by exact prefixLift 1087052
  have htrace : WordTrace (prefixWord ++ tailWord_1087052) baseStart_1087052 baseEnd_1087052 := by
    simpa [prefixWord, tailWord_1087052, baseEnd_1087052] using wordTrace_append hprefix tailTrace_1087052
  have hstable : (prefixWord ++ tailWord_1087052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087052).length < 2 ^ (prefixWord ++ tailWord_1087052).sum := by decide
  have hdescent : baseEnd_1087052 < baseStart_1087052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087053 : List Nat := [1, 6, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_1087053 : Nat := 118140960795 + 1087053 * 2 ^ 59
def prefixEnd_1087053 : Nat := 4983230072969 + 3 ^ 40 * 1087053 * 2
def baseEnd_1087053 : Nat := 558180685912040633838241

theorem tailTrace_1087053 : CollatzResearch.WordTrace tailWord_1087053 prefixEnd_1087053 558180685912040633838241 := by
  unfold tailWord_1087053
  simp only [CollatzResearch.WordTrace]
  refine ⟨39648080130800109716849813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26432053420533406477899875 39648080130800109716849813)
  ·
    refine ⟨1858503756131255142977335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 39648080130800109716849813 1858503756131255142977335)
    ·
      refine ⟨2787755634196882714466003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1858503756131255142977335 2787755634196882714466003)
      ·
        refine ⟨4181633451295324071699005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2787755634196882714466003 4181633451295324071699005)
        ·
          refine ⟨1568112544235746526887127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4181633451295324071699005 1568112544235746526887127)
          ·
            refine ⟨2352168816353619790330691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568112544235746526887127 2352168816353619790330691)
            ·
              refine ⟨3528253224530429685496037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352168816353619790330691 3528253224530429685496037)
              ·
                refine ⟨661547479599455566030507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3528253224530429685496037 661547479599455566030507)
                ·
                  refine ⟨992321219399183349045761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661547479599455566030507 992321219399183349045761)
                  ·
                    refine ⟨744240914549387511784321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992321219399183349045761 744240914549387511784321)
                    ·
                      refine ⟨558180685912040633838241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744240914549387511784321 558180685912040633838241)
                      ·
                        rfl

theorem cell23_1087053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_1087053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087053 prefixEnd_1087053 := by exact prefixLift 1087053
  have htrace : WordTrace (prefixWord ++ tailWord_1087053) baseStart_1087053 baseEnd_1087053 := by
    simpa [prefixWord, tailWord_1087053, baseEnd_1087053] using wordTrace_append hprefix tailTrace_1087053
  have hstable : (prefixWord ++ tailWord_1087053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087053).length < 2 ^ (prefixWord ++ tailWord_1087053).sum := by decide
  have hdescent : baseEnd_1087053 < baseStart_1087053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087105 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1087105 : Nat := 118140960795 + 1087105 * 2 ^ 59
def prefixEnd_1087105 : Nat := 4983230072969 + 3 ^ 40 * 1087105 * 2
def baseEnd_1087105 : Nat := 558207386906074430388001

theorem tailTrace_1087105 : CollatzResearch.WordTrace tailWord_1087105 prefixEnd_1087105 558207386906074430388001 := by
  unfold tailWord_1087105
  simp only [CollatzResearch.WordTrace]
  refine ⟨39649976726611722597742769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26433317817741148398495179 39649976726611722597742769)
  ·
    refine ⟨29737482544958791948307077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39649976726611722597742769 29737482544958791948307077)
    ·
      refine ⟨5575777977179773490307577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29737482544958791948307077 5575777977179773490307577)
      ·
        refine ⟨4181833482884830117730683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5575777977179773490307577 4181833482884830117730683)
        ·
          refine ⟨6272750224327245176596025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4181833482884830117730683 6272750224327245176596025)
          ·
            refine ⟨4704562668245433882447019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6272750224327245176596025 4704562668245433882447019)
            ·
              refine ⟨7056844002368150823670529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4704562668245433882447019 7056844002368150823670529)
              ·
                refine ⟨5292633001776113117752897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7056844002368150823670529 5292633001776113117752897)
                ·
                  refine ⟨3969474751332084838314673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5292633001776113117752897 3969474751332084838314673)
                  ·
                    refine ⟨2977106063499063628736005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3969474751332084838314673 2977106063499063628736005)
                    ·
                      refine ⟨558207386906074430388001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2977106063499063628736005 558207386906074430388001)
                      ·
                        rfl

theorem cell23_1087105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1087105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087105 prefixEnd_1087105 := by exact prefixLift 1087105
  have htrace : WordTrace (prefixWord ++ tailWord_1087105) baseStart_1087105 baseEnd_1087105 := by
    simpa [prefixWord, tailWord_1087105, baseEnd_1087105] using wordTrace_append hprefix tailTrace_1087105
  have hstable : (prefixWord ++ tailWord_1087105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087105).length < 2 ^ (prefixWord ++ tailWord_1087105).sum := by decide
  have hdescent : baseEnd_1087105 < baseStart_1087105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087115 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 5]
def baseStart_1087115 : Nat := 118140960795 + 1087115 * 2 ^ 59
def prefixEnd_1087115 : Nat := 4983230072969 + 3 ^ 40 * 1087115 * 2
def baseEnd_1087115 : Nat := 62023613523624376806995

theorem tailTrace_1087115 : CollatzResearch.WordTrace tailWord_1087115 prefixEnd_1087115 62023613523624376806995 := by
  unfold tailWord_1087115
  simp only [CollatzResearch.WordTrace]
  refine ⟨39650341456575494305606799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26433560971050329537071199 39650341456575494305606799)
  ·
    refine ⟨59475512184863241458410199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39650341456575494305606799 59475512184863241458410199)
    ·
      refine ⟨89213268277294862187615299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59475512184863241458410199 89213268277294862187615299)
      ·
        refine ⟨133819902415942293281422949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89213268277294862187615299 133819902415942293281422949)
        ·
          refine ⟨25091231702989179990266803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 133819902415942293281422949 25091231702989179990266803)
          ·
            refine ⟨37636847554483769985400205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25091231702989179990266803 37636847554483769985400205)
            ·
              refine ⟨14113817832931413744525077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37636847554483769985400205 14113817832931413744525077)
              ·
                refine ⟨661585210918660019274613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14113817832931413744525077 661585210918660019274613)
                ·
                  refine ⟨62023613523624376806995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661585210918660019274613 62023613523624376806995)
                  ·
                    rfl

theorem cell23_1087115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 5].length) (baseStart_1087115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087115 prefixEnd_1087115 := by exact prefixLift 1087115
  have htrace : WordTrace (prefixWord ++ tailWord_1087115) baseStart_1087115 baseEnd_1087115 := by
    simpa [prefixWord, tailWord_1087115, baseEnd_1087115] using wordTrace_append hprefix tailTrace_1087115
  have hstable : (prefixWord ++ tailWord_1087115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087115).length < 2 ^ (prefixWord ++ tailWord_1087115).sum := by decide
  have hdescent : baseEnd_1087115 < baseStart_1087115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087182 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_1087182 : Nat := 118140960795 + 1087182 * 2 ^ 59
def prefixEnd_1087182 : Nat := 4983230072969 + 3 ^ 40 * 1087182 * 2
def baseEnd_1087182 : Nat := 558246924916470629125147

theorem tailTrace_1087182 : CollatzResearch.WordTrace tailWord_1087182 prefixEnd_1087182 558246924916470629125147 := by
  unfold tailWord_1087182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4956598143416595593536975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26435190098221843165530533 4956598143416595593536975)
  ·
    refine ⟨7434897215124893390305463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4956598143416595593536975 7434897215124893390305463)
    ·
      refine ⟨11152345822687340085458195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7434897215124893390305463 11152345822687340085458195)
      ·
        refine ⟨16728518734031010128187293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11152345822687340085458195 16728518734031010128187293)
        ·
          refine ⟨6273194525261628798070235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16728518734031010128187293 6273194525261628798070235)
          ·
            refine ⟨9409791787892443197105353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6273194525261628798070235 9409791787892443197105353)
            ·
              refine ⟨7057343840919332397829015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9409791787892443197105353 7057343840919332397829015)
              ·
                refine ⟨10586015761378998596743523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7057343840919332397829015 10586015761378998596743523)
                ·
                  refine ⟨15879023642068497895115285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10586015761378998596743523 15879023642068497895115285)
                  ·
                    refine ⟨744329233221960838833529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15879023642068497895115285 744329233221960838833529)
                    ·
                      refine ⟨558246924916470629125147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744329233221960838833529 558246924916470629125147)
                      ·
                        rfl

theorem cell23_1087182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_1087182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087182 prefixEnd_1087182 := by exact prefixLift 1087182
  have htrace : WordTrace (prefixWord ++ tailWord_1087182) baseStart_1087182 baseEnd_1087182 := by
    simpa [prefixWord, tailWord_1087182, baseEnd_1087182] using wordTrace_append hprefix tailTrace_1087182
  have hstable : (prefixWord ++ tailWord_1087182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087182).length < 2 ^ (prefixWord ++ tailWord_1087182).sum := by decide
  have hdescent : baseEnd_1087182 < baseStart_1087182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087222 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1087222 : Nat := 118140960795 + 1087222 * 2 ^ 59
def prefixEnd_1087222 : Nat := 4983230072969 + 3 ^ 40 * 1087222 * 2
def baseEnd_1087222 : Nat := 62029718238072274736107

theorem tailTrace_1087222 : CollatzResearch.WordTrace tailWord_1087222 prefixEnd_1087222 62029718238072274736107 := by
  unfold tailWord_1087222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478390254199240723734495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26436162711458567719834613 2478390254199240723734495)
  ·
    refine ⟨3717585381298861085601743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478390254199240723734495 3717585381298861085601743)
    ·
      refine ⟨5576378071948291628402615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3717585381298861085601743 5576378071948291628402615)
      ·
        refine ⟨8364567107922437442603923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5576378071948291628402615 8364567107922437442603923)
        ·
          refine ⟨12546850661883656163905885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8364567107922437442603923 12546850661883656163905885)
          ·
            refine ⟨4705068998206371061464707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12546850661883656163905885 4705068998206371061464707)
            ·
              refine ⟨7057603497309556592197061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705068998206371061464707 7057603497309556592197061)
              ·
                refine ⟨1323300655745541861036949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7057603497309556592197061 1323300655745541861036949)
                ·
                  refine ⟨62029718238072274736107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1323300655745541861036949 62029718238072274736107)
                  ·
                    rfl

theorem cell23_1087222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1087222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087222 prefixEnd_1087222 := by exact prefixLift 1087222
  have htrace : WordTrace (prefixWord ++ tailWord_1087222) baseStart_1087222 baseEnd_1087222 := by
    simpa [prefixWord, tailWord_1087222, baseEnd_1087222] using wordTrace_append hprefix tailTrace_1087222
  have hstable : (prefixWord ++ tailWord_1087222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087222).length < 2 ^ (prefixWord ++ tailWord_1087222).sum := by decide
  have hdescent : baseEnd_1087222 < baseStart_1087222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087235 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 3, 5]
def baseStart_1087235 : Nat := 118140960795 + 1087235 * 2 ^ 59
def prefixEnd_1087235 : Nat := 4983230072969 + 3 ^ 40 * 1087235 * 2
def baseEnd_1087235 : Nat := 186091379797052973920801

theorem tailTrace_1087235 : CollatzResearch.WordTrace tailWord_1087235 prefixEnd_1087235 186091379797052973920801 := by
  unfold tailWord_1087235
  simp only [CollatzResearch.WordTrace]
  refine ⟨39654718216140754799975159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26436478810760503199983439 39654718216140754799975159)
  ·
    refine ⟨59482077324211132199962739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39654718216140754799975159 59482077324211132199962739)
    ·
      refine ⟨89223115986316698299944109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59482077324211132199962739 89223115986316698299944109)
      ·
        refine ⟨33458668494868761862479041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89223115986316698299944109 33458668494868761862479041)
        ·
          refine ⟨25094001371151571396859281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33458668494868761862479041 25094001371151571396859281)
          ·
            refine ⟨18820501028363678547644461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25094001371151571396859281 18820501028363678547644461)
            ·
              refine ⟨7057687885636379455366673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18820501028363678547644461 7057687885636379455366673)
              ·
                refine ⟨5293265914227284591525005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7057687885636379455366673 5293265914227284591525005)
                ·
                  refine ⟨1984974717835231721821877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5293265914227284591525005 1984974717835231721821877)
                  ·
                    refine ⟨186091379797052973920801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1984974717835231721821877 186091379797052973920801)
                    ·
                      rfl

theorem cell23_1087235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 5].length) (baseStart_1087235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087235 prefixEnd_1087235 := by exact prefixLift 1087235
  have htrace : WordTrace (prefixWord ++ tailWord_1087235) baseStart_1087235 baseEnd_1087235 := by
    simpa [prefixWord, tailWord_1087235, baseEnd_1087235] using wordTrace_append hprefix tailTrace_1087235
  have hstable : (prefixWord ++ tailWord_1087235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087235).length < 2 ^ (prefixWord ++ tailWord_1087235).sum := by decide
  have hdescent : baseEnd_1087235 < baseStart_1087235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087269 : List Nat := [1, 3, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_1087269 : Nat := 118140960795 + 1087269 * 2 ^ 59
def prefixEnd_1087269 : Nat := 4983230072969 + 3 ^ 40 * 1087269 * 2
def baseEnd_1087269 : Nat := 186097199244470596245749

theorem tailTrace_1087269 : CollatzResearch.WordTrace tailWord_1087269 prefixEnd_1087269 186097199244470596245749 := by
  unfold tailWord_1087269
  simp only [CollatzResearch.WordTrace]
  refine ⟨39655958298017578606712861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26437305532011719071141907 39655958298017578606712861)
  ·
    refine ⟨14870984361756591977517323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39655958298017578606712861 14870984361756591977517323)
    ·
      refine ⟨22306476542634887966275985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14870984361756591977517323 22306476542634887966275985)
      ·
        refine ⟨16729857406976165974706989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22306476542634887966275985 16729857406976165974706989)
        ·
          refine ⟨6273696527616062240515121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16729857406976165974706989 6273696527616062240515121)
          ·
            refine ⟨4705272395712046680386341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6273696527616062240515121 4705272395712046680386341)
            ·
              refine ⟨882238574196008752572439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4705272395712046680386341 882238574196008752572439)
              ·
                refine ⟨1323357861294013128858659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882238574196008752572439 1323357861294013128858659)
                ·
                  refine ⟨1985036791941019693287989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323357861294013128858659 1985036791941019693287989)
                  ·
                    refine ⟨186097199244470596245749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1985036791941019693287989 186097199244470596245749)
                    ·
                      rfl

theorem cell23_1087269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_1087269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087269 prefixEnd_1087269 := by exact prefixLift 1087269
  have htrace : WordTrace (prefixWord ++ tailWord_1087269) baseStart_1087269 baseEnd_1087269 := by
    simpa [prefixWord, tailWord_1087269, baseEnd_1087269] using wordTrace_append hprefix tailTrace_1087269
  have hstable : (prefixWord ++ tailWord_1087269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087269).length < 2 ^ (prefixWord ++ tailWord_1087269).sum := by decide
  have hdescent : baseEnd_1087269 < baseStart_1087269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087275 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3]
def baseStart_1087275 : Nat := 118140960795 + 1087275 * 2 ^ 59
def prefixEnd_1087275 : Nat := 4983230072969 + 3 ^ 40 * 1087275 * 2
def baseEnd_1087275 : Nat := 558294678617338765262219

theorem tailTrace_1087275 : CollatzResearch.WordTrace tailWord_1087275 prefixEnd_1087275 558294678617338765262219 := by
  unfold tailWord_1087275
  simp only [CollatzResearch.WordTrace]
  refine ⟨39656177135995841631431279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26437451423997227754287519 39656177135995841631431279)
  ·
    refine ⟨59484265703993762447146919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39656177135995841631431279 59484265703993762447146919)
    ·
      refine ⟨89226398555990643670720379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59484265703993762447146919 89226398555990643670720379)
      ·
        refine ⟨133839597833985965506080569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89226398555990643670720379 133839597833985965506080569)
        ·
          refine ⟨100379698375489474129560427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133839597833985965506080569 100379698375489474129560427)
          ·
            refine ⟨150569547563234211194340641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100379698375489474129560427 150569547563234211194340641)
            ·
              refine ⟨112927160672425658395755481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150569547563234211194340641 112927160672425658395755481)
              ·
                refine ⟨84695370504319243796816611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112927160672425658395755481 84695370504319243796816611)
                ·
                  refine ⟨127043055756478865695224917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84695370504319243796816611 127043055756478865695224917)
                  ·
                    refine ⟨1488785809646236707365917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 127043055756478865695224917 1488785809646236707365917)
                    ·
                      refine ⟨558294678617338765262219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488785809646236707365917 558294678617338765262219)
                      ·
                        rfl

theorem cell23_1087275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 3].length) (baseStart_1087275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087275 prefixEnd_1087275 := by exact prefixLift 1087275
  have htrace : WordTrace (prefixWord ++ tailWord_1087275) baseStart_1087275 baseEnd_1087275 := by
    simpa [prefixWord, tailWord_1087275, baseEnd_1087275] using wordTrace_append hprefix tailTrace_1087275
  have hstable : (prefixWord ++ tailWord_1087275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087275).length < 2 ^ (prefixWord ++ tailWord_1087275).sum := by decide
  have hdescent : baseEnd_1087275 < baseStart_1087275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087292 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_1087292 : Nat := 118140960795 + 1087292 * 2 ^ 59
def prefixEnd_1087292 : Nat := 4983230072969 + 3 ^ 40 * 1087292 * 2
def baseEnd_1087292 : Nat := 558303407788465198749641

theorem tailTrace_1087292 : CollatzResearch.WordTrace tailWord_1087292 prefixEnd_1087292 558303407788465198749641 := by
  unfold tailWord_1087292
  simp only [CollatzResearch.WordTrace]
  refine ⟨19828398588467126767400065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26437864784622835689866753 19828398588467126767400065)
  ·
    refine ⟨14871298941350345075550049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19828398588467126767400065 14871298941350345075550049)
    ·
      refine ⟨11153474206012758806662537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14871298941350345075550049 11153474206012758806662537)
      ·
        refine ⟨8365105654509569104996903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11153474206012758806662537 8365105654509569104996903)
        ·
          refine ⟨12547658481764353657495355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365105654509569104996903 12547658481764353657495355)
          ·
            refine ⟨18821487722646530486243033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12547658481764353657495355 18821487722646530486243033)
            ·
              refine ⟨14116115791984897864682275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18821487722646530486243033 14116115791984897864682275)
              ·
                refine ⟨21174173687977346797023413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14116115791984897864682275 21174173687977346797023413)
                ·
                  refine ⟨1985078783247876262220945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21174173687977346797023413 1985078783247876262220945)
                  ·
                    refine ⟨1488809087435907196665709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985078783247876262220945 1488809087435907196665709)
                    ·
                      refine ⟨558303407788465198749641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488809087435907196665709 558303407788465198749641)
                      ·
                        rfl

theorem cell23_1087292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_1087292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087292 prefixEnd_1087292 := by exact prefixLift 1087292
  have htrace : WordTrace (prefixWord ++ tailWord_1087292) baseStart_1087292 baseEnd_1087292 := by
    simpa [prefixWord, tailWord_1087292, baseEnd_1087292] using wordTrace_append hprefix tailTrace_1087292
  have hstable : (prefixWord ++ tailWord_1087292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087292).length < 2 ^ (prefixWord ++ tailWord_1087292).sum := by decide
  have hdescent : baseEnd_1087292 < baseStart_1087292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087322 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1087322 : Nat := 118140960795 + 1087322 * 2 ^ 59
def prefixEnd_1087322 : Nat := 4983230072969 + 3 ^ 40 * 1087322 * 2
def baseEnd_1087322 : Nat := 558318812208100081374503

theorem tailTrace_1087322 : CollatzResearch.WordTrace tailWord_1087322 prefixEnd_1087322 558318812208100081374503 := by
  unfold tailWord_1087322
  simp only [CollatzResearch.WordTrace]
  refine ⟨9914472841706392164598055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26438594244550379105594813 9914472841706392164598055)
  ·
    refine ⟨14871709262559588246897083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9914472841706392164598055 14871709262559588246897083)
    ·
      refine ⟨22307563893839382370345625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14871709262559588246897083 22307563893839382370345625)
      ·
        refine ⟨16730672920379536777759219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22307563893839382370345625 16730672920379536777759219)
        ·
          refine ⟨25096009380569305166638829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16730672920379536777759219 25096009380569305166638829)
          ·
            refine ⟨9411003517713489437489561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25096009380569305166638829 9411003517713489437489561)
            ·
              refine ⟨7058252638285117078117171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9411003517713489437489561 7058252638285117078117171)
              ·
                refine ⟨10587378957427675617175757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058252638285117078117171 10587378957427675617175757)
                ·
                  refine ⟨3970267109035378356440909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10587378957427675617175757 3970267109035378356440909)
                  ·
                    refine ⟨1488850165888266883665341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3970267109035378356440909 1488850165888266883665341)
                    ·
                      refine ⟨558318812208100081374503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488850165888266883665341 558318812208100081374503)
                      ·
                        rfl

theorem cell23_1087322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1087322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087322 prefixEnd_1087322 := by exact prefixLift 1087322
  have htrace : WordTrace (prefixWord ++ tailWord_1087322) baseStart_1087322 baseEnd_1087322 := by
    simpa [prefixWord, tailWord_1087322, baseEnd_1087322] using wordTrace_append hprefix tailTrace_1087322
  have hstable : (prefixWord ++ tailWord_1087322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087322).length < 2 ^ (prefixWord ++ tailWord_1087322).sum := by decide
  have hdescent : baseEnd_1087322 < baseStart_1087322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087339 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 3]
def baseStart_1087339 : Nat := 118140960795 + 1087339 * 2 ^ 59
def prefixEnd_1087339 : Nat := 4983230072969 + 3 ^ 40 * 1087339 * 2
def baseEnd_1087339 : Nat := 558327541379226514861925

theorem tailTrace_1087339 : CollatzResearch.WordTrace tailWord_1087339 prefixEnd_1087339 558327541379226514861925 := by
  unfold tailWord_1087339
  simp only [CollatzResearch.WordTrace]
  refine ⟨39658511407763980561761071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26439007605175987041174047 39658511407763980561761071)
  ·
    refine ⟨59487767111645970842641607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39658511407763980561761071 59487767111645970842641607)
    ·
      refine ⟨89231650667468956263962411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59487767111645970842641607 89231650667468956263962411)
      ·
        refine ⟨133847476001203434395943617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89231650667468956263962411 133847476001203434395943617)
        ·
          refine ⟨100385607000902575796957713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133847476001203434395943617 100385607000902575796957713)
          ·
            refine ⟨75289205250676931847718285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100385607000902575796957713 75289205250676931847718285)
            ·
              refine ⟨28233451969003849442894357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75289205250676931847718285 28233451969003849442894357)
              ·
                refine ⟨1323443061047055442635673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28233451969003849442894357 1323443061047055442635673)
                ·
                  refine ⟨992582295785291581976755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323443061047055442635673 992582295785291581976755)
                  ·
                    refine ⟨1488873443677937372965133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 992582295785291581976755 1488873443677937372965133)
                    ·
                      refine ⟨558327541379226514861925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488873443677937372965133 558327541379226514861925)
                      ·
                        rfl

theorem cell23_1087339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 2, 1, 3].length) (baseStart_1087339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087339 prefixEnd_1087339 := by exact prefixLift 1087339
  have htrace : WordTrace (prefixWord ++ tailWord_1087339) baseStart_1087339 baseEnd_1087339 := by
    simpa [prefixWord, tailWord_1087339, baseEnd_1087339] using wordTrace_append hprefix tailTrace_1087339
  have hstable : (prefixWord ++ tailWord_1087339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087339).length < 2 ^ (prefixWord ++ tailWord_1087339).sum := by decide
  have hdescent : baseEnd_1087339 < baseStart_1087339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087340 : List Nat := [2, 2, 1, 1, 4, 3, 3, 2, 1, 2, 2]
def baseStart_1087340 : Nat := 118140960795 + 1087340 * 2 ^ 59
def prefixEnd_1087340 : Nat := 4983230072969 + 3 ^ 40 * 1087340 * 2
def baseEnd_1087340 : Nat := 558328054859881010949421

theorem tailTrace_1087340 : CollatzResearch.WordTrace tailWord_1087340 prefixEnd_1087340 558328054859881010949421 := by
  unfold tailWord_1087340
  simp only [CollatzResearch.WordTrace]
  refine ⟨19829273940380178866273737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26439031920506905155031649 19829273940380178866273737)
  ·
    refine ⟨14871955455285134149705303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19829273940380178866273737 14871955455285134149705303)
    ·
      refine ⟨22307933182927701224557955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14871955455285134149705303 22307933182927701224557955)
      ·
        refine ⟨33461899774391551836836933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22307933182927701224557955 33461899774391551836836933)
        ·
          refine ⟨6274106207698415969406925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33461899774391551836836933 6274106207698415969406925)
          ·
            refine ⟨2352789827886905988527597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6274106207698415969406925 2352789827886905988527597)
            ·
              refine ⟨882296185457589745697849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2352789827886905988527597 882296185457589745697849)
              ·
                refine ⟨661722139093192309273387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882296185457589745697849 661722139093192309273387)
                ·
                  refine ⟨992583208639788463910081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 661722139093192309273387 992583208639788463910081)
                  ·
                    refine ⟨744437406479841347932561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992583208639788463910081 744437406479841347932561)
                    ·
                      refine ⟨558328054859881010949421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744437406479841347932561 558328054859881010949421)
                      ·
                        rfl

theorem cell23_1087340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_1087340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087340 prefixEnd_1087340 := by exact prefixLift 1087340
  have htrace : WordTrace (prefixWord ++ tailWord_1087340) baseStart_1087340 baseEnd_1087340 := by
    simpa [prefixWord, tailWord_1087340, baseEnd_1087340] using wordTrace_append hprefix tailTrace_1087340
  have hstable : (prefixWord ++ tailWord_1087340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087340).length < 2 ^ (prefixWord ++ tailWord_1087340).sum := by decide
  have hdescent : baseEnd_1087340 < baseStart_1087340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087350 : List Nat := [5, 1, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1087350 : Nat := 118140960795 + 1087350 * 2 ^ 59
def prefixEnd_1087350 : Nat := 4983230072969 + 3 ^ 40 * 1087350 * 2
def baseEnd_1087350 : Nat := 186111063222141990608125

theorem tailTrace_1087350 : CollatzResearch.WordTrace tailWord_1087350 prefixEnd_1087350 186111063222141990608125 := by
  unfold tailWord_1087350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478682038170258090025719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26439275073816086293607669 2478682038170258090025719)
  ·
    refine ⟨3718023057255387135038579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478682038170258090025719 3718023057255387135038579)
    ·
      refine ⟨5577034585883080702557869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3718023057255387135038579 5577034585883080702557869)
      ·
        refine ⟨2091387969706155263459201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5577034585883080702557869 2091387969706155263459201)
        ·
          refine ⟨1568540977279616447594401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091387969706155263459201 1568540977279616447594401)
          ·
            refine ⟨1176405732959712335695801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1568540977279616447594401 1176405732959712335695801)
            ·
              refine ⟨882304299719784251771851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1176405732959712335695801 882304299719784251771851)
              ·
                refine ⟨1323456449579676377657777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882304299719784251771851 1323456449579676377657777)
                ·
                  refine ⟨992592337184757283243333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323456449579676377657777 992592337184757283243333)
                  ·
                    refine ⟨186111063222141990608125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 992592337184757283243333 186111063222141990608125)
                    ·
                      rfl

theorem cell23_1087350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1087350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087350 prefixEnd_1087350 := by exact prefixLift 1087350
  have htrace : WordTrace (prefixWord ++ tailWord_1087350) baseStart_1087350 baseEnd_1087350 := by
    simpa [prefixWord, tailWord_1087350, baseEnd_1087350] using wordTrace_append hprefix tailTrace_1087350
  have hstable : (prefixWord ++ tailWord_1087350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087350).length < 2 ^ (prefixWord ++ tailWord_1087350).sum := by decide
  have hdescent : baseEnd_1087350 < baseStart_1087350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087355 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 8]
def baseStart_1087355 : Nat := 118140960795 + 1087355 * 2 ^ 59
def prefixEnd_1087355 : Nat := 4983230072969 + 3 ^ 40 * 1087355 * 2
def baseEnd_1087355 : Nat := 186111919023232817420617

theorem tailTrace_1087355 : CollatzResearch.WordTrace tailWord_1087355 prefixEnd_1087355 186111919023232817420617 := by
  unfold tailWord_1087355
  simp only [CollatzResearch.WordTrace]
  refine ⟨39659094975706015294343519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26439396650470676862895679 39659094975706015294343519)
  ·
    refine ⟨59488642463559022941515279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39659094975706015294343519 59488642463559022941515279)
    ·
      refine ⟨89232963695338534412272919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59488642463559022941515279 89232963695338534412272919)
      ·
        refine ⟨133849445543007801618409379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89232963695338534412272919 133849445543007801618409379)
        ·
          refine ⟨200774168314511702427614069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133849445543007801618409379 200774168314511702427614069)
          ·
            refine ⟨18822578279485472102588819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 200774168314511702427614069 18822578279485472102588819)
            ·
              refine ⟨28233867419228208153883229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18822578279485472102588819 28233867419228208153883229)
              ·
                refine ⟨10587700282210578057706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28233867419228208153883229 10587700282210578057706211)
                ·
                  refine ⟨15881550423315867086559317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10587700282210578057706211 15881550423315867086559317)
                  ·
                    refine ⟨186111919023232817420617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15881550423315867086559317 186111919023232817420617)
                    ·
                      rfl

theorem cell23_1087355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_1087355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087355 prefixEnd_1087355 := by exact prefixLift 1087355
  have htrace : WordTrace (prefixWord ++ tailWord_1087355) baseStart_1087355 baseEnd_1087355 := by
    simpa [prefixWord, tailWord_1087355, baseEnd_1087355] using wordTrace_append hprefix tailTrace_1087355
  have hstable : (prefixWord ++ tailWord_1087355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087355).length < 2 ^ (prefixWord ++ tailWord_1087355).sum := by decide
  have hdescent : baseEnd_1087355 < baseStart_1087355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_1087375 : Nat := 118140960795 + 1087375 * 2 ^ 59
def prefixEnd_1087375 : Nat := 4983230072969 + 3 ^ 40 * 1087375 * 2
def baseEnd_1087375 : Nat := 558346026682788374011759

theorem tailTrace_1087375 : CollatzResearch.WordTrace tailWord_1087375 prefixEnd_1087375 558346026682788374011759 := by
  unfold tailWord_1087375
  simp only [CollatzResearch.WordTrace]
  refine ⟨39659824435633558710071579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26439882957089039140047719 39659824435633558710071579)
  ·
    refine ⟨59489736653450338065107369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39659824435633558710071579 59489736653450338065107369)
    ·
      refine ⟨44617302490087753548830527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59489736653450338065107369 44617302490087753548830527)
      ·
        refine ⟨66925953735131630323245791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44617302490087753548830527 66925953735131630323245791)
        ·
          refine ⟨100388930602697445484868687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66925953735131630323245791 100388930602697445484868687)
          ·
            refine ⟨150583395904046168227303031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100388930602697445484868687 150583395904046168227303031)
            ·
              refine ⟨225875093856069252340954547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150583395904046168227303031 225875093856069252340954547)
              ·
                refine ⟨338812640784103878511431821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225875093856069252340954547 338812640784103878511431821)
                ·
                  refine ⟨127054740294038954441786933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338812640784103878511431821 127054740294038954441786933)
                  ·
                    refine ⟨11911381902566151978917525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 127054740294038954441786933 11911381902566151978917525)
                    ·
                      refine ⟨558346026682788374011759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11911381902566151978917525 558346026682788374011759)
                      ·
                        rfl

theorem cell23_1087375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_1087375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087375 prefixEnd_1087375 := by exact prefixLift 1087375
  have htrace : WordTrace (prefixWord ++ tailWord_1087375) baseStart_1087375 baseEnd_1087375 := by
    simpa [prefixWord, tailWord_1087375, baseEnd_1087375] using wordTrace_append hprefix tailTrace_1087375
  have hstable : (prefixWord ++ tailWord_1087375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087375).length < 2 ^ (prefixWord ++ tailWord_1087375).sum := by decide
  have hdescent : baseEnd_1087375 < baseStart_1087375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087383 : List Nat := [1, 1, 3, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_1087383 : Nat := 118140960795 + 1087383 * 2 ^ 59
def prefixEnd_1087383 : Nat := 4983230072969 + 3 ^ 40 * 1087383 * 2
def baseEnd_1087383 : Nat := 558350134528024342711723

theorem tailTrace_1087383 : CollatzResearch.WordTrace tailWord_1087383 prefixEnd_1087383 558350134528024342711723 := by
  unfold tailWord_1087383
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660116219604576076362803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26440077479736384050908535 39660116219604576076362803)
  ·
    refine ⟨59490174329406864114544205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39660116219604576076362803 59490174329406864114544205)
    ·
      refine ⟨22308815373527574042954077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59490174329406864114544205 22308815373527574042954077)
      ·
        refine ⟨8365805765072840266107779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22308815373527574042954077 8365805765072840266107779)
        ·
          refine ⟨12548708647609260399161669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365805765072840266107779 12548708647609260399161669)
          ·
            refine ⟨2352882871426736324842813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12548708647609260399161669 2352882871426736324842813)
            ·
              refine ⟨882331076785026121816055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2352882871426736324842813 882331076785026121816055)
              ·
                refine ⟨1323496615177539182724083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882331076785026121816055 1323496615177539182724083)
                ·
                  refine ⟨1985244922766308774086125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323496615177539182724083 1985244922766308774086125)
                  ·
                    refine ⟨744466846037365790282297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1985244922766308774086125 744466846037365790282297)
                    ·
                      refine ⟨558350134528024342711723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744466846037365790282297 558350134528024342711723)
                      ·
                        rfl

theorem cell23_1087383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_1087383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087383 prefixEnd_1087383 := by exact prefixLift 1087383
  have htrace : WordTrace (prefixWord ++ tailWord_1087383) baseStart_1087383 baseEnd_1087383 := by
    simpa [prefixWord, tailWord_1087383, baseEnd_1087383] using wordTrace_append hprefix tailTrace_1087383
  have hstable : (prefixWord ++ tailWord_1087383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087383).length < 2 ^ (prefixWord ++ tailWord_1087383).sum := by decide
  have hdescent : baseEnd_1087383 < baseStart_1087383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087392 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_1087392 : Nat := 118140960795 + 1087392 * 2 ^ 59
def prefixEnd_1087392 : Nat := 4983230072969 + 3 ^ 40 * 1087392 * 2
def baseEnd_1087392 : Nat := 558354755853914807499181

theorem tailTrace_1087392 : CollatzResearch.WordTrace tailWord_1087392 prefixEnd_1087392 558354755853914807499181 := by
  unfold tailWord_1087392
  simp only [CollatzResearch.WordTrace]
  refine ⟨19830222238285985306720215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26440296317714647075626953 19830222238285985306720215)
  ·
    refine ⟨29745333357428977960080323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19830222238285985306720215 29745333357428977960080323)
    ·
      refine ⟨44618000036143466940120485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29745333357428977960080323 44618000036143466940120485)
      ·
        refine ⟨8365875006776900051272591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44618000036143466940120485 8365875006776900051272591)
        ·
          refine ⟨12548812510165350076908887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8365875006776900051272591 12548812510165350076908887)
          ·
            refine ⟨18823218765248025115363331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12548812510165350076908887 18823218765248025115363331)
            ·
              refine ⟨28234828147872037673044997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18823218765248025115363331 28234828147872037673044997)
              ·
                refine ⟨5294030277726007063695937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28234828147872037673044997 5294030277726007063695937)
                ·
                  refine ⟨3970522708294505297771953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294030277726007063695937 3970522708294505297771953)
                  ·
                    refine ⟨2977892031220878973328965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970522708294505297771953 2977892031220878973328965)
                    ·
                      refine ⟨558354755853914807499181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2977892031220878973328965 558354755853914807499181)
                      ·
                        rfl

theorem cell23_1087392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_1087392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087392 prefixEnd_1087392 := by exact prefixLift 1087392
  have htrace : WordTrace (prefixWord ++ tailWord_1087392) baseStart_1087392 baseEnd_1087392 := by
    simpa [prefixWord, tailWord_1087392, baseEnd_1087392] using wordTrace_append hprefix tailTrace_1087392
  have hstable : (prefixWord ++ tailWord_1087392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087392).length < 2 ^ (prefixWord ++ tailWord_1087392).sum := by decide
  have hdescent : baseEnd_1087392 < baseStart_1087392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087399 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1087399 : Nat := 118140960795 + 1087399 * 2 ^ 59
def prefixEnd_1087399 : Nat := 4983230072969 + 3 ^ 40 * 1087399 * 2
def baseEnd_1087399 : Nat := 558358350218496280111649

theorem tailTrace_1087399 : CollatzResearch.WordTrace tailWord_1087399 prefixEnd_1087399 558358350218496280111649 := by
  unfold tailWord_1087399
  simp only [CollatzResearch.WordTrace]
  refine ⟨39660699787546610808945251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26440466525031073872630167 39660699787546610808945251)
  ·
    refine ⟨59491049681319916213417877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39660699787546610808945251 59491049681319916213417877)
    ·
      refine ⟨2788642953811871072503963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59491049681319916213417877 2788642953811871072503963)
      ·
        refine ⟨4182964430717806608755945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2788642953811871072503963 4182964430717806608755945)
        ·
          refine ⟨3137223323038354956566959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4182964430717806608755945 3137223323038354956566959)
          ·
            refine ⟨4705834984557532434850439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137223323038354956566959 4705834984557532434850439)
            ·
              refine ⟨7058752476836298652275659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4705834984557532434850439 7058752476836298652275659)
              ·
                refine ⟨10588128715254447978413489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7058752476836298652275659 10588128715254447978413489)
                ·
                  refine ⟨7941096536440835983810117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10588128715254447978413489 7941096536440835983810117)
                  ·
                    refine ⟨1488955600582656746964397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7941096536440835983810117 1488955600582656746964397)
                    ·
                      refine ⟨558358350218496280111649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1488955600582656746964397 558358350218496280111649)
                      ·
                        rfl

theorem cell23_1087399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1087399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087399 prefixEnd_1087399 := by exact prefixLift 1087399
  have htrace : WordTrace (prefixWord ++ tailWord_1087399) baseStart_1087399 baseEnd_1087399 := by
    simpa [prefixWord, tailWord_1087399, baseEnd_1087399] using wordTrace_append hprefix tailTrace_1087399
  have hstable : (prefixWord ++ tailWord_1087399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087399).length < 2 ^ (prefixWord ++ tailWord_1087399).sum := by decide
  have hdescent : baseEnd_1087399 < baseStart_1087399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087409 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1087409 : Nat := 118140960795 + 1087409 * 2 ^ 59
def prefixEnd_1087409 : Nat := 4983230072969 + 3 ^ 40 * 1087409 * 2
def baseEnd_1087409 : Nat := 558363485025041240986603

theorem tailTrace_1087409 : CollatzResearch.WordTrace tailWord_1087409 prefixEnd_1087409 558363485025041240986603 := by
  unfold tailWord_1087409
  simp only [CollatzResearch.WordTrace]
  refine ⟨39661064517510382516809281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26440709678340255011206187 39661064517510382516809281)
  ·
    refine ⟨29745798388132786887606961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39661064517510382516809281 29745798388132786887606961)
    ·
      refine ⟨22309348791099590165705221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29745798388132786887606961 22309348791099590165705221)
      ·
        refine ⟨4183002898331173156069729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22309348791099590165705221 4183002898331173156069729)
        ·
          refine ⟨3137252173748379867052297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4183002898331173156069729 3137252173748379867052297)
          ·
            refine ⟨2352939130311284900289223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3137252173748379867052297 2352939130311284900289223)
            ·
              refine ⟨3529408695466927350433835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2352939130311284900289223 3529408695466927350433835)
              ·
                refine ⟨5294113043200391025650753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529408695466927350433835 5294113043200391025650753)
                ·
                  refine ⟨3970584782400293269238065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5294113043200391025650753 3970584782400293269238065)
                  ·
                    refine ⟨2977938586800219951928549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3970584782400293269238065 2977938586800219951928549)
                    ·
                      refine ⟨558363485025041240986603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2977938586800219951928549 558363485025041240986603)
                      ·
                        rfl

theorem cell23_1087409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1087409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087409 prefixEnd_1087409 := by exact prefixLift 1087409
  have htrace : WordTrace (prefixWord ++ tailWord_1087409) baseStart_1087409 baseEnd_1087409 := by
    simpa [prefixWord, tailWord_1087409, baseEnd_1087409] using wordTrace_append hprefix tailTrace_1087409
  have hstable : (prefixWord ++ tailWord_1087409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087409).length < 2 ^ (prefixWord ++ tailWord_1087409).sum := by decide
  have hdescent : baseEnd_1087409 < baseStart_1087409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087413 : List Nat := [1, 3, 3, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_1087413 : Nat := 118140960795 + 1087413 * 2 ^ 59
def prefixEnd_1087413 : Nat := 4983230072969 + 3 ^ 40 * 1087413 * 2
def baseEnd_1087413 : Nat := 558365538947659225336585

theorem tailTrace_1087413 : CollatzResearch.WordTrace tailWord_1087413 prefixEnd_1087413 558365538947659225336585 := by
  unfold tailWord_1087413
  simp only [CollatzResearch.WordTrace]
  refine ⟨39661210409495891199954893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26440806939663927466636595 39661210409495891199954893)
  ·
    refine ⟨14872953903560959199983085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39661210409495891199954893 14872953903560959199983085)
    ·
      refine ⟨5577357713835359699993657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14872953903560959199983085 5577357713835359699993657)
      ·
        refine ⟨4183018285376519774995243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5577357713835359699993657 4183018285376519774995243)
        ·
          refine ⟨6274527428064779662492865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183018285376519774995243 6274527428064779662492865)
          ·
            refine ⟨4705895571048584746869649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6274527428064779662492865 4705895571048584746869649)
            ·
              refine ⟨3529421678286438560152237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4705895571048584746869649 3529421678286438560152237)
              ·
                refine ⟨1323533129357414460057089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3529421678286438560152237 1323533129357414460057089)
                ·
                  refine ⟨992649847018060845042817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1323533129357414460057089 992649847018060845042817)
                  ·
                    refine ⟨744487385263545633782113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992649847018060845042817 744487385263545633782113)
                    ·
                      refine ⟨558365538947659225336585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744487385263545633782113 558365538947659225336585)
                      ·
                        rfl

theorem cell23_1087413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_1087413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087413 prefixEnd_1087413 := by exact prefixLift 1087413
  have htrace : WordTrace (prefixWord ++ tailWord_1087413) baseStart_1087413 baseEnd_1087413 := by
    simpa [prefixWord, tailWord_1087413, baseEnd_1087413] using wordTrace_append hprefix tailTrace_1087413
  have hstable : (prefixWord ++ tailWord_1087413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087413).length < 2 ^ (prefixWord ++ tailWord_1087413).sum := by decide
  have hdescent : baseEnd_1087413 < baseStart_1087413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087436 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 5]
def baseStart_1087436 : Nat := 118140960795 + 1087436 * 2 ^ 59
def prefixEnd_1087436 : Nat := 4983230072969 + 3 ^ 40 * 1087436 * 2
def baseEnd_1087436 : Nat := 62041927666968070594331

theorem tailTrace_1087436 : CollatzResearch.WordTrace tailWord_1087436 prefixEnd_1087436 62041927666968070594331 := by
  unfold tailWord_1087436
  simp only [CollatzResearch.WordTrace]
  refine ⟨19831024644206283064021081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26441366192275044085361441 19831024644206283064021081)
  ·
    refine ⟨14873268483154712298015811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19831024644206283064021081 14873268483154712298015811)
    ·
      refine ⟨22309902724732068447023717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14873268483154712298015811 22309902724732068447023717)
      ·
        refine ⟨4183106760887262833816947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22309902724732068447023717 4183106760887262833816947)
        ·
          refine ⟨6274660141330894250725421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4183106760887262833816947 6274660141330894250725421)
          ·
            refine ⟨2352997552999085344022033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6274660141330894250725421 2352997552999085344022033)
            ·
              refine ⟨1764748164749314008016525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2352997552999085344022033 1764748164749314008016525)
              ·
                refine ⟨661780561780992753006197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1764748164749314008016525 661780561780992753006197)
                ·
                  refine ⟨62041927666968070594331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661780561780992753006197 62041927666968070594331)
                  ·
                    rfl

theorem cell23_1087436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_1087436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087436 prefixEnd_1087436 := by exact prefixLift 1087436
  have htrace : WordTrace (prefixWord ++ tailWord_1087436) baseStart_1087436 baseEnd_1087436 := by
    simpa [prefixWord, tailWord_1087436, baseEnd_1087436] using wordTrace_append hprefix tailTrace_1087436
  have hstable : (prefixWord ++ tailWord_1087436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087436).length < 2 ^ (prefixWord ++ tailWord_1087436).sum := by decide
  have hdescent : baseEnd_1087436 < baseStart_1087436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087486 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1087486 : Nat := 118140960795 + 1087486 * 2 ^ 59
def prefixEnd_1087486 : Nat := 4983230072969 + 3 ^ 40 * 1087486 * 2
def baseEnd_1087486 : Nat := 558403023035437439723749

theorem tailTrace_1087486 : CollatzResearch.WordTrace tailWord_1087486 prefixEnd_1087486 558403023035437439723749 := by
  unfold tailWord_1087486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4957984117278928083420289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26442581958820949778241541 4957984117278928083420289)
  ·
    refine ⟨3718488087959196062565217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4957984117278928083420289 3718488087959196062565217)
    ·
      refine ⟨2788866065969397046923913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3718488087959196062565217 2788866065969397046923913)
      ·
        refine ⟨2091649549477047785192935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2788866065969397046923913 2091649549477047785192935)
        ·
          refine ⟨3137474324215571677789403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2091649549477047785192935 3137474324215571677789403)
          ·
            refine ⟨4706211486323357516684105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3137474324215571677789403 4706211486323357516684105)
            ·
              refine ⟨3529658614742518137513079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706211486323357516684105 3529658614742518137513079)
              ·
                refine ⟨5294487922113777206269619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3529658614742518137513079 5294487922113777206269619)
                ·
                  refine ⟨7941731883170665809404429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294487922113777206269619 7941731883170665809404429)
                  ·
                    refine ⟨2978149456188999678526661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7941731883170665809404429 2978149456188999678526661)
                    ·
                      refine ⟨558403023035437439723749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2978149456188999678526661 558403023035437439723749)
                      ·
                        rfl

theorem cell23_1087486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1087486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087486 prefixEnd_1087486 := by exact prefixLift 1087486
  have htrace : WordTrace (prefixWord ++ tailWord_1087486) baseStart_1087486 baseEnd_1087486 := by
    simpa [prefixWord, tailWord_1087486, baseEnd_1087486] using wordTrace_append hprefix tailTrace_1087486
  have hstable : (prefixWord ++ tailWord_1087486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087486).length < 2 ^ (prefixWord ++ tailWord_1087486).sum := by decide
  have hdescent : baseEnd_1087486 < baseStart_1087486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087489 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1087489 : Nat := 118140960795 + 1087489 * 2 ^ 59
def prefixEnd_1087489 : Nat := 4983230072969 + 3 ^ 40 * 1087489 * 2
def baseEnd_1087489 : Nat := 558404563477400927986235

theorem tailTrace_1087489 : CollatzResearch.WordTrace tailWord_1087489 prefixEnd_1087489 558404563477400927986235 := by
  unfold tailWord_1087489
  simp only [CollatzResearch.WordTrace]
  refine ⟨39663982357220556179721521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26442654904813704119814347 39663982357220556179721521)
  ·
    refine ⟨29747986767915417134791141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39663982357220556179721521 29747986767915417134791141)
    ·
      refine ⟨5577747518984140712773339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29747986767915417134791141 5577747518984140712773339)
      ·
        refine ⟨8366621278476211069160009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5577747518984140712773339 8366621278476211069160009)
        ·
          refine ⟨6274965958857158301870007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8366621278476211069160009 6274965958857158301870007)
          ·
            refine ⟨9412448938285737452805011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6274965958857158301870007 9412448938285737452805011)
            ·
              refine ⟨14118673407428606179207517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9412448938285737452805011 14118673407428606179207517)
              ·
                refine ⟨5294502527785727317202819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14118673407428606179207517 5294502527785727317202819)
                ·
                  refine ⟨7941753791678590975804229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5294502527785727317202819 7941753791678590975804229)
                  ·
                    refine ⟨1489078835939735807963293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7941753791678590975804229 1489078835939735807963293)
                    ·
                      refine ⟨558404563477400927986235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489078835939735807963293 558404563477400927986235)
                      ·
                        rfl

theorem cell23_1087489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1087489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087489 prefixEnd_1087489 := by exact prefixLift 1087489
  have htrace : WordTrace (prefixWord ++ tailWord_1087489) baseStart_1087489 baseEnd_1087489 := by
    simpa [prefixWord, tailWord_1087489, baseEnd_1087489] using wordTrace_append hprefix tailTrace_1087489
  have hstable : (prefixWord ++ tailWord_1087489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087489).length < 2 ^ (prefixWord ++ tailWord_1087489).sum := by decide
  have hdescent : baseEnd_1087489 < baseStart_1087489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087532 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7]
def baseStart_1087532 : Nat := 118140960795 + 1087532 * 2 ^ 59
def prefixEnd_1087532 : Nat := 4983230072969 + 3 ^ 40 * 1087532 * 2
def baseEnd_1087532 : Nat := 558426643145544259748537

theorem tailTrace_1087532 : CollatzResearch.WordTrace tailWord_1087532 prefixEnd_1087532 558426643145544259748537 := by
  unfold tailWord_1087532
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832775348032387261768425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26443700464043183015691233 19832775348032387261768425)
  ·
    refine ⟨14874581511024290446326319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19832775348032387261768425 14874581511024290446326319)
    ·
      refine ⟨22311872266536435669489479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14874581511024290446326319 22311872266536435669489479)
      ·
        refine ⟨33467808399804653504234219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22311872266536435669489479 33467808399804653504234219)
        ·
          refine ⟨50201712599706980256351329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33467808399804653504234219 50201712599706980256351329)
          ·
            refine ⟨37651284449780235192263497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50201712599706980256351329 37651284449780235192263497)
            ·
              refine ⟨28238463337335176394197623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37651284449780235192263497 28238463337335176394197623)
              ·
                refine ⟨42357695006002764591296435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28238463337335176394197623 42357695006002764591296435)
                ·
                  refine ⟨63536542509004146886944653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42357695006002764591296435 63536542509004146886944653)
                  ·
                    refine ⟨23826203440876555082604245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63536542509004146886944653 23826203440876555082604245)
                    ·
                      refine ⟨558426643145544259748537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23826203440876555082604245 558426643145544259748537)
                      ·
                        rfl

theorem cell23_1087532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_1087532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087532 prefixEnd_1087532 := by exact prefixLift 1087532
  have htrace : WordTrace (prefixWord ++ tailWord_1087532) baseStart_1087532 baseEnd_1087532 := by
    simpa [prefixWord, tailWord_1087532, baseEnd_1087532] using wordTrace_append hprefix tailTrace_1087532
  have hstable : (prefixWord ++ tailWord_1087532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087532).length < 2 ^ (prefixWord ++ tailWord_1087532).sum := by decide
  have hdescent : baseEnd_1087532 < baseStart_1087532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087540 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_1087540 : Nat := 118140960795 + 1087540 * 2 ^ 59
def prefixEnd_1087540 : Nat := 4983230072969 + 3 ^ 40 * 1087540 * 2
def baseEnd_1087540 : Nat := 558430750990780228448501

theorem tailTrace_1087540 : CollatzResearch.WordTrace tailWord_1087540 prefixEnd_1087540 558430750990780228448501 := by
  unfold tailWord_1087540
  simp only [CollatzResearch.WordTrace]
  refine ⟨19832921240017895944914037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26443894986690527926552049 19832921240017895944914037)
  ·
    refine ⟨1859336366251677744835691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19832921240017895944914037 1859336366251677744835691)
    ·
      refine ⟨2789004549377516617253537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1859336366251677744835691 2789004549377516617253537)
      ·
        refine ⟨2091753412033137462940153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2789004549377516617253537 2091753412033137462940153)
        ·
          refine ⟨1568815059024853097205115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2091753412033137462940153 1568815059024853097205115)
          ·
            refine ⟨2353222588537279645807673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1568815059024853097205115 2353222588537279645807673)
            ·
              refine ⟨1764916941402959734355755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2353222588537279645807673 1764916941402959734355755)
              ·
                refine ⟨2647375412104439601533633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1764916941402959734355755 2647375412104439601533633)
                ·
                  refine ⟨1985531559078329701150225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647375412104439601533633 1985531559078329701150225)
                  ·
                    refine ⟨1489148669308747275862669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985531559078329701150225 1489148669308747275862669)
                    ·
                      refine ⟨558430750990780228448501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489148669308747275862669 558430750990780228448501)
                      ·
                        rfl

theorem cell23_1087540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_1087540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087540 prefixEnd_1087540 := by exact prefixLift 1087540
  have htrace : WordTrace (prefixWord ++ tailWord_1087540) baseStart_1087540 baseEnd_1087540 := by
    simpa [prefixWord, tailWord_1087540, baseEnd_1087540] using wordTrace_append hprefix tailTrace_1087540
  have hstable : (prefixWord ++ tailWord_1087540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087540).length < 2 ^ (prefixWord ++ tailWord_1087540).sum := by decide
  have hdescent : baseEnd_1087540 < baseStart_1087540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087593 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 3, 2, 2]
def baseStart_1087593 : Nat := 118140960795 + 1087593 * 2 ^ 59
def prefixEnd_1087593 : Nat := 4983230072969 + 3 ^ 40 * 1087593 * 2
def baseEnd_1087593 : Nat := 558457965465468521085757

theorem tailTrace_1087593 : CollatzResearch.WordTrace tailWord_1087593 prefixEnd_1087593 558457965465468521085757 := by
  unfold tailWord_1087593
  simp only [CollatzResearch.WordTrace]
  refine ⟨39667775548843781941507433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26445183699229187961004955 39667775548843781941507433)
  ·
    refine ⟨29750831661632836456130575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39667775548843781941507433 29750831661632836456130575)
    ·
      refine ⟨44626247492449254684195863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29750831661632836456130575 44626247492449254684195863)
      ·
        refine ⟨66939371238673882026293795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44626247492449254684195863 66939371238673882026293795)
        ·
          refine ⟨100409056858010823039440693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66939371238673882026293795 100409056858010823039440693)
          ·
            refine ⟨9413349080438514659947565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 100409056858010823039440693 9413349080438514659947565)
            ·
              refine ⟨3530005905164442997480337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9413349080438514659947565 3530005905164442997480337)
              ·
                refine ⟨2647504428873332248110253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3530005905164442997480337 2647504428873332248110253)
                ·
                  refine ⟨992814160827499593041345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2647504428873332248110253 992814160827499593041345)
                  ·
                    refine ⟨744610620620624694781009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 992814160827499593041345 744610620620624694781009)
                    ·
                      refine ⟨558457965465468521085757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744610620620624694781009 558457965465468521085757)
                      ·
                        rfl

theorem cell23_1087593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 2, 2].length) (baseStart_1087593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087593 prefixEnd_1087593 := by exact prefixLift 1087593
  have htrace : WordTrace (prefixWord ++ tailWord_1087593) baseStart_1087593 baseEnd_1087593 := by
    simpa [prefixWord, tailWord_1087593, baseEnd_1087593] using wordTrace_append hprefix tailTrace_1087593
  have hstable : (prefixWord ++ tailWord_1087593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087593).length < 2 ^ (prefixWord ++ tailWord_1087593).sum := by decide
  have hdescent : baseEnd_1087593 < baseStart_1087593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087596 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 3]
def baseStart_1087596 : Nat := 118140960795 + 1087596 * 2 ^ 59
def prefixEnd_1087596 : Nat := 4983230072969 + 3 ^ 40 * 1087596 * 2
def baseEnd_1087596 : Nat := 558459505907432009348243

theorem tailTrace_1087596 : CollatzResearch.WordTrace tailWord_1087596 prefixEnd_1087596 558459505907432009348243 := by
  unfold tailWord_1087596
  simp only [CollatzResearch.WordTrace]
  refine ⟨19833942483916456726933321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26445256645221942302577761 19833942483916456726933321)
  ·
    refine ⟨14875456862937342545199991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19833942483916456726933321 14875456862937342545199991)
    ·
      refine ⟨22313185294406013817799987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14875456862937342545199991 22313185294406013817799987)
      ·
        refine ⟨33469777941609020726699981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22313185294406013817799987 33469777941609020726699981)
        ·
          refine ⟨12551166728103382772512493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33469777941609020726699981 12551166728103382772512493)
          ·
            refine ⟨4706687523038768539692185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12551166728103382772512493 4706687523038768539692185)
            ·
              refine ⟨3530015642279076404769139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4706687523038768539692185 3530015642279076404769139)
              ·
                refine ⟨5295023463418614607153709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3530015642279076404769139 5295023463418614607153709)
                ·
                  refine ⟨1985633798781980477682641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5295023463418614607153709 1985633798781980477682641)
                  ·
                    refine ⟨1489225349086485358261981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985633798781980477682641 1489225349086485358261981)
                    ·
                      refine ⟨558459505907432009348243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489225349086485358261981 558459505907432009348243)
                      ·
                        rfl

theorem cell23_1087596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_1087596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087596 prefixEnd_1087596 := by exact prefixLift 1087596
  have htrace : WordTrace (prefixWord ++ tailWord_1087596) baseStart_1087596 baseEnd_1087596 := by
    simpa [prefixWord, tailWord_1087596, baseEnd_1087596] using wordTrace_append hprefix tailTrace_1087596
  have hstable : (prefixWord ++ tailWord_1087596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087596).length < 2 ^ (prefixWord ++ tailWord_1087596).sum := by decide
  have hdescent : baseEnd_1087596 < baseStart_1087596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087613 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_1087613 : Nat := 118140960795 + 1087613 * 2 ^ 59
def prefixEnd_1087613 : Nat := 4983230072969 + 3 ^ 40 * 1087613 * 2
def baseEnd_1087613 : Nat := 558468235078558442835665

theorem tailTrace_1087613 : CollatzResearch.WordTrace tailWord_1087613 prefixEnd_1087613 558468235078558442835665 := by
  unfold tailWord_1087613
  simp only [CollatzResearch.WordTrace]
  refine ⟨39668505008771325357235493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26445670005847550238156995 39668505008771325357235493)
  ·
    refine ⟨7437844689144623504481655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39668505008771325357235493 7437844689144623504481655)
    ·
      refine ⟨11156767033716935256722483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7437844689144623504481655 11156767033716935256722483)
      ·
        refine ⟨16735150550575402885083725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11156767033716935256722483 16735150550575402885083725)
        ·
          refine ⟨6275681456465776081906397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16735150550575402885083725 6275681456465776081906397)
          ·
            refine ⟨2353380546174666030714899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6275681456465776081906397 2353380546174666030714899)
            ·
              refine ⟨3530070819261999046072349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2353380546174666030714899 3530070819261999046072349)
              ·
                refine ⟨1323776557223249642277131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3530070819261999046072349 1323776557223249642277131)
                ·
                  refine ⟨1985664835834874463415697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1323776557223249642277131 1985664835834874463415697)
                  ·
                    refine ⟨1489248626876155847561773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1985664835834874463415697 1489248626876155847561773)
                    ·
                      refine ⟨558468235078558442835665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489248626876155847561773 558468235078558442835665)
                      ·
                        rfl

theorem cell23_1087613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_1087613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087613 prefixEnd_1087613 := by exact prefixLift 1087613
  have htrace : WordTrace (prefixWord ++ tailWord_1087613) baseStart_1087613 baseEnd_1087613 := by
    simpa [prefixWord, tailWord_1087613, baseEnd_1087613] using wordTrace_append hprefix tailTrace_1087613
  have hstable : (prefixWord ++ tailWord_1087613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087613).length < 2 ^ (prefixWord ++ tailWord_1087613).sum := by decide
  have hdescent : baseEnd_1087613 < baseStart_1087613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087640 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4]
def baseStart_1087640 : Nat := 118140960795 + 1087640 * 2 ^ 59
def prefixEnd_1087640 : Nat := 4983230072969 + 3 ^ 40 * 1087640 * 2
def baseEnd_1087640 : Nat := 558482099056229837198041

theorem tailTrace_1087640 : CollatzResearch.WordTrace tailWord_1087640 prefixEnd_1087640 558482099056229837198041 := by
  unfold tailWord_1087640
  simp only [CollatzResearch.WordTrace]
  refine ⟨19834744889836754484234187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26446326519782339312312249 19834744889836754484234187)
  ·
    refine ⟨29752117334755131726351281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19834744889836754484234187 29752117334755131726351281)
    ·
      refine ⟨22314088001066348794763461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29752117334755131726351281 22314088001066348794763461)
      ·
        refine ⟨4183891500199940399018149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22314088001066348794763461 4183891500199940399018149)
        ·
          refine ⟨784479656287488824815903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4183891500199940399018149 784479656287488824815903)
          ·
            refine ⟨1176719484431233237223855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 784479656287488824815903 1176719484431233237223855)
            ·
              refine ⟨1765079226646849855835783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176719484431233237223855 1765079226646849855835783)
              ·
                refine ⟨2647618839970274783753675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765079226646849855835783 2647618839970274783753675)
                ·
                  refine ⟨3971428259955412175630513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2647618839970274783753675 3971428259955412175630513)
                  ·
                    refine ⟨2978571194966559131722885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3971428259955412175630513 2978571194966559131722885)
                    ·
                      refine ⟨558482099056229837198041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2978571194966559131722885 558482099056229837198041)
                      ·
                        rfl

theorem cell23_1087640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_1087640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087640 prefixEnd_1087640 := by exact prefixLift 1087640
  have htrace : WordTrace (prefixWord ++ tailWord_1087640) baseStart_1087640 baseEnd_1087640 := by
    simpa [prefixWord, tailWord_1087640, baseEnd_1087640] using wordTrace_append hprefix tailTrace_1087640
  have hstable : (prefixWord ++ tailWord_1087640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087640).length < 2 ^ (prefixWord ++ tailWord_1087640).sum := by decide
  have hdescent : baseEnd_1087640 < baseStart_1087640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087689 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 7]
def baseStart_1087689 : Nat := 118140960795 + 1087689 * 2 ^ 59
def prefixEnd_1087689 : Nat := 4983230072969 + 3 ^ 40 * 1087689 * 2
def baseEnd_1087689 : Nat := 62056362178700016165035

theorem tailTrace_1087689 : CollatzResearch.WordTrace tailWord_1087689 prefixEnd_1087689 62056362178700016165035 := by
  unfold tailWord_1087689
  simp only [CollatzResearch.WordTrace]
  refine ⟨39671276956495990337002121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26447517970997326891334747 39671276956495990337002121)
  ·
    refine ⟨29753457717371992752751591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39671276956495990337002121 29753457717371992752751591)
    ·
      refine ⟨44630186576057989129127387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29753457717371992752751591 44630186576057989129127387)
      ·
        refine ⟨66945279864086983693691081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44630186576057989129127387 66945279864086983693691081)
        ·
          refine ⟨50208959898065237770268311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66945279864086983693691081 50208959898065237770268311)
          ·
            refine ⟨75313439847097856655402467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50208959898065237770268311 75313439847097856655402467)
            ·
              refine ⟨112970159770646784983103701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75313439847097856655402467 112970159770646784983103701)
              ·
                refine ⟨2647738119624534023041493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112970159770646784983103701 2647738119624534023041493)
                ·
                  refine ⟨62056362178700016165035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2647738119624534023041493 62056362178700016165035)
                  ·
                    rfl

theorem cell23_1087689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_1087689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087689 prefixEnd_1087689 := by exact prefixLift 1087689
  have htrace : WordTrace (prefixWord ++ tailWord_1087689) baseStart_1087689 baseEnd_1087689 := by
    simpa [prefixWord, tailWord_1087689, baseEnd_1087689] using wordTrace_append hprefix tailTrace_1087689
  have hstable : (prefixWord ++ tailWord_1087689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087689).length < 2 ^ (prefixWord ++ tailWord_1087689).sum := by decide
  have hdescent : baseEnd_1087689 < baseStart_1087689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087716 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1087716 : Nat := 118140960795 + 1087716 * 2 ^ 59
def prefixEnd_1087716 : Nat := 4983230072969 + 3 ^ 40 * 1087716 * 2
def baseEnd_1087716 : Nat := 558521123585971539847691

theorem tailTrace_1087716 : CollatzResearch.WordTrace tailWord_1087716 prefixEnd_1087716 558521123585971539847691 := by
  unfold tailWord_1087716
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836130863699086974117501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26448174484932115965490001 19836130863699086974117501)
  ·
    refine ⟨7438549073887157615294063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19836130863699086974117501 7438549073887157615294063)
    ·
      refine ⟨11157823610830736422941095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7438549073887157615294063 11157823610830736422941095)
      ·
        refine ⟨16736735416246104634411643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11157823610830736422941095 16736735416246104634411643)
        ·
          refine ⟨25105103124369156951617465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16736735416246104634411643 25105103124369156951617465)
          ·
            refine ⟨18828827343276867713713099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25105103124369156951617465 18828827343276867713713099)
            ·
              refine ⟨28243241014915301570569649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18828827343276867713713099 28243241014915301570569649)
              ·
                refine ⟨21182430761186476177927237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28243241014915301570569649 21182430761186476177927237)
                ·
                  refine ⟨3971705767722464283361357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21182430761186476177927237 3971705767722464283361357)
                  ·
                    refine ⟨1489389662895924106260509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3971705767722464283361357 1489389662895924106260509)
                    ·
                      refine ⟨558521123585971539847691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489389662895924106260509 558521123585971539847691)
                      ·
                        rfl

theorem cell23_1087716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1087716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087716 prefixEnd_1087716 := by exact prefixLift 1087716
  have htrace : WordTrace (prefixWord ++ tailWord_1087716) baseStart_1087716 baseEnd_1087716 := by
    simpa [prefixWord, tailWord_1087716, baseEnd_1087716] using wordTrace_append hprefix tailTrace_1087716
  have hstable : (prefixWord ++ tailWord_1087716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087716).length < 2 ^ (prefixWord ++ tailWord_1087716).sum := by decide
  have hdescent : baseEnd_1087716 < baseStart_1087716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087740 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 5]
def baseStart_1087740 : Nat := 118140960795 + 1087740 * 2 ^ 59
def prefixEnd_1087740 : Nat := 4983230072969 + 3 ^ 40 * 1087740 * 2
def baseEnd_1087740 : Nat := 62059271902408827327509

theorem tailTrace_1087740 : CollatzResearch.WordTrace tailWord_1087740 prefixEnd_1087740 62059271902408827327509 := by
  unfold tailWord_1087740
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836568539655613023554337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26448758052874150698072449 19836568539655613023554337)
  ·
    refine ⟨14877426404741709767665753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836568539655613023554337 14877426404741709767665753)
    ·
      refine ⟨11158069803556282325749315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14877426404741709767665753 11158069803556282325749315)
      ·
        refine ⟨16737104705334423488623973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11158069803556282325749315 16737104705334423488623973)
        ·
          refine ⟨3138207132250204404116995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16737104705334423488623973 3138207132250204404116995)
          ·
            refine ⟨4707310698375306606175493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138207132250204404116995 4707310698375306606175493)
            ·
              refine ⟨882620755945369988657905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4707310698375306606175493 882620755945369988657905)
              ·
                refine ⟨661965566959027491493429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 882620755945369988657905 661965566959027491493429)
                ·
                  refine ⟨62059271902408827327509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 661965566959027491493429 62059271902408827327509)
                  ·
                    rfl

theorem cell23_1087740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 5].length) (baseStart_1087740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087740 prefixEnd_1087740 := by exact prefixLift 1087740
  have htrace : WordTrace (prefixWord ++ tailWord_1087740) baseStart_1087740 baseEnd_1087740 := by
    simpa [prefixWord, tailWord_1087740, baseEnd_1087740] using wordTrace_append hprefix tailTrace_1087740
  have hstable : (prefixWord ++ tailWord_1087740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087740).length < 2 ^ (prefixWord ++ tailWord_1087740).sum := by decide
  have hdescent : baseEnd_1087740 < baseStart_1087740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087756 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 1, 3, 4]
def baseStart_1087756 : Nat := 118140960795 + 1087756 * 2 ^ 59
def prefixEnd_1087756 : Nat := 4983230072969 + 3 ^ 40 * 1087756 * 2
def baseEnd_1087756 : Nat := 558541662812151383347507

theorem tailTrace_1087756 : CollatzResearch.WordTrace tailWord_1087756 prefixEnd_1087756 558541662812151383347507 := by
  unfold tailWord_1087756
  simp only [CollatzResearch.WordTrace]
  refine ⟨19836860323626630389845561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26449147098168840519794081 19836860323626630389845561)
  ·
    refine ⟨14877645242719972792384171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19836860323626630389845561 14877645242719972792384171)
    ·
      refine ⟨22316467864079959188576257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877645242719972792384171 22316467864079959188576257)
      ·
        refine ⟨16737350898059969391432193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22316467864079959188576257 16737350898059969391432193)
        ·
          refine ⟨12553013173544977043574145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16737350898059969391432193 12553013173544977043574145)
          ·
            refine ⟨9414759880158732782680609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12553013173544977043574145 9414759880158732782680609)
            ·
              refine ⟨7061069910119049587010457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9414759880158732782680609 7061069910119049587010457)
              ·
                refine ⟨5295802432589287190257843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7061069910119049587010457 5295802432589287190257843)
                ·
                  refine ⟨7943703648883930785386765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5295802432589287190257843 7943703648883930785386765)
                  ·
                    refine ⟨2978888868331474044520037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7943703648883930785386765 2978888868331474044520037)
                    ·
                      refine ⟨558541662812151383347507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2978888868331474044520037 558541662812151383347507)
                      ·
                        rfl

theorem cell23_1087756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_1087756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087756 prefixEnd_1087756 := by exact prefixLift 1087756
  have htrace : WordTrace (prefixWord ++ tailWord_1087756) baseStart_1087756 baseEnd_1087756 := by
    simpa [prefixWord, tailWord_1087756, baseEnd_1087756] using wordTrace_append hprefix tailTrace_1087756
  have hstable : (prefixWord ++ tailWord_1087756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087756).length < 2 ^ (prefixWord ++ tailWord_1087756).sum := by decide
  have hdescent : baseEnd_1087756 < baseStart_1087756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087770 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 2, 5]
def baseStart_1087770 : Nat := 118140960795 + 1087770 * 2 ^ 59
def prefixEnd_1087770 : Nat := 4983230072969 + 3 ^ 40 * 1087770 * 2
def baseEnd_1087770 : Nat := 186182950513771442857481

theorem tailTrace_1087770 : CollatzResearch.WordTrace tailWord_1087770 prefixEnd_1087770 186182950513771442857481 := by
  unfold tailWord_1087770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9918557817300635292675191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26449487512801694113800509 9918557817300635292675191)
  ·
    refine ⟨14877836725950952939012787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9918557817300635292675191 14877836725950952939012787)
    ·
      refine ⟨22316755088926429408519181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14877836725950952939012787 22316755088926429408519181)
      ·
        refine ⟨8368783158347411028194693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22316755088926429408519181 8368783158347411028194693)
        ·
          refine ⟨1569146842190139567786505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8368783158347411028194693 1569146842190139567786505)
          ·
            refine ⟨1176860131642604675839879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1569146842190139567786505 1176860131642604675839879)
            ·
              refine ⟨1765290197463907013759819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1176860131642604675839879 1765290197463907013759819)
              ·
                refine ⟨2647935296195860520639729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765290197463907013759819 2647935296195860520639729)
                ·
                  refine ⟨1985951472146895390479797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2647935296195860520639729 1985951472146895390479797)
                  ·
                    refine ⟨186182950513771442857481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1985951472146895390479797 186182950513771442857481)
                    ·
                      rfl

theorem cell23_1087770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_1087770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087770 prefixEnd_1087770 := by exact prefixLift 1087770
  have htrace : WordTrace (prefixWord ++ tailWord_1087770) baseStart_1087770 baseEnd_1087770 := by
    simpa [prefixWord, tailWord_1087770, baseEnd_1087770] using wordTrace_append hprefix tailTrace_1087770
  have hstable : (prefixWord ++ tailWord_1087770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087770).length < 2 ^ (prefixWord ++ tailWord_1087770).sum := by decide
  have hdescent : baseEnd_1087770 < baseStart_1087770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087800 : List Nat := [2, 1, 2, 1, 3, 1, 4, 4, 1, 4]
def baseStart_1087800 : Nat := 118140960795 + 1087800 * 2 ^ 59
def prefixEnd_1087800 : Nat := 4983230072969 + 3 ^ 40 * 1087800 * 2
def baseEnd_1087800 : Nat := 186188085320316403732435

theorem tailTrace_1087800 : CollatzResearch.WordTrace tailWord_1087800 prefixEnd_1087800 186188085320316403732435 := by
  unfold tailWord_1087800
  simp only [CollatzResearch.WordTrace]
  refine ⟨19837662729546928147146427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26450216972729237529528569 19837662729546928147146427)
  ·
    refine ⟨29756494094320392220719641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19837662729546928147146427 29756494094320392220719641)
    ·
      refine ⟨22317370570740294165539731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29756494094320392220719641 22317370570740294165539731)
      ·
        refine ⟨33476055856110441248309597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22317370570740294165539731 33476055856110441248309597)
        ·
          refine ⟨12553520946041415468116099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33476055856110441248309597 12553520946041415468116099)
          ·
            refine ⟨18830281419062123202174149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12553520946041415468116099 18830281419062123202174149)
            ·
              refine ⟨3530677766074148100407653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18830281419062123202174149 3530677766074148100407653)
              ·
                refine ⟨662002081138902768826435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3530677766074148100407653 662002081138902768826435)
                ·
                  refine ⟨993003121708354153239653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662002081138902768826435 993003121708354153239653)
                  ·
                    refine ⟨186188085320316403732435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993003121708354153239653 186188085320316403732435)
                    ·
                      rfl

theorem cell23_1087800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_1087800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087800 prefixEnd_1087800 := by exact prefixLift 1087800
  have htrace : WordTrace (prefixWord ++ tailWord_1087800) baseStart_1087800 baseEnd_1087800 := by
    simpa [prefixWord, tailWord_1087800, baseEnd_1087800] using wordTrace_append hprefix tailTrace_1087800
  have hstable : (prefixWord ++ tailWord_1087800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087800).length < 2 ^ (prefixWord ++ tailWord_1087800).sum := by decide
  have hdescent : baseEnd_1087800 < baseStart_1087800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087823 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_1087823 : Nat := 118140960795 + 1087823 * 2 ^ 59
def prefixEnd_1087823 : Nat := 4983230072969 + 3 ^ 40 * 1087823 * 2
def baseEnd_1087823 : Nat := 558576066016002621209699

theorem tailTrace_1087823 : CollatzResearch.WordTrace tailWord_1087823 prefixEnd_1087823 558576066016002621209699 := by
  unfold tailWord_1087823
  simp only [CollatzResearch.WordTrace]
  refine ⟨39676164338010531222380123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26450776225340354148253415 39676164338010531222380123)
  ·
    refine ⟨59514246507015796833570185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39676164338010531222380123 59514246507015796833570185)
    ·
      refine ⟨44635684880261847625177639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59514246507015796833570185 44635684880261847625177639)
      ·
        refine ⟨66953527320392771437766459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44635684880261847625177639 66953527320392771437766459)
        ·
          refine ⟨100430290980589157156649689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66953527320392771437766459 100430290980589157156649689)
          ·
            refine ⟨75322718235441867867487267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100430290980589157156649689 75322718235441867867487267)
            ·
              refine ⟨112984077353162801801230901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75322718235441867867487267 112984077353162801801230901)
              ·
                refine ⟨10592257251859012668865397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112984077353162801801230901 10592257251859012668865397)
                ·
                  refine ⟨993024117361782437706131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10592257251859012668865397 993024117361782437706131)
                  ·
                    refine ⟨1489536176042673656559197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 993024117361782437706131 1489536176042673656559197)
                    ·
                      refine ⟨558576066016002621209699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489536176042673656559197 558576066016002621209699)
                      ·
                        rfl

theorem cell23_1087823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_1087823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087823 prefixEnd_1087823 := by exact prefixLift 1087823
  have htrace : WordTrace (prefixWord ++ tailWord_1087823) baseStart_1087823 baseEnd_1087823 := by
    simpa [prefixWord, tailWord_1087823, baseEnd_1087823] using wordTrace_append hprefix tailTrace_1087823
  have hstable : (prefixWord ++ tailWord_1087823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087823).length < 2 ^ (prefixWord ++ tailWord_1087823).sum := by decide
  have hdescent : baseEnd_1087823 < baseStart_1087823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087843 : List Nat := [1, 1, 1, 5, 2, 1, 1, 5, 1, 5]
def baseStart_1087843 : Nat := 118140960795 + 1087843 * 2 ^ 59
def prefixEnd_1087843 : Nat := 4983230072969 + 3 ^ 40 * 1087843 * 2
def baseEnd_1087843 : Nat := 186195445209697514319869

theorem tailTrace_1087843 : CollatzResearch.WordTrace tailWord_1087843 prefixEnd_1087843 186195445209697514319869 := by
  unfold tailWord_1087843
  simp only [CollatzResearch.WordTrace]
  refine ⟨39676893797938074638108183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26451262531958716425405455 39676893797938074638108183)
  ·
    refine ⟨59515340696907111957162275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39676893797938074638108183 59515340696907111957162275)
    ·
      refine ⟨89273011045360667935743413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59515340696907111957162275 89273011045360667935743413)
      ·
        refine ⟨8369344785502562618975945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89273011045360667935743413 8369344785502562618975945)
        ·
          refine ⟨6277008589126921964231959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8369344785502562618975945 6277008589126921964231959)
          ·
            refine ⟨9415512883690382946347939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277008589126921964231959 9415512883690382946347939)
            ·
              refine ⟨14123269325535574419521909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9415512883690382946347939 14123269325535574419521909)
              ·
                refine ⟨1324056499268960101830179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14123269325535574419521909 1324056499268960101830179)
                ·
                  refine ⟨1986084748903440152745269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324056499268960101830179 1986084748903440152745269)
                  ·
                    refine ⟨186195445209697514319869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1986084748903440152745269 186195445209697514319869)
                    ·
                      rfl

theorem cell23_1087843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 5].length) (baseStart_1087843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087843 prefixEnd_1087843 := by exact prefixLift 1087843
  have htrace : WordTrace (prefixWord ++ tailWord_1087843) baseStart_1087843 baseEnd_1087843 := by
    simpa [prefixWord, tailWord_1087843, baseEnd_1087843] using wordTrace_append hprefix tailTrace_1087843
  have hstable : (prefixWord ++ tailWord_1087843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087843).length < 2 ^ (prefixWord ++ tailWord_1087843).sum := by decide
  have hdescent : baseEnd_1087843 < baseStart_1087843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087863 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_1087863 : Nat := 118140960795 + 1087863 * 2 ^ 59
def prefixEnd_1087863 : Nat := 4983230072969 + 3 ^ 40 * 1087863 * 2
def baseEnd_1087863 : Nat := 558596605242182464709515

theorem tailTrace_1087863 : CollatzResearch.WordTrace tailWord_1087863 prefixEnd_1087863 558596605242182464709515 := by
  unfold tailWord_1087863
  simp only [CollatzResearch.WordTrace]
  refine ⟨39677623257865618053836243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26451748838577078702557495 39677623257865618053836243)
  ·
    refine ⟨59516434886798427080754365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39677623257865618053836243 59516434886798427080754365)
    ·
      refine ⟨22318663082549410155282887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59516434886798427080754365 22318663082549410155282887)
      ·
        refine ⟨33477994623824115232924331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22318663082549410155282887 33477994623824115232924331)
        ·
          refine ⟨50216991935736172849386497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33477994623824115232924331 50216991935736172849386497)
          ·
            refine ⟨37662743951802129637039873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50216991935736172849386497 37662743951802129637039873)
            ·
              refine ⟨28247057963851597227779905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37662743951802129637039873 28247057963851597227779905)
              ·
                refine ⟨21185293472888697920834929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28247057963851597227779905 21185293472888697920834929)
                ·
                  refine ⟨15888970104666523440626197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21185293472888697920834929 15888970104666523440626197)
                  ·
                    refine ⟨744795473656243286279353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15888970104666523440626197 744795473656243286279353)
                    ·
                      refine ⟨558596605242182464709515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744795473656243286279353 558596605242182464709515)
                      ·
                        rfl

theorem cell23_1087863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_1087863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087863 prefixEnd_1087863 := by exact prefixLift 1087863
  have htrace : WordTrace (prefixWord ++ tailWord_1087863) baseStart_1087863 baseEnd_1087863 := by
    simpa [prefixWord, tailWord_1087863, baseEnd_1087863] using wordTrace_append hprefix tailTrace_1087863
  have hstable : (prefixWord ++ tailWord_1087863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087863).length < 2 ^ (prefixWord ++ tailWord_1087863).sum := by decide
  have hdescent : baseEnd_1087863 < baseStart_1087863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087924 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1087924 : Nat := 118140960795 + 1087924 * 2 ^ 59
def prefixEnd_1087924 : Nat := 4983230072969 + 3 ^ 40 * 1087924 * 2
def baseEnd_1087924 : Nat := 186209309187368908682245

theorem tailTrace_1087924 : CollatzResearch.WordTrace tailWord_1087924 prefixEnd_1087924 186209309187368908682245 := by
  unfold tailWord_1087924
  simp only [CollatzResearch.WordTrace]
  refine ⟨19839924055322312735903413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26453232073763083647871217 19839924055322312735903413)
  ·
    refine ⟨1859992880186466818990945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19839924055322312735903413 1859992880186466818990945)
    ·
      refine ⟨1394994660139850114243209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1859992880186466818990945 1394994660139850114243209)
      ·
        refine ⟨1046245995104887585682407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1394994660139850114243209 1046245995104887585682407)
        ·
          refine ⟨1569368992657331378523611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046245995104887585682407 1569368992657331378523611)
          ·
            refine ⟨2354053488985997067785417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569368992657331378523611 2354053488985997067785417)
            ·
              refine ⟨1765540116739497800839063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354053488985997067785417 1765540116739497800839063)
              ·
                refine ⟨2648310175109246701258595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1765540116739497800839063 2648310175109246701258595)
                ·
                  refine ⟨3972465262663870051887893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2648310175109246701258595 3972465262663870051887893)
                  ·
                    refine ⟨186209309187368908682245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3972465262663870051887893 186209309187368908682245)
                    ·
                      rfl

theorem cell23_1087924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1087924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087924 prefixEnd_1087924 := by exact prefixLift 1087924
  have htrace : WordTrace (prefixWord ++ tailWord_1087924) baseStart_1087924 baseEnd_1087924 := by
    simpa [prefixWord, tailWord_1087924, baseEnd_1087924] using wordTrace_append hprefix tailTrace_1087924
  have hstable : (prefixWord ++ tailWord_1087924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087924).length < 2 ^ (prefixWord ++ tailWord_1087924).sum := by decide
  have hdescent : baseEnd_1087924 < baseStart_1087924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087981 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1087981 : Nat := 118140960795 + 1087981 * 2 ^ 59
def prefixEnd_1087981 : Nat := 4983230072969 + 3 ^ 40 * 1087981 * 2
def baseEnd_1087981 : Nat := 558657195959413003033973

theorem tailTrace_1087981 : CollatzResearch.WordTrace tailWord_1087981 prefixEnd_1087981 558657195959413003033973 := by
  unfold tailWord_1087981
  simp only [CollatzResearch.WordTrace]
  refine ⟨39681927071438124206631797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26454618047625416137754531 39681927071438124206631797)
  ·
    refine ⟨3720180662947324144371731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39681927071438124206631797 3720180662947324144371731)
    ·
      refine ⟨5580270994420986216557597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3720180662947324144371731 5580270994420986216557597)
      ·
        refine ⟨2092601622907869831209099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5580270994420986216557597 2092601622907869831209099)
        ·
          refine ⟨3138902434361804746813649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092601622907869831209099 3138902434361804746813649)
          ·
            refine ⟨2354176825771353560110237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3138902434361804746813649 2354176825771353560110237)
            ·
              refine ⟨882816309664257585041339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2354176825771353560110237 882816309664257585041339)
              ·
                refine ⟨1324224464496386377562009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 882816309664257585041339 1324224464496386377562009)
                ·
                  refine ⟨993168348372289783171507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324224464496386377562009 993168348372289783171507)
                  ·
                    refine ⟨1489752522558434674757261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 993168348372289783171507 1489752522558434674757261)
                    ·
                      refine ⟨558657195959413003033973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489752522558434674757261 558657195959413003033973)
                      ·
                        rfl

theorem cell23_1087981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1087981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087981 prefixEnd_1087981 := by exact prefixLift 1087981
  have htrace : WordTrace (prefixWord ++ tailWord_1087981) baseStart_1087981 baseEnd_1087981 := by
    simpa [prefixWord, tailWord_1087981, baseEnd_1087981] using wordTrace_append hprefix tailTrace_1087981
  have hstable : (prefixWord ++ tailWord_1087981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087981).length < 2 ^ (prefixWord ++ tailWord_1087981).sum := by decide
  have hdescent : baseEnd_1087981 < baseStart_1087981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087990 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1087990 : Nat := 118140960795 + 1087990 * 2 ^ 59
def prefixEnd_1087990 : Nat := 4983230072969 + 3 ^ 40 * 1087990 * 2
def baseEnd_1087990 : Nat := 558661817285303467821431

theorem tailTrace_1087990 : CollatzResearch.WordTrace tailWord_1087990 prefixEnd_1087990 558661817285303467821431 := by
  unfold tailWord_1087990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2480140958025344921481839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26454836885603679162472949 2480140958025344921481839)
  ·
    refine ⟨3720211437038017382222759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2480140958025344921481839 3720211437038017382222759)
    ·
      refine ⟨5580317155557026073334139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3720211437038017382222759 5580317155557026073334139)
      ·
        refine ⟨8370475733335539110001209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5580317155557026073334139 8370475733335539110001209)
        ·
          refine ⟨6277856800001654332500907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8370475733335539110001209 6277856800001654332500907)
          ·
            refine ⟨9416785200002481498751361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6277856800001654332500907 9416785200002481498751361)
            ·
              refine ⟨7062588900001861124063521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9416785200002481498751361 7062588900001861124063521)
              ·
                refine ⟨5296941675001395843047641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7062588900001861124063521 5296941675001395843047641)
                ·
                  refine ⟨3972706256251046882285731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5296941675001395843047641 3972706256251046882285731)
                  ·
                    refine ⟨5959059384376570323428597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3972706256251046882285731 5959059384376570323428597)
                    ·
                      refine ⟨558661817285303467821431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5959059384376570323428597 558661817285303467821431)
                      ·
                        rfl

theorem cell23_1087990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1087990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087990 prefixEnd_1087990 := by exact prefixLift 1087990
  have htrace : WordTrace (prefixWord ++ tailWord_1087990) baseStart_1087990 baseEnd_1087990 := by
    simpa [prefixWord, tailWord_1087990, baseEnd_1087990] using wordTrace_append hprefix tailTrace_1087990
  have hstable : (prefixWord ++ tailWord_1087990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087990).length < 2 ^ (prefixWord ++ tailWord_1087990).sum := by decide
  have hdescent : baseEnd_1087990 < baseStart_1087990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1087993 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 7]
def baseStart_1087993 : Nat := 118140960795 + 1087993 * 2 ^ 59
def prefixEnd_1087993 : Nat := 4983230072969 + 3 ^ 40 * 1087993 * 2
def baseEnd_1087993 : Nat := 62073706414140772898213

theorem tailTrace_1087993 : CollatzResearch.WordTrace tailWord_1087993 prefixEnd_1087993 62073706414140772898213 := by
  unfold tailWord_1087993
  simp only [CollatzResearch.WordTrace]
  refine ⟨39682364747394650256068633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26454909831596433504045755 39682364747394650256068633)
  ·
    refine ⟨29761773560545987692051475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39682364747394650256068633 29761773560545987692051475)
    ·
      refine ⟨44642660340818981538077213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29761773560545987692051475 44642660340818981538077213)
      ·
        refine ⟨16740997627807118076778955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44642660340818981538077213 16740997627807118076778955)
        ·
          refine ⟨25111496441710677115168433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16740997627807118076778955 25111496441710677115168433)
          ·
            refine ⟨18833622331283007836376325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25111496441710677115168433 18833622331283007836376325)
            ·
              refine ⟨3531304187115563969320561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18833622331283007836376325 3531304187115563969320561)
              ·
                refine ⟨2648478140336672976990421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3531304187115563969320561 2648478140336672976990421)
                ·
                  refine ⟨62073706414140772898213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2648478140336672976990421 62073706414140772898213)
                  ·
                    rfl

theorem cell23_1087993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_1087993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1087993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1087993 prefixEnd_1087993 := by exact prefixLift 1087993
  have htrace : WordTrace (prefixWord ++ tailWord_1087993) baseStart_1087993 baseEnd_1087993 := by
    simpa [prefixWord, tailWord_1087993, baseEnd_1087993] using wordTrace_append hprefix tailTrace_1087993
  have hstable : (prefixWord ++ tailWord_1087993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1087993).length < 2 ^ (prefixWord ++ tailWord_1087993).sum := by decide
  have hdescent : baseEnd_1087993 < baseStart_1087993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1087993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088004 : List Nat := [2, 3, 2, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1088004 : Nat := 118140960795 + 1088004 * 2 ^ 59
def prefixEnd_1088004 : Nat := 4983230072969 + 3 ^ 40 * 1088004 * 2
def baseEnd_1088004 : Nat := 558669006014466413046367

theorem tailTrace_1088004 : CollatzResearch.WordTrace tailWord_1088004 prefixEnd_1088004 558669006014466413046367 := by
  unfold tailWord_1088004
  simp only [CollatzResearch.WordTrace]
  refine ⟨19841382975177399567359533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26455177300236532756479377 19841382975177399567359533)
  ·
    refine ⟨7440518615691524837759825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19841382975177399567359533 7440518615691524837759825)
    ·
      refine ⟨5580388961768643628319869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7440518615691524837759825 5580388961768643628319869)
      ·
        refine ⟨2092645860663241360619951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5580388961768643628319869 2092645860663241360619951)
        ·
          refine ⟨3138968790994862040929927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2092645860663241360619951 3138968790994862040929927)
          ·
            refine ⟨4708453186492293061394891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3138968790994862040929927 4708453186492293061394891)
            ·
              refine ⟨7062679779738439592092337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4708453186492293061394891 7062679779738439592092337)
              ·
                refine ⟨5297009834803829694069253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7062679779738439592092337 5297009834803829694069253)
                ·
                  refine ⟨993189344025718067637985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5297009834803829694069253 993189344025718067637985)
                  ·
                    refine ⟨744892008019288550728489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 993189344025718067637985 744892008019288550728489)
                    ·
                      refine ⟨558669006014466413046367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744892008019288550728489 558669006014466413046367)
                      ·
                        rfl

theorem cell23_1088004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1088004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088004 prefixEnd_1088004 := by exact prefixLift 1088004
  have htrace : WordTrace (prefixWord ++ tailWord_1088004) baseStart_1088004 baseEnd_1088004 := by
    simpa [prefixWord, tailWord_1088004, baseEnd_1088004] using wordTrace_append hprefix tailTrace_1088004
  have hstable : (prefixWord ++ tailWord_1088004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088004).length < 2 ^ (prefixWord ++ tailWord_1088004).sum := by decide
  have hdescent : baseEnd_1088004 < baseStart_1088004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088043 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4]
def baseStart_1088043 : Nat := 118140960795 + 1088043 * 2 ^ 59
def prefixEnd_1088043 : Nat := 4983230072969 + 3 ^ 40 * 1088043 * 2
def baseEnd_1088043 : Nat := 558689031759991760458687

theorem tailTrace_1088043 : CollatzResearch.WordTrace tailWord_1088043 prefixEnd_1088043 558689031759991760458687 := by
  unfold tailWord_1088043
  simp only [CollatzResearch.WordTrace]
  refine ⟨39684188397213508795388783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26456125598142339196925855 39684188397213508795388783)
  ·
    refine ⟨59526282595820263193083175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39684188397213508795388783 59526282595820263193083175)
    ·
      refine ⟨89289423893730394789624763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59526282595820263193083175 89289423893730394789624763)
      ·
        refine ⟨133934135840595592184437145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89289423893730394789624763 133934135840595592184437145)
        ·
          refine ⟨100450601880446694138327859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133934135840595592184437145 100450601880446694138327859)
          ·
            refine ⟨150675902820670041207491789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100450601880446694138327859 150675902820670041207491789)
            ·
              refine ⟨56503463557751265452809421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 150675902820670041207491789 56503463557751265452809421)
              ·
                refine ⟨21188798834156724544803533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56503463557751265452809421 21188798834156724544803533)
                ·
                  refine ⟨7945799562808771704301325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21188798834156724544803533 7945799562808771704301325)
                  ·
                    refine ⟨2979674836053289389112997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7945799562808771704301325 2979674836053289389112997)
                    ·
                      refine ⟨558689031759991760458687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2979674836053289389112997 558689031759991760458687)
                      ·
                        rfl

theorem cell23_1088043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 3, 3, 4].length) (baseStart_1088043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088043 prefixEnd_1088043 := by exact prefixLift 1088043
  have htrace : WordTrace (prefixWord ++ tailWord_1088043) baseStart_1088043 baseEnd_1088043 := by
    simpa [prefixWord, tailWord_1088043, baseEnd_1088043] using wordTrace_append hprefix tailTrace_1088043
  have hstable : (prefixWord ++ tailWord_1088043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088043).length < 2 ^ (prefixWord ++ tailWord_1088043).sum := by decide
  have hdescent : baseEnd_1088043 < baseStart_1088043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088080 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3]
def baseStart_1088080 : Nat := 118140960795 + 1088080 * 2 ^ 59
def prefixEnd_1088080 : Nat := 4983230072969 + 3 ^ 40 * 1088080 * 2
def baseEnd_1088080 : Nat := 558708030544208115696017

theorem tailTrace_1088080 : CollatzResearch.WordTrace tailWord_1088080 prefixEnd_1088080 558708030544208115696017 := by
  unfold tailWord_1088080
  simp only [CollatzResearch.WordTrace]
  refine ⟨19842768949039732057242847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26457025265386309409657129 19842768949039732057242847)
  ·
    refine ⟨29764153423559598085864271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19842768949039732057242847 29764153423559598085864271)
    ·
      refine ⟨44646230135339397128796407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29764153423559598085864271 44646230135339397128796407)
      ·
        refine ⟨66969345203009095693194611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44646230135339397128796407 66969345203009095693194611)
        ·
          refine ⟨100454017804513643539791917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66969345203009095693194611 100454017804513643539791917)
          ·
            refine ⟨37670256676692616327421969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 100454017804513643539791917 37670256676692616327421969)
            ·
              refine ⟨28252692507519462245566477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37670256676692616327421969 28252692507519462245566477)
              ·
                refine ⟨10594759690319798342087429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28252692507519462245566477 10594759690319798342087429)
                ·
                  refine ⟨1986517441934962189141393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10594759690319798342087429 1986517441934962189141393)
                  ·
                    refine ⟨1489888081451221641856045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1986517441934962189141393 1489888081451221641856045)
                    ·
                      refine ⟨558708030544208115696017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1489888081451221641856045 558708030544208115696017)
                      ·
                        rfl

theorem cell23_1088080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 3].length) (baseStart_1088080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088080 prefixEnd_1088080 := by exact prefixLift 1088080
  have htrace : WordTrace (prefixWord ++ tailWord_1088080) baseStart_1088080 baseEnd_1088080 := by
    simpa [prefixWord, tailWord_1088080, baseEnd_1088080] using wordTrace_append hprefix tailTrace_1088080
  have hstable : (prefixWord ++ tailWord_1088080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088080).length < 2 ^ (prefixWord ++ tailWord_1088080).sum := by decide
  have hdescent : baseEnd_1088080 < baseStart_1088080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088100 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 6]
def baseStart_1088100 : Nat := 118140960795 + 1088100 * 2 ^ 59
def prefixEnd_1088100 : Nat := 4983230072969 + 3 ^ 40 * 1088100 * 2
def baseEnd_1088100 : Nat := 62079811128588670827325

theorem tailTrace_1088100 : CollatzResearch.WordTrace tailWord_1088100 prefixEnd_1088100 62079811128588670827325 := by
  unfold tailWord_1088100
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843133679003503765106877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26457511572004671686809169 19843133679003503765106877)
  ·
    refine ⟨7441175129626313911915079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19843133679003503765106877 7441175129626313911915079)
    ·
      refine ⟨11161762694439470867872619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7441175129626313911915079 11161762694439470867872619)
      ·
        refine ⟨16742644041659206301808929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11161762694439470867872619 16742644041659206301808929)
        ·
          refine ⟨12556983031244404726356697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16742644041659206301808929 12556983031244404726356697)
          ·
            refine ⟨9417737273433303544767523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12556983031244404726356697 9417737273433303544767523)
            ·
              refine ⟨14126605910149955317151285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9417737273433303544767523 14126605910149955317151285)
              ·
                refine ⟨1324369304076558310982933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14126605910149955317151285 1324369304076558310982933)
                ·
                  refine ⟨62079811128588670827325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1324369304076558310982933 62079811128588670827325)
                  ·
                    rfl

theorem cell23_1088100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_1088100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088100 prefixEnd_1088100 := by exact prefixLift 1088100
  have htrace : WordTrace (prefixWord ++ tailWord_1088100) baseStart_1088100 baseEnd_1088100 := by
    simpa [prefixWord, tailWord_1088100, baseEnd_1088100] using wordTrace_append hprefix tailTrace_1088100
  have hstable : (prefixWord ++ tailWord_1088100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088100).length < 2 ^ (prefixWord ++ tailWord_1088100).sum := by decide
  have hdescent : baseEnd_1088100 < baseStart_1088100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088104 : List Nat := [2, 1, 4, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1088104 : Nat := 118140960795 + 1088104 * 2 ^ 59
def prefixEnd_1088104 : Nat := 4983230072969 + 3 ^ 40 * 1088104 * 2
def baseEnd_1088104 : Nat := 186240118026638673931969

theorem tailTrace_1088104 : CollatzResearch.WordTrace tailWord_1088104 prefixEnd_1088104 186240118026638673931969 := by
  unfold tailWord_1088104
  simp only [CollatzResearch.WordTrace]
  refine ⟨19843206624996258106679683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26457608833328344142239577 19843206624996258106679683)
  ·
    refine ⟨29764809937494387160019525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19843206624996258106679683 29764809937494387160019525)
    ·
      refine ⟨5580901863280197592503661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29764809937494387160019525 5580901863280197592503661)
      ·
        refine ⟨2092838198730074097188873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5580901863280197592503661 2092838198730074097188873)
        ·
          refine ⟨1569628649047555572891655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2092838198730074097188873 1569628649047555572891655)
          ·
            refine ⟨2354442973571333359337483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569628649047555572891655 2354442973571333359337483)
            ·
              refine ⟨3531664460357000039006225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2354442973571333359337483 3531664460357000039006225)
              ·
                refine ⟨2648748345267750029254669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3531664460357000039006225 2648748345267750029254669)
                ·
                  refine ⟨993280629475406260970501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2648748345267750029254669 993280629475406260970501)
                  ·
                    refine ⟨186240118026638673931969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993280629475406260970501 186240118026638673931969)
                    ·
                      rfl

theorem cell23_1088104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1088104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088104 prefixEnd_1088104 := by exact prefixLift 1088104
  have htrace : WordTrace (prefixWord ++ tailWord_1088104) baseStart_1088104 baseEnd_1088104 := by
    simpa [prefixWord, tailWord_1088104, baseEnd_1088104] using wordTrace_append hprefix tailTrace_1088104
  have hstable : (prefixWord ++ tailWord_1088104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088104).length < 2 ^ (prefixWord ++ tailWord_1088104).sum := by decide
  have hdescent : baseEnd_1088104 < baseStart_1088104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088137 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 4, 3, 2]
def baseStart_1088137 : Nat := 118140960795 + 1088137 * 2 ^ 59
def prefixEnd_1088137 : Nat := 4983230072969 + 3 ^ 40 * 1088137 * 2
def baseEnd_1088137 : Nat := 558737298941514392683255

theorem tailTrace_1088137 : CollatzResearch.WordTrace tailWord_1088137 prefixEnd_1088137 558737298941514392683255 := by
  unfold tailWord_1088137
  simp only [CollatzResearch.WordTrace]
  refine ⟨39687616858872962849310665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26458411239248641899540443 39687616858872962849310665)
  ·
    refine ⟨29765712644154722136982999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39687616858872962849310665 29765712644154722136982999)
    ·
      refine ⟨44648568966232083205474499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29765712644154722136982999 44648568966232083205474499)
      ·
        refine ⟨66972853449348124808211749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44648568966232083205474499 66972853449348124808211749)
        ·
          refine ⟨12557410021752773401539703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66972853449348124808211749 12557410021752773401539703)
          ·
            refine ⟨18836115032629160102309555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12557410021752773401539703 18836115032629160102309555)
            ·
              refine ⟨28254172548943740153464333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18836115032629160102309555 28254172548943740153464333)
              ·
                refine ⟨10595314705853902557549125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28254172548943740153464333 10595314705853902557549125)
                ·
                  refine ⟨1986621507347606729540461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10595314705853902557549125 1986621507347606729540461)
                  ·
                    refine ⟨744983065255352523577673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1986621507347606729540461 744983065255352523577673)
                    ·
                      refine ⟨558737298941514392683255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 744983065255352523577673 558737298941514392683255)
                      ·
                        rfl

theorem cell23_1088137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 3, 2].length) (baseStart_1088137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088137 prefixEnd_1088137 := by exact prefixLift 1088137
  have htrace : WordTrace (prefixWord ++ tailWord_1088137) baseStart_1088137 baseEnd_1088137 := by
    simpa [prefixWord, tailWord_1088137, baseEnd_1088137] using wordTrace_append hprefix tailTrace_1088137
  have hstable : (prefixWord ++ tailWord_1088137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088137).length < 2 ^ (prefixWord ++ tailWord_1088137).sum := by decide
  have hdescent : baseEnd_1088137 < baseStart_1088137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088217 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_1088217 : Nat := 118140960795 + 1088217 * 2 ^ 59
def prefixEnd_1088217 : Nat := 4983230072969 + 3 ^ 40 * 1088217 * 2
def baseEnd_1088217 : Nat := 558778377393874079682887

theorem tailTrace_1088217 : CollatzResearch.WordTrace tailWord_1088217 prefixEnd_1088217 558778377393874079682887 := by
  unfold tailWord_1088217
  simp only [CollatzResearch.WordTrace]
  refine ⟨39690534698583136512222905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26460356465722091008148603 39690534698583136512222905)
  ·
    refine ⟨29767901023937352384167179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39690534698583136512222905 29767901023937352384167179)
    ·
      refine ⟨44651851535906028576250769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29767901023937352384167179 44651851535906028576250769)
      ·
        refine ⟨33488888651929521432188077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44651851535906028576250769 33488888651929521432188077)
        ·
          refine ⟨12558333244473570537070529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33488888651929521432188077 12558333244473570537070529)
          ·
            refine ⟨9418749933355177902802897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12558333244473570537070529 9418749933355177902802897)
            ·
              refine ⟨7064062450016383427102173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9418749933355177902802897 7064062450016383427102173)
              ·
                refine ⟨2649023418756143785163315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7064062450016383427102173 2649023418756143785163315)
                ·
                  refine ⟨3973535128134215677744973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2649023418756143785163315 3973535128134215677744973)
                  ·
                    refine ⟨1490075673050330879154365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3973535128134215677744973 1490075673050330879154365)
                    ·
                      refine ⟨558778377393874079682887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490075673050330879154365 558778377393874079682887)
                      ·
                        rfl

theorem cell23_1088217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_1088217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088217 prefixEnd_1088217 := by exact prefixLift 1088217
  have htrace : WordTrace (prefixWord ++ tailWord_1088217) baseStart_1088217 baseEnd_1088217 := by
    simpa [prefixWord, tailWord_1088217, baseEnd_1088217] using wordTrace_append hprefix tailTrace_1088217
  have hstable : (prefixWord ++ tailWord_1088217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088217).length < 2 ^ (prefixWord ++ tailWord_1088217).sum := by decide
  have hdescent : baseEnd_1088217 < baseStart_1088217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088245 : List Nat := [1, 3, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1088245 : Nat := 118140960795 + 1088245 * 2 ^ 59
def prefixEnd_1088245 : Nat := 4983230072969 + 3 ^ 40 * 1088245 * 2
def baseEnd_1088245 : Nat := 186264251617399990044253

theorem tailTrace_1088245 : CollatzResearch.WordTrace tailWord_1088245 prefixEnd_1088245 186264251617399990044253 := by
  unfold tailWord_1088245
  simp only [CollatzResearch.WordTrace]
  refine ⟨39691555942481697294242189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26461037294987798196161459 39691555942481697294242189)
  ·
    refine ⟨14884333478430636485340821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39691555942481697294242189 14884333478430636485340821)
    ·
      refine ⟨697703131801436085250351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14884333478430636485340821 697703131801436085250351)
      ·
        refine ⟨1046554697702154127875527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697703131801436085250351 1046554697702154127875527)
        ·
          refine ⟨1569832046553231191813291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1046554697702154127875527 1569832046553231191813291)
          ·
            refine ⟨2354748069829846787719937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569832046553231191813291 2354748069829846787719937)
            ·
              refine ⟨1766061052372385090789953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354748069829846787719937 1766061052372385090789953)
              ·
                refine ⟨1324545789279288818092465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766061052372385090789953 1324545789279288818092465)
                ·
                  refine ⟨993409341959466613569349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324545789279288818092465 993409341959466613569349)
                  ·
                    refine ⟨186264251617399990044253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993409341959466613569349 186264251617399990044253)
                    ·
                      rfl

theorem cell23_1088245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1088245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088245 prefixEnd_1088245 := by exact prefixLift 1088245
  have htrace : WordTrace (prefixWord ++ tailWord_1088245) baseStart_1088245 baseEnd_1088245 := by
    simpa [prefixWord, tailWord_1088245, baseEnd_1088245] using wordTrace_append hprefix tailTrace_1088245
  have hstable : (prefixWord ++ tailWord_1088245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088245).length < 2 ^ (prefixWord ++ tailWord_1088245).sum := by decide
  have hdescent : baseEnd_1088245 < baseStart_1088245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088277 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1088277 : Nat := 118140960795 + 1088277 * 2 ^ 59
def prefixEnd_1088277 : Nat := 4983230072969 + 3 ^ 40 * 1088277 * 2
def baseEnd_1088277 : Nat := 558809186233143844932611

theorem tailTrace_1088277 : CollatzResearch.WordTrace tailWord_1088277 prefixEnd_1088277 558809186233143844932611 := by
  unfold tailWord_1088277
  simp only [CollatzResearch.WordTrace]
  refine ⟨39692723078365766759407085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26461815385577177839604723 39692723078365766759407085)
  ·
    refine ⟨14884771154387162534777657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39692723078365766759407085 14884771154387162534777657)
    ·
      refine ⟨11163578365790371901083243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14884771154387162534777657 11163578365790371901083243)
      ·
        refine ⟨16745367548685557851624865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11163578365790371901083243 16745367548685557851624865)
        ·
          refine ⟨12559025661514168388718649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16745367548685557851624865 12559025661514168388718649)
          ·
            refine ⟨9419269246135626291538987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12559025661514168388718649 9419269246135626291538987)
            ·
              refine ⟨14128903869203439437308481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9419269246135626291538987 14128903869203439437308481)
              ·
                refine ⟨10596677901902579577981361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14128903869203439437308481 10596677901902579577981361)
                ·
                  refine ⟨7947508426426934683486021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10596677901902579577981361 7947508426426934683486021)
                  ·
                    refine ⟨1490157829955050253153629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7947508426426934683486021 1490157829955050253153629)
                    ·
                      refine ⟨558809186233143844932611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490157829955050253153629 558809186233143844932611)
                      ·
                        rfl

theorem cell23_1088277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1088277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088277 prefixEnd_1088277 := by exact prefixLift 1088277
  have htrace : WordTrace (prefixWord ++ tailWord_1088277) baseStart_1088277 baseEnd_1088277 := by
    simpa [prefixWord, tailWord_1088277, baseEnd_1088277] using wordTrace_append hprefix tailTrace_1088277
  have hstable : (prefixWord ++ tailWord_1088277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088277).length < 2 ^ (prefixWord ++ tailWord_1088277).sum := by decide
  have hdescent : baseEnd_1088277 < baseStart_1088277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088314 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 7]
def baseStart_1088314 : Nat := 118140960795 + 1088314 * 2 ^ 59
def prefixEnd_1088314 : Nat := 4983230072969 + 3 ^ 40 * 1088314 * 2
def baseEnd_1088314 : Nat := 62092020557484466685549

theorem tailTrace_1088314 : CollatzResearch.WordTrace tailWord_1088314 prefixEnd_1088314 62092020557484466685549 := by
  unfold tailWord_1088314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9923518144807930519625999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26462715052821148052335997 9923518144807930519625999)
  ·
    refine ⟨14885277217211895779438999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9923518144807930519625999 14885277217211895779438999)
    ·
      refine ⟨22327915825817843669158499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14885277217211895779438999 22327915825817843669158499)
      ·
        refine ⟨33491873738726765503737749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22327915825817843669158499 33491873738726765503737749)
        ·
          refine ⟨1569931581502817132987707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33491873738726765503737749 1569931581502817132987707)
          ·
            refine ⟨2354897372254225699481561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1569931581502817132987707 2354897372254225699481561)
            ·
              refine ⟨1766173029190669274611171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2354897372254225699481561 1766173029190669274611171)
              ·
                refine ⟨2649259543786003911916757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766173029190669274611171 2649259543786003911916757)
                ·
                  refine ⟨62092020557484466685549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2649259543786003911916757 62092020557484466685549)
                  ·
                    rfl

theorem cell23_1088314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 7].length) (baseStart_1088314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088314 prefixEnd_1088314 := by exact prefixLift 1088314
  have htrace : WordTrace (prefixWord ++ tailWord_1088314) baseStart_1088314 baseEnd_1088314 := by
    simpa [prefixWord, tailWord_1088314, baseEnd_1088314] using wordTrace_append hprefix tailTrace_1088314
  have hstable : (prefixWord ++ tailWord_1088314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088314).length < 2 ^ (prefixWord ++ tailWord_1088314).sum := by decide
  have hdescent : baseEnd_1088314 < baseStart_1088314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088334 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_1088334 : Nat := 118140960795 + 1088334 * 2 ^ 59
def prefixEnd_1088334 : Nat := 4983230072969 + 3 ^ 40 * 1088334 * 2
def baseEnd_1088334 : Nat := 558838454630450121919849

theorem tailTrace_1088334 : CollatzResearch.WordTrace tailWord_1088334 prefixEnd_1088334 558838454630450121919849 := by
  unfold tailWord_1088334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4961850254894908186779007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26463201359439510329488037 4961850254894908186779007)
  ·
    refine ⟨7442775382342362280168511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4961850254894908186779007 7442775382342362280168511)
    ·
      refine ⟨11164163073513543420252767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7442775382342362280168511 11164163073513543420252767)
      ·
        refine ⟨16746244610270315130379151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11164163073513543420252767 16746244610270315130379151)
        ·
          refine ⟨25119366915405472695568727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16746244610270315130379151 25119366915405472695568727)
          ·
            refine ⟨37679050373108209043353091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25119366915405472695568727 37679050373108209043353091)
            ·
              refine ⟨56518575559662313565029637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37679050373108209043353091 56518575559662313565029637)
              ·
                refine ⟨10597232917436683793443057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56518575559662313565029637 10597232917436683793443057)
                ·
                  refine ⟨7947924688077512845082293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10597232917436683793443057 7947924688077512845082293)
                  ·
                    refine ⟨745117939507266829226465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7947924688077512845082293 745117939507266829226465)
                    ·
                      refine ⟨558838454630450121919849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745117939507266829226465 558838454630450121919849)
                      ·
                        rfl

theorem cell23_1088334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_1088334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088334 prefixEnd_1088334 := by exact prefixLift 1088334
  have htrace : WordTrace (prefixWord ++ tailWord_1088334) baseStart_1088334 baseEnd_1088334 := by
    simpa [prefixWord, tailWord_1088334, baseEnd_1088334] using wordTrace_append hprefix tailTrace_1088334
  have hstable : (prefixWord ++ tailWord_1088334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088334).length < 2 ^ (prefixWord ++ tailWord_1088334).sum := by decide
  have hdescent : baseEnd_1088334 < baseStart_1088334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088348 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 5]
def baseStart_1088348 : Nat := 118140960795 + 1088348 * 2 ^ 59
def prefixEnd_1088348 : Nat := 4983230072969 + 3 ^ 40 * 1088348 * 2
def baseEnd_1088348 : Nat := 62093960373290340793865

theorem tailTrace_1088348 : CollatzResearch.WordTrace tailWord_1088348 prefixEnd_1088348 62093960373290340793865 := by
  unfold tailWord_1088348
  simp only [CollatzResearch.WordTrace]
  refine ⟨19847656330554272942620849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26463541774072363923494465 19847656330554272942620849)
  ·
    refine ⟨14885742247915704706965637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19847656330554272942620849 14885742247915704706965637)
    ·
      refine ⟨2791076671484194632556057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14885742247915704706965637 2791076671484194632556057)
      ·
        refine ⟨2093307503613145974417043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2791076671484194632556057 2093307503613145974417043)
        ·
          refine ⟨3139961255419718961625565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093307503613145974417043 3139961255419718961625565)
          ·
            refine ⟨1177485470782394610609587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3139961255419718961625565 1177485470782394610609587)
            ·
              refine ⟨1766228206173591915914381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177485470782394610609587 1766228206173591915914381)
              ·
                refine ⟨662335577315096968467893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1766228206173591915914381 662335577315096968467893)
                ·
                  refine ⟨62093960373290340793865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662335577315096968467893 62093960373290340793865)
                  ·
                    rfl

theorem cell23_1088348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_1088348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088348 prefixEnd_1088348 := by exact prefixLift 1088348
  have htrace : WordTrace (prefixWord ++ tailWord_1088348) baseStart_1088348 baseEnd_1088348 := by
    simpa [prefixWord, tailWord_1088348, baseEnd_1088348] using wordTrace_append hprefix tailTrace_1088348
  have hstable : (prefixWord ++ tailWord_1088348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088348).length < 2 ^ (prefixWord ++ tailWord_1088348).sum := by decide
  have hdescent : baseEnd_1088348 < baseStart_1088348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088364 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 4]
def baseStart_1088364 : Nat := 118140960795 + 1088364 * 2 ^ 59
def prefixEnd_1088364 : Nat := 4983230072969 + 3 ^ 40 * 1088364 * 2
def baseEnd_1088364 : Nat := 558853859050085004544711

theorem tailTrace_1088364 : CollatzResearch.WordTrace tailWord_1088364 prefixEnd_1088364 558853859050085004544711 := by
  unfold tailWord_1088364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19847948114525290308912073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26463930819367053745216097 19847948114525290308912073)
  ·
    refine ⟨14885961085893967731684055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19847948114525290308912073 14885961085893967731684055)
    ·
      refine ⟨22328941628840951597526083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14885961085893967731684055 22328941628840951597526083)
      ·
        refine ⟨33493412443261427396289125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22328941628840951597526083 33493412443261427396289125)
        ·
          refine ⟨6280014833111517636804211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33493412443261427396289125 6280014833111517636804211)
          ·
            refine ⟨9420022249667276455206317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6280014833111517636804211 9420022249667276455206317)
            ·
              refine ⟨3532508343625228670702369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9420022249667276455206317 3532508343625228670702369)
              ·
                refine ⟨2649381257718921503026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3532508343625228670702369 2649381257718921503026777)
                ·
                  refine ⟨1987035943289191127270083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649381257718921503026777 1987035943289191127270083)
                  ·
                    refine ⟨2980553914933786690905125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987035943289191127270083 2980553914933786690905125)
                    ·
                      refine ⟨558853859050085004544711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2980553914933786690905125 558853859050085004544711)
                      ·
                        rfl

theorem cell23_1088364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_1088364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088364 prefixEnd_1088364 := by exact prefixLift 1088364
  have htrace : WordTrace (prefixWord ++ tailWord_1088364) baseStart_1088364 baseEnd_1088364 := by
    simpa [prefixWord, tailWord_1088364, baseEnd_1088364] using wordTrace_append hprefix tailTrace_1088364
  have hstable : (prefixWord ++ tailWord_1088364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088364).length < 2 ^ (prefixWord ++ tailWord_1088364).sum := by decide
  have hdescent : baseEnd_1088364 < baseStart_1088364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088452 : List Nat := [2, 3, 3, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1088452 : Nat := 118140960795 + 1088452 * 2 ^ 59
def prefixEnd_1088452 : Nat := 4983230072969 + 3 ^ 40 * 1088452 * 2
def baseEnd_1088452 : Nat := 558899045347680660244307

theorem tailTrace_1088452 : CollatzResearch.WordTrace tailWord_1088452 prefixEnd_1088452 558899045347680660244307 := by
  unfold tailWord_1088452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849552926365885823513805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26466070568487847764685073 19849552926365885823513805)
  ·
    refine ⟨7443582347387207183817677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19849552926365885823513805 7443582347387207183817677)
    ·
      refine ⟨2791343380270202693931629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7443582347387207183817677 2791343380270202693931629)
      ·
        refine ⟨1046753767601326010224361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2791343380270202693931629 1046753767601326010224361)
        ·
          refine ⟨785065325700994507668271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1046753767601326010224361 785065325700994507668271)
          ·
            refine ⟨1177597988551491761502407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785065325700994507668271 1177597988551491761502407)
            ·
              refine ⟨1766396982827237642253611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1177597988551491761502407 1766396982827237642253611)
              ·
                refine ⟨2649595474240856463380417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1766396982827237642253611 2649595474240856463380417)
                ·
                  refine ⟨1987196605680642347535313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2649595474240856463380417 1987196605680642347535313)
                  ·
                    refine ⟨1490397454260481760651485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987196605680642347535313 1490397454260481760651485)
                    ·
                      refine ⟨558899045347680660244307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490397454260481760651485 558899045347680660244307)
                      ·
                        rfl

theorem cell23_1088452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1088452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088452 prefixEnd_1088452 := by exact prefixLift 1088452
  have htrace : WordTrace (prefixWord ++ tailWord_1088452) baseStart_1088452 baseEnd_1088452 := by
    simpa [prefixWord, tailWord_1088452, baseEnd_1088452] using wordTrace_append hprefix tailTrace_1088452
  have hstable : (prefixWord ++ tailWord_1088452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088452).length < 2 ^ (prefixWord ++ tailWord_1088452).sum := by decide
  have hdescent : baseEnd_1088452 < baseStart_1088452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088457 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_1088457 : Nat := 118140960795 + 1088457 * 2 ^ 59
def prefixEnd_1088457 : Nat := 4983230072969 + 3 ^ 40 * 1088457 * 2
def baseEnd_1088457 : Nat := 558901612750953140681783

theorem tailTrace_1088457 : CollatzResearch.WordTrace tailWord_1088457 prefixEnd_1088457 558901612750953140681783 := by
  unfold tailWord_1088457
  simp only [CollatzResearch.WordTrace]
  refine ⟨39699288217713657500959625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26466192145142438333973083 39699288217713657500959625)
  ·
    refine ⟨29774466163285243125719719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39699288217713657500959625 29774466163285243125719719)
    ·
      refine ⟨44661699244927864688579579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29774466163285243125719719 44661699244927864688579579)
      ·
        refine ⟨66992548867391797032869369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44661699244927864688579579 66992548867391797032869369)
        ·
          refine ⟨50244411650543847774652027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66992548867391797032869369 50244411650543847774652027)
          ·
            refine ⟨75366617475815771661978041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50244411650543847774652027 75366617475815771661978041)
            ·
              refine ⟨56524963106861828746483531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75366617475815771661978041 56524963106861828746483531)
              ·
                refine ⟨84787444660292743119725297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56524963106861828746483531 84787444660292743119725297)
                ·
                  refine ⟨63590583495219557339793973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84787444660292743119725297 63590583495219557339793973)
                  ·
                    refine ⟨5961617202676833500605685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63590583495219557339793973 5961617202676833500605685)
                    ·
                      refine ⟨558901612750953140681783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5961617202676833500605685 558901612750953140681783)
                      ·
                        rfl

theorem cell23_1088457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_1088457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088457 prefixEnd_1088457 := by exact prefixLift 1088457
  have htrace : WordTrace (prefixWord ++ tailWord_1088457) baseStart_1088457 baseEnd_1088457 := by
    simpa [prefixWord, tailWord_1088457, baseEnd_1088457] using wordTrace_append hprefix tailTrace_1088457
  have hstable : (prefixWord ++ tailWord_1088457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088457).length < 2 ^ (prefixWord ++ tailWord_1088457).sum := by decide
  have hdescent : baseEnd_1088457 < baseStart_1088457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088464 : List Nat := [2, 1, 1, 1, 1, 2, 3, 4, 4, 4]
def baseStart_1088464 : Nat := 118140960795 + 1088464 * 2 ^ 59
def prefixEnd_1088464 : Nat := 4983230072969 + 3 ^ 40 * 1088464 * 2
def baseEnd_1088464 : Nat := 186301735705178204431417

theorem tailTrace_1088464 : CollatzResearch.WordTrace tailWord_1088464 prefixEnd_1088464 186301735705178204431417 := by
  unfold tailWord_1088464
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849771764344148848232223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26466362352458865130976297 19849771764344148848232223)
  ·
    refine ⟨29774657646516223272348335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19849771764344148848232223 29774657646516223272348335)
    ·
      refine ⟨44661986469774334908522503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29774657646516223272348335 44661986469774334908522503)
      ·
        refine ⟨66992979704661502362783755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44661986469774334908522503 66992979704661502362783755)
        ·
          refine ⟨100489469556992253544175633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66992979704661502362783755 100489469556992253544175633)
          ·
            refine ⟨75367102167744190158131725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 100489469556992253544175633 75367102167744190158131725)
            ·
              refine ⟨28262663312904071309299397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75367102167744190158131725 28262663312904071309299397)
              ·
                refine ⟨5299249371169513370493637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28262663312904071309299397 5299249371169513370493637)
                ·
                  refine ⟨993609257094283756967557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5299249371169513370493637 993609257094283756967557)
                  ·
                    refine ⟨186301735705178204431417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 993609257094283756967557 186301735705178204431417)
                    ·
                      rfl

theorem cell23_1088464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 4, 4, 4].length) (baseStart_1088464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088464 prefixEnd_1088464 := by exact prefixLift 1088464
  have htrace : WordTrace (prefixWord ++ tailWord_1088464) baseStart_1088464 baseEnd_1088464 := by
    simpa [prefixWord, tailWord_1088464, baseEnd_1088464] using wordTrace_append hprefix tailTrace_1088464
  have hstable : (prefixWord ++ tailWord_1088464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088464).length < 2 ^ (prefixWord ++ tailWord_1088464).sum := by decide
  have hdescent : baseEnd_1088464 < baseStart_1088464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088468 : List Nat := [2, 4, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_1088468 : Nat := 118140960795 + 1088468 * 2 ^ 59
def prefixEnd_1088468 : Nat := 4983230072969 + 3 ^ 40 * 1088468 * 2
def baseEnd_1088468 : Nat := 186302420346050865881411

theorem tailTrace_1088468 : CollatzResearch.WordTrace tailWord_1088468 prefixEnd_1088468 186302420346050865881411 := by
  unfold tailWord_1088468
  simp only [CollatzResearch.WordTrace]
  refine ⟨19849844710336903189805029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26466459613782537586406705 19849844710336903189805029)
  ·
    refine ⟨3721845883188169348088443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19849844710336903189805029 3721845883188169348088443)
    ·
      refine ⟨5582768824782254022132665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3721845883188169348088443 5582768824782254022132665)
      ·
        refine ⟨4187076618586690516599499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5582768824782254022132665 4187076618586690516599499)
        ·
          refine ⟨6280614927880035774899249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4187076618586690516599499 6280614927880035774899249)
          ·
            refine ⟨4710461195910026831174437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6280614927880035774899249 4710461195910026831174437)
            ·
              refine ⟨883211474233130030845207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4710461195910026831174437 883211474233130030845207)
              ·
                refine ⟨1324817211349695046267811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883211474233130030845207 1324817211349695046267811)
                ·
                  refine ⟨1987225817024542569401717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324817211349695046267811 1987225817024542569401717)
                  ·
                    refine ⟨186302420346050865881411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1987225817024542569401717 186302420346050865881411)
                    ·
                      rfl

theorem cell23_1088468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_1088468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088468 prefixEnd_1088468 := by exact prefixLift 1088468
  have htrace : WordTrace (prefixWord ++ tailWord_1088468) baseStart_1088468 baseEnd_1088468 := by
    simpa [prefixWord, tailWord_1088468, baseEnd_1088468] using wordTrace_append hprefix tailTrace_1088468
  have hstable : (prefixWord ++ tailWord_1088468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088468).length < 2 ^ (prefixWord ++ tailWord_1088468).sum := by decide
  have hdescent : baseEnd_1088468 < baseStart_1088468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088482 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1088482 : Nat := 118140960795 + 1088482 * 2 ^ 59
def prefixEnd_1088482 : Nat := 4983230072969 + 3 ^ 40 * 1088482 * 2
def baseEnd_1088482 : Nat := 558914449767315542869169

theorem tailTrace_1088482 : CollatzResearch.WordTrace tailWord_1088482 prefixEnd_1088482 558914449767315542869169 := by
  unfold tailWord_1088482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925050010655771692654925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26466800028415391180413133 9925050010655771692654925)
  ·
    refine ⟨3721893753995914384745597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9925050010655771692654925 3721893753995914384745597)
    ·
      refine ⟨1395710157748467894279599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3721893753995914384745597 1395710157748467894279599)
      ·
        refine ⟨2093565236622701841419399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395710157748467894279599 2093565236622701841419399)
        ·
          refine ⟨3140347854934052762129099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093565236622701841419399 3140347854934052762129099)
          ·
            refine ⟨4710521782401079143193649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140347854934052762129099 4710521782401079143193649)
            ·
              refine ⟨3532891336800809357395237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4710521782401079143193649 3532891336800809357395237)
              ·
                refine ⟨662417125650151754511607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3532891336800809357395237 662417125650151754511607)
                ·
                  refine ⟨993625688475227631767411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662417125650151754511607 993625688475227631767411)
                  ·
                    refine ⟨1490438532712841447651117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 993625688475227631767411 1490438532712841447651117)
                    ·
                      refine ⟨558914449767315542869169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490438532712841447651117 558914449767315542869169)
                      ·
                        rfl

theorem cell23_1088482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1088482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088482 prefixEnd_1088482 := by exact prefixLift 1088482
  have htrace : WordTrace (prefixWord ++ tailWord_1088482) baseStart_1088482 baseEnd_1088482 := by
    simpa [prefixWord, tailWord_1088482, baseEnd_1088482] using wordTrace_append hprefix tailTrace_1088482
  have hstable : (prefixWord ++ tailWord_1088482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088482).length < 2 ^ (prefixWord ++ tailWord_1088482).sum := by decide
  have hdescent : baseEnd_1088482 < baseStart_1088482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088488 : List Nat := [2, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2]
def baseStart_1088488 : Nat := 118140960795 + 1088488 * 2 ^ 59
def prefixEnd_1088488 : Nat := 4983230072969 + 3 ^ 40 * 1088488 * 2
def baseEnd_1088488 : Nat := 558917530651242519394141

theorem tailTrace_1088488 : CollatzResearch.WordTrace tailWord_1088488 prefixEnd_1088488 558917530651242519394141 := by
  unfold tailWord_1088488
  simp only [CollatzResearch.WordTrace]
  refine ⟨19850209440300674897669059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26466945920400899863558745 19850209440300674897669059)
  ·
    refine ⟨29775314160451012346503589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19850209440300674897669059 29775314160451012346503589)
    ·
      refine ⟨5582871405084564814969423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29775314160451012346503589 5582871405084564814969423)
      ·
        refine ⟨8374307107626847222454135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5582871405084564814969423 8374307107626847222454135)
        ·
          refine ⟨12561460661440270833681203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374307107626847222454135 12561460661440270833681203)
          ·
            refine ⟨18842190992160406250521805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12561460661440270833681203 18842190992160406250521805)
            ·
              refine ⟨7065821622060152343945677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18842190992160406250521805 7065821622060152343945677)
              ·
                refine ⟨2649683108272557128979629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7065821622060152343945677 2649683108272557128979629)
                ·
                  refine ⟨993631165602208923367361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2649683108272557128979629 993631165602208923367361)
                  ·
                    refine ⟨745223374201656692525521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 993631165602208923367361 745223374201656692525521)
                    ·
                      refine ⟨558917530651242519394141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745223374201656692525521 558917530651242519394141)
                      ·
                        rfl

theorem cell23_1088488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_1088488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088488 prefixEnd_1088488 := by exact prefixLift 1088488
  have htrace : WordTrace (prefixWord ++ tailWord_1088488) baseStart_1088488 baseEnd_1088488 := by
    simpa [prefixWord, tailWord_1088488, baseEnd_1088488] using wordTrace_append hprefix tailTrace_1088488
  have hstable : (prefixWord ++ tailWord_1088488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088488).length < 2 ^ (prefixWord ++ tailWord_1088488).sum := by decide
  have hdescent : baseEnd_1088488 < baseStart_1088488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088508 : List Nat := [2, 2, 2, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_1088508 : Nat := 118140960795 + 1088508 * 2 ^ 59
def prefixEnd_1088508 : Nat := 4983230072969 + 3 ^ 40 * 1088508 * 2
def baseEnd_1088508 : Nat := 558927800264332441144049

theorem tailTrace_1088508 : CollatzResearch.WordTrace tailWord_1088508 prefixEnd_1088508 558927800264332441144049 := by
  unfold tailWord_1088508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19850574170264446605533089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26467432227019262140710785 19850574170264446605533089)
  ·
    refine ⟨14887930627698334954149817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19850574170264446605533089 14887930627698334954149817)
    ·
      refine ⟨11165947970773751215612363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14887930627698334954149817 11165947970773751215612363)
      ·
        refine ⟨16748921956160626823418545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11165947970773751215612363 16748921956160626823418545)
        ·
          refine ⟨12561691467120470117563909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16748921956160626823418545 12561691467120470117563909)
          ·
            refine ⟨2355317150085088147043233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12561691467120470117563909 2355317150085088147043233)
            ·
              refine ⟨1766487862563816110282425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2355317150085088147043233 1766487862563816110282425)
              ·
                refine ⟨1324865896922862082711819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1766487862563816110282425 1324865896922862082711819)
                ·
                  refine ⟨1987298845384293124067729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1324865896922862082711819 1987298845384293124067729)
                  ·
                    refine ⟨1490474134038219843050797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987298845384293124067729 1490474134038219843050797)
                    ·
                      refine ⟨558927800264332441144049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490474134038219843050797 558927800264332441144049)
                      ·
                        rfl

theorem cell23_1088508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_1088508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088508 prefixEnd_1088508 := by exact prefixLift 1088508
  have htrace : WordTrace (prefixWord ++ tailWord_1088508) baseStart_1088508 baseEnd_1088508 := by
    simpa [prefixWord, tailWord_1088508, baseEnd_1088508] using wordTrace_append hprefix tailTrace_1088508
  have hstable : (prefixWord ++ tailWord_1088508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088508).length < 2 ^ (prefixWord ++ tailWord_1088508).sum := by decide
  have hdescent : baseEnd_1088508 < baseStart_1088508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088522 : List Nat := [3, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_1088522 : Nat := 118140960795 + 1088522 * 2 ^ 59
def prefixEnd_1088522 : Nat := 4983230072969 + 3 ^ 40 * 1088522 * 2
def baseEnd_1088522 : Nat := 558934988993495386368985

theorem tailTrace_1088522 : CollatzResearch.WordTrace tailWord_1088522 prefixEnd_1088522 558934988993495386368985 := by
  unfold tailWord_1088522
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925414740619543400518955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26467772641652115734717213 9925414740619543400518955)
  ·
    refine ⟨14888122110929315100778433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9925414740619543400518955 14888122110929315100778433)
    ·
      refine ⟨11166091583196986325583825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14888122110929315100778433 11166091583196986325583825)
      ·
        refine ⟨8374568687397739744187869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11166091583196986325583825 8374568687397739744187869)
        ·
          refine ⟨3140463257774152404070451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8374568687397739744187869 3140463257774152404070451)
          ·
            refine ⟨4710694886661228606105677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140463257774152404070451 4710694886661228606105677)
            ·
              refine ⟨1766510582497960727289629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4710694886661228606105677 1766510582497960727289629)
              ·
                refine ⟨662441468436735272733611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1766510582497960727289629 662441468436735272733611)
                ·
                  refine ⟨993662202655102909100417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662441468436735272733611 993662202655102909100417)
                  ·
                    refine ⟨745246651991327181825313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 993662202655102909100417 745246651991327181825313)
                    ·
                      refine ⟨558934988993495386368985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745246651991327181825313 558934988993495386368985)
                      ·
                        rfl

theorem cell23_1088522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_1088522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088522 prefixEnd_1088522 := by exact prefixLift 1088522
  have htrace : WordTrace (prefixWord ++ tailWord_1088522) baseStart_1088522 baseEnd_1088522 := by
    simpa [prefixWord, tailWord_1088522, baseEnd_1088522] using wordTrace_append hprefix tailTrace_1088522
  have hstable : (prefixWord ++ tailWord_1088522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088522).length < 2 ^ (prefixWord ++ tailWord_1088522).sum := by decide
  have hdescent : baseEnd_1088522 < baseStart_1088522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088531 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 5, 3, 2]
def baseStart_1088531 : Nat := 118140960795 + 1088531 * 2 ^ 59
def prefixEnd_1088531 : Nat := 4983230072969 + 3 ^ 40 * 1088531 * 2
def baseEnd_1088531 : Nat := 558939610319385851156443

theorem tailTrace_1088531 : CollatzResearch.WordTrace tailWord_1088531 prefixEnd_1088531 558939610319385851156443 := by
  unfold tailWord_1088531
  simp only [CollatzResearch.WordTrace]
  refine ⟨39701987219445568139153447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26467991479630378759435631 39701987219445568139153447)
  ·
    refine ⟨59552980829168352208730171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39701987219445568139153447 59552980829168352208730171)
    ·
      refine ⟨89329471243752528313095257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59552980829168352208730171 89329471243752528313095257)
      ·
        refine ⟨66997103432814396234821443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89329471243752528313095257 66997103432814396234821443)
        ·
          refine ⟨100495655149221594352232165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66997103432814396234821443 100495655149221594352232165)
          ·
            refine ⟨18842935340479048941043531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100495655149221594352232165 18842935340479048941043531)
            ·
              refine ⟨28264403010718573411565297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18842935340479048941043531 28264403010718573411565297)
              ·
                refine ⟨21198302258038930058673973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28264403010718573411565297 21198302258038930058673973)
                ·
                  refine ⟨1987340836691149693000685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21198302258038930058673973 1987340836691149693000685)
                  ·
                    refine ⟨745252813759181134875257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1987340836691149693000685 745252813759181134875257)
                    ·
                      refine ⟨558939610319385851156443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745252813759181134875257 558939610319385851156443)
                      ·
                        rfl

theorem cell23_1088531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3, 2].length) (baseStart_1088531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088531 prefixEnd_1088531 := by exact prefixLift 1088531
  have htrace : WordTrace (prefixWord ++ tailWord_1088531) baseStart_1088531 baseEnd_1088531 := by
    simpa [prefixWord, tailWord_1088531, baseEnd_1088531] using wordTrace_append hprefix tailTrace_1088531
  have hstable : (prefixWord ++ tailWord_1088531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088531).length < 2 ^ (prefixWord ++ tailWord_1088531).sum := by decide
  have hdescent : baseEnd_1088531 < baseStart_1088531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088538 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_1088538 : Nat := 118140960795 + 1088538 * 2 ^ 59
def prefixEnd_1088538 : Nat := 4983230072969 + 3 ^ 40 * 1088538 * 2
def baseEnd_1088538 : Nat := 558943204683967323768911

theorem tailTrace_1088538 : CollatzResearch.WordTrace tailWord_1088538 prefixEnd_1088538 558943204683967323768911 := by
  unfold tailWord_1088538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9925560632605052083664567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26468161686946805556438845 9925560632605052083664567)
  ·
    refine ⟨14888340948907578125496851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9925560632605052083664567 14888340948907578125496851)
    ·
      refine ⟨22332511423361367188245277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14888340948907578125496851 22332511423361367188245277)
      ·
        refine ⟨8374691783760512695591979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22332511423361367188245277 8374691783760512695591979)
        ·
          refine ⟨12562037675640769043387969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8374691783760512695591979 12562037675640769043387969)
          ·
            refine ⟨9421528256730576782540977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12562037675640769043387969 9421528256730576782540977)
            ·
              refine ⟨7066146192547932586905733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9421528256730576782540977 7066146192547932586905733)
              ·
                refine ⟨1324902411102737360044825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7066146192547932586905733 1324902411102737360044825)
                ·
                  refine ⟨993676808327053020033619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1324902411102737360044825 993676808327053020033619)
                  ·
                    refine ⟨1490515212490579530050429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 993676808327053020033619 1490515212490579530050429)
                    ·
                      refine ⟨558943204683967323768911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490515212490579530050429 558943204683967323768911)
                      ·
                        rfl

theorem cell23_1088538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_1088538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088538 prefixEnd_1088538 := by exact prefixLift 1088538
  have htrace : WordTrace (prefixWord ++ tailWord_1088538) baseStart_1088538 baseEnd_1088538 := by
    simpa [prefixWord, tailWord_1088538, baseEnd_1088538] using wordTrace_append hprefix tailTrace_1088538
  have hstable : (prefixWord ++ tailWord_1088538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088538).length < 2 ^ (prefixWord ++ tailWord_1088538).sum := by decide
  have hdescent : baseEnd_1088538 < baseStart_1088538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088651 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4]
def baseStart_1088651 : Nat := 118140960795 + 1088651 * 2 ^ 59
def prefixEnd_1088651 : Nat := 4983230072969 + 3 ^ 40 * 1088651 * 2
def baseEnd_1088651 : Nat := 559001227997925381655891

theorem tailTrace_1088651 : CollatzResearch.WordTrace tailWord_1088651 prefixEnd_1088651 559001227997925381655891 := by
  unfold tailWord_1088651
  simp only [CollatzResearch.WordTrace]
  refine ⟨39706363979010828633521807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26470909319340552422347871 39706363979010828633521807)
  ·
    refine ⟨59559545968516242950282711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39706363979010828633521807 59559545968516242950282711)
    ·
      refine ⟨89339318952774364425424067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59559545968516242950282711 89339318952774364425424067)
      ·
        refine ⟨134008978429161546638136101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89339318952774364425424067 134008978429161546638136101)
        ·
          refine ⟨25126683455467789994650519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134008978429161546638136101 25126683455467789994650519)
          ·
            refine ⟨37690025183201684991975779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25126683455467789994650519 37690025183201684991975779)
            ·
              refine ⟨56535037774802527487963669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37690025183201684991975779 56535037774802527487963669)
              ·
                refine ⟨2650079895693868475998297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56535037774802527487963669 2650079895693868475998297)
                ·
                  refine ⟨1987559921770401356998723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650079895693868475998297 1987559921770401356998723)
                  ·
                    refine ⟨2981339882655602035498085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1987559921770401356998723 2981339882655602035498085)
                    ·
                      refine ⟨559001227997925381655891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2981339882655602035498085 559001227997925381655891)
                      ·
                        rfl

theorem cell23_1088651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 4].length) (baseStart_1088651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088651 prefixEnd_1088651 := by exact prefixLift 1088651
  have htrace : WordTrace (prefixWord ++ tailWord_1088651) baseStart_1088651 baseEnd_1088651 := by
    simpa [prefixWord, tailWord_1088651, baseEnd_1088651] using wordTrace_append hprefix tailTrace_1088651
  have hstable : (prefixWord ++ tailWord_1088651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088651).length < 2 ^ (prefixWord ++ tailWord_1088651).sum := by decide
  have hdescent : baseEnd_1088651 < baseStart_1088651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088705 : List Nat := [1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1088705 : Nat := 118140960795 + 1088705 * 2 ^ 59
def prefixEnd_1088705 : Nat := 4983230072969 + 3 ^ 40 * 1088705 * 2
def baseEnd_1088705 : Nat := 559028955953268170380643

theorem tailTrace_1088705 : CollatzResearch.WordTrace tailWord_1088705 prefixEnd_1088705 559028955953268170380643 := by
  unfold tailWord_1088705
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708333520815195855987569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26472222347210130570658379 39708333520815195855987569)
  ·
    refine ⟨29781250140611396891990677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39708333520815195855987569 29781250140611396891990677)
    ·
      refine ⟨1395996100341159229312063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 29781250140611396891990677 1395996100341159229312063)
      ·
        refine ⟨2093994150511738843968095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1395996100341159229312063 2093994150511738843968095)
        ·
          refine ⟨3140991225767608265952143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2093994150511738843968095 3140991225767608265952143)
          ·
            refine ⟨4711486838651412398928215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3140991225767608265952143 4711486838651412398928215)
            ·
              refine ⟨7067230257977118598392323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4711486838651412398928215 7067230257977118598392323)
              ·
                refine ⟨10600845386965677897588485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7067230257977118598392323 10600845386965677897588485)
                ·
                  refine ⟨1987658510056064605797841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10600845386965677897588485 1987658510056064605797841)
                  ·
                    refine ⟨1490743882542048454348381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1987658510056064605797841 1490743882542048454348381)
                    ·
                      refine ⟨559028955953268170380643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490743882542048454348381 559028955953268170380643)
                      ·
                        rfl

theorem cell23_1088705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1088705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088705 prefixEnd_1088705 := by exact prefixLift 1088705
  have htrace : WordTrace (prefixWord ++ tailWord_1088705) baseStart_1088705 baseEnd_1088705 := by
    simpa [prefixWord, tailWord_1088705, baseEnd_1088705] using wordTrace_append hprefix tailTrace_1088705
  have hstable : (prefixWord ++ tailWord_1088705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088705).length < 2 ^ (prefixWord ++ tailWord_1088705).sum := by decide
  have hdescent : baseEnd_1088705 < baseStart_1088705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088721 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_1088721 : Nat := 118140960795 + 1088721 * 2 ^ 59
def prefixEnd_1088721 : Nat := 4983230072969 + 3 ^ 40 * 1088721 * 2
def baseEnd_1088721 : Nat := 186345723881246702593523

theorem tailTrace_1088721 : CollatzResearch.WordTrace tailWord_1088721 prefixEnd_1088721 186345723881246702593523 := by
  unfold tailWord_1088721
  simp only [CollatzResearch.WordTrace]
  refine ⟨39708917088757230588570017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26472611392504820392380011 39708917088757230588570017)
  ·
    refine ⟨29781687816567922941427513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39708917088757230588570017 29781687816567922941427513)
    ·
      refine ⟨22336265862425942206070635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29781687816567922941427513 22336265862425942206070635)
      ·
        refine ⟨33504398793638913309105953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22336265862425942206070635 33504398793638913309105953)
        ·
          refine ⟨25128299095229184981829465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33504398793638913309105953 25128299095229184981829465)
          ·
            refine ⟨18846224321421888736372099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25128299095229184981829465 18846224321421888736372099)
            ·
              refine ⟨28269336482132833104558149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18846224321421888736372099 28269336482132833104558149)
              ·
                refine ⟨5300500590399906207104653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28269336482132833104558149 5300500590399906207104653)
                ·
                  refine ⟨1987687721399964827664245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5300500590399906207104653 1987687721399964827664245)
                  ·
                    refine ⟨186345723881246702593523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1987687721399964827664245 186345723881246702593523)
                    ·
                      rfl

theorem cell23_1088721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_1088721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088721 prefixEnd_1088721 := by exact prefixLift 1088721
  have htrace : WordTrace (prefixWord ++ tailWord_1088721) baseStart_1088721 baseEnd_1088721 := by
    simpa [prefixWord, tailWord_1088721, baseEnd_1088721] using wordTrace_append hprefix tailTrace_1088721
  have hstable : (prefixWord ++ tailWord_1088721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088721).length < 2 ^ (prefixWord ++ tailWord_1088721).sum := by decide
  have hdescent : baseEnd_1088721 < baseStart_1088721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088725 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 6]
def baseStart_1088725 : Nat := 118140960795 + 1088725 * 2 ^ 59
def prefixEnd_1088725 : Nat := 4983230072969 + 3 ^ 40 * 1088725 * 2
def baseEnd_1088725 : Nat := 62115469507373121347839

theorem tailTrace_1088725 : CollatzResearch.WordTrace tailWord_1088725 prefixEnd_1088725 62115469507373121347839 := by
  unfold tailWord_1088725
  simp only [CollatzResearch.WordTrace]
  refine ⟨39709062980742739271715629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26472708653828492847810419 39709062980742739271715629)
  ·
    refine ⟨14890898617778527226893361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39709062980742739271715629 14890898617778527226893361)
    ·
      refine ⟨11168173963333895420170021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14890898617778527226893361 11168173963333895420170021)
      ·
        refine ⟨2094032618125105391281879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11168173963333895420170021 2094032618125105391281879)
        ·
          refine ⟨3141048927187658086922819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094032618125105391281879 3141048927187658086922819)
          ·
            refine ⟨4711573390781487130384229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141048927187658086922819 4711573390781487130384229)
            ·
              refine ⟨883420010771528836947043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4711573390781487130384229 883420010771528836947043)
              ·
                refine ⟨1325130016157293255420565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883420010771528836947043 1325130016157293255420565)
                ·
                  refine ⟨62115469507373121347839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1325130016157293255420565 62115469507373121347839)
                  ·
                    rfl

theorem cell23_1088725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_1088725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088725 prefixEnd_1088725 := by exact prefixLift 1088725
  have htrace : WordTrace (prefixWord ++ tailWord_1088725) baseStart_1088725 baseEnd_1088725 := by
    simpa [prefixWord, tailWord_1088725, baseEnd_1088725] using wordTrace_append hprefix tailTrace_1088725
  have hstable : (prefixWord ++ tailWord_1088725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088725).length < 2 ^ (prefixWord ++ tailWord_1088725).sum := by decide
  have hdescent : baseEnd_1088725 < baseStart_1088725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088755 : List Nat := [1, 1, 1, 2, 2, 6, 3, 1, 1, 5]
def baseStart_1088755 : Nat := 118140960795 + 1088755 * 2 ^ 59
def prefixEnd_1088755 : Nat := 4983230072969 + 3 ^ 40 * 1088755 * 2
def baseEnd_1088755 : Nat := 186351543328664324918471

theorem tailTrace_1088755 : CollatzResearch.WordTrace tailWord_1088755 prefixEnd_1088755 186351543328664324918471 := by
  unfold tailWord_1088755
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710157170634054395307719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26473438113756036263538479 39710157170634054395307719)
  ·
    refine ⟨59565235755951081592961579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39710157170634054395307719 59565235755951081592961579)
    ·
      refine ⟨89347853633926622389442369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59565235755951081592961579 89347853633926622389442369)
      ·
        refine ⟨67010890225444966792081777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89347853633926622389442369 67010890225444966792081777)
        ·
          refine ⟨50258167669083725094061333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67010890225444966792081777 50258167669083725094061333)
          ·
            refine ⟨2355851609488299613784125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 50258167669083725094061333 2355851609488299613784125)
            ·
              refine ⟨883444353558112355169047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2355851609488299613784125 883444353558112355169047)
              ·
                refine ⟨1325166530337168532753571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883444353558112355169047 1325166530337168532753571)
                ·
                  refine ⟨1987749795505752799130357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325166530337168532753571 1987749795505752799130357)
                  ·
                    refine ⟨186351543328664324918471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1987749795505752799130357 186351543328664324918471)
                    ·
                      rfl

theorem cell23_1088755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 1, 1, 5].length) (baseStart_1088755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088755 prefixEnd_1088755 := by exact prefixLift 1088755
  have htrace : WordTrace (prefixWord ++ tailWord_1088755) baseStart_1088755 baseEnd_1088755 := by
    simpa [prefixWord, tailWord_1088755, baseEnd_1088755] using wordTrace_append hprefix tailTrace_1088755
  have hstable : (prefixWord ++ tailWord_1088755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088755).length < 2 ^ (prefixWord ++ tailWord_1088755).sum := by decide
  have hdescent : baseEnd_1088755 < baseStart_1088755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088769 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1088769 : Nat := 118140960795 + 1088769 * 2 ^ 59
def prefixEnd_1088769 : Nat := 4983230072969 + 3 ^ 40 * 1088769 * 2
def baseEnd_1088769 : Nat := 559061818715155919980349

theorem tailTrace_1088769 : CollatzResearch.WordTrace tailWord_1088769 prefixEnd_1088769 559061818715155919980349 := by
  unfold tailWord_1088769
  simp only [CollatzResearch.WordTrace]
  refine ⟨39710667792583334786317361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26473778528388889857544907 39710667792583334786317361)
  ·
    refine ⟨29783000844437501089738021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39710667792583334786317361 29783000844437501089738021)
    ·
      refine ⟨5584312658332031454325879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29783000844437501089738021 5584312658332031454325879)
      ·
        refine ⟨8376468987498047181488819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5584312658332031454325879 8376468987498047181488819)
        ·
          refine ⟨12564703481247070772233229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376468987498047181488819 12564703481247070772233229)
          ·
            refine ⟨4711763805467651539587461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12564703481247070772233229 4711763805467651539587461)
            ·
              refine ⟨883455713525184663672649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4711763805467651539587461 883455713525184663672649)
              ·
                refine ⟨662591785143888497754487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 883455713525184663672649 662591785143888497754487)
                ·
                  refine ⟨993887677715832746631731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662591785143888497754487 993887677715832746631731)
                  ·
                    refine ⟨1490831516573749119947597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 993887677715832746631731 1490831516573749119947597)
                    ·
                      refine ⟨559061818715155919980349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1490831516573749119947597 559061818715155919980349)
                      ·
                        rfl

theorem cell23_1088769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1088769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088769 prefixEnd_1088769 := by exact prefixLift 1088769
  have htrace : WordTrace (prefixWord ++ tailWord_1088769) baseStart_1088769 baseEnd_1088769 := by
    simpa [prefixWord, tailWord_1088769, baseEnd_1088769] using wordTrace_append hprefix tailTrace_1088769
  have hstable : (prefixWord ++ tailWord_1088769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088769).length < 2 ^ (prefixWord ++ tailWord_1088769).sum := by decide
  have hdescent : baseEnd_1088769 < baseStart_1088769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088792 : List Nat := [2, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1088792 : Nat := 118140960795 + 1088792 * 2 ^ 59
def prefixEnd_1088792 : Nat := 4983230072969 + 3 ^ 40 * 1088792 * 2
def baseEnd_1088792 : Nat := 559073628770209329992743

theorem tailTrace_1088792 : CollatzResearch.WordTrace tailWord_1088792 prefixEnd_1088792 559073628770209329992743 := by
  unfold tailWord_1088792
  simp only [CollatzResearch.WordTrace]
  refine ⟨19855753335750004857202315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26474337781000006476269753 19855753335750004857202315)
  ·
    refine ⟨29783630003625007285803473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19855753335750004857202315 29783630003625007285803473)
    ·
      refine ⟨22337722502718755464352605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29783630003625007285803473 22337722502718755464352605)
      ·
        refine ⟨8376645938519533299132227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22337722502718755464352605 8376645938519533299132227)
        ·
          refine ⟨12564968907779299948698341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8376645938519533299132227 12564968907779299948698341)
          ·
            refine ⟨2355931670208618740380939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12564968907779299948698341 2355931670208618740380939)
            ·
              refine ⟨3533897505312928110571409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2355931670208618740380939 3533897505312928110571409)
              ·
                refine ⟨2650423128984696082928557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3533897505312928110571409 2650423128984696082928557)
                ·
                  refine ⟨993908673369261031098209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2650423128984696082928557 993908673369261031098209)
                  ·
                    refine ⟨745431505026945773323657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 993908673369261031098209 745431505026945773323657)
                    ·
                      refine ⟨559073628770209329992743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745431505026945773323657 559073628770209329992743)
                      ·
                        rfl

theorem cell23_1088792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1088792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088792 prefixEnd_1088792 := by exact prefixLift 1088792
  have htrace : WordTrace (prefixWord ++ tailWord_1088792) baseStart_1088792 baseEnd_1088792 := by
    simpa [prefixWord, tailWord_1088792, baseEnd_1088792] using wordTrace_append hprefix tailTrace_1088792
  have hstable : (prefixWord ++ tailWord_1088792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088792).length < 2 ^ (prefixWord ++ tailWord_1088792).sum := by decide
  have hdescent : baseEnd_1088792 < baseStart_1088792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088865 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_1088865 : Nat := 118140960795 + 1088865 * 2 ^ 59
def prefixEnd_1088865 : Nat := 4983230072969 + 3 ^ 40 * 1088865 * 2
def baseEnd_1088865 : Nat := 559111112857987544379907

theorem tailTrace_1088865 : CollatzResearch.WordTrace tailWord_1088865 prefixEnd_1088865 559111112857987544379907 := by
  unfold tailWord_1088865
  simp only [CollatzResearch.WordTrace]
  refine ⟨39714169200235543181812049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26476112800157028787874699 39714169200235543181812049)
  ·
    refine ⟨29785626900176657386359037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39714169200235543181812049 29785626900176657386359037)
    ·
      refine ⟨11169610087566246519884639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29785626900176657386359037 11169610087566246519884639)
      ·
        refine ⟨16754415131349369779826959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11169610087566246519884639 16754415131349369779826959)
        ·
          refine ⟨25131622697024054669740439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16754415131349369779826959 25131622697024054669740439)
          ·
            refine ⟨37697434045536082004610659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25131622697024054669740439 37697434045536082004610659)
            ·
              refine ⟨56546151068304123006915989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37697434045536082004610659 56546151068304123006915989)
              ·
                refine ⟨2650600831326755765949187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56546151068304123006915989 2650600831326755765949187)
                ·
                  refine ⟨3975901246990133648923781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2650600831326755765949187 3975901246990133648923781)
                  ·
                    refine ⟨745481483810650059173209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3975901246990133648923781 745481483810650059173209)
                    ·
                      refine ⟨559111112857987544379907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745481483810650059173209 559111112857987544379907)
                      ·
                        rfl

theorem cell23_1088865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_1088865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088865 prefixEnd_1088865 := by exact prefixLift 1088865
  have htrace : WordTrace (prefixWord ++ tailWord_1088865) baseStart_1088865 baseEnd_1088865 := by
    simpa [prefixWord, tailWord_1088865, baseEnd_1088865] using wordTrace_append hprefix tailTrace_1088865
  have hstable : (prefixWord ++ tailWord_1088865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088865).length < 2 ^ (prefixWord ++ tailWord_1088865).sum := by decide
  have hdescent : baseEnd_1088865 < baseStart_1088865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088868 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1088868 : Nat := 118140960795 + 1088868 * 2 ^ 59
def prefixEnd_1088868 : Nat := 4983230072969 + 3 ^ 40 * 1088868 * 2
def baseEnd_1088868 : Nat := 559112653299951032642393

theorem tailTrace_1088868 : CollatzResearch.WordTrace tailWord_1088868 prefixEnd_1088868 559112653299951032642393 := by
  unfold tailWord_1088868
  simp only [CollatzResearch.WordTrace]
  refine ⟨19857139309612337347085629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26476185746149783129447505 19857139309612337347085629)
  ·
    refine ⟨7446427241104626505157111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19857139309612337347085629 7446427241104626505157111)
    ·
      refine ⟨11169640861656939757735667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446427241104626505157111 11169640861656939757735667)
      ·
        refine ⟨16754461292485409636603501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11169640861656939757735667 16754461292485409636603501)
        ·
          refine ⟨6282922984682028613726313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16754461292485409636603501 6282922984682028613726313)
          ·
            refine ⟨4712192238511521460294735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6282922984682028613726313 4712192238511521460294735)
            ·
              refine ⟨7068288357767282190442103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4712192238511521460294735 7068288357767282190442103)
              ·
                refine ⟨10602432536650923285663155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7068288357767282190442103 10602432536650923285663155)
                ·
                  refine ⟨15903648804976384928494733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10602432536650923285663155 15903648804976384928494733)
                  ·
                    refine ⟨5963868301866144348185525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15903648804976384928494733 5963868301866144348185525)
                    ·
                      refine ⟨559112653299951032642393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5963868301866144348185525 559112653299951032642393)
                      ·
                        rfl

theorem cell23_1088868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1088868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088868 prefixEnd_1088868 := by exact prefixLift 1088868
  have htrace : WordTrace (prefixWord ++ tailWord_1088868) baseStart_1088868 baseEnd_1088868 := by
    simpa [prefixWord, tailWord_1088868, baseEnd_1088868] using wordTrace_append hprefix tailTrace_1088868
  have hstable : (prefixWord ++ tailWord_1088868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088868).length < 2 ^ (prefixWord ++ tailWord_1088868).sum := by decide
  have hdescent : baseEnd_1088868 < baseStart_1088868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088882 : List Nat := [3, 2, 1, 2, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1088882 : Nat := 118140960795 + 1088882 * 2 ^ 59
def prefixEnd_1088882 : Nat := 4983230072969 + 3 ^ 40 * 1088882 * 2
def baseEnd_1088882 : Nat := 559119842029113977867329

theorem tailTrace_1088882 : CollatzResearch.WordTrace tailWord_1088882 prefixEnd_1088882 559119842029113977867329 := by
  unfold tailWord_1088882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9928697310293488771295225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26476526160782636723453933 9928697310293488771295225)
  ·
    refine ⟨7446522982720116578471419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9928697310293488771295225 7446522982720116578471419)
    ·
      refine ⟨11169784474080174867707129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7446522982720116578471419 11169784474080174867707129)
      ·
        refine ⟨8377338355560131150780347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11169784474080174867707129 8377338355560131150780347)
        ·
          refine ⟨12566007533340196726170521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8377338355560131150780347 12566007533340196726170521)
          ·
            refine ⟨9424505650005147544627891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12566007533340196726170521 9424505650005147544627891)
            ·
              refine ⟨14136758475007721316941837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9424505650005147544627891 14136758475007721316941837)
              ·
                refine ⟨5301284428127895493853189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14136758475007721316941837 5301284428127895493853189)
                ·
                  refine ⟨993990830273980405097473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5301284428127895493853189 993990830273980405097473)
                  ·
                    refine ⟨745493122705485303823105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 993990830273980405097473 745493122705485303823105)
                    ·
                      refine ⟨559119842029113977867329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745493122705485303823105 559119842029113977867329)
                      ·
                        rfl

theorem cell23_1088882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1088882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088882 prefixEnd_1088882 := by exact prefixLift 1088882
  have htrace : WordTrace (prefixWord ++ tailWord_1088882) baseStart_1088882 baseEnd_1088882 := by
    simpa [prefixWord, tailWord_1088882, baseEnd_1088882] using wordTrace_append hprefix tailTrace_1088882
  have hstable : (prefixWord ++ tailWord_1088882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088882).length < 2 ^ (prefixWord ++ tailWord_1088882).sum := by decide
  have hdescent : baseEnd_1088882 < baseStart_1088882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088899 : List Nat := [1, 1, 1, 3, 5, 2, 1, 3, 2, 2, 2]
def baseStart_1088899 : Nat := 118140960795 + 1088899 * 2 ^ 59
def prefixEnd_1088899 : Nat := 4983230072969 + 3 ^ 40 * 1088899 * 2
def baseEnd_1088899 : Nat := 559128571200240411354751

theorem tailTrace_1088899 : CollatzResearch.WordTrace tailWord_1088899 prefixEnd_1088899 559128571200240411354751 := by
  unfold tailWord_1088899
  simp only [CollatzResearch.WordTrace]
  refine ⟨39715409282112366988549751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26476939521408244659033167 39715409282112366988549751)
  ·
    refine ⟨59573113923168550482824627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39715409282112366988549751 59573113923168550482824627)
    ·
      refine ⟨89359670884752825724236941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59573113923168550482824627 89359670884752825724236941)
      ·
        refine ⟨33509876581782309646588853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89359670884752825724236941 33509876581782309646588853)
        ·
          refine ⟨3141550929542091529367705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33509876581782309646588853 3141550929542091529367705)
          ·
            refine ⟨2356163197156568647025779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3141550929542091529367705 2356163197156568647025779)
            ·
              refine ⟨3534244795734852970538669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356163197156568647025779 3534244795734852970538669)
              ·
                refine ⟨1325341798400569863952001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3534244795734852970538669 1325341798400569863952001)
                ·
                  refine ⟨994006348800427397964001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325341798400569863952001 994006348800427397964001)
                  ·
                    refine ⟨745504761600320548473001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 994006348800427397964001 745504761600320548473001)
                    ·
                      refine ⟨559128571200240411354751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745504761600320548473001 559128571200240411354751)
                      ·
                        rfl

theorem cell23_1088899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_1088899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088899 prefixEnd_1088899 := by exact prefixLift 1088899
  have htrace : WordTrace (prefixWord ++ tailWord_1088899) baseStart_1088899 baseEnd_1088899 := by
    simpa [prefixWord, tailWord_1088899, baseEnd_1088899] using wordTrace_append hprefix tailTrace_1088899
  have hstable : (prefixWord ++ tailWord_1088899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088899).length < 2 ^ (prefixWord ++ tailWord_1088899).sum := by decide
  have hdescent : baseEnd_1088899 < baseStart_1088899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088928 : List Nat := [2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_1088928 : Nat := 118140960795 + 1088928 * 2 ^ 59
def prefixEnd_1088928 : Nat := 4983230072969 + 3 ^ 40 * 1088928 * 2
def baseEnd_1088928 : Nat := 559143462139220797892117

theorem tailTrace_1088928 : CollatzResearch.WordTrace tailWord_1088928 prefixEnd_1088928 559143462139220797892117 := by
  unfold tailWord_1088928
  simp only [CollatzResearch.WordTrace]
  refine ⟨19858233499503652470677719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26477644666004869960903625 19858233499503652470677719)
  ·
    refine ⟨29787350249255478706016579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19858233499503652470677719 29787350249255478706016579)
    ·
      refine ⟨44681025373883218059024869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29787350249255478706016579 44681025373883218059024869)
      ·
        refine ⟨8377692257603103386067163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44681025373883218059024869 8377692257603103386067163)
        ·
          refine ⟨12566538386404655079100745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8377692257603103386067163 12566538386404655079100745)
          ·
            refine ⟨9424903789803491309325559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12566538386404655079100745 9424903789803491309325559)
            ·
              refine ⟨14137355684705236963988339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9424903789803491309325559 14137355684705236963988339)
              ·
                refine ⟨21206033527057855445982509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14137355684705236963988339 21206033527057855445982509)
                ·
                  refine ⟨7952262572646695792243441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21206033527057855445982509 7952262572646695792243441)
                  ·
                    refine ⟨5964196929485021844182581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7952262572646695792243441 5964196929485021844182581)
                    ·
                      refine ⟨559143462139220797892117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5964196929485021844182581 559143462139220797892117)
                      ·
                        rfl

theorem cell23_1088928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_1088928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088928 prefixEnd_1088928 := by exact prefixLift 1088928
  have htrace : WordTrace (prefixWord ++ tailWord_1088928) baseStart_1088928 baseEnd_1088928 := by
    simpa [prefixWord, tailWord_1088928, baseEnd_1088928] using wordTrace_append hprefix tailTrace_1088928
  have hstable : (prefixWord ++ tailWord_1088928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088928).length < 2 ^ (prefixWord ++ tailWord_1088928).sum := by decide
  have hdescent : baseEnd_1088928 < baseStart_1088928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088935 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 2, 5]
def baseStart_1088935 : Nat := 118140960795 + 1088935 * 2 ^ 59
def prefixEnd_1088935 : Nat := 4983230072969 + 3 ^ 40 * 1088935 * 2
def baseEnd_1088935 : Nat := 186382352167934090168195

theorem tailTrace_1088935 : CollatzResearch.WordTrace tailWord_1088935 prefixEnd_1088935 186382352167934090168195 := by
  unfold tailWord_1088935
  simp only [CollatzResearch.WordTrace]
  refine ⟨39716722309981945136860259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26477814873321296757906839 39716722309981945136860259)
  ·
    refine ⟨59575083464972917705290389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39716722309981945136860259 59575083464972917705290389)
    ·
      refine ⟨2792582037420605517435487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 59575083464972917705290389 2792582037420605517435487)
      ·
        refine ⟨4188873056130908276153231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792582037420605517435487 4188873056130908276153231)
        ·
          refine ⟨6283309584196362414229847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4188873056130908276153231 6283309584196362414229847)
          ·
            refine ⟨9424964376294543621344771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6283309584196362414229847 9424964376294543621344771)
            ·
              refine ⟨14137446564441815432017157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9424964376294543621344771 14137446564441815432017157)
              ·
                refine ⟨2650771230832840393503217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14137446564441815432017157 2650771230832840393503217)
                ·
                  refine ⟨1988078423124630295127413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650771230832840393503217 1988078423124630295127413)
                  ·
                    refine ⟨186382352167934090168195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1988078423124630295127413 186382352167934090168195)
                    ·
                      rfl

theorem cell23_1088935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_1088935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088935 prefixEnd_1088935 := by exact prefixLift 1088935
  have htrace : WordTrace (prefixWord ++ tailWord_1088935) baseStart_1088935 baseEnd_1088935 := by
    simpa [prefixWord, tailWord_1088935, baseEnd_1088935] using wordTrace_append hprefix tailTrace_1088935
  have hstable : (prefixWord ++ tailWord_1088935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088935).length < 2 ^ (prefixWord ++ tailWord_1088935).sum := by decide
  have hdescent : baseEnd_1088935 < baseStart_1088935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088972 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1088972 : Nat := 118140960795 + 1088972 * 2 ^ 59
def prefixEnd_1088972 : Nat := 4983230072969 + 3 ^ 40 * 1088972 * 2
def baseEnd_1088972 : Nat := 559166055288018625741915

theorem tailTrace_1088972 : CollatzResearch.WordTrace tailWord_1088972 prefixEnd_1088972 559166055288018625741915 := by
  unfold tailWord_1088972
  simp only [CollatzResearch.WordTrace]
  refine ⟨19859035905423950227978585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26478714540565266970638113 19859035905423950227978585)
  ·
    refine ⟨14894276929067962670983939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19859035905423950227978585 14894276929067962670983939)
    ·
      refine ⟨22341415393601944006475909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14894276929067962670983939 22341415393601944006475909)
      ·
        refine ⟨4189015386300364501214233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22341415393601944006475909 4189015386300364501214233)
        ·
          refine ⟨3141761539725273375910675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189015386300364501214233 3141761539725273375910675)
          ·
            refine ⟨4712642309587910063866013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3141761539725273375910675 4712642309587910063866013)
            ·
              refine ⟨1767240866095466273949755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4712642309587910063866013 1767240866095466273949755)
              ·
                refine ⟨2650861299143199410924633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767240866095466273949755 2650861299143199410924633)
                ·
                  refine ⟨1988145974357399558193475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2650861299143199410924633 1988145974357399558193475)
                  ·
                    refine ⟨2982218961536099337290213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988145974357399558193475 2982218961536099337290213)
                    ·
                      refine ⟨559166055288018625741915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2982218961536099337290213 559166055288018625741915)
                      ·
                        rfl

theorem cell23_1088972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1088972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088972 prefixEnd_1088972 := by exact prefixLift 1088972
  have htrace : WordTrace (prefixWord ++ tailWord_1088972) baseStart_1088972 baseEnd_1088972 := by
    simpa [prefixWord, tailWord_1088972, baseEnd_1088972] using wordTrace_append hprefix tailTrace_1088972
  have hstable : (prefixWord ++ tailWord_1088972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088972).length < 2 ^ (prefixWord ++ tailWord_1088972).sum := by decide
  have hdescent : baseEnd_1088972 < baseStart_1088972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088995 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 8]
def baseStart_1088995 : Nat := 118140960795 + 1088995 * 2 ^ 59
def prefixEnd_1088995 : Nat := 4983230072969 + 3 ^ 40 * 1088995 * 2
def baseEnd_1088995 : Nat := 62130873927008003972701

theorem tailTrace_1088995 : CollatzResearch.WordTrace tailWord_1088995 prefixEnd_1088995 62130873927008003972701 := by
  unfold tailWord_1088995
  simp only [CollatzResearch.WordTrace]
  refine ⟨39718910689764575384044439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26479273793176383589362959 39718910689764575384044439)
  ·
    refine ⟨59578366034646863076066659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39718910689764575384044439 59578366034646863076066659)
    ·
      refine ⟨89367549051970294614099989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59578366034646863076066659 89367549051970294614099989)
      ·
        refine ⟨4189103861811107560035937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89367549051970294614099989 4189103861811107560035937)
        ·
          refine ⟨3141827896358330670026953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189103861811107560035937 3141827896358330670026953)
          ·
            refine ⟨2356370922268748002520215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3141827896358330670026953 2356370922268748002520215)
            ·
              refine ⟨3534556383403122003780323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356370922268748002520215 3534556383403122003780323)
              ·
                refine ⟨5301834575104683005670485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534556383403122003780323 5301834575104683005670485)
                ·
                  refine ⟨62130873927008003972701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5301834575104683005670485 62130873927008003972701)
                  ·
                    rfl

theorem cell23_1088995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 8].length) (baseStart_1088995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088995 prefixEnd_1088995 := by exact prefixLift 1088995
  have htrace : WordTrace (prefixWord ++ tailWord_1088995) baseStart_1088995 baseEnd_1088995 := by
    simpa [prefixWord, tailWord_1088995, baseEnd_1088995] using wordTrace_append hprefix tailTrace_1088995
  have hstable : (prefixWord ++ tailWord_1088995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088995).length < 2 ^ (prefixWord ++ tailWord_1088995).sum := by decide
  have hdescent : baseEnd_1088995 < baseStart_1088995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1088999 : List Nat := [1, 1, 5, 2, 1, 2, 2, 4, 1, 4]
def baseStart_1088999 : Nat := 118140960795 + 1088999 * 2 ^ 59
def prefixEnd_1088999 : Nat := 4983230072969 + 3 ^ 40 * 1088999 * 2
def baseEnd_1088999 : Nat := 186393306421896673368097

theorem tailTrace_1088999 : CollatzResearch.WordTrace tailWord_1088999 prefixEnd_1088999 186393306421896673368097 := by
  unfold tailWord_1088999
  simp only [CollatzResearch.WordTrace]
  refine ⟨39719056581750084067190051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26479371054500056044793367 39719056581750084067190051)
  ·
    refine ⟨59578584872625126100785077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39719056581750084067190051 59578584872625126100785077)
    ·
      refine ⟨5585492331808605571948601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59578584872625126100785077 5585492331808605571948601)
      ·
        refine ⟨4189119248856454178961451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5585492331808605571948601 4189119248856454178961451)
        ·
          refine ⟨6283678873284681268442177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4189119248856454178961451 6283678873284681268442177)
          ·
            refine ⟨4712759154963510951331633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6283678873284681268442177 4712759154963510951331633)
            ·
              refine ⟨3534569366222633213498725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4712759154963510951331633 3534569366222633213498725)
              ·
                refine ⟨662731756166743727531011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3534569366222633213498725 662731756166743727531011)
                ·
                  refine ⟨994097634250115591296517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 662731756166743727531011 994097634250115591296517)
                  ·
                    refine ⟨186393306421896673368097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 994097634250115591296517 186393306421896673368097)
                    ·
                      rfl

theorem cell23_1088999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_1088999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1088999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1088999 prefixEnd_1088999 := by exact prefixLift 1088999
  have htrace : WordTrace (prefixWord ++ tailWord_1088999) baseStart_1088999 baseEnd_1088999 := by
    simpa [prefixWord, tailWord_1088999, baseEnd_1088999] using wordTrace_append hprefix tailTrace_1088999
  have hstable : (prefixWord ++ tailWord_1088999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1088999).length < 2 ^ (prefixWord ++ tailWord_1088999).sum := by decide
  have hdescent : baseEnd_1088999 < baseStart_1088999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1088999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089032 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2]
def baseStart_1089032 : Nat := 118140960795 + 1089032 * 2 ^ 59
def prefixEnd_1089032 : Nat := 4983230072969 + 3 ^ 40 * 1089032 * 2
def baseEnd_1089032 : Nat := 559196864127288390991639

theorem tailTrace_1089032 : CollatzResearch.WordTrace tailWord_1089032 prefixEnd_1089032 559196864127288390991639 := by
  unfold tailWord_1089032
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860130095315265351570675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26480173460420353802094233 19860130095315265351570675)
  ·
    refine ⟨29790195142972898027356013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860130095315265351570675 29790195142972898027356013)
    ·
      refine ⟨11171323178614836760258505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29790195142972898027356013 11171323178614836760258505)
      ·
        refine ⟨8378492383961127570193879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11171323178614836760258505 8378492383961127570193879)
        ·
          refine ⟨12567738575941691355290819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8378492383961127570193879 12567738575941691355290819)
          ·
            refine ⟨18851607863912537032936229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12567738575941691355290819 18851607863912537032936229)
            ·
              refine ⟨3534676474483600693675543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18851607863912537032936229 3534676474483600693675543)
              ·
                refine ⟨5302014711725401040513315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534676474483600693675543 5302014711725401040513315)
                ·
                  refine ⟨7953022067588101560769973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302014711725401040513315 7953022067588101560769973)
                  ·
                    refine ⟨745595818836384521322185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7953022067588101560769973 745595818836384521322185)
                    ·
                      refine ⟨559196864127288390991639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745595818836384521322185 559196864127288390991639)
                      ·
                        rfl

theorem cell23_1089032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_1089032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089032 prefixEnd_1089032 := by exact prefixLift 1089032
  have htrace : WordTrace (prefixWord ++ tailWord_1089032) baseStart_1089032 baseEnd_1089032 := by
    simpa [prefixWord, tailWord_1089032, baseEnd_1089032] using wordTrace_append hprefix tailTrace_1089032
  have hstable : (prefixWord ++ tailWord_1089032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089032).length < 2 ^ (prefixWord ++ tailWord_1089032).sum := by decide
  have hdescent : baseEnd_1089032 < baseStart_1089032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089056 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1089056 : Nat := 118140960795 + 1089056 * 2 ^ 59
def prefixEnd_1089056 : Nat := 4983230072969 + 3 ^ 40 * 1089056 * 2
def baseEnd_1089056 : Nat := 559209187662996297091529

theorem tailTrace_1089056 : CollatzResearch.WordTrace tailWord_1089056 prefixEnd_1089056 559209187662996297091529 := by
  unfold tailWord_1089056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19860567771271791401007511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26480757028362388534676681 19860567771271791401007511)
  ·
    refine ⟨29790851656907687101511267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19860567771271791401007511 29790851656907687101511267)
    ·
      refine ⟨44686277485361530652266901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29790851656907687101511267 44686277485361530652266901)
      ·
        refine ⟨2094669257126321749325011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 44686277485361530652266901 2094669257126321749325011)
        ·
          refine ⟨3142003885689482623987517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094669257126321749325011 3142003885689482623987517)
          ·
            refine ⟨1178251457133555983995319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3142003885689482623987517 1178251457133555983995319)
            ·
              refine ⟨1767377185700333975992979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178251457133555983995319 1767377185700333975992979)
              ·
                refine ⟨2651065778550500963989469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767377185700333975992979 2651065778550500963989469)
                ·
                  refine ⟨994149666956437861496051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2651065778550500963989469 994149666956437861496051)
                  ·
                    refine ⟨1491224500434656792244077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994149666956437861496051 1491224500434656792244077)
                    ·
                      refine ⟨559209187662996297091529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491224500434656792244077 559209187662996297091529)
                      ·
                        rfl

theorem cell23_1089056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1089056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089056 prefixEnd_1089056 := by exact prefixLift 1089056
  have htrace : WordTrace (prefixWord ++ tailWord_1089056) baseStart_1089056 baseEnd_1089056 := by
    simpa [prefixWord, tailWord_1089056, baseEnd_1089056] using wordTrace_append hprefix tailTrace_1089056
  have hstable : (prefixWord ++ tailWord_1089056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089056).length < 2 ^ (prefixWord ++ tailWord_1089056).sum := by decide
  have hdescent : baseEnd_1089056 < baseStart_1089056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089075 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_1089075 : Nat := 118140960795 + 1089075 * 2 ^ 59
def prefixEnd_1089075 : Nat := 4983230072969 + 3 ^ 40 * 1089075 * 2
def baseEnd_1089075 : Nat := 559218943795431722753941

theorem tailTrace_1089075 : CollatzResearch.WordTrace tailWord_1089075 prefixEnd_1089075 559218943795431722753941 := by
  unfold tailWord_1089075
  simp only [CollatzResearch.WordTrace]
  refine ⟨39721828529474749046956679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26481219019649832697971119 39721828529474749046956679)
  ·
    refine ⟨59582742794212123570435019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39721828529474749046956679 59582742794212123570435019)
    ·
      refine ⟨89374114191318185355652529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59582742794212123570435019 89374114191318185355652529)
      ·
        refine ⟨67030585643488639016739397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89374114191318185355652529 67030585643488639016739397)
        ·
          refine ⟨12568234808154119815638637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67030585643488639016739397 12568234808154119815638637)
          ·
            refine ⟨4713088053057794930864489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12568234808154119815638637 4713088053057794930864489)
            ·
              refine ⟨3534816039793346198148367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4713088053057794930864489 3534816039793346198148367)
              ·
                refine ⟨5302224059690019297222551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534816039793346198148367 5302224059690019297222551)
                ·
                  refine ⟨7953336089535028945833827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5302224059690019297222551 7953336089535028945833827)
                  ·
                    refine ⟨11930004134302543418750741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7953336089535028945833827 11930004134302543418750741)
                    ·
                      refine ⟨559218943795431722753941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11930004134302543418750741 559218943795431722753941)
                      ·
                        rfl

theorem cell23_1089075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_1089075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089075 prefixEnd_1089075 := by exact prefixLift 1089075
  have htrace : WordTrace (prefixWord ++ tailWord_1089075) baseStart_1089075 baseEnd_1089075 := by
    simpa [prefixWord, tailWord_1089075, baseEnd_1089075] using wordTrace_append hprefix tailTrace_1089075
  have hstable : (prefixWord ++ tailWord_1089075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089075).length < 2 ^ (prefixWord ++ tailWord_1089075).sum := by decide
  have hdescent : baseEnd_1089075 < baseStart_1089075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089079 : List Nat := [1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 4]
def baseStart_1089079 : Nat := 118140960795 + 1089079 * 2 ^ 59
def prefixEnd_1089079 : Nat := 4983230072969 + 3 ^ 40 * 1089079 * 2
def baseEnd_1089079 : Nat := 559220997718049707103923

theorem tailTrace_1089079 : CollatzResearch.WordTrace tailWord_1089079 prefixEnd_1089079 559220997718049707103923 := by
  unfold tailWord_1089079
  simp only [CollatzResearch.WordTrace]
  refine ⟨39721974421460257730102291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26481316280973505153401527 39721974421460257730102291)
  ·
    refine ⟨59582961632190386595153437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39721974421460257730102291 59582961632190386595153437)
    ·
      refine ⟨22343610612071394973182539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59582961632190386595153437 22343610612071394973182539)
      ·
        refine ⟨33515415918107092459773809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343610612071394973182539 33515415918107092459773809)
        ·
          refine ⟨25136561938580319344830357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33515415918107092459773809 25136561938580319344830357)
          ·
            refine ⟨1178276340870952469288923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25136561938580319344830357 1178276340870952469288923)
            ·
              refine ⟨1767414511306428703933385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178276340870952469288923 1767414511306428703933385)
              ·
                refine ⟨1325560883479821527950039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767414511306428703933385 1325560883479821527950039)
                ·
                  refine ⟨1988341325219732291925059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1325560883479821527950039 1988341325219732291925059)
                  ·
                    refine ⟨2982511987829598437887589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1988341325219732291925059 2982511987829598437887589)
                    ·
                      refine ⟨559220997718049707103923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2982511987829598437887589 559220997718049707103923)
                      ·
                        rfl

theorem cell23_1089079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_1089079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089079 prefixEnd_1089079 := by exact prefixLift 1089079
  have htrace : WordTrace (prefixWord ++ tailWord_1089079) baseStart_1089079 baseEnd_1089079 := by
    simpa [prefixWord, tailWord_1089079, baseEnd_1089079] using wordTrace_append hprefix tailTrace_1089079
  have hstable : (prefixWord ++ tailWord_1089079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089079).length < 2 ^ (prefixWord ++ tailWord_1089079).sum := by decide
  have hdescent : baseEnd_1089079 < baseStart_1089079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089082 : List Nat := [3, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1089082 : Nat := 118140960795 + 1089082 * 2 ^ 59
def prefixEnd_1089082 : Nat := 4983230072969 + 3 ^ 40 * 1089082 * 2
def baseEnd_1089082 : Nat := 559222538160013195366409

theorem tailTrace_1089082 : CollatzResearch.WordTrace tailWord_1089082 prefixEnd_1089082 559222538160013195366409 := by
  unfold tailWord_1089082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9930520960112347310615375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26481389226966259494974333 9930520960112347310615375)
  ·
    refine ⟨14895781440168520965923063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9930520960112347310615375 14895781440168520965923063)
    ·
      refine ⟨22343672160252781448884595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14895781440168520965923063 22343672160252781448884595)
      ·
        refine ⟨33515508240379172173326893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22343672160252781448884595 33515508240379172173326893)
        ·
          refine ⟨12568315590142189564997585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33515508240379172173326893 12568315590142189564997585)
          ·
            refine ⟨9426236692606642173748189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12568315590142189564997585 9426236692606642173748189)
            ·
              refine ⟨3534838759727490815155571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9426236692606642173748189 3534838759727490815155571)
              ·
                refine ⟨5302258139591236222733357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3534838759727490815155571 5302258139591236222733357)
                ·
                  refine ⟨1988346802346713583525009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5302258139591236222733357 1988346802346713583525009)
                  ·
                    refine ⟨1491260101760035187643757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1988346802346713583525009 1491260101760035187643757)
                    ·
                      refine ⟨559222538160013195366409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491260101760035187643757 559222538160013195366409)
                      ·
                        rfl

theorem cell23_1089082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1089082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089082 prefixEnd_1089082 := by exact prefixLift 1089082
  have htrace : WordTrace (prefixWord ++ tailWord_1089082) baseStart_1089082 baseEnd_1089082 := by
    simpa [prefixWord, tailWord_1089082, baseEnd_1089082] using wordTrace_append hprefix tailTrace_1089082
  have hstable : (prefixWord ++ tailWord_1089082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089082).length < 2 ^ (prefixWord ++ tailWord_1089082).sum := by decide
  have hdescent : baseEnd_1089082 < baseStart_1089082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089129 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_1089129 : Nat := 118140960795 + 1089129 * 2 ^ 59
def prefixEnd_1089129 : Nat := 4983230072969 + 3 ^ 40 * 1089129 * 2
def baseEnd_1089129 : Nat := 559246671750774511478693

theorem tailTrace_1089129 : CollatzResearch.WordTrace tailWord_1089129 prefixEnd_1089129 559246671750774511478693 := by
  unfold tailWord_1089129
  simp only [CollatzResearch.WordTrace]
  refine ⟨39723798071279116269422441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26482532047519410846281627 39723798071279116269422441)
  ·
    refine ⟨29792848553459337202066831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39723798071279116269422441 29792848553459337202066831)
    ·
      refine ⟨44689272830189005803100247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29792848553459337202066831 44689272830189005803100247)
      ·
        refine ⟨67033909245283508704650371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44689272830189005803100247 67033909245283508704650371)
        ·
          refine ⟨100550863867925263056975557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67033909245283508704650371 100550863867925263056975557)
          ·
            refine ⟨18853286975235986823182917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 100550863867925263056975557 18853286975235986823182917)
            ·
              refine ⟨3534991307856747529346797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18853286975235986823182917 3534991307856747529346797)
              ·
                refine ⟨1325621740446280323505049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3534991307856747529346797 1325621740446280323505049)
                ·
                  refine ⟨994216305334710242628787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1325621740446280323505049 994216305334710242628787)
                  ·
                    refine ⟨1491324458002065363943181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994216305334710242628787 1491324458002065363943181)
                    ·
                      refine ⟨559246671750774511478693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491324458002065363943181 559246671750774511478693)
                      ·
                        rfl

theorem cell23_1089129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_1089129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089129 prefixEnd_1089129 := by exact prefixLift 1089129
  have htrace : WordTrace (prefixWord ++ tailWord_1089129) baseStart_1089129 baseEnd_1089129 := by
    simpa [prefixWord, tailWord_1089129, baseEnd_1089129] using wordTrace_append hprefix tailTrace_1089129
  have hstable : (prefixWord ++ tailWord_1089129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089129).length < 2 ^ (prefixWord ++ tailWord_1089129).sum := by decide
  have hdescent : baseEnd_1089129 < baseStart_1089129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089135 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_1089135 : Nat := 118140960795 + 1089135 * 2 ^ 59
def prefixEnd_1089135 : Nat := 4983230072969 + 3 ^ 40 * 1089135 * 2
def baseEnd_1089135 : Nat := 559249752634701488003665

theorem tailTrace_1089135 : CollatzResearch.WordTrace tailWord_1089135 prefixEnd_1089135 559249752634701488003665 := by
  unfold tailWord_1089135
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724016909257379294140859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26482677939504919529427239 39724016909257379294140859)
  ·
    refine ⟨59586025363886068941211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39724016909257379294140859 59586025363886068941211289)
    ·
      refine ⟨44689519022914551705908467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59586025363886068941211289 44689519022914551705908467)
      ·
        refine ⟨67034278534371827558862701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44689519022914551705908467 67034278534371827558862701)
        ·
          refine ⟨25137854450389435334573513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67034278534371827558862701 25137854450389435334573513)
          ·
            refine ⟨18853390837792076500930135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25137854450389435334573513 18853390837792076500930135)
            ·
              refine ⟨28280086256688114751395203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18853390837792076500930135 28280086256688114751395203)
              ·
                refine ⟨42420129385032172127092805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28280086256688114751395203 42420129385032172127092805)
                ·
                  refine ⟨7953774259693532273829901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42420129385032172127092805 7953774259693532273829901)
                  ·
                    refine ⟨2982665347385074602686213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7953774259693532273829901 2982665347385074602686213)
                    ·
                      refine ⟨559249752634701488003665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2982665347385074602686213 559249752634701488003665)
                      ·
                        rfl

theorem cell23_1089135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_1089135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089135 prefixEnd_1089135 := by exact prefixLift 1089135
  have htrace : WordTrace (prefixWord ++ tailWord_1089135) baseStart_1089135 baseEnd_1089135 := by
    simpa [prefixWord, tailWord_1089135, baseEnd_1089135] using wordTrace_append hprefix tailTrace_1089135
  have hstable : (prefixWord ++ tailWord_1089135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089135).length < 2 ^ (prefixWord ++ tailWord_1089135).sum := by decide
  have hdescent : baseEnd_1089135 < baseStart_1089135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089145 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_1089145 : Nat := 118140960795 + 1089145 * 2 ^ 59
def prefixEnd_1089145 : Nat := 4983230072969 + 3 ^ 40 * 1089145 * 2
def baseEnd_1089145 : Nat := 186418295813748816292873

theorem tailTrace_1089145 : CollatzResearch.WordTrace tailWord_1089145 prefixEnd_1089145 186418295813748816292873 := by
  unfold tailWord_1089145
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724381639221151002004889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26482921092814100668003259 39724381639221151002004889)
  ·
    refine ⟨29793286229415863251503667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39724381639221151002004889 29793286229415863251503667)
    ·
      refine ⟨44689929344123794877255501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29793286229415863251503667 44689929344123794877255501)
      ·
        refine ⟨16758723504046423078970813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44689929344123794877255501 16758723504046423078970813)
        ·
          refine ⟨6284521314017408654614055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16758723504046423078970813 6284521314017408654614055)
          ·
            refine ⟨9426781971026112981921083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6284521314017408654614055 9426781971026112981921083)
            ·
              refine ⟨14140172956539169472881625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9426781971026112981921083 14140172956539169472881625)
              ·
                refine ⟨10605129717404377104661219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14140172956539169472881625 10605129717404377104661219)
                ·
                  refine ⟨15907694576106565656991829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605129717404377104661219 15907694576106565656991829)
                  ·
                    refine ⟨186418295813748816292873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 15907694576106565656991829 186418295813748816292873)
                    ·
                      rfl

theorem cell23_1089145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_1089145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089145 prefixEnd_1089145 := by exact prefixLift 1089145
  have htrace : WordTrace (prefixWord ++ tailWord_1089145) baseStart_1089145 baseEnd_1089145 := by
    simpa [prefixWord, tailWord_1089145, baseEnd_1089145] using wordTrace_append hprefix tailTrace_1089145
  have hstable : (prefixWord ++ tailWord_1089145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089145).length < 2 ^ (prefixWord ++ tailWord_1089145).sum := by decide
  have hdescent : baseEnd_1089145 < baseStart_1089145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089155 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_1089155 : Nat := 118140960795 + 1089155 * 2 ^ 59
def prefixEnd_1089155 : Nat := 4983230072969 + 3 ^ 40 * 1089155 * 2
def baseEnd_1089155 : Nat := 559260022247791409753573

theorem tailTrace_1089155 : CollatzResearch.WordTrace tailWord_1089155 prefixEnd_1089155 559260022247791409753573 := by
  unfold tailWord_1089155
  simp only [CollatzResearch.WordTrace]
  refine ⟨39724746369184922709868919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26483164246123281806579279 39724746369184922709868919)
  ·
    refine ⟨59587119553777384064803379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39724746369184922709868919 59587119553777384064803379)
    ·
      refine ⟨89380679330666076097205069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59587119553777384064803379 89380679330666076097205069)
      ·
        refine ⟨33517754748999778536451901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89380679330666076097205069 33517754748999778536451901)
        ·
          refine ⟨12569158030874916951169463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33517754748999778536451901 12569158030874916951169463)
          ·
            refine ⟨18853737046312375426754195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569158030874916951169463 18853737046312375426754195)
            ·
              refine ⟨28280605569468563140131293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18853737046312375426754195 28280605569468563140131293)
              ·
                refine ⟨10605227088550711177549235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28280605569468563140131293 10605227088550711177549235)
                ·
                  refine ⟨15907840632826066766323853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605227088550711177549235 15907840632826066766323853)
                  ·
                    refine ⟨5965440237309775037371445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15907840632826066766323853 5965440237309775037371445)
                    ·
                      refine ⟨559260022247791409753573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5965440237309775037371445 559260022247791409753573)
                      ·
                        rfl

theorem cell23_1089155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_1089155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089155 prefixEnd_1089155 := by exact prefixLift 1089155
  have htrace : WordTrace (prefixWord ++ tailWord_1089155) baseStart_1089155 baseEnd_1089155 := by
    simpa [prefixWord, tailWord_1089155, baseEnd_1089155] using wordTrace_append hprefix tailTrace_1089155
  have hstable : (prefixWord ++ tailWord_1089155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089155).length < 2 ^ (prefixWord ++ tailWord_1089155).sum := by decide
  have hdescent : baseEnd_1089155 < baseStart_1089155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089162 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 2, 6]
def baseStart_1089162 : Nat := 118140960795 + 1089162 * 2 ^ 59
def prefixEnd_1089162 : Nat := 4983230072969 + 3 ^ 40 * 1089162 * 2
def baseEnd_1089162 : Nat := 186421205537457627455347

theorem tailTrace_1089162 : CollatzResearch.WordTrace tailWord_1089162 prefixEnd_1089162 186421205537457627455347 := by
  unfold tailWord_1089162
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931250420039890726343435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26483334453439708603582493 9931250420039890726343435)
  ·
    refine ⟨14896875630059836089515153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9931250420039890726343435 14896875630059836089515153)
    ·
      refine ⟨11172656722544877067136365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14896875630059836089515153 11172656722544877067136365)
      ·
        refine ⟨4189746270954328900176137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11172656722544877067136365 4189746270954328900176137)
        ·
          refine ⟨3142309703215746675132103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4189746270954328900176137 3142309703215746675132103)
          ·
            refine ⟨4713464554823620012698155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3142309703215746675132103 4713464554823620012698155)
            ·
              refine ⟨7070196832235430019047233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4713464554823620012698155 7070196832235430019047233)
              ·
                refine ⟨5302647624176572514285425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7070196832235430019047233 5302647624176572514285425)
                ·
                  refine ⟨3976985718132429385714069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302647624176572514285425 3976985718132429385714069)
                  ·
                    refine ⟨186421205537457627455347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3976985718132429385714069 186421205537457627455347)
                    ·
                      rfl

theorem cell23_1089162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_1089162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089162 prefixEnd_1089162 := by exact prefixLift 1089162
  have htrace : WordTrace (prefixWord ++ tailWord_1089162) baseStart_1089162 baseEnd_1089162 := by
    simpa [prefixWord, tailWord_1089162, baseEnd_1089162] using wordTrace_append hprefix tailTrace_1089162
  have hstable : (prefixWord ++ tailWord_1089162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089162).length < 2 ^ (prefixWord ++ tailWord_1089162).sum := by decide
  have hdescent : baseEnd_1089162 < baseStart_1089162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089202 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3]
def baseStart_1089202 : Nat := 118140960795 + 1089202 * 2 ^ 59
def prefixEnd_1089202 : Nat := 4983230072969 + 3 ^ 40 * 1089202 * 2
def baseEnd_1089202 : Nat := 559284155838552725865857

theorem tailTrace_1089202 : CollatzResearch.WordTrace tailWord_1089202 prefixEnd_1089202 559284155838552725865857 := by
  unfold tailWord_1089202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931615150003662434207465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26484307066676433157886573 9931615150003662434207465)
  ·
    refine ⟨7448711362502746825655599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9931615150003662434207465 7448711362502746825655599)
    ·
      refine ⟨11173067043754120238483399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7448711362502746825655599 11173067043754120238483399)
      ·
        refine ⟨16759600565631180357725099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173067043754120238483399 16759600565631180357725099)
        ·
          refine ⟨25139400848446770536587649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16759600565631180357725099 25139400848446770536587649)
          ·
            refine ⟨18854550636335077902440737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25139400848446770536587649 18854550636335077902440737)
            ·
              refine ⟨14140912977251308426830553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18854550636335077902440737 14140912977251308426830553)
              ·
                refine ⟨10605684732938481320122915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14140912977251308426830553 10605684732938481320122915)
                ·
                  refine ⟨15908527099407721980184373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10605684732938481320122915 15908527099407721980184373)
                  ·
                    refine ⟨1491424415569473935642285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15908527099407721980184373 1491424415569473935642285)
                    ·
                      refine ⟨559284155838552725865857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491424415569473935642285 559284155838552725865857)
                      ·
                        rfl

theorem cell23_1089202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_1089202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089202 prefixEnd_1089202 := by exact prefixLift 1089202
  have htrace : WordTrace (prefixWord ++ tailWord_1089202) baseStart_1089202 baseEnd_1089202 := by
    simpa [prefixWord, tailWord_1089202, baseEnd_1089202] using wordTrace_append hprefix tailTrace_1089202
  have hstable : (prefixWord ++ tailWord_1089202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089202).length < 2 ^ (prefixWord ++ tailWord_1089202).sum := by decide
  have hdescent : baseEnd_1089202 < baseStart_1089202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089206 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1089206 : Nat := 118140960795 + 1089206 * 2 ^ 59
def prefixEnd_1089206 : Nat := 4983230072969 + 3 ^ 40 * 1089206 * 2
def baseEnd_1089206 : Nat := 559286209761170710215839

theorem tailTrace_1089206 : CollatzResearch.WordTrace tailWord_1089206 prefixEnd_1089206 559286209761170710215839 := by
  unfold tailWord_1089206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482912905750009901248467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26484404328000105613316981 2482912905750009901248467)
  ·
    refine ⟨3724369358625014851872701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482912905750009901248467 3724369358625014851872701)
    ·
      refine ⟨1396638509484380569452263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3724369358625014851872701 1396638509484380569452263)
      ·
        refine ⟨2094957764226570854178395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396638509484380569452263 2094957764226570854178395)
        ·
          refine ⟨3142436646339856281267593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2094957764226570854178395 3142436646339856281267593)
          ·
            refine ⟨2356827484754892210950695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142436646339856281267593 2356827484754892210950695)
            ·
              refine ⟨3535241227132338316426043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2356827484754892210950695 3535241227132338316426043)
              ·
                refine ⟨5302861840698507474639065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3535241227132338316426043 5302861840698507474639065)
                ·
                  refine ⟨3977146380523880605979299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5302861840698507474639065 3977146380523880605979299)
                  ·
                    refine ⟨5965719570785820908968949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3977146380523880605979299 5965719570785820908968949)
                    ·
                      refine ⟨559286209761170710215839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5965719570785820908968949 559286209761170710215839)
                      ·
                        rfl

theorem cell23_1089206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1089206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089206 prefixEnd_1089206 := by exact prefixLift 1089206
  have htrace : WordTrace (prefixWord ++ tailWord_1089206) baseStart_1089206 baseEnd_1089206 := by
    simpa [prefixWord, tailWord_1089206, baseEnd_1089206] using wordTrace_append hprefix tailTrace_1089206
  have hstable : (prefixWord ++ tailWord_1089206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089206).length < 2 ^ (prefixWord ++ tailWord_1089206).sum := by decide
  have hdescent : baseEnd_1089206 < baseStart_1089206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089209 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 5]
def baseStart_1089209 : Nat := 118140960795 + 1089209 * 2 ^ 59
def prefixEnd_1089209 : Nat := 4983230072969 + 3 ^ 40 * 1089209 * 2
def baseEnd_1089209 : Nat := 62143083355903799830925

theorem tailTrace_1089209 : CollatzResearch.WordTrace tailWord_1089209 prefixEnd_1089209 62143083355903799830925 := by
  unfold tailWord_1089209
  simp only [CollatzResearch.WordTrace]
  refine ⟨39726715910989289932334681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26484477273992859954889787 39726715910989289932334681)
  ·
    refine ⟨29795036933241967449251011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39726715910989289932334681 29795036933241967449251011)
    ·
      refine ⟨44692555399862951173876517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29795036933241967449251011 44692555399862951173876517)
      ·
        refine ⟨8379854137474303345101847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44692555399862951173876517 8379854137474303345101847)
        ·
          refine ⟨12569781206211455017652771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8379854137474303345101847 12569781206211455017652771)
          ·
            refine ⟨18854671809317182526479157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12569781206211455017652771 18854671809317182526479157)
            ·
              refine ⟨1767625482123485861857421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18854671809317182526479157 1767625482123485861857421)
              ·
                refine ⟨662859555796307198196533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1767625482123485861857421 662859555796307198196533)
                ·
                  refine ⟨62143083355903799830925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 662859555796307198196533 62143083355903799830925)
                  ·
                    rfl

theorem cell23_1089209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 5].length) (baseStart_1089209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089209 prefixEnd_1089209 := by exact prefixLift 1089209
  have htrace : WordTrace (prefixWord ++ tailWord_1089209) baseStart_1089209 baseEnd_1089209 := by
    simpa [prefixWord, tailWord_1089209, baseEnd_1089209] using wordTrace_append hprefix tailTrace_1089209
  have hstable : (prefixWord ++ tailWord_1089209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089209).length < 2 ^ (prefixWord ++ tailWord_1089209).sum := by decide
  have hdescent : baseEnd_1089209 < baseStart_1089209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089225 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_1089225 : Nat := 118140960795 + 1089225 * 2 ^ 59
def prefixEnd_1089225 : Nat := 4983230072969 + 3 ^ 40 * 1089225 * 2
def baseEnd_1089225 : Nat := 559295965893606135878251

theorem tailTrace_1089225 : CollatzResearch.WordTrace tailWord_1089225 prefixEnd_1089225 559295965893606135878251 := by
  unfold tailWord_1089225
  simp only [CollatzResearch.WordTrace]
  refine ⟨39727299478931324664917129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26484866319287549776611419 39727299478931324664917129)
  ·
    refine ⟨29795474609198493498687847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39727299478931324664917129 29795474609198493498687847)
    ·
      refine ⟨44693211913797740248031771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29795474609198493498687847 44693211913797740248031771)
      ·
        refine ⟨67039817870696610372047657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44693211913797740248031771 67039817870696610372047657)
        ·
          refine ⟨50279863403022457779035743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67039817870696610372047657 50279863403022457779035743)
          ·
            refine ⟨75419795104533686668553615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50279863403022457779035743 75419795104533686668553615)
            ·
              refine ⟨113129692656800530002830423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75419795104533686668553615 113129692656800530002830423)
              ·
                refine ⟨169694538985200795004245635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113129692656800530002830423 169694538985200795004245635)
                ·
                  refine ⟨254541808477801192506368453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169694538985200795004245635 254541808477801192506368453)
                  ·
                    refine ⟨47726589089587723594944085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 254541808477801192506368453 47726589089587723594944085)
                    ·
                      refine ⟨559295965893606135878251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 47726589089587723594944085 559295965893606135878251)
                      ·
                        rfl

theorem cell23_1089225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_1089225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089225 prefixEnd_1089225 := by exact prefixLift 1089225
  have htrace : WordTrace (prefixWord ++ tailWord_1089225) baseStart_1089225 baseEnd_1089225 := by
    simpa [prefixWord, tailWord_1089225, baseEnd_1089225] using wordTrace_append hprefix tailTrace_1089225
  have hstable : (prefixWord ++ tailWord_1089225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089225).length < 2 ^ (prefixWord ++ tailWord_1089225).sum := by decide
  have hdescent : baseEnd_1089225 < baseStart_1089225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089226 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 7]
def baseStart_1089226 : Nat := 118140960795 + 1089226 * 2 ^ 59
def prefixEnd_1089226 : Nat := 4983230072969 + 3 ^ 40 * 1089226 * 2
def baseEnd_1089226 : Nat := 62144053263806736885083

theorem tailTrace_1089226 : CollatzResearch.WordTrace tailWord_1089226 prefixEnd_1089226 62144053263806736885083 := by
  unfold tailWord_1089226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9931833987981925458925883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26484890634618467890469021 9931833987981925458925883)
  ·
    refine ⟨14897750981972888188388825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9931833987981925458925883 14897750981972888188388825)
    ·
      refine ⟨11173313236479666141291619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14897750981972888188388825 11173313236479666141291619)
      ·
        refine ⟨16759969854719499211937429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11173313236479666141291619 16759969854719499211937429)
        ·
          refine ⟨785623586939976525559567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 16759969854719499211937429 785623586939976525559567)
          ·
            refine ⟨1178435380409964788339351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785623586939976525559567 1178435380409964788339351)
            ·
              refine ⟨1767653070614947182509027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178435380409964788339351 1767653070614947182509027)
              ·
                refine ⟨2651479605922420773763541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767653070614947182509027 2651479605922420773763541)
                ·
                  refine ⟨62144053263806736885083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2651479605922420773763541 62144053263806736885083)
                  ·
                    rfl

theorem cell23_1089226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 7].length) (baseStart_1089226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089226 prefixEnd_1089226 := by exact prefixLift 1089226
  have htrace : WordTrace (prefixWord ++ tailWord_1089226) baseStart_1089226 baseEnd_1089226 := by
    simpa [prefixWord, tailWord_1089226, baseEnd_1089226] using wordTrace_append hprefix tailTrace_1089226
  have hstable : (prefixWord ++ tailWord_1089226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089226).length < 2 ^ (prefixWord ++ tailWord_1089226).sum := by decide
  have hdescent : baseEnd_1089226 < baseStart_1089226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089235 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 10]
def baseStart_1089235 : Nat := 118140960795 + 1089235 * 2 ^ 59
def prefixEnd_1089235 : Nat := 4983230072969 + 3 ^ 40 * 1089235 * 2
def baseEnd_1089235 : Nat := 186433700233383698917735

theorem tailTrace_1089235 : CollatzResearch.WordTrace tailWord_1089235 prefixEnd_1089235 186433700233383698917735 := by
  unfold tailWord_1089235
  simp only [CollatzResearch.WordTrace]
  refine ⟨39727664208895096372781159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26485109472596730915187439 39727664208895096372781159)
  ·
    refine ⟨59591496313342644559171739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39727664208895096372781159 59591496313342644559171739)
    ·
      refine ⟨89387244470013966838757609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59591496313342644559171739 89387244470013966838757609)
      ·
        refine ⟨67040433352510475129068207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89387244470013966838757609 67040433352510475129068207)
        ·
          refine ⟨100560650028765712693602311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67040433352510475129068207 100560650028765712693602311)
          ·
            refine ⟨150840975043148569040403467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100560650028765712693602311 150840975043148569040403467)
            ·
              refine ⟨226261462564722853560605201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150840975043148569040403467 226261462564722853560605201)
              ·
                refine ⟨169696096923542140170453901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226261462564722853560605201 169696096923542140170453901)
                ·
                  refine ⟨63636036346328302563920213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 169696096923542140170453901 63636036346328302563920213)
                  ·
                    refine ⟨186433700233383698917735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 63636036346328302563920213 186433700233383698917735)
                    ·
                      rfl

theorem cell23_1089235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_1089235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089235 prefixEnd_1089235 := by exact prefixLift 1089235
  have htrace : WordTrace (prefixWord ++ tailWord_1089235) baseStart_1089235 baseEnd_1089235 := by
    simpa [prefixWord, tailWord_1089235, baseEnd_1089235] using wordTrace_append hprefix tailTrace_1089235
  have hstable : (prefixWord ++ tailWord_1089235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089235).length < 2 ^ (prefixWord ++ tailWord_1089235).sum := by decide
  have hdescent : baseEnd_1089235 < baseStart_1089235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089279 : List Nat := [1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_1089279 : Nat := 118140960795 + 1089279 * 2 ^ 59
def prefixEnd_1089279 : Nat := 4983230072969 + 3 ^ 40 * 1089279 * 2
def baseEnd_1089279 : Nat := 559323693848948924603003

theorem tailTrace_1089279 : CollatzResearch.WordTrace tailWord_1089279 prefixEnd_1089279 559323693848948924603003 := by
  unfold tailWord_1089279
  simp only [CollatzResearch.WordTrace]
  refine ⟨39729269020735691887382891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26486179347157127924921927 39729269020735691887382891)
  ·
    refine ⟨59593903531103537831074337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39729269020735691887382891 59593903531103537831074337)
    ·
      refine ⟨44695427648327653373305753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59593903531103537831074337 44695427648327653373305753)
      ·
        refine ⟨33521570736245740029979315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44695427648327653373305753 33521570736245740029979315)
        ·
          refine ⟨50282356104368610044968973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33521570736245740029979315 50282356104368610044968973)
          ·
            refine ⟨18855883539138228766863365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50282356104368610044968973 18855883539138228766863365)
            ·
              refine ⟨3535478163588417893786881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18855883539138228766863365 3535478163588417893786881)
              ·
                refine ⟨2651608622691313420340161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3535478163588417893786881 2651608622691313420340161)
                ·
                  refine ⟨1988706467018485065255121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2651608622691313420340161 1988706467018485065255121)
                  ·
                    refine ⟨1491529850263863798941341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1988706467018485065255121 1491529850263863798941341)
                    ·
                      refine ⟨559323693848948924603003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491529850263863798941341 559323693848948924603003)
                      ·
                        rfl

theorem cell23_1089279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_1089279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089279 prefixEnd_1089279 := by exact prefixLift 1089279
  have htrace : WordTrace (prefixWord ++ tailWord_1089279) baseStart_1089279 baseEnd_1089279 := by
    simpa [prefixWord, tailWord_1089279, baseEnd_1089279] using wordTrace_append hprefix tailTrace_1089279
  have hstable : (prefixWord ++ tailWord_1089279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089279).length < 2 ^ (prefixWord ++ tailWord_1089279).sum := by decide
  have hdescent : baseEnd_1089279 < baseStart_1089279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089333 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 6]
def baseStart_1089333 : Nat := 118140960795 + 1089333 * 2 ^ 59
def prefixEnd_1089333 : Nat := 4983230072969 + 3 ^ 40 * 1089333 * 2
def baseEnd_1089333 : Nat := 62150157978254634814195

theorem tailTrace_1089333 : CollatzResearch.WordTrace tailWord_1089333 prefixEnd_1089333 62150157978254634814195 := by
  unfold tailWord_1089333
  simp only [CollatzResearch.WordTrace]
  refine ⟨39731238562540059109848653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26487492375026706073232435 39731238562540059109848653)
  ·
    refine ⟨14899214460952522166193245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39731238562540059109848653 14899214460952522166193245)
    ·
      refine ⟨5587205422857195812322467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14899214460952522166193245 5587205422857195812322467)
      ·
        refine ⟨8380808134285793718483701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5587205422857195812322467 8380808134285793718483701)
        ·
          refine ⟨785700762589293161107847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8380808134285793718483701 785700762589293161107847)
          ·
            refine ⟨1178551143883939741661771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 785700762589293161107847 1178551143883939741661771)
            ·
              refine ⟨1767826715825909612492657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178551143883939741661771 1767826715825909612492657)
              ·
                refine ⟨1325870036869432209369493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1767826715825909612492657 1325870036869432209369493)
                ·
                  refine ⟨62150157978254634814195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1325870036869432209369493 62150157978254634814195)
                  ·
                    rfl

theorem cell23_1089333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_1089333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089333 prefixEnd_1089333 := by exact prefixLift 1089333
  have htrace : WordTrace (prefixWord ++ tailWord_1089333) baseStart_1089333 baseEnd_1089333 := by
    simpa [prefixWord, tailWord_1089333, baseEnd_1089333] using wordTrace_append hprefix tailTrace_1089333
  have hstable : (prefixWord ++ tailWord_1089333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089333).length < 2 ^ (prefixWord ++ tailWord_1089333).sum := by decide
  have hdescent : baseEnd_1089333 < baseStart_1089333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089343 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 3]
def baseStart_1089343 : Nat := 118140960795 + 1089343 * 2 ^ 59
def prefixEnd_1089343 : Nat := 4983230072969 + 3 ^ 40 * 1089343 * 2
def baseEnd_1089343 : Nat := 559356556610836674202709

theorem tailTrace_1089343 : CollatzResearch.WordTrace tailWord_1089343 prefixEnd_1089343 559356556610836674202709 := by
  unfold tailWord_1089343
  simp only [CollatzResearch.WordTrace]
  refine ⟨39731603292503830817712683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26487735528335887211808455 39731603292503830817712683)
  ·
    refine ⟨59597404938755746226569025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39731603292503830817712683 59597404938755746226569025)
    ·
      refine ⟨44698053704066809669926769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59597404938755746226569025 44698053704066809669926769)
      ·
        refine ⟨33523540278050107252445077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44698053704066809669926769 33523540278050107252445077)
        ·
          refine ⟨1571415950533598777458363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33523540278050107252445077 1571415950533598777458363)
          ·
            refine ⟨2357123925800398166187545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1571415950533598777458363 2357123925800398166187545)
            ·
              refine ⟨1767842944350298624640659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2357123925800398166187545 1767842944350298624640659)
              ·
                refine ⟨2651764416525447936960989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1767842944350298624640659 2651764416525447936960989)
                ·
                  refine ⟨994411656197042976360371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2651764416525447936960989 994411656197042976360371)
                  ·
                    refine ⟨1491617484295564464540557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 994411656197042976360371 1491617484295564464540557)
                    ·
                      refine ⟨559356556610836674202709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491617484295564464540557 559356556610836674202709)
                      ·
                        rfl

theorem cell23_1089343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_1089343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089343 prefixEnd_1089343 := by exact prefixLift 1089343
  have htrace : WordTrace (prefixWord ++ tailWord_1089343) baseStart_1089343 baseEnd_1089343 := by
    simpa [prefixWord, tailWord_1089343, baseEnd_1089343] using wordTrace_append hprefix tailTrace_1089343
  have hstable : (prefixWord ++ tailWord_1089343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089343).length < 2 ^ (prefixWord ++ tailWord_1089343).sum := by decide
  have hdescent : baseEnd_1089343 < baseStart_1089343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089350 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1089350 : Nat := 118140960795 + 1089350 * 2 ^ 59
def prefixEnd_1089350 : Nat := 4983230072969 + 3 ^ 40 * 1089350 * 2
def baseEnd_1089350 : Nat := 62151127886157571868353

theorem tailTrace_1089350 : CollatzResearch.WordTrace tailWord_1089350 prefixEnd_1089350 62151127886157571868353 := by
  unfold tailWord_1089350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241620581358702219163047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26487905735652314008811669 1241620581358702219163047)
  ·
    refine ⟨1862430872038053328744571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241620581358702219163047 1862430872038053328744571)
    ·
      refine ⟨2793646308057079993116857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1862430872038053328744571 2793646308057079993116857)
      ·
        refine ⟨2095234731042809994837643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2793646308057079993116857 2095234731042809994837643)
        ·
          refine ⟨3142852096564214992256465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095234731042809994837643 3142852096564214992256465)
          ·
            refine ⟨2357139072423161244192349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3142852096564214992256465 2357139072423161244192349)
            ·
              refine ⟨883927152158685466572131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2357139072423161244192349 883927152158685466572131)
              ·
                refine ⟨1325890728238028199858197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 883927152158685466572131 1325890728238028199858197)
                ·
                  refine ⟨62151127886157571868353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1325890728238028199858197 62151127886157571868353)
                  ·
                    rfl

theorem cell23_1089350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1089350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089350 prefixEnd_1089350 := by exact prefixLift 1089350
  have htrace : WordTrace (prefixWord ++ tailWord_1089350) baseStart_1089350 baseEnd_1089350 := by
    simpa [prefixWord, tailWord_1089350, baseEnd_1089350] using wordTrace_append hprefix tailTrace_1089350
  have hstable : (prefixWord ++ tailWord_1089350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089350).length < 2 ^ (prefixWord ++ tailWord_1089350).sum := by decide
  have hdescent : baseEnd_1089350 < baseStart_1089350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089406 : List Nat := [4, 2, 3, 1, 1, 1, 1, 10]
def baseStart_1089406 : Nat := 118140960795 + 1089406 * 2 ^ 59
def prefixEnd_1089406 : Nat := 4983230072969 + 3 ^ 40 * 1089406 * 2
def baseEnd_1089406 : Nat := 20718107625632219544997

theorem tailTrace_1089406 : CollatzResearch.WordTrace tailWord_1089406 prefixEnd_1089406 20718107625632219544997 := by
  unfold tailWord_1089406
  simp only [CollatzResearch.WordTrace]
  refine ⟨4966737636409449072157009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26489267394183728384837381 4966737636409449072157009)
  ·
    refine ⟨3725053227307086804117757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4966737636409449072157009 3725053227307086804117757)
    ·
      refine ⟨1396894960240157551544159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3725053227307086804117757 1396894960240157551544159)
      ·
        refine ⟨2095342440360236327316239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1396894960240157551544159 2095342440360236327316239)
        ·
          refine ⟨3143013660540354490974359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2095342440360236327316239 3143013660540354490974359)
          ·
            refine ⟨4714520490810531736461539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3143013660540354490974359 4714520490810531736461539)
            ·
              refine ⟨7071780736215797604692309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4714520490810531736461539 7071780736215797604692309)
              ·
                refine ⟨20718107625632219544997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 7071780736215797604692309 20718107625632219544997)
                ·
                  rfl

theorem cell23_1089406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_1089406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089406 prefixEnd_1089406 := by exact prefixLift 1089406
  have htrace : WordTrace (prefixWord ++ tailWord_1089406) baseStart_1089406 baseEnd_1089406 := by
    simpa [prefixWord, tailWord_1089406, baseEnd_1089406] using wordTrace_append hprefix tailTrace_1089406
  have hstable : (prefixWord ++ tailWord_1089406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089406).length < 2 ^ (prefixWord ++ tailWord_1089406).sum := by decide
  have hdescent : baseEnd_1089406 < baseStart_1089406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089459 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3]
def baseStart_1089459 : Nat := 118140960795 + 1089459 * 2 ^ 59
def prefixEnd_1089459 : Nat := 4983230072969 + 3 ^ 40 * 1089459 * 2
def baseEnd_1089459 : Nat := 559416120366758220352175

theorem tailTrace_1089459 : CollatzResearch.WordTrace tailWord_1089459 prefixEnd_1089459 559416120366758220352175 := by
  unfold tailWord_1089459
  simp only [CollatzResearch.WordTrace]
  refine ⟨39735834160083582628935431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26490556106722388419290287 39735834160083582628935431)
  ·
    refine ⟨59603751240125373943403147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39735834160083582628935431 59603751240125373943403147)
    ·
      refine ⟨89405626860188060915104721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59603751240125373943403147 89405626860188060915104721)
      ·
        refine ⟨67054220145141045686328541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89405626860188060915104721 67054220145141045686328541)
        ·
          refine ⟨25145332554427892132373203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67054220145141045686328541 25145332554427892132373203)
          ·
            refine ⟨37717998831641838198559805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25145332554427892132373203 37717998831641838198559805)
            ·
              refine ⟨14144249561865689324459927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37717998831641838198559805 14144249561865689324459927)
              ·
                refine ⟨21216374342798533986689891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14144249561865689324459927 21216374342798533986689891)
                ·
                  refine ⟨31824561514197800980034837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21216374342798533986689891 31824561514197800980034837)
                  ·
                    refine ⟨1491776320978021920939133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 31824561514197800980034837 1491776320978021920939133)
                    ·
                      refine ⟨559416120366758220352175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1491776320978021920939133 559416120366758220352175)
                      ·
                        rfl

theorem cell23_1089459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_1089459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089459 prefixEnd_1089459 := by exact prefixLift 1089459
  have htrace : WordTrace (prefixWord ++ tailWord_1089459) baseStart_1089459 baseEnd_1089459 := by
    simpa [prefixWord, tailWord_1089459, baseEnd_1089459] using wordTrace_append hprefix tailTrace_1089459
  have hstable : (prefixWord ++ tailWord_1089459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089459).length < 2 ^ (prefixWord ++ tailWord_1089459).sum := by decide
  have hdescent : baseEnd_1089459 < baseStart_1089459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089507 : List Nat := [1, 1, 1, 6, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1089507 : Nat := 118140960795 + 1089507 * 2 ^ 59
def prefixEnd_1089507 : Nat := 4983230072969 + 3 ^ 40 * 1089507 * 2
def baseEnd_1089507 : Nat := 559440767438174032551955

theorem tailTrace_1089507 : CollatzResearch.WordTrace tailWord_1089507 prefixEnd_1089507 559440767438174032551955 := by
  unfold tailWord_1089507
  simp only [CollatzResearch.WordTrace]
  refine ⟨39737584863909686826682775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26491723242606457884455183 39737584863909686826682775)
  ·
    refine ⟨59606377295864530240024163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39737584863909686826682775 59606377295864530240024163)
    ·
      refine ⟨89409565943796795360036245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59606377295864530240024163 89409565943796795360036245)
      ·
        refine ⟨4191073403615474782501699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 89409565943796795360036245 4191073403615474782501699)
        ·
          refine ⟨6286610105423212173752549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4191073403615474782501699 6286610105423212173752549)
          ·
            refine ⟨1178739394766852282578603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6286610105423212173752549 1178739394766852282578603)
            ·
              refine ⟨1768109092150278423867905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178739394766852282578603 1768109092150278423867905)
              ·
                refine ⟨1326081819112708817900929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1768109092150278423867905 1326081819112708817900929)
                ·
                  refine ⟨994561364334531613425697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1326081819112708817900929 994561364334531613425697)
                  ·
                    refine ⟨745921023250898710069273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 994561364334531613425697 745921023250898710069273)
                    ·
                      refine ⟨559440767438174032551955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745921023250898710069273 559440767438174032551955)
                      ·
                        rfl

theorem cell23_1089507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1089507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089507 prefixEnd_1089507 := by exact prefixLift 1089507
  have htrace : WordTrace (prefixWord ++ tailWord_1089507) baseStart_1089507 baseEnd_1089507 := by
    simpa [prefixWord, tailWord_1089507, baseEnd_1089507] using wordTrace_append hprefix tailTrace_1089507
  have hstable : (prefixWord ++ tailWord_1089507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089507).length < 2 ^ (prefixWord ++ tailWord_1089507).sum := by decide
  have hdescent : baseEnd_1089507 < baseStart_1089507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089516 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 7, 2]
def baseStart_1089516 : Nat := 118140960795 + 1089516 * 2 ^ 59
def prefixEnd_1089516 : Nat := 4983230072969 + 3 ^ 40 * 1089516 * 2
def baseEnd_1089516 : Nat := 559445388764064497339413

theorem tailTrace_1089516 : CollatzResearch.WordTrace tailWord_1089516 prefixEnd_1089516 559445388764064497339413 := by
  unfold tailWord_1089516
  simp only [CollatzResearch.WordTrace]
  refine ⟨19868956560438540681880201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26491942080584720909173601 19868956560438540681880201)
  ·
    refine ⟨14901717420328905511410151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19868956560438540681880201 14901717420328905511410151)
    ·
      refine ⟨22352576130493358267115227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14901717420328905511410151 22352576130493358267115227)
      ·
        refine ⟨33528864195740037400672841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22352576130493358267115227 33528864195740037400672841)
        ·
          refine ⟨25146648146805028050504631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33528864195740037400672841 25146648146805028050504631)
          ·
            refine ⟨37719972220207542075756947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25146648146805028050504631 37719972220207542075756947)
            ·
              refine ⟨56579958330311313113635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37719972220207542075756947 56579958330311313113635421)
              ·
                refine ⟨21217484373866742417613283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56579958330311313113635421 21217484373866742417613283)
                ·
                  refine ⟨31826226560800113626419925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21217484373866742417613283 31826226560800113626419925)
                  ·
                    refine ⟨745927185018752663119217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31826226560800113626419925 745927185018752663119217)
                    ·
                      refine ⟨559445388764064497339413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 745927185018752663119217 559445388764064497339413)
                      ·
                        rfl

theorem cell23_1089516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_1089516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089516 prefixEnd_1089516 := by exact prefixLift 1089516
  have htrace : WordTrace (prefixWord ++ tailWord_1089516) baseStart_1089516 baseEnd_1089516 := by
    simpa [prefixWord, tailWord_1089516, baseEnd_1089516] using wordTrace_append hprefix tailTrace_1089516
  have hstable : (prefixWord ++ tailWord_1089516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089516).length < 2 ^ (prefixWord ++ tailWord_1089516).sum := by decide
  have hdescent : baseEnd_1089516 < baseStart_1089516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089519 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_1089519 : Nat := 118140960795 + 1089519 * 2 ^ 59
def prefixEnd_1089519 : Nat := 4983230072969 + 3 ^ 40 * 1089519 * 2
def baseEnd_1089519 : Nat := 559446929206027985601899

theorem tailTrace_1089519 : CollatzResearch.WordTrace tailWord_1089519 prefixEnd_1089519 559446929206027985601899 := by
  unfold tailWord_1089519
  simp only [CollatzResearch.WordTrace]
  refine ⟨39738022539866212876119611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26492015026577475250746407 39738022539866212876119611)
  ·
    refine ⟨59607033809799319314179417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39738022539866212876119611 59607033809799319314179417)
    ·
      refine ⟨44705275357349489485634563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59607033809799319314179417 44705275357349489485634563)
      ·
        refine ⟨67057913036024234228451845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44705275357349489485634563 67057913036024234228451845)
        ·
          refine ⟨12573358694254543917834721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67057913036024234228451845 12573358694254543917834721)
          ·
            refine ⟨9430019020690907938376041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12573358694254543917834721 9430019020690907938376041)
            ·
              refine ⟨7072514265518180953782031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9430019020690907938376041 7072514265518180953782031)
              ·
                refine ⟨10608771398277271430673047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7072514265518180953782031 10608771398277271430673047)
                ·
                  refine ⟨15913157097415907146009571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10608771398277271430673047 15913157097415907146009571)
                  ·
                    refine ⟨23869735646123860719014357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15913157097415907146009571 23869735646123860719014357)
                    ·
                      refine ⟨559446929206027985601899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 23869735646123860719014357 559446929206027985601899)
                      ·
                        rfl

theorem cell23_1089519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_1089519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089519 prefixEnd_1089519 := by exact prefixLift 1089519
  have htrace : WordTrace (prefixWord ++ tailWord_1089519) baseStart_1089519 baseEnd_1089519 := by
    simpa [prefixWord, tailWord_1089519, baseEnd_1089519] using wordTrace_append hprefix tailTrace_1089519
  have hstable : (prefixWord ++ tailWord_1089519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089519).length < 2 ^ (prefixWord ++ tailWord_1089519).sum := by decide
  have hdescent : baseEnd_1089519 < baseStart_1089519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089573 : List Nat := [1, 3, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_1089573 : Nat := 118140960795 + 1089573 * 2 ^ 59
def prefixEnd_1089573 : Nat := 4983230072969 + 3 ^ 40 * 1089573 * 2
def baseEnd_1089573 : Nat := 186491552387123591442217

theorem tailTrace_1089573 : CollatzResearch.WordTrace tailWord_1089573 prefixEnd_1089573 186491552387123591442217 := by
  unfold tailWord_1089573
  simp only [CollatzResearch.WordTrace]
  refine ⟨39739992081670580098585373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26493328054447053399056915 39739992081670580098585373)
  ·
    refine ⟨14902497030626467536969515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39739992081670580098585373 14902497030626467536969515)
    ·
      refine ⟨22353745545939701305454273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14902497030626467536969515 22353745545939701305454273)
      ·
        refine ⟨16765309159454775979090705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22353745545939701305454273 16765309159454775979090705)
        ·
          refine ⟨12573981869591081984318029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16765309159454775979090705 12573981869591081984318029)
          ·
            refine ⟨4715243201096655744119261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12573981869591081984318029 4715243201096655744119261)
            ·
              refine ⟨1768216200411245904044723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4715243201096655744119261 1768216200411245904044723)
              ·
                refine ⟨2652324300616868856067085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768216200411245904044723 2652324300616868856067085)
                ·
                  refine ⟨994621612731325821025157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2652324300616868856067085 994621612731325821025157)
                  ·
                    refine ⟨186491552387123591442217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 994621612731325821025157 186491552387123591442217)
                    ·
                      rfl

theorem cell23_1089573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_1089573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089573 prefixEnd_1089573 := by exact prefixLift 1089573
  have htrace : WordTrace (prefixWord ++ tailWord_1089573) baseStart_1089573 baseEnd_1089573 := by
    simpa [prefixWord, tailWord_1089573, baseEnd_1089573] using wordTrace_append hprefix tailTrace_1089573
  have hstable : (prefixWord ++ tailWord_1089573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089573).length < 2 ^ (prefixWord ++ tailWord_1089573).sum := by decide
  have hdescent : baseEnd_1089573 < baseStart_1089573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1089657 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 2, 3, 2]
def baseStart_1089657 : Nat := 118140960795 + 1089657 * 2 ^ 59
def prefixEnd_1089657 : Nat := 4983230072969 + 3 ^ 40 * 1089657 * 2
def baseEnd_1089657 : Nat := 559517789536348445676265

theorem tailTrace_1089657 : CollatzResearch.WordTrace tailWord_1089657 prefixEnd_1089657 559517789536348445676265 := by
  unfold tailWord_1089657
  simp only [CollatzResearch.WordTrace]
  refine ⟨39743055813366262444643225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26495370542244174963095483 39743055813366262444643225)
  ·
    refine ⟨29807291860024696833482419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39743055813366262444643225 29807291860024696833482419)
    ·
      refine ⟨44710937790037045250223629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29807291860024696833482419 44710937790037045250223629)
      ·
        refine ⟨16766601671263891968833861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44710937790037045250223629 16766601671263891968833861)
        ·
          refine ⟨3143737813361979744156349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16766601671263891968833861 3143737813361979744156349)
          ·
            refine ⟨1178901680010742404058631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3143737813361979744156349 1178901680010742404058631)
            ·
              refine ⟨1768352520016113606087947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1178901680010742404058631 1768352520016113606087947)
              ·
                refine ⟨2652528780024170409131921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1768352520016113606087947 2652528780024170409131921)
                ·
                  refine ⟨1989396585018127806848941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2652528780024170409131921 1989396585018127806848941)
                  ·
                    refine ⟨746023719381797927568353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1989396585018127806848941 746023719381797927568353)
                    ·
                      refine ⟨559517789536348445676265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 746023719381797927568353 559517789536348445676265)
                      ·
                        rfl

theorem cell23_1089657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_1089657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1089657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1089657 prefixEnd_1089657 := by exact prefixLift 1089657
  have htrace : WordTrace (prefixWord ++ tailWord_1089657) baseStart_1089657 baseEnd_1089657 := by
    simpa [prefixWord, tailWord_1089657, baseEnd_1089657] using wordTrace_append hprefix tailTrace_1089657
  have hstable : (prefixWord ++ tailWord_1089657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1089657).length < 2 ^ (prefixWord ++ tailWord_1089657).sum := by decide
  have hdescent : baseEnd_1089657 < baseStart_1089657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1089657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
