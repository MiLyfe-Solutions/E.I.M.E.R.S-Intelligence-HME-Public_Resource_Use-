import V185TrunkScan21Chunk008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_108114 : List Nat := [3, 2, 2, 1, 2, 3, 3, 5]
def baseStart_108114 : Nat := 118140960795 + 108114 * 2 ^ 59
def prefixEnd_108114 : Nat := 4983230072969 + 3 ^ 40 * 108114 * 2
def baseEnd_108114 : Nat := 8224362589673368470785

theorem tailTrace_108114 : CollatzResearch.WordTrace tailWord_108114 prefixEnd_108114 8224362589673368470785 := by
  unfold tailWord_108114
  simp only [CollatzResearch.WordTrace]
  refine ⟨985810382582229311570849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2628827686885944830855597 985810382582229311570849)
  ·
    refine ⟨739357786936671983678137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 985810382582229311570849 739357786936671983678137)
    ·
      refine ⟨554518340202503987758603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 739357786936671983678137 554518340202503987758603)
      ·
        refine ⟨831777510303755981637905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554518340202503987758603 831777510303755981637905)
        ·
          refine ⟨623833132727816986228429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831777510303755981637905 623833132727816986228429)
          ·
            refine ⟨233937424772931369835661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623833132727816986228429 233937424772931369835661)
            ·
              refine ⟨87726534289849263688373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233937424772931369835661 87726534289849263688373)
              ·
                refine ⟨8224362589673368470785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87726534289849263688373 8224362589673368470785)
                ·
                  rfl

theorem cell21_108114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 5].length) (baseStart_108114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108114 prefixEnd_108114 := by exact prefixLift 108114
  have htrace : WordTrace (prefixWord ++ tailWord_108114) baseStart_108114 baseEnd_108114 := by
    simpa [prefixWord, tailWord_108114, baseEnd_108114] using wordTrace_append hprefix tailTrace_108114
  have hstable : (prefixWord ++ tailWord_108114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108114).length < 2 ^ (prefixWord ++ tailWord_108114).sum := by decide
  have hdescent : baseEnd_108114 < baseStart_108114 := by decide
  rcases family_descends (prefixWord ++ tailWord_108114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108156 : List Nat := [2, 2, 2, 1, 1, 2, 1, 10]
def baseStart_108156 : Nat := 118140960795 + 108156 * 2 ^ 59
def prefixEnd_108156 : Nat := 4983230072969 + 3 ^ 40 * 108156 * 2
def baseEnd_108156 : Nat := 8227557580412455237423

theorem tailTrace_108156 : CollatzResearch.WordTrace tailWord_108156 prefixEnd_108156 8227557580412455237423 := by
  unfold tailWord_108156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972386698088379209656161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2629848930784505612874881 1972386698088379209656161)
  ·
    refine ⟨1479290023566284407242121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1972386698088379209656161 1479290023566284407242121)
    ·
      refine ⟨1109467517674713305431591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479290023566284407242121 1109467517674713305431591)
      ·
        refine ⟨1664201276512069958147387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109467517674713305431591 1664201276512069958147387)
        ·
          refine ⟨2496301914768104937221081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664201276512069958147387 2496301914768104937221081)
          ·
            refine ⟨1872226436076078702915811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496301914768104937221081 1872226436076078702915811)
            ·
              refine ⟨2808339654114118054373717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872226436076078702915811 2808339654114118054373717)
              ·
                refine ⟨8227557580412455237423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2808339654114118054373717 8227557580412455237423)
                ·
                  rfl

theorem cell21_108156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 10].length) (baseStart_108156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108156 prefixEnd_108156 := by exact prefixLift 108156
  have htrace : WordTrace (prefixWord ++ tailWord_108156) baseStart_108156 baseEnd_108156 := by
    simpa [prefixWord, tailWord_108156, baseEnd_108156] using wordTrace_append hprefix tailTrace_108156
  have hstable : (prefixWord ++ tailWord_108156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108156).length < 2 ^ (prefixWord ++ tailWord_108156).sum := by decide
  have hdescent : baseEnd_108156 < baseStart_108156 := by decide
  rcases family_descends (prefixWord ++ tailWord_108156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108190 : List Nat := [4, 3, 1, 1, 1, 4, 7]
def baseStart_108190 : Nat := 118140960795 + 108190 * 2 ^ 59
def prefixEnd_108190 : Nat := 4983230072969 + 3 ^ 40 * 108190 * 2
def baseEnd_108190 : Nat := 2743381333828984682837

theorem tailTrace_108190 : CollatzResearch.WordTrace tailWord_108190 prefixEnd_108190 2743381333828984682837 := by
  unfold tailWord_108190
  simp only [CollatzResearch.WordTrace]
  refine ⟨493251684756697778256253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2630675652035721484033349 493251684756697778256253)
  ·
    refine ⟨184969381783761666846095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 493251684756697778256253 184969381783761666846095)
    ·
      refine ⟨277454072675642500269143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184969381783761666846095 277454072675642500269143)
      ·
        refine ⟨416181109013463750403715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277454072675642500269143 416181109013463750403715)
        ·
          refine ⟨624271663520195625605573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416181109013463750403715 624271663520195625605573)
          ·
            refine ⟨117050936910036679801045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 624271663520195625605573 117050936910036679801045)
            ·
              refine ⟨2743381333828984682837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117050936910036679801045 2743381333828984682837)
              ·
                rfl

theorem cell21_108190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 7].length) (baseStart_108190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108190 prefixEnd_108190 := by exact prefixLift 108190
  have htrace : WordTrace (prefixWord ++ tailWord_108190) baseStart_108190 baseEnd_108190 := by
    simpa [prefixWord, tailWord_108190, baseEnd_108190] using wordTrace_append hprefix tailTrace_108190
  have hstable : (prefixWord ++ tailWord_108190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108190).length < 2 ^ (prefixWord ++ tailWord_108190).sum := by decide
  have hdescent : baseEnd_108190 < baseStart_108190 := by decide
  rcases family_descends (prefixWord ++ tailWord_108190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108201 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 10]
def baseStart_108201 : Nat := 118140960795 + 108201 * 2 ^ 59
def prefixEnd_108201 : Nat := 4983230072969 + 3 ^ 40 * 108201 * 2
def baseEnd_108201 : Nat := 24692942354327287462177

theorem tailTrace_108201 : CollatzResearch.WordTrace tailWord_108201 prefixEnd_108201 24692942354327287462177 := by
  unfold tailWord_108201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946414681013731104700457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2630943120675820736466971 3946414681013731104700457)
  ·
    refine ⟨2959811010760298328525343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3946414681013731104700457 2959811010760298328525343)
    ·
      refine ⟨4439716516140447492788015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959811010760298328525343 4439716516140447492788015)
      ·
        refine ⟨6659574774210671239182023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439716516140447492788015 6659574774210671239182023)
        ·
          refine ⟨9989362161316006858773035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659574774210671239182023 9989362161316006858773035)
          ·
            refine ⟨14984043241974010288159553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9989362161316006858773035 14984043241974010288159553)
            ·
              refine ⟨11238032431480507716119665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14984043241974010288159553 11238032431480507716119665)
              ·
                refine ⟨8428524323610380787089749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11238032431480507716119665 8428524323610380787089749)
                ·
                  refine ⟨24692942354327287462177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 8428524323610380787089749 24692942354327287462177)
                  ·
                    rfl

theorem cell21_108201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_108201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108201 prefixEnd_108201 := by exact prefixLift 108201
  have htrace : WordTrace (prefixWord ++ tailWord_108201) baseStart_108201 baseEnd_108201 := by
    simpa [prefixWord, tailWord_108201, baseEnd_108201] using wordTrace_append hprefix tailTrace_108201
  have hstable : (prefixWord ++ tailWord_108201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108201).length < 2 ^ (prefixWord ++ tailWord_108201).sum := by decide
  have hdescent : baseEnd_108201 < baseStart_108201 := by decide
  rcases family_descends (prefixWord ++ tailWord_108201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108232 : List Nat := [2, 1, 3, 1, 2, 2, 1, 9]
def baseStart_108232 : Nat := 118140960795 + 108232 * 2 ^ 59
def prefixEnd_108232 : Nat := 4983230072969 + 3 ^ 40 * 108232 * 2
def baseEnd_108232 : Nat := 8233338992226040815149

theorem tailTrace_108232 : CollatzResearch.WordTrace tailWord_108232 prefixEnd_108232 8233338992226040815149 := by
  unfold tailWord_108232
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973772671950711699539475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2631696895934282266052633 1973772671950711699539475)
  ·
    refine ⟨2960659007926067549309213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973772671950711699539475 2960659007926067549309213)
    ·
      refine ⟨1110247127972275330990955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2960659007926067549309213 1110247127972275330990955)
      ·
        refine ⟨1665370691958412996486433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110247127972275330990955 1665370691958412996486433)
        ·
          refine ⟨1249028018968809747364825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665370691958412996486433 1249028018968809747364825)
          ·
            refine ⟨936771014226607310523619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249028018968809747364825 936771014226607310523619)
            ·
              refine ⟨1405156521339910965785429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936771014226607310523619 1405156521339910965785429)
              ·
                refine ⟨8233338992226040815149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1405156521339910965785429 8233338992226040815149)
                ·
                  rfl

theorem cell21_108232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_108232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108232 prefixEnd_108232 := by exact prefixLift 108232
  have htrace : WordTrace (prefixWord ++ tailWord_108232) baseStart_108232 baseEnd_108232 := by
    simpa [prefixWord, tailWord_108232, baseEnd_108232] using wordTrace_append hprefix tailTrace_108232
  have hstable : (prefixWord ++ tailWord_108232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108232).length < 2 ^ (prefixWord ++ tailWord_108232).sum := by decide
  have hdescent : baseEnd_108232 < baseStart_108232 := by decide
  rcases family_descends (prefixWord ++ tailWord_108232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108311 : List Nat := [1, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_108311 : Nat := 118140960795 + 108311 * 2 ^ 59
def prefixEnd_108311 : Nat := 4983230072969 + 3 ^ 40 * 108311 * 2
def baseEnd_108311 : Nat := 24718045852991540628619

theorem tailTrace_108311 : CollatzResearch.WordTrace tailWord_108311 prefixEnd_108311 24718045852991540628619 := by
  unfold tailWord_108311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950426710615219891204787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2633617807076813260803191 3950426710615219891204787)
  ·
    refine ⟨5925640065922829836807181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3950426710615219891204787 5925640065922829836807181)
    ·
      refine ⟨2222115024721061188802693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5925640065922829836807181 2222115024721061188802693)
      ·
        refine ⟨416646567135198972900505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2222115024721061188802693 416646567135198972900505)
        ·
          refine ⟨312484925351399229675379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416646567135198972900505 312484925351399229675379)
          ·
            refine ⟨468727388027098844513069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312484925351399229675379 468727388027098844513069)
            ·
              refine ⟨175772770510162066692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468727388027098844513069 175772770510162066692401)
              ·
                refine ⟨131829577882621550019301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175772770510162066692401 131829577882621550019301)
                ·
                  refine ⟨24718045852991540628619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131829577882621550019301 24718045852991540628619)
                  ·
                    rfl

theorem cell21_108311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_108311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108311 prefixEnd_108311 := by exact prefixLift 108311
  have htrace : WordTrace (prefixWord ++ tailWord_108311) baseStart_108311 baseEnd_108311 := by
    simpa [prefixWord, tailWord_108311, baseEnd_108311] using wordTrace_append hprefix tailTrace_108311
  have hstable : (prefixWord ++ tailWord_108311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108311).length < 2 ^ (prefixWord ++ tailWord_108311).sum := by decide
  have hdescent : baseEnd_108311 < baseStart_108311 := by decide
  rcases family_descends (prefixWord ++ tailWord_108311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108328 : List Nat := [2, 1, 5, 1, 1, 3, 3, 1, 4]
def baseStart_108328 : Nat := 118140960795 + 108328 * 2 ^ 59
def prefixEnd_108328 : Nat := 4983230072969 + 3 ^ 40 * 108328 * 2
def baseEnd_108328 : Nat := 24721925484603288845251

theorem tailTrace_108328 : CollatzResearch.WordTrace tailWord_108328 prefixEnd_108328 24721925484603288845251 := by
  unfold tailWord_108328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1975523375776815897286819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2634031167702421196382425 1975523375776815897286819)
  ·
    refine ⟨2963285063665223845930229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1975523375776815897286819 2963285063665223845930229)
    ·
      refine ⟨277807974718614735555959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2963285063665223845930229 277807974718614735555959)
      ·
        refine ⟨416711962077922103333939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277807974718614735555959 416711962077922103333939)
        ·
          refine ⟨625067943116883155000909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416711962077922103333939 625067943116883155000909)
          ·
            refine ⟨234400478668831183125341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625067943116883155000909 234400478668831183125341)
            ·
              refine ⟨87900179500811693672003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234400478668831183125341 87900179500811693672003)
              ·
                refine ⟨131850269251217540508005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87900179500811693672003 131850269251217540508005)
                ·
                  refine ⟨24721925484603288845251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131850269251217540508005 24721925484603288845251)
                  ·
                    rfl

theorem cell21_108328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 1, 4].length) (baseStart_108328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108328 prefixEnd_108328 := by exact prefixLift 108328
  have htrace : WordTrace (prefixWord ++ tailWord_108328) baseStart_108328 baseEnd_108328 := by
    simpa [prefixWord, tailWord_108328, baseEnd_108328] using wordTrace_append hprefix tailTrace_108328
  have hstable : (prefixWord ++ tailWord_108328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108328).length < 2 ^ (prefixWord ++ tailWord_108328).sum := by decide
  have hdescent : baseEnd_108328 < baseStart_108328 := by decide
  rcases family_descends (prefixWord ++ tailWord_108328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108342 : List Nat := [5, 1, 2, 2, 1, 2, 1, 7]
def baseStart_108342 : Nat := 118140960795 + 108342 * 2 ^ 59
def prefixEnd_108342 : Nat := 4983230072969 + 3 ^ 40 * 108342 * 2
def baseEnd_108342 : Nat := 8241706825114125203963

theorem tailTrace_108342 : CollatzResearch.WordTrace tailWord_108342 prefixEnd_108342 8241706825114125203963 := by
  unfold tailWord_108342
  simp only [CollatzResearch.WordTrace]
  refine ⟨246972335843932011598955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2634371582335274790388853 246972335843932011598955)
  ·
    refine ⟨370458503765898017398433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 246972335843932011598955 370458503765898017398433)
    ·
      refine ⟨277843877824423513048825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370458503765898017398433 277843877824423513048825)
      ·
        refine ⟨208382908368317634786619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277843877824423513048825 208382908368317634786619)
        ·
          refine ⟨312574362552476452179929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208382908368317634786619 312574362552476452179929)
          ·
            refine ⟨234430771914357339134947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312574362552476452179929 234430771914357339134947)
            ·
              refine ⟨351646157871536008702421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234430771914357339134947 351646157871536008702421)
              ·
                refine ⟨8241706825114125203963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 351646157871536008702421 8241706825114125203963)
                ·
                  rfl

theorem cell21_108342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_108342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108342 prefixEnd_108342 := by exact prefixLift 108342
  have htrace : WordTrace (prefixWord ++ tailWord_108342) baseStart_108342 baseEnd_108342 := by
    simpa [prefixWord, tailWord_108342, baseEnd_108342] using wordTrace_append hprefix tailTrace_108342
  have hstable : (prefixWord ++ tailWord_108342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108342).length < 2 ^ (prefixWord ++ tailWord_108342).sum := by decide
  have hdescent : baseEnd_108342 < baseStart_108342 := by decide
  rcases family_descends (prefixWord ++ tailWord_108342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108370 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 6]
def baseStart_108370 : Nat := 118140960795 + 108370 * 2 ^ 59
def prefixEnd_108370 : Nat := 4983230072969 + 3 ^ 40 * 108370 * 2
def baseEnd_108370 : Nat := 24731510456820549145165

theorem tailTrace_108370 : CollatzResearch.WordTrace tailWord_108370 prefixEnd_108370 24731510456820549145165 := by
  unfold tailWord_108370
  simp only [CollatzResearch.WordTrace]
  refine ⟨988144654350368241900641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2635052411600981978401709 988144654350368241900641)
  ·
    refine ⟨741108490762776181425481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 988144654350368241900641 741108490762776181425481)
    ·
      refine ⟨555831368072082136069111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 741108490762776181425481 555831368072082136069111)
      ·
        refine ⟨833747052108123204103667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555831368072082136069111 833747052108123204103667)
        ·
          refine ⟨1250620578162184806155501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833747052108123204103667 1250620578162184806155501)
          ·
            refine ⟨468982716810819302308313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250620578162184806155501 468982716810819302308313)
            ·
              refine ⟨351737037608114476731235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468982716810819302308313 351737037608114476731235)
              ·
                refine ⟨527605556412171715096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351737037608114476731235 527605556412171715096853)
                ·
                  refine ⟨24731510456820549145165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527605556412171715096853 24731510456820549145165)
                  ·
                    rfl

theorem cell21_108370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_108370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108370 prefixEnd_108370 := by exact prefixLift 108370
  have htrace : WordTrace (prefixWord ++ tailWord_108370) baseStart_108370 baseEnd_108370 := by
    simpa [prefixWord, tailWord_108370, baseEnd_108370] using wordTrace_append hprefix tailTrace_108370
  have hstable : (prefixWord ++ tailWord_108370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108370).length < 2 ^ (prefixWord ++ tailWord_108370).sum := by decide
  have hdescent : baseEnd_108370 < baseStart_108370 := by decide
  rcases family_descends (prefixWord ++ tailWord_108370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108384 : List Nat := [2, 1, 1, 3, 3, 2, 1, 8]
def baseStart_108384 : Nat := 118140960795 + 108384 * 2 ^ 59
def prefixEnd_108384 : Nat := 4983230072969 + 3 ^ 40 * 108384 * 2
def baseEnd_108384 : Nat := 8244901815853211970601

theorem tailTrace_108384 : CollatzResearch.WordTrace tailWord_108384 prefixEnd_108384 8244901815853211970601 := by
  unfold tailWord_108384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976544619675376679306103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2635392826233835572408137 1976544619675376679306103)
  ·
    refine ⟨2964816929513065018959155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976544619675376679306103 2964816929513065018959155)
    ·
      refine ⟨4447225394269597528438733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964816929513065018959155 4447225394269597528438733)
      ·
        refine ⟨1667709522851099073164525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4447225394269597528438733 1667709522851099073164525)
        ·
          refine ⟨625391071069162152436697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1667709522851099073164525 625391071069162152436697)
          ·
            refine ⟨469043303301871614327523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625391071069162152436697 469043303301871614327523)
            ·
              refine ⟨703564954952807421491285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469043303301871614327523 703564954952807421491285)
              ·
                refine ⟨8244901815853211970601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 703564954952807421491285 8244901815853211970601)
                ·
                  rfl

theorem cell21_108384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 8].length) (baseStart_108384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108384 prefixEnd_108384 := by exact prefixLift 108384
  have htrace : WordTrace (prefixWord ++ tailWord_108384) baseStart_108384 baseEnd_108384 := by
    simpa [prefixWord, tailWord_108384, baseEnd_108384] using wordTrace_append hprefix tailTrace_108384
  have hstable : (prefixWord ++ tailWord_108384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108384).length < 2 ^ (prefixWord ++ tailWord_108384).sum := by decide
  have hdescent : baseEnd_108384 < baseStart_108384 := by decide
  rcases family_descends (prefixWord ++ tailWord_108384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108387 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 4]
def baseStart_108387 : Nat := 118140960795 + 108387 * 2 ^ 59
def prefixEnd_108387 : Nat := 4983230072969 + 3 ^ 40 * 108387 * 2
def baseEnd_108387 : Nat := 24735390088432297361797

theorem tailTrace_108387 : CollatzResearch.WordTrace tailWord_108387 prefixEnd_108387 24735390088432297361797 := by
  unfold tailWord_108387
  simp only [CollatzResearch.WordTrace]
  refine ⟨3953198658339884870971415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2635465772226589913980943 3953198658339884870971415)
  ·
    refine ⟨5929797987509827306457123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3953198658339884870971415 5929797987509827306457123)
    ·
      refine ⟨8894696981264740959685685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929797987509827306457123 8894696981264740959685685)
      ·
        refine ⟨833877841993569464970533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8894696981264740959685685 833877841993569464970533)
        ·
          refine ⟨156352095373794274681975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 833877841993569464970533 156352095373794274681975)
          ·
            refine ⟨234528143060691412022963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156352095373794274681975 234528143060691412022963)
            ·
              refine ⟨351792214591037118034445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234528143060691412022963 351792214591037118034445)
              ·
                refine ⟨131922080471638919262917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351792214591037118034445 131922080471638919262917)
                ·
                  refine ⟨24735390088432297361797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131922080471638919262917 24735390088432297361797)
                  ·
                    rfl

theorem cell21_108387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 4].length) (baseStart_108387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108387 prefixEnd_108387 := by exact prefixLift 108387
  have htrace : WordTrace (prefixWord ++ tailWord_108387) baseStart_108387 baseEnd_108387 := by
    simpa [prefixWord, tailWord_108387, baseEnd_108387] using wordTrace_append hprefix tailTrace_108387
  have hstable : (prefixWord ++ tailWord_108387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108387).length < 2 ^ (prefixWord ++ tailWord_108387).sum := by decide
  have hdescent : baseEnd_108387 < baseStart_108387 := by decide
  rcases family_descends (prefixWord ++ tailWord_108387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108491 : List Nat := [1, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_108491 : Nat := 118140960795 + 108491 * 2 ^ 59
def prefixEnd_108491 : Nat := 4983230072969 + 3 ^ 40 * 108491 * 2
def baseEnd_108491 : Nat := 24759124305351227628251

theorem tailTrace_108491 : CollatzResearch.WordTrace tailWord_108491 prefixEnd_108491 24759124305351227628251 := by
  unfold tailWord_108491
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956991849963110632757327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2637994566642073755171551 3956991849963110632757327)
  ·
    refine ⟨5935487774944665949135991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956991849963110632757327 5935487774944665949135991)
    ·
      refine ⟨8903231662416998923703987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935487774944665949135991 8903231662416998923703987)
      ·
        refine ⟨13354847493625498385555981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903231662416998923703987 13354847493625498385555981)
        ·
          refine ⟨5008067810109561894583493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13354847493625498385555981 5008067810109561894583493)
          ·
            refine ⟨939012714395542855234405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5008067810109561894583493 939012714395542855234405)
            ·
              refine ⟨176064883949164285356451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 939012714395542855234405 176064883949164285356451)
              ·
                refine ⟨264097325923746428034677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176064883949164285356451 264097325923746428034677)
                ·
                  refine ⟨24759124305351227628251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 264097325923746428034677 24759124305351227628251)
                  ·
                    rfl

theorem cell21_108491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_108491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108491 prefixEnd_108491 := by exact prefixLift 108491
  have htrace : WordTrace (prefixWord ++ tailWord_108491) baseStart_108491 baseEnd_108491 := by
    simpa [prefixWord, tailWord_108491, baseEnd_108491] using wordTrace_append hprefix tailTrace_108491
  have hstable : (prefixWord ++ tailWord_108491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108491).length < 2 ^ (prefixWord ++ tailWord_108491).sum := by decide
  have hdescent : baseEnd_108491 < baseStart_108491 := by decide
  rcases family_descends (prefixWord ++ tailWord_108491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108601 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 3]
def baseStart_108601 : Nat := 118140960795 + 108601 * 2 ^ 59
def prefixEnd_108601 : Nat := 4983230072969 + 3 ^ 40 * 108601 * 2
def baseEnd_108601 : Nat := 24784227804015480794693

theorem tailTrace_108601 : CollatzResearch.WordTrace tailWord_108601 prefixEnd_108601 24784227804015480794693 := by
  unfold tailWord_108601
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961003879564599419261657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2640669253043066279507771 3961003879564599419261657)
  ·
    refine ⟨2970752909673449564446243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3961003879564599419261657 2970752909673449564446243)
    ·
      refine ⟨4456129364510174346669365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970752909673449564446243 4456129364510174346669365)
      ·
        refine ⟨417762127922828845000253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4456129364510174346669365 417762127922828845000253)
        ·
          refine ⟨156660797971060816875095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 417762127922828845000253 156660797971060816875095)
          ·
            refine ⟨234991196956591225312643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156660797971060816875095 234991196956591225312643)
            ·
              refine ⟨352486795434886837968965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234991196956591225312643 352486795434886837968965)
              ·
                refine ⟨66091274144041282119181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352486795434886837968965 66091274144041282119181)
                ·
                  refine ⟨24784227804015480794693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66091274144041282119181 24784227804015480794693)
                  ·
                    rfl

theorem cell21_108601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 3].length) (baseStart_108601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108601 prefixEnd_108601 := by exact prefixLift 108601
  have htrace : WordTrace (prefixWord ++ tailWord_108601) baseStart_108601 baseEnd_108601 := by
    simpa [prefixWord, tailWord_108601, baseEnd_108601] using wordTrace_append hprefix tailTrace_108601
  have hstable : (prefixWord ++ tailWord_108601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108601).length < 2 ^ (prefixWord ++ tailWord_108601).sum := by decide
  have hdescent : baseEnd_108601 < baseStart_108601 := by decide
  rcases family_descends (prefixWord ++ tailWord_108601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108629 : List Nat := [1, 3, 2, 2, 1, 4, 3, 5]
def baseStart_108629 : Nat := 118140960795 + 108629 * 2 ^ 59
def prefixEnd_108629 : Nat := 4983230072969 + 3 ^ 40 * 108629 * 2
def baseEnd_108629 : Nat := 8263539261831218109323

theorem tailTrace_108629 : CollatzResearch.WordTrace tailWord_108629 prefixEnd_108629 8263539261831218109323 := by
  unfold tailWord_108629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962025123463160201280941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2641350082308773467520627 3962025123463160201280941)
  ·
    refine ⟨1485759421298685075480353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3962025123463160201280941 1485759421298685075480353)
    ·
      refine ⟨1114319565974013806610265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1485759421298685075480353 1114319565974013806610265)
      ·
        refine ⟨835739674480510354957699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1114319565974013806610265 835739674480510354957699)
        ·
          refine ⟨1253609511720765532436549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835739674480510354957699 1253609511720765532436549)
          ·
            refine ⟨235051783447643537331853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1253609511720765532436549 235051783447643537331853)
            ·
              refine ⟨88144418792866326499445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235051783447643537331853 88144418792866326499445)
              ·
                refine ⟨8263539261831218109323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88144418792866326499445 8263539261831218109323)
                ·
                  rfl

theorem cell21_108629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 5].length) (baseStart_108629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108629 prefixEnd_108629 := by exact prefixLift 108629
  have htrace : WordTrace (prefixWord ++ tailWord_108629) baseStart_108629 baseEnd_108629 := by
    simpa [prefixWord, tailWord_108629, baseEnd_108629] using wordTrace_append hprefix tailTrace_108629
  have hstable : (prefixWord ++ tailWord_108629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108629).length < 2 ^ (prefixWord ++ tailWord_108629).sum := by decide
  have hdescent : baseEnd_108629 < baseStart_108629 := by decide
  rcases family_descends (prefixWord ++ tailWord_108629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108657 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 6]
def baseStart_108657 : Nat := 118140960795 + 108657 * 2 ^ 59
def prefixEnd_108657 : Nat := 4983230072969 + 3 ^ 40 * 108657 * 2
def baseEnd_108657 : Nat := 24797007766971827861245

theorem tailTrace_108657 : CollatzResearch.WordTrace tailWord_108657 prefixEnd_108657 24797007766971827861245 := by
  unfold tailWord_108657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3963046367361720983300225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2642030911574480655533483 3963046367361720983300225)
  ·
    refine ⟨2972284775521290737475169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3963046367361720983300225 2972284775521290737475169)
    ·
      refine ⟨2229213581640968053106377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972284775521290737475169 2229213581640968053106377)
      ·
        refine ⟨1671910186230726039829783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2229213581640968053106377 1671910186230726039829783)
        ·
          refine ⟨2507865279346089059744675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671910186230726039829783 2507865279346089059744675)
          ·
            refine ⟨3761797919019133589617013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507865279346089059744675 3761797919019133589617013)
            ·
              refine ⟨352668554908043774026595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3761797919019133589617013 352668554908043774026595)
              ·
                refine ⟨529002832362065661039893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352668554908043774026595 529002832362065661039893)
                ·
                  refine ⟨24797007766971827861245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 529002832362065661039893 24797007766971827861245)
                  ·
                    rfl

theorem cell21_108657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_108657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108657 prefixEnd_108657 := by exact prefixLift 108657
  have htrace : WordTrace (prefixWord ++ tailWord_108657) baseStart_108657 baseEnd_108657 := by
    simpa [prefixWord, tailWord_108657, baseEnd_108657] using wordTrace_append hprefix tailTrace_108657
  have hstable : (prefixWord ++ tailWord_108657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108657).length < 2 ^ (prefixWord ++ tailWord_108657).sum := by decide
  have hdescent : baseEnd_108657 < baseStart_108657 := by decide
  rcases family_descends (prefixWord ++ tailWord_108657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108725 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 4]
def baseStart_108725 : Nat := 118140960795 + 108725 * 2 ^ 59
def prefixEnd_108725 : Nat := 4983230072969 + 3 ^ 40 * 108725 * 2
def baseEnd_108725 : Nat := 24812526293418820727773

theorem tailTrace_108725 : CollatzResearch.WordTrace tailWord_108725 prefixEnd_108725 24812526293418820727773 := by
  unfold tailWord_108725
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965526531115368596775629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2643684354076912397850419 3965526531115368596775629)
  ·
    refine ⟨1487072449168263223790861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3965526531115368596775629 1487072449168263223790861)
    ·
      refine ⟨557652168438098708921573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1487072449168263223790861 557652168438098708921573)
      ·
        refine ⟨104559781582143507922795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 557652168438098708921573 104559781582143507922795)
        ·
          refine ⟨156839672373215261884193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104559781582143507922795 156839672373215261884193)
          ·
            refine ⟨117629754279911446413145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156839672373215261884193 117629754279911446413145)
            ·
              refine ⟨88222315709933584809859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117629754279911446413145 88222315709933584809859)
              ·
                refine ⟨132333473564900377214789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88222315709933584809859 132333473564900377214789)
                ·
                  refine ⟨24812526293418820727773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132333473564900377214789 24812526293418820727773)
                  ·
                    rfl

theorem cell21_108725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_108725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108725 prefixEnd_108725 := by exact prefixLift 108725
  have htrace : WordTrace (prefixWord ++ tailWord_108725) baseStart_108725 baseEnd_108725 := by
    simpa [prefixWord, tailWord_108725, baseEnd_108725] using wordTrace_append hprefix tailTrace_108725
  have hstable : (prefixWord ++ tailWord_108725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108725).length < 2 ^ (prefixWord ++ tailWord_108725).sum := by decide
  have hdescent : baseEnd_108725 < baseStart_108725 := by decide
  rcases family_descends (prefixWord ++ tailWord_108725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108747 : List Nat := [1, 1, 1, 1, 3, 2, 3, 9]
def baseStart_108747 : Nat := 118140960795 + 108747 * 2 ^ 59
def prefixEnd_108747 : Nat := 4983230072969 + 3 ^ 40 * 108747 * 2
def baseEnd_108747 : Nat := 8272515664383890453687

theorem tailTrace_108747 : CollatzResearch.WordTrace tailWord_108747 prefixEnd_108747 8272515664383890453687 := by
  unfold tailWord_108747
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966328937035666354076495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2644219291357110902717663 3966328937035666354076495)
  ·
    refine ⟨5949493405553499531114743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966328937035666354076495 5949493405553499531114743)
    ·
      refine ⟨8924240108330249296672115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5949493405553499531114743 8924240108330249296672115)
      ·
        refine ⟨13386360162495373945008173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924240108330249296672115 13386360162495373945008173)
        ·
          refine ⟨5019885060935765229378065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13386360162495373945008173 5019885060935765229378065)
          ·
            refine ⟨3764913795701823922033549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019885060935765229378065 3764913795701823922033549)
            ·
              refine ⟨1411842673388183970762581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3764913795701823922033549 1411842673388183970762581)
              ·
                refine ⟨8272515664383890453687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1411842673388183970762581 8272515664383890453687)
                ·
                  rfl

theorem cell21_108747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 9].length) (baseStart_108747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108747 prefixEnd_108747 := by exact prefixLift 108747
  have htrace : WordTrace (prefixWord ++ tailWord_108747) baseStart_108747 baseEnd_108747 := by
    simpa [prefixWord, tailWord_108747, baseEnd_108747] using wordTrace_append hprefix tailTrace_108747
  have hstable : (prefixWord ++ tailWord_108747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108747).length < 2 ^ (prefixWord ++ tailWord_108747).sum := by decide
  have hdescent : baseEnd_108747 < baseStart_108747 := by decide
  rcases family_descends (prefixWord ++ tailWord_108747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108812 : List Nat := [2, 2, 1, 2, 2, 2, 4, 3, 3]
def baseStart_108812 : Nat := 118140960795 + 108812 * 2 ^ 59
def prefixEnd_108812 : Nat := 4983230072969 + 3 ^ 40 * 108812 * 2
def baseEnd_108812 : Nat := 24832380878726002777595

theorem tailTrace_108812 : CollatzResearch.WordTrace tailWord_108812 prefixEnd_108812 24832380878726002777595 := by
  unfold tailWord_108812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1984349840900091227596345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2645799787866788303461793 1984349840900091227596345)
  ·
    refine ⟨1488262380675068420697259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1984349840900091227596345 1488262380675068420697259)
    ·
      refine ⟨2232393571012602631045889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488262380675068420697259 2232393571012602631045889)
      ·
        refine ⟨1674295178259451973284417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2232393571012602631045889 1674295178259451973284417)
        ·
          refine ⟨1255721383694588979963313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1674295178259451973284417 1255721383694588979963313)
          ·
            refine ⟨941791037770941734972485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1255721383694588979963313 941791037770941734972485)
            ·
              refine ⟨176585819582051575307341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 941791037770941734972485 176585819582051575307341)
              ·
                refine ⟨66219682343269340740253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176585819582051575307341 66219682343269340740253)
                ·
                  refine ⟨24832380878726002777595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66219682343269340740253 24832380878726002777595)
                  ·
                    rfl

theorem cell21_108812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 3, 3].length) (baseStart_108812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108812 prefixEnd_108812 := by exact prefixLift 108812
  have htrace : WordTrace (prefixWord ++ tailWord_108812) baseStart_108812 baseEnd_108812 := by
    simpa [prefixWord, tailWord_108812, baseEnd_108812] using wordTrace_append hprefix tailTrace_108812
  have hstable : (prefixWord ++ tailWord_108812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108812).length < 2 ^ (prefixWord ++ tailWord_108812).sum := by decide
  have hdescent : baseEnd_108812 < baseStart_108812 := by decide
  rcases family_descends (prefixWord ++ tailWord_108812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108826 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_108826 : Nat := 118140960795 + 108826 * 2 ^ 59
def prefixEnd_108826 : Nat := 4983230072969 + 3 ^ 40 * 108826 * 2
def baseEnd_108826 : Nat := 24835575869465089544233

theorem tailTrace_108826 : CollatzResearch.WordTrace tailWord_108826 prefixEnd_108826 24835575869465089544233 := by
  unfold tailWord_108826
  simp only [CollatzResearch.WordTrace]
  refine ⟨992302575937365711550583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2646140202499641897468221 992302575937365711550583)
  ·
    refine ⟨1488453863906048567325875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 992302575937365711550583 1488453863906048567325875)
    ·
      refine ⟨2232680795859072850988813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488453863906048567325875 2232680795859072850988813)
      ·
        refine ⟨837255298447152319120805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2232680795859072850988813 837255298447152319120805)
        ·
          refine ⟨156985368458841059835151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 837255298447152319120805 156985368458841059835151)
          ·
            refine ⟨235478052688261589752727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156985368458841059835151 235478052688261589752727)
            ·
              refine ⟨353217079032392384629091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235478052688261589752727 353217079032392384629091)
              ·
                refine ⟨529825618548588576943637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 353217079032392384629091 529825618548588576943637)
                ·
                  refine ⟨24835575869465089544233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 529825618548588576943637 24835575869465089544233)
                  ·
                    rfl

theorem cell21_108826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_108826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108826 prefixEnd_108826 := by exact prefixLift 108826
  have htrace : WordTrace (prefixWord ++ tailWord_108826) baseStart_108826 baseEnd_108826 := by
    simpa [prefixWord, tailWord_108826, baseEnd_108826] using wordTrace_append hprefix tailTrace_108826
  have hstable : (prefixWord ++ tailWord_108826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108826).length < 2 ^ (prefixWord ++ tailWord_108826).sum := by decide
  have hdescent : baseEnd_108826 < baseStart_108826 := by decide
  rcases family_descends (prefixWord ++ tailWord_108826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108857 : List Nat := [1, 2, 1, 6, 1, 1, 4, 5]
def baseStart_108857 : Nat := 118140960795 + 108857 * 2 ^ 59
def prefixEnd_108857 : Nat := 4983230072969 + 3 ^ 40 * 108857 * 2
def baseEnd_108857 : Nat := 8280883497271974842501

theorem tailTrace_108857 : CollatzResearch.WordTrace tailWord_108857 prefixEnd_108857 8280883497271974842501 := by
  unfold tailWord_108857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970340966637155140580825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2646893977758103427053883 3970340966637155140580825)
  ·
    refine ⟨2977755724977866355435619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3970340966637155140580825 2977755724977866355435619)
    ·
      refine ⟨4466633587466799533153429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2977755724977866355435619 4466633587466799533153429)
      ·
        refine ⟨209373449412506228116567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4466633587466799533153429 209373449412506228116567)
        ·
          refine ⟨314060174118759342174851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209373449412506228116567 314060174118759342174851)
          ·
            refine ⟨471090261178139013262277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314060174118759342174851 471090261178139013262277)
            ·
              refine ⟨88329423970901064986677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 471090261178139013262277 88329423970901064986677)
              ·
                refine ⟨8280883497271974842501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88329423970901064986677 8280883497271974842501)
                ·
                  rfl

theorem cell21_108857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 5].length) (baseStart_108857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108857 prefixEnd_108857 := by exact prefixLift 108857
  have htrace : WordTrace (prefixWord ++ tailWord_108857) baseStart_108857 baseEnd_108857 := by
    simpa [prefixWord, tailWord_108857, baseEnd_108857] using wordTrace_append hprefix tailTrace_108857
  have hstable : (prefixWord ++ tailWord_108857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108857).length < 2 ^ (prefixWord ++ tailWord_108857).sum := by decide
  have hdescent : baseEnd_108857 < baseStart_108857 := by decide
  rcases family_descends (prefixWord ++ tailWord_108857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108894 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_108894 : Nat := 118140960795 + 108894 * 2 ^ 59
def prefixEnd_108894 : Nat := 4983230072969 + 3 ^ 40 * 108894 * 2
def baseEnd_108894 : Nat := 24851094395912082410761

theorem tailTrace_108894 : CollatzResearch.WordTrace tailWord_108894 prefixEnd_108894 24851094395912082410761 := by
  unfold tailWord_108894
  simp only [CollatzResearch.WordTrace]
  refine ⟨496461308437888807459717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2647793645002073639785157 496461308437888807459717)
  ·
    refine ⟨93086495332104151398697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 496461308437888807459717 93086495332104151398697)
    ·
      refine ⟨69814871499078113549023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93086495332104151398697 69814871499078113549023)
      ·
        refine ⟨104722307248617170323535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69814871499078113549023 104722307248617170323535)
        ·
          refine ⟨157083460872925755485303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104722307248617170323535 157083460872925755485303)
          ·
            refine ⟨235625191309388633227955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157083460872925755485303 235625191309388633227955)
            ·
              refine ⟨353437786964082949841933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235625191309388633227955 353437786964082949841933)
              ·
                refine ⟨132539170111531106190725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353437786964082949841933 132539170111531106190725)
                ·
                  refine ⟨24851094395912082410761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132539170111531106190725 24851094395912082410761)
                  ·
                    rfl

theorem cell21_108894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_108894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108894 prefixEnd_108894 := by exact prefixLift 108894
  have htrace : WordTrace (prefixWord ++ tailWord_108894) baseStart_108894 baseEnd_108894 := by
    simpa [prefixWord, tailWord_108894, baseEnd_108894] using wordTrace_append hprefix tailTrace_108894
  have hstable : (prefixWord ++ tailWord_108894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108894).length < 2 ^ (prefixWord ++ tailWord_108894).sum := by decide
  have hdescent : baseEnd_108894 < baseStart_108894 := by decide
  rcases family_descends (prefixWord ++ tailWord_108894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_108981 : List Nat := [1, 3, 3, 2, 3, 1, 2, 3, 3]
def baseStart_108981 : Nat := 118140960795 + 108981 * 2 ^ 59
def prefixEnd_108981 : Nat := 4983230072969 + 3 ^ 40 * 108981 * 2
def baseEnd_108981 : Nat := 24870948981219264460583

theorem tailTrace_108981 : CollatzResearch.WordTrace tailWord_108981 prefixEnd_108981 24870948981219264460583 := by
  unfold tailWord_108981
  simp only [CollatzResearch.WordTrace]
  refine ⟨3974863618187924318094797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2649909078791949545396531 3974863618187924318094797)
  ·
    refine ⟨1490573856820471619285549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3974863618187924318094797 1490573856820471619285549)
    ·
      refine ⟨558965196307676857232081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1490573856820471619285549 558965196307676857232081)
      ·
        refine ⟨419223897230757642924061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 558965196307676857232081 419223897230757642924061)
        ·
          refine ⟨157208961461534116096523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419223897230757642924061 157208961461534116096523)
          ·
            refine ⟨235813442192301174144785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157208961461534116096523 235813442192301174144785)
            ·
              refine ⟨176860081644225880608589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235813442192301174144785 176860081644225880608589)
              ·
                refine ⟨66322530616584705228221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176860081644225880608589 66322530616584705228221)
                ·
                  refine ⟨24870948981219264460583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66322530616584705228221 24870948981219264460583)
                  ·
                    rfl

theorem cell21_108981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_108981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_108981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_108981 prefixEnd_108981 := by exact prefixLift 108981
  have htrace : WordTrace (prefixWord ++ tailWord_108981) baseStart_108981 baseEnd_108981 := by
    simpa [prefixWord, tailWord_108981, baseEnd_108981] using wordTrace_append hprefix tailTrace_108981
  have hstable : (prefixWord ++ tailWord_108981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_108981).length < 2 ^ (prefixWord ++ tailWord_108981).sum := by decide
  have hdescent : baseEnd_108981 < baseStart_108981 := by decide
  rcases family_descends (prefixWord ++ tailWord_108981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109026 : List Nat := [3, 3, 3, 2, 1, 1, 1, 7]
def baseStart_109026 : Nat := 118140960795 + 109026 * 2 ^ 59
def prefixEnd_109026 : Nat := 4983230072969 + 3 ^ 40 * 109026 * 2
def baseEnd_109026 : Nat := 8293739531436395403497

theorem tailTrace_109026 : CollatzResearch.WordTrace tailWord_109026 prefixEnd_109026 8293739531436395403497 := by
  unfold tailWord_109026
  simp only [CollatzResearch.WordTrace]
  refine ⟨994126225756224250870733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2651003268683264668988621 994126225756224250870733)
  ·
    refine ⟨372797334658584094076525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 994126225756224250870733 372797334658584094076525)
    ·
      refine ⟨139799000496969035278697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372797334658584094076525 139799000496969035278697)
      ·
        refine ⟨104849250372726776459023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139799000496969035278697 104849250372726776459023)
        ·
          refine ⟨157273875559090164688535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104849250372726776459023 157273875559090164688535)
          ·
            refine ⟨235910813338635247032803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157273875559090164688535 235910813338635247032803)
            ·
              refine ⟨353866220007952870549205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235910813338635247032803 353866220007952870549205)
              ·
                refine ⟨8293739531436395403497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 353866220007952870549205 8293739531436395403497)
                ·
                  rfl

theorem cell21_109026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_109026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109026 prefixEnd_109026 := by exact prefixLift 109026
  have htrace : WordTrace (prefixWord ++ tailWord_109026) baseStart_109026 baseEnd_109026 := by
    simpa [prefixWord, tailWord_109026, baseEnd_109026] using wordTrace_append hprefix tailTrace_109026
  have hstable : (prefixWord ++ tailWord_109026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109026).length < 2 ^ (prefixWord ++ tailWord_109026).sum := by decide
  have hdescent : baseEnd_109026 < baseStart_109026 := by decide
  rcases family_descends (prefixWord ++ tailWord_109026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109057 : List Nat := [1, 2, 4, 1, 3, 2, 3, 2, 3]
def baseStart_109057 : Nat := 118140960795 + 109057 * 2 ^ 59
def prefixEnd_109057 : Nat := 4983230072969 + 3 ^ 40 * 109057 * 2
def baseEnd_109057 : Nat := 24888293216660021193761

theorem tailTrace_109057 : CollatzResearch.WordTrace tailWord_109057 prefixEnd_109057 24888293216660021193761 := by
  unfold tailWord_109057
  simp only [CollatzResearch.WordTrace]
  refine ⟨3977635565912589297861425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2651757043941726198574283 3977635565912589297861425)
  ·
    refine ⟨2983226674434441973396069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3977635565912589297861425 2983226674434441973396069)
    ·
      refine ⟨559355001456457870011763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2983226674434441973396069 559355001456457870011763)
      ·
        refine ⟨839032502184686805017645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559355001456457870011763 839032502184686805017645)
        ·
          refine ⟨314637188319257551881617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839032502184686805017645 314637188319257551881617)
          ·
            refine ⟨235977891239443163911213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314637188319257551881617 235977891239443163911213)
            ·
              refine ⟨88491709214791186466705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 235977891239443163911213 88491709214791186466705)
              ·
                refine ⟨66368781911093389850029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88491709214791186466705 66368781911093389850029)
                ·
                  refine ⟨24888293216660021193761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66368781911093389850029 24888293216660021193761)
                  ·
                    rfl

theorem cell21_109057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 2, 3].length) (baseStart_109057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109057 prefixEnd_109057 := by exact prefixLift 109057
  have htrace : WordTrace (prefixWord ++ tailWord_109057) baseStart_109057 baseEnd_109057 := by
    simpa [prefixWord, tailWord_109057, baseEnd_109057] using wordTrace_append hprefix tailTrace_109057
  have hstable : (prefixWord ++ tailWord_109057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109057).length < 2 ^ (prefixWord ++ tailWord_109057).sum := by decide
  have hdescent : baseEnd_109057 < baseStart_109057 := by decide
  rcases family_descends (prefixWord ++ tailWord_109057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109068 : List Nat := [2, 2, 1, 2, 4, 2, 2, 6]
def baseStart_109068 : Nat := 118140960795 + 109068 * 2 ^ 59
def prefixEnd_109068 : Nat := 4983230072969 + 3 ^ 40 * 109068 * 2
def baseEnd_109068 : Nat := 8296934522175482170135

theorem tailTrace_109068 : CollatzResearch.WordTrace tailWord_109068 prefixEnd_109068 8296934522175482170135 := by
  unfold tailWord_109068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989018384436369088255929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2652024512581825451007905 1989018384436369088255929)
  ·
    refine ⟨1491763788327276816191947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989018384436369088255929 1491763788327276816191947)
    ·
      refine ⟨2237645682490915224287921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491763788327276816191947 2237645682490915224287921)
      ·
        refine ⟨1678234261868186418215941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2237645682490915224287921 1678234261868186418215941)
        ·
          refine ⟨314668924100284953415489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1678234261868186418215941 314668924100284953415489)
          ·
            refine ⟨236001693075213715061617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314668924100284953415489 236001693075213715061617)
            ·
              refine ⟨177001269806410286296213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236001693075213715061617 177001269806410286296213)
              ·
                refine ⟨8296934522175482170135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177001269806410286296213 8296934522175482170135)
                ·
                  rfl

theorem cell21_109068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_109068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109068 prefixEnd_109068 := by exact prefixLift 109068
  have htrace : WordTrace (prefixWord ++ tailWord_109068) baseStart_109068 baseEnd_109068 := by
    simpa [prefixWord, tailWord_109068, baseEnd_109068] using wordTrace_append hprefix tailTrace_109068
  have hstable : (prefixWord ++ tailWord_109068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109068).length < 2 ^ (prefixWord ++ tailWord_109068).sum := by decide
  have hdescent : baseEnd_109068 < baseStart_109068 := by decide
  rcases family_descends (prefixWord ++ tailWord_109068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109082 : List Nat := [3, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_109082 : Nat := 118140960795 + 109082 * 2 ^ 59
def prefixEnd_109082 : Nat := 4983230072969 + 3 ^ 40 * 109082 * 2
def baseEnd_109082 : Nat := 24893998557265533277043

theorem tailTrace_109082 : CollatzResearch.WordTrace tailWord_109082 prefixEnd_109082 24893998557265533277043 := by
  unfold tailWord_109082
  simp only [CollatzResearch.WordTrace]
  refine ⟨994636847705504641880375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2652364927214679045014333 994636847705504641880375)
  ·
    refine ⟨1491955271558256962820563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 994636847705504641880375 1491955271558256962820563)
    ·
      refine ⟨2237932907337385444230845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491955271558256962820563 2237932907337385444230845)
      ·
        refine ⟨839224840251519541586567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2237932907337385444230845 839224840251519541586567)
        ·
          refine ⟨1258837260377279312379851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 839224840251519541586567 1258837260377279312379851)
          ·
            refine ⟨1888255890565918968569777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258837260377279312379851 1888255890565918968569777)
            ·
              refine ⟨1416191917924439226427333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1888255890565918968569777 1416191917924439226427333)
              ·
                refine ⟨265535984610832354955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1416191917924439226427333 265535984610832354955125)
                ·
                  refine ⟨24893998557265533277043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265535984610832354955125 24893998557265533277043)
                  ·
                    rfl

theorem cell21_109082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_109082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109082 prefixEnd_109082 := by exact prefixLift 109082
  have htrace : WordTrace (prefixWord ++ tailWord_109082) baseStart_109082 baseEnd_109082 := by
    simpa [prefixWord, tailWord_109082, baseEnd_109082] using wordTrace_append hprefix tailTrace_109082
  have hstable : (prefixWord ++ tailWord_109082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109082).length < 2 ^ (prefixWord ++ tailWord_109082).sum := by decide
  have hdescent : baseEnd_109082 < baseStart_109082 := by decide
  rcases family_descends (prefixWord ++ tailWord_109082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109108 : List Nat := [2, 5, 1, 3, 2, 1, 2, 2, 3]
def baseStart_109108 : Nat := 118140960795 + 109108 * 2 ^ 59
def prefixEnd_109108 : Nat := 4983230072969 + 3 ^ 40 * 109108 * 2
def baseEnd_109108 : Nat := 24899932111495265843657

theorem tailTrace_109108 : CollatzResearch.WordTrace tailWord_109108 prefixEnd_109108 24899932111495265843657 := by
  unfold tailWord_109108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989747844363912503983989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2652997125818550005311985 1989747844363912503983989)
  ·
    refine ⟨186538860409116797248499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1989747844363912503983989 186538860409116797248499)
    ·
      refine ⟨279808290613675195872749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186538860409116797248499 279808290613675195872749)
      ·
        refine ⟨104928108980128198452281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279808290613675195872749 104928108980128198452281)
        ·
          refine ⟨78696081735096148839211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104928108980128198452281 78696081735096148839211)
          ·
            refine ⟨118044122602644223258817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78696081735096148839211 118044122602644223258817)
            ·
              refine ⟨88533091951983167444113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118044122602644223258817 88533091951983167444113)
              ·
                refine ⟨66399818963987375583085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88533091951983167444113 66399818963987375583085)
                ·
                  refine ⟨24899932111495265843657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66399818963987375583085 24899932111495265843657)
                  ·
                    rfl

theorem cell21_109108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_109108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109108 prefixEnd_109108 := by exact prefixLift 109108
  have htrace : WordTrace (prefixWord ++ tailWord_109108) baseStart_109108 baseEnd_109108 := by
    simpa [prefixWord, tailWord_109108, baseEnd_109108] using wordTrace_append hprefix tailTrace_109108
  have hstable : (prefixWord ++ tailWord_109108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109108).length < 2 ^ (prefixWord ++ tailWord_109108).sum := by decide
  have hdescent : baseEnd_109108 < baseStart_109108 := by decide
  rcases family_descends (prefixWord ++ tailWord_109108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109116 : List Nat := [2, 2, 2, 2, 3, 2, 1, 4, 3]
def baseStart_109116 : Nat := 118140960795 + 109116 * 2 ^ 59
def prefixEnd_109116 : Nat := 4983230072969 + 3 ^ 40 * 109116 * 2
def baseEnd_109116 : Nat := 24901757820489029710307

theorem tailTrace_109116 : CollatzResearch.WordTrace tailWord_109116 prefixEnd_109116 24901757820489029710307 := by
  unfold tailWord_109116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989893736349421187129601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2653191648465894916172801 1989893736349421187129601)
  ·
    refine ⟨1492420302262065890347201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1989893736349421187129601 1492420302262065890347201)
    ·
      refine ⟨1119315226696549417760401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492420302262065890347201 1119315226696549417760401)
      ·
        refine ⟨839486420022412063320301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1119315226696549417760401 839486420022412063320301)
        ·
          refine ⟨314807407508404523745113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839486420022412063320301 314807407508404523745113)
          ·
            refine ⟨236105555631303392808835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314807407508404523745113 236105555631303392808835)
            ·
              refine ⟨354158333446955089213253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236105555631303392808835 354158333446955089213253)
              ·
                refine ⟨66404687521304079227485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354158333446955089213253 66404687521304079227485)
                ·
                  refine ⟨24901757820489029710307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66404687521304079227485 24901757820489029710307)
                  ·
                    rfl

theorem cell21_109116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 3].length) (baseStart_109116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109116 prefixEnd_109116 := by exact prefixLift 109116
  have htrace : WordTrace (prefixWord ++ tailWord_109116) baseStart_109116 baseEnd_109116 := by
    simpa [prefixWord, tailWord_109116, baseEnd_109116] using wordTrace_append hprefix tailTrace_109116
  have hstable : (prefixWord ++ tailWord_109116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109116).length < 2 ^ (prefixWord ++ tailWord_109116).sum := by decide
  have hdescent : baseEnd_109116 < baseStart_109116 := by decide
  rcases family_descends (prefixWord ++ tailWord_109116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109175 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 3]
def baseStart_109175 : Nat := 118140960795 + 109175 * 2 ^ 59
def prefixEnd_109175 : Nat := 4983230072969 + 3 ^ 40 * 109175 * 2
def baseEnd_109175 : Nat := 24915222424318038226853

theorem tailTrace_109175 : CollatzResearch.WordTrace tailWord_109175 prefixEnd_109175 24915222424318038226853 := by
  unfold tailWord_109175
  simp only [CollatzResearch.WordTrace]
  refine ⟨3981939379485095450656979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2654626252990063633771319 3981939379485095450656979)
  ·
    refine ⟨5972909069227643175985469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3981939379485095450656979 5972909069227643175985469)
    ·
      refine ⟨2239840900960366190994551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5972909069227643175985469 2239840900960366190994551)
      ·
        refine ⟨3359761351440549286491827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239840900960366190994551 3359761351440549286491827)
        ·
          refine ⟨5039642027160823929737741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3359761351440549286491827 5039642027160823929737741)
          ·
            refine ⟨1889865760185308973651653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5039642027160823929737741 1889865760185308973651653)
            ·
              refine ⟨354349830034745432559685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1889865760185308973651653 354349830034745432559685)
              ·
                refine ⟨66440593131514768604941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354349830034745432559685 66440593131514768604941)
                ·
                  refine ⟨24915222424318038226853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66440593131514768604941 24915222424318038226853)
                  ·
                    rfl

theorem cell21_109175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 3].length) (baseStart_109175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109175 prefixEnd_109175 := by exact prefixLift 109175
  have htrace : WordTrace (prefixWord ++ tailWord_109175) baseStart_109175 baseEnd_109175 := by
    simpa [prefixWord, tailWord_109175, baseEnd_109175] using wordTrace_append hprefix tailTrace_109175
  have hstable : (prefixWord ++ tailWord_109175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109175).length < 2 ^ (prefixWord ++ tailWord_109175).sum := by decide
  have hdescent : baseEnd_109175 < baseStart_109175 := by decide
  rcases family_descends (prefixWord ++ tailWord_109175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109226 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_109226 : Nat := 118140960795 + 109226 * 2 ^ 59
def prefixEnd_109226 : Nat := 4983230072969 + 3 ^ 40 * 109226 * 2
def baseEnd_109226 : Nat := 24926861319153282876749

theorem tailTrace_109226 : CollatzResearch.WordTrace tailWord_109226 prefixEnd_109226 24926861319153282876749 := by
  unfold tailWord_109226
  simp only [CollatzResearch.WordTrace]
  refine ⟨995949875575082790190883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2655866334866887440509021 995949875575082790190883)
  ·
    refine ⟨1493924813362624185286325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995949875575082790190883 1493924813362624185286325)
    ·
      refine ⟨140055451252746017370593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1493924813362624185286325 140055451252746017370593)
      ·
        refine ⟨105041588439559513027945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140055451252746017370593 105041588439559513027945)
        ·
          refine ⟨78781191329669634770959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105041588439559513027945 78781191329669634770959)
          ·
            refine ⟨118171786994504452156439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78781191329669634770959 118171786994504452156439)
            ·
              refine ⟨177257680491756678234659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118171786994504452156439 177257680491756678234659)
              ·
                refine ⟨265886520737635017351989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177257680491756678234659 265886520737635017351989)
                ·
                  refine ⟨24926861319153282876749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 265886520737635017351989 24926861319153282876749)
                  ·
                    rfl

theorem cell21_109226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_109226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109226 prefixEnd_109226 := by exact prefixLift 109226
  have htrace : WordTrace (prefixWord ++ tailWord_109226) baseStart_109226 baseEnd_109226 := by
    simpa [prefixWord, tailWord_109226, baseEnd_109226] using wordTrace_append hprefix tailTrace_109226
  have hstable : (prefixWord ++ tailWord_109226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109226).length < 2 ^ (prefixWord ++ tailWord_109226).sum := by decide
  have hdescent : baseEnd_109226 < baseStart_109226 := by decide
  rcases family_descends (prefixWord ++ tailWord_109226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109285 : List Nat := [1, 3, 1, 4, 1, 4, 2, 2, 3]
def baseStart_109285 : Nat := 118140960795 + 109285 * 2 ^ 59
def prefixEnd_109285 : Nat := 4983230072969 + 3 ^ 40 * 109285 * 2
def baseEnd_109285 : Nat := 24940325922982291393295

theorem tailTrace_109285 : CollatzResearch.WordTrace tailWord_109285 prefixEnd_109285 24940325922982291393295 := by
  unfold tailWord_109285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3985951409086584237161309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2657300939391056158107539 3985951409086584237161309)
  ·
    refine ⟨1494731778407469088935491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3985951409086584237161309 1494731778407469088935491)
    ·
      refine ⟨2242097667611203633403237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1494731778407469088935491 2242097667611203633403237)
      ·
        refine ⟨420393312677100681263107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2242097667611203633403237 420393312677100681263107)
        ·
          refine ⟨630589969015651021894661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420393312677100681263107 630589969015651021894661)
          ·
            refine ⟨118235619190434566605249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 630589969015651021894661 118235619190434566605249)
            ·
              refine ⟨88676714392825924953937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118235619190434566605249 88676714392825924953937)
              ·
                refine ⟨66507535794619443715453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88676714392825924953937 66507535794619443715453)
                ·
                  refine ⟨24940325922982291393295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66507535794619443715453 24940325922982291393295)
                  ·
                    rfl

theorem cell21_109285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 2, 3].length) (baseStart_109285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109285 prefixEnd_109285 := by exact prefixLift 109285
  have htrace : WordTrace (prefixWord ++ tailWord_109285) baseStart_109285 baseEnd_109285 := by
    simpa [prefixWord, tailWord_109285, baseEnd_109285] using wordTrace_append hprefix tailTrace_109285
  have hstable : (prefixWord ++ tailWord_109285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109285).length < 2 ^ (prefixWord ++ tailWord_109285).sum := by decide
  have hdescent : baseEnd_109285 < baseStart_109285 := by decide
  rcases family_descends (prefixWord ++ tailWord_109285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109324 : List Nat := [2, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_109324 : Nat := 118140960795 + 109324 * 2 ^ 59
def prefixEnd_109324 : Nat := 4983230072969 + 3 ^ 40 * 109324 * 2
def baseEnd_109324 : Nat := 24949226254326890243215

theorem tailTrace_109324 : CollatzResearch.WordTrace tailWord_109324 prefixEnd_109324 24949226254326890243215 := by
  unfold tailWord_109324
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993686927972646948915513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2658249237296862598554017 1993686927972646948915513)
  ·
    refine ⟨1495265195979485211686635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1993686927972646948915513 1495265195979485211686635)
    ·
      refine ⟨2242897793969227817529953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495265195979485211686635 2242897793969227817529953)
      ·
        refine ⟨1682173345476920863147465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2242897793969227817529953 1682173345476920863147465)
        ·
          refine ⟨1261630009107690647360599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682173345476920863147465 1261630009107690647360599)
          ·
            refine ⟨1892445013661535971040899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261630009107690647360599 1892445013661535971040899)
            ·
              refine ⟨2838667520492303956561349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1892445013661535971040899 2838667520492303956561349)
              ·
                refine ⟨532250160092306991855253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2838667520492303956561349 532250160092306991855253)
                ·
                  refine ⟨24949226254326890243215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532250160092306991855253 24949226254326890243215)
                  ·
                    rfl

theorem cell21_109324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_109324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109324 prefixEnd_109324 := by exact prefixLift 109324
  have htrace : WordTrace (prefixWord ++ tailWord_109324) baseStart_109324 baseEnd_109324 := by
    simpa [prefixWord, tailWord_109324, baseEnd_109324] using wordTrace_append hprefix tailTrace_109324
  have hstable : (prefixWord ++ tailWord_109324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109324).length < 2 ^ (prefixWord ++ tailWord_109324).sum := by decide
  have hdescent : baseEnd_109324 < baseStart_109324 := by decide
  rcases family_descends (prefixWord ++ tailWord_109324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109327 : List Nat := [1, 1, 2, 1, 1, 1, 8, 3, 3]
def baseStart_109327 : Nat := 118140960795 + 109327 * 2 ^ 59
def prefixEnd_109327 : Nat := 4983230072969 + 3 ^ 40 * 109327 * 2
def baseEnd_109327 : Nat := 24949910895199551693209

theorem tailTrace_109327 : CollatzResearch.WordTrace tailWord_109327 prefixEnd_109327 24949910895199551693209 := by
  unfold tailWord_109327
  simp only [CollatzResearch.WordTrace]
  refine ⟨3987483274934425410190235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2658322183289616940126823 3987483274934425410190235)
  ·
    refine ⟨5981224912401638115285353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3987483274934425410190235 5981224912401638115285353)
    ·
      refine ⟨4485918684301228586464015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5981224912401638115285353 4485918684301228586464015)
      ·
        refine ⟨6728878026451842879696023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4485918684301228586464015 6728878026451842879696023)
        ·
          refine ⟨10093317039677764319544035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6728878026451842879696023 10093317039677764319544035)
          ·
            refine ⟨15139975559516646479316053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10093317039677764319544035 15139975559516646479316053)
            ·
              refine ⟨177421588588085700929485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 15139975559516646479316053 177421588588085700929485)
              ·
                refine ⟨66533095720532137848557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177421588588085700929485 66533095720532137848557)
                ·
                  refine ⟨24949910895199551693209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66533095720532137848557 24949910895199551693209)
                  ·
                    rfl

theorem cell21_109327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 3, 3].length) (baseStart_109327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109327 prefixEnd_109327 := by exact prefixLift 109327
  have htrace : WordTrace (prefixWord ++ tailWord_109327) baseStart_109327 baseEnd_109327 := by
    simpa [prefixWord, tailWord_109327, baseEnd_109327] using wordTrace_append hprefix tailTrace_109327
  have hstable : (prefixWord ++ tailWord_109327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109327).length < 2 ^ (prefixWord ++ tailWord_109327).sum := by decide
  have hdescent : baseEnd_109327 < baseStart_109327 := by decide
  rcases family_descends (prefixWord ++ tailWord_109327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109389 : List Nat := [1, 6, 1, 2, 2, 2, 7]
def baseStart_109389 : Nat := 118140960795 + 109389 * 2 ^ 59
def prefixEnd_109389 : Nat := 4983230072969 + 3 ^ 40 * 109389 * 2
def baseEnd_109389 : Nat := 2773784459989024628861

theorem tailTrace_109389 : CollatzResearch.WordTrace tailWord_109389 prefixEnd_109389 2773784459989024628861 := by
  unfold tailWord_109389
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989744600709809998947221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2659829733806539999298147 3989744600709809998947221)
  ·
    refine ⟨187019278158272343700651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3989744600709809998947221 187019278158272343700651)
    ·
      refine ⟨280528917237408515550977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 187019278158272343700651 280528917237408515550977)
      ·
        refine ⟨210396687928056386663233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280528917237408515550977 210396687928056386663233)
        ·
          refine ⟨157797515946042289997425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210396687928056386663233 157797515946042289997425)
          ·
            refine ⟨118348136959531717498069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157797515946042289997425 118348136959531717498069)
            ·
              refine ⟨2773784459989024628861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118348136959531717498069 2773784459989024628861)
              ·
                rfl

theorem cell21_109389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 7].length) (baseStart_109389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109389 prefixEnd_109389 := by exact prefixLift 109389
  have htrace : WordTrace (prefixWord ++ tailWord_109389) baseStart_109389 baseEnd_109389 := by
    simpa [prefixWord, tailWord_109389, baseEnd_109389] using wordTrace_append hprefix tailTrace_109389
  have hstable : (prefixWord ++ tailWord_109389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109389).length < 2 ^ (prefixWord ++ tailWord_109389).sum := by decide
  have hdescent : baseEnd_109389 < baseStart_109389 := by decide
  rcases family_descends (prefixWord ++ tailWord_109389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109479 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 5]
def baseStart_109479 : Nat := 118140960795 + 109479 * 2 ^ 59
def prefixEnd_109479 : Nat := 4983230072969 + 3 ^ 40 * 109479 * 2
def baseEnd_109479 : Nat := 24984599366081065159565

theorem tailTrace_109479 : CollatzResearch.WordTrace tailWord_109479 prefixEnd_109479 24984599366081065159565 := by
  unfold tailWord_109479
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993027170383755369723491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2662018113589170246482327 3993027170383755369723491)
  ·
    refine ⟨5989540755575633054585237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3993027170383755369723491 5989540755575633054585237)
    ·
      refine ⟨280759722917607799433683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5989540755575633054585237 280759722917607799433683)
      ·
        refine ⟨421139584376411699150525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280759722917607799433683 421139584376411699150525)
        ·
          refine ⟨157927344141154387181447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 421139584376411699150525 157927344141154387181447)
          ·
            refine ⟨236891016211731580772171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157927344141154387181447 236891016211731580772171)
            ·
              refine ⟨355336524317597371158257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236891016211731580772171 355336524317597371158257)
              ·
                refine ⟨266502393238198028368693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355336524317597371158257 266502393238198028368693)
                ·
                  refine ⟨24984599366081065159565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266502393238198028368693 24984599366081065159565)
                  ·
                    rfl

theorem cell21_109479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_109479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109479 prefixEnd_109479 := by exact prefixLift 109479
  have htrace : WordTrace (prefixWord ++ tailWord_109479) baseStart_109479 baseEnd_109479 := by
    simpa [prefixWord, tailWord_109479, baseEnd_109479] using wordTrace_append hprefix tailTrace_109479
  have hstable : (prefixWord ++ tailWord_109479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109479).length < 2 ^ (prefixWord ++ tailWord_109479).sum := by decide
  have hdescent : baseEnd_109479 < baseStart_109479 := by decide
  rcases family_descends (prefixWord ++ tailWord_109479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109724 : List Nat := [2, 2, 3, 2, 1, 4, 1, 3, 3]
def baseStart_109724 : Nat := 118140960795 + 109724 * 2 ^ 59
def prefixEnd_109724 : Nat := 4983230072969 + 3 ^ 40 * 109724 * 2
def baseEnd_109724 : Nat := 25040511704015083575731

theorem tailTrace_109724 : CollatzResearch.WordTrace tailWord_109724 prefixEnd_109724 25040511704015083575731 := by
  unfold tailWord_109724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000981527248081106196113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2667975369664108141594817 2000981527248081106196113)
  ·
    refine ⟨1500736145436060829647085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000981527248081106196113 1500736145436060829647085)
    ·
      refine ⟨562776054538522811117657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1500736145436060829647085 562776054538522811117657)
      ·
        refine ⟨422082040903892108338243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 562776054538522811117657 422082040903892108338243)
        ·
          refine ⟨633123061355838162507365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422082040903892108338243 633123061355838162507365)
          ·
            refine ⟨118710574004219655470131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 633123061355838162507365 118710574004219655470131)
            ·
              refine ⟨178065861006329483205197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118710574004219655470131 178065861006329483205197)
              ·
                refine ⟨66774697877373556201949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178065861006329483205197 66774697877373556201949)
                ·
                  refine ⟨25040511704015083575731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66774697877373556201949 25040511704015083575731)
                  ·
                    rfl

theorem cell21_109724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_109724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109724 prefixEnd_109724 := by exact prefixLift 109724
  have htrace : WordTrace (prefixWord ++ tailWord_109724) baseStart_109724 baseEnd_109724 := by
    simpa [prefixWord, tailWord_109724, baseEnd_109724] using wordTrace_append hprefix tailTrace_109724
  have hstable : (prefixWord ++ tailWord_109724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109724).length < 2 ^ (prefixWord ++ tailWord_109724).sum := by decide
  have hdescent : baseEnd_109724 < baseStart_109724 := by decide
  rcases family_descends (prefixWord ++ tailWord_109724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109735 : List Nat := [1, 1, 6, 2, 1, 1, 9]
def baseStart_109735 : Nat := 118140960795 + 109735 * 2 ^ 59
def prefixEnd_109735 : Nat := 4983230072969 + 3 ^ 40 * 109735 * 2
def baseEnd_109735 : Nat := 2782558005986834321375

theorem tailTrace_109735 : CollatzResearch.WordTrace tailWord_109735 prefixEnd_109735 2782558005986834321375 := by
  unfold tailWord_109735
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002364257456311091042659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668242838304207394028439 4002364257456311091042659)
  ·
    refine ⟨6003546386184466636563989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002364257456311091042659 6003546386184466636563989)
    ·
      refine ⟨281416236852396873588937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6003546386184466636563989 281416236852396873588937)
      ·
        refine ⟨211062177639297655191703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281416236852396873588937 211062177639297655191703)
        ·
          refine ⟨316593266458946482787555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211062177639297655191703 316593266458946482787555)
          ·
            refine ⟨474889899688419724181333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316593266458946482787555 474889899688419724181333)
            ·
              refine ⟨2782558005986834321375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 474889899688419724181333 2782558005986834321375)
              ·
                rfl

theorem cell21_109735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_109735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109735 prefixEnd_109735 := by exact prefixLift 109735
  have htrace : WordTrace (prefixWord ++ tailWord_109735) baseStart_109735 baseEnd_109735 := by
    simpa [prefixWord, tailWord_109735, baseEnd_109735] using wordTrace_append hprefix tailTrace_109735
  have hstable : (prefixWord ++ tailWord_109735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109735).length < 2 ^ (prefixWord ++ tailWord_109735).sum := by decide
  have hdescent : baseEnd_109735 < baseStart_109735 := by decide
  rcases family_descends (prefixWord ++ tailWord_109735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109741 : List Nat := [1, 5, 2, 1, 3, 1, 3, 2, 3]
def baseStart_109741 : Nat := 118140960795 + 109741 * 2 ^ 59
def prefixEnd_109741 : Nat := 4983230072969 + 3 ^ 40 * 109741 * 2
def baseEnd_109741 : Nat := 25044391335626831792363

theorem tailTrace_109741 : CollatzResearch.WordTrace tailWord_109741 prefixEnd_109741 25044391335626831792363 := by
  unfold tailWord_109741
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002583095434574115761077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668388730289716077174051 4002583095434574115761077)
  ·
    refine ⟨375242165196991323352601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4002583095434574115761077 375242165196991323352601)
    ·
      refine ⟨281431623897743492514451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375242165196991323352601 281431623897743492514451)
      ·
        refine ⟨422147435846615238771677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281431623897743492514451 422147435846615238771677)
        ·
          refine ⟨158305288442480714539379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422147435846615238771677 158305288442480714539379)
          ·
            refine ⟨237457932663721071809069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158305288442480714539379 237457932663721071809069)
            ·
              refine ⟨89046724748895401928401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237457932663721071809069 89046724748895401928401)
              ·
                refine ⟨66785043561671551446301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89046724748895401928401 66785043561671551446301)
                ·
                  refine ⟨25044391335626831792363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66785043561671551446301 25044391335626831792363)
                  ·
                    rfl

theorem cell21_109741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_109741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109741 prefixEnd_109741 := by exact prefixLift 109741
  have htrace : WordTrace (prefixWord ++ tailWord_109741) baseStart_109741 baseEnd_109741 := by
    simpa [prefixWord, tailWord_109741, baseEnd_109741] using wordTrace_append hprefix tailTrace_109741
  have hstable : (prefixWord ++ tailWord_109741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109741).length < 2 ^ (prefixWord ++ tailWord_109741).sum := by decide
  have hdescent : baseEnd_109741 < baseStart_109741 := by decide
  rcases family_descends (prefixWord ++ tailWord_109741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109763 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_109763 : Nat := 118140960795 + 109763 * 2 ^ 59
def prefixEnd_109763 : Nat := 4983230072969 + 3 ^ 40 * 109763 * 2
def baseEnd_109763 : Nat := 25049412035359682425651

theorem tailTrace_109763 : CollatzResearch.WordTrace tailWord_109763 prefixEnd_109763 25049412035359682425651 := by
  unfold tailWord_109763
  simp only [CollatzResearch.WordTrace]
  refine ⟨4003385501354871873061943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2668923667569914582041295 4003385501354871873061943)
  ·
    refine ⟨6005078252032307809592915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4003385501354871873061943 6005078252032307809592915)
    ·
      refine ⟨9007617378048461714389373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6005078252032307809592915 9007617378048461714389373)
      ·
        refine ⟨3377856516768173142896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9007617378048461714389373 3377856516768173142896015)
        ·
          refine ⟨5066784775152259714344023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377856516768173142896015 5066784775152259714344023)
          ·
            refine ⟨7600177162728389571516035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066784775152259714344023 7600177162728389571516035)
            ·
              refine ⟨11400265744092584357274053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600177162728389571516035 11400265744092584357274053)
              ·
                refine ⟨2137549827017359566988885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11400265744092584357274053 2137549827017359566988885)
                ·
                  refine ⟨25049412035359682425651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2137549827017359566988885 25049412035359682425651)
                  ·
                    rfl

theorem cell21_109763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_109763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109763 prefixEnd_109763 := by exact prefixLift 109763
  have htrace : WordTrace (prefixWord ++ tailWord_109763) baseStart_109763 baseEnd_109763 := by
    simpa [prefixWord, tailWord_109763, baseEnd_109763] using wordTrace_append hprefix tailTrace_109763
  have hstable : (prefixWord ++ tailWord_109763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109763).length < 2 ^ (prefixWord ++ tailWord_109763).sum := by decide
  have hdescent : baseEnd_109763 < baseStart_109763 := by decide
  rcases family_descends (prefixWord ++ tailWord_109763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109811 : List Nat := [1, 1, 1, 2, 2, 7, 1, 6]
def baseStart_109811 : Nat := 118140960795 + 109811 * 2 ^ 59
def prefixEnd_109811 : Nat := 4983230072969 + 3 ^ 40 * 109811 * 2
def baseEnd_109811 : Nat := 8353455429774088541851

theorem tailTrace_109811 : CollatzResearch.WordTrace tailWord_109811 prefixEnd_109811 8353455429774088541851 := by
  unfold tailWord_109811
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005136205180976070809287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2670090803453984047206191 4005136205180976070809287)
  ·
    refine ⟨6007704307771464106213931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005136205180976070809287 6007704307771464106213931)
    ·
      refine ⟨9011556461657196159320897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007704307771464106213931 9011556461657196159320897)
      ·
        refine ⟨6758667346242897119490673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011556461657196159320897 6758667346242897119490673)
        ·
          refine ⟨5069000509682172839618005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6758667346242897119490673 5069000509682172839618005)
          ·
            refine ⟨118804699445675925928547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 5069000509682172839618005 118804699445675925928547)
            ·
              refine ⟨178207049168513888892821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118804699445675925928547 178207049168513888892821)
              ·
                refine ⟨8353455429774088541851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178207049168513888892821 8353455429774088541851)
                ·
                  rfl

theorem cell21_109811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_109811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109811 prefixEnd_109811 := by exact prefixLift 109811
  have htrace : WordTrace (prefixWord ++ tailWord_109811) baseStart_109811 baseEnd_109811 := by
    simpa [prefixWord, tailWord_109811, baseEnd_109811] using wordTrace_append hprefix tailTrace_109811
  have hstable : (prefixWord ++ tailWord_109811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109811).length < 2 ^ (prefixWord ++ tailWord_109811).sum := by decide
  have hdescent : baseEnd_109811 < baseStart_109811 := by decide
  rcases family_descends (prefixWord ++ tailWord_109811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109825 : List Nat := [1, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_109825 : Nat := 118140960795 + 109825 * 2 ^ 59
def prefixEnd_109825 : Nat := 4983230072969 + 3 ^ 40 * 109825 * 2
def baseEnd_109825 : Nat := 25063561280061352392191

theorem tailTrace_109825 : CollatzResearch.WordTrace tailWord_109825 prefixEnd_109825 25063561280061352392191 := by
  unfold tailWord_109825
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005646827130256461818929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2670431218086837641212619 4005646827130256461818929)
  ·
    refine ⟨3004235120347692346364197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4005646827130256461818929 3004235120347692346364197)
    ·
      refine ⟨563294085065192314943287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3004235120347692346364197 563294085065192314943287)
      ·
        refine ⟨844941127597788472414931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563294085065192314943287 844941127597788472414931)
        ·
          refine ⟨1267411691396682708622397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844941127597788472414931 1267411691396682708622397)
          ·
            refine ⟨475279384273756015733399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267411691396682708622397 475279384273756015733399)
            ·
              refine ⟨712919076410634023600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475279384273756015733399 712919076410634023600099)
              ·
                refine ⟨1069378614615951035400149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712919076410634023600099 1069378614615951035400149)
                ·
                  refine ⟨25063561280061352392191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1069378614615951035400149 25063561280061352392191)
                  ·
                    rfl

theorem cell21_109825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_109825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109825 prefixEnd_109825 := by exact prefixLift 109825
  have htrace : WordTrace (prefixWord ++ tailWord_109825) baseStart_109825 baseEnd_109825 := by
    simpa [prefixWord, tailWord_109825, baseEnd_109825] using wordTrace_append hprefix tailTrace_109825
  have hstable : (prefixWord ++ tailWord_109825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109825).length < 2 ^ (prefixWord ++ tailWord_109825).sum := by decide
  have hdescent : baseEnd_109825 < baseStart_109825 := by decide
  rcases family_descends (prefixWord ++ tailWord_109825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109828 : List Nat := [2, 3, 2, 2, 2, 2, 3, 5]
def baseStart_109828 : Nat := 118140960795 + 109828 * 2 ^ 59
def prefixEnd_109828 : Nat := 4983230072969 + 3 ^ 40 * 109828 * 2
def baseEnd_109828 : Nat := 8354748640311337947395

theorem tailTrace_109828 : CollatzResearch.WordTrace tailWord_109828 prefixEnd_109828 8354748640311337947395 := by
  unfold tailWord_109828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2002878123059693987089069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2670504164079591982785425 2002878123059693987089069)
  ·
    refine ⟨751079296147385245158401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2002878123059693987089069 751079296147385245158401)
    ·
      refine ⟨563309472110538933868801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 751079296147385245158401 563309472110538933868801)
      ·
        refine ⟨422482104082904200401601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563309472110538933868801 422482104082904200401601)
        ·
          refine ⟨316861578062178150301201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422482104082904200401601 316861578062178150301201)
          ·
            refine ⟨237646183546633612725901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316861578062178150301201 237646183546633612725901)
            ·
              refine ⟨89117318829987604772213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237646183546633612725901 89117318829987604772213)
              ·
                refine ⟨8354748640311337947395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89117318829987604772213 8354748640311337947395)
                ·
                  rfl

theorem cell21_109828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 5].length) (baseStart_109828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109828 prefixEnd_109828 := by exact prefixLift 109828
  have htrace : WordTrace (prefixWord ++ tailWord_109828) baseStart_109828 baseEnd_109828 := by
    simpa [prefixWord, tailWord_109828, baseEnd_109828] using wordTrace_append hprefix tailTrace_109828
  have hstable : (prefixWord ++ tailWord_109828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109828).length < 2 ^ (prefixWord ++ tailWord_109828).sum := by decide
  have hdescent : baseEnd_109828 < baseStart_109828 := by decide
  rcases family_descends (prefixWord ++ tailWord_109828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109887 : List Nat := [1, 1, 2, 2, 4, 2, 4, 5]
def baseStart_109887 : Nat := 118140960795 + 109887 * 2 ^ 59
def prefixEnd_109887 : Nat := 4983230072969 + 3 ^ 40 * 109887 * 2
def baseEnd_109887 : Nat := 8359236841587674119577

theorem tailTrace_109887 : CollatzResearch.WordTrace tailWord_109887 prefixEnd_109887 8359236841587674119577 := by
  unfold tailWord_109887
  simp only [CollatzResearch.WordTrace]
  refine ⟨4007908152905641050575915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2671938768603760700383943 4007908152905641050575915)
  ·
    refine ⟨6011862229358461575863873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4007908152905641050575915 6011862229358461575863873)
    ·
      refine ⟨4508896672018846181897905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6011862229358461575863873 4508896672018846181897905)
      ·
        refine ⟨3381672504014134636423429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4508896672018846181897905 3381672504014134636423429)
        ·
          refine ⟨634063594502650244329393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3381672504014134636423429 634063594502650244329393)
          ·
            refine ⟨475547695876987683247045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634063594502650244329393 475547695876987683247045)
            ·
              refine ⟨89165192976935190608821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 475547695876987683247045 89165192976935190608821)
              ·
                refine ⟨8359236841587674119577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89165192976935190608821 8359236841587674119577)
                ·
                  rfl

theorem cell21_109887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 5].length) (baseStart_109887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109887 prefixEnd_109887 := by exact prefixLift 109887
  have htrace : WordTrace (prefixWord ++ tailWord_109887) baseStart_109887 baseEnd_109887 := by
    simpa [prefixWord, tailWord_109887, baseEnd_109887] using wordTrace_append hprefix tailTrace_109887
  have hstable : (prefixWord ++ tailWord_109887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109887).length < 2 ^ (prefixWord ++ tailWord_109887).sum := by decide
  have hdescent : baseEnd_109887 < baseStart_109887 := by decide
  rcases family_descends (prefixWord ++ tailWord_109887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109910 : List Nat := [5, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_109910 : Nat := 118140960795 + 109910 * 2 ^ 59
def prefixEnd_109910 : Nat := 4983230072969 + 3 ^ 40 * 109910 * 2
def baseEnd_109910 : Nat := 25082959438120093475351

theorem tailTrace_109910 : CollatzResearch.WordTrace tailWord_109910 prefixEnd_109910 25082959438120093475351 := by
  unfold tailWord_109910
  simp only [CollatzResearch.WordTrace]
  refine ⟨250546689488894748666449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2672498021214877319108789 250546689488894748666449)
  ·
    refine ⟨187910017116671061499837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250546689488894748666449 187910017116671061499837)
    ·
      refine ⟨70466256418751648062439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 187910017116671061499837 70466256418751648062439)
      ·
        refine ⟨105699384628127472093659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70466256418751648062439 105699384628127472093659)
        ·
          refine ⟨158549076942191208140489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105699384628127472093659 158549076942191208140489)
          ·
            refine ⟨118911807706643406105367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158549076942191208140489 118911807706643406105367)
            ·
              refine ⟨178367711559965109158051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118911807706643406105367 178367711559965109158051)
              ·
                refine ⟨267551567339947663737077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178367711559965109158051 267551567339947663737077)
                ·
                  refine ⟨25082959438120093475351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 267551567339947663737077 25082959438120093475351)
                  ·
                    rfl

theorem cell21_109910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_109910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109910 prefixEnd_109910 := by exact prefixLift 109910
  have htrace : WordTrace (prefixWord ++ tailWord_109910) baseStart_109910 baseEnd_109910 := by
    simpa [prefixWord, tailWord_109910, baseEnd_109910] using wordTrace_append hprefix tailTrace_109910
  have hstable : (prefixWord ++ tailWord_109910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109910).length < 2 ^ (prefixWord ++ tailWord_109910).sum := by decide
  have hdescent : baseEnd_109910 < baseStart_109910 := by decide
  rcases family_descends (prefixWord ++ tailWord_109910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_109966 : List Nat := [4, 1, 1, 4, 2, 1, 2, 2, 4]
def baseStart_109966 : Nat := 118140960795 + 109966 * 2 ^ 59
def prefixEnd_109966 : Nat := 4983230072969 + 3 ^ 40 * 109966 * 2
def baseEnd_109966 : Nat := 25095739401076440541903

theorem tailTrace_109966 : CollatzResearch.WordTrace tailWord_109966 prefixEnd_109966 25095739401076440541903 := by
  unfold tailWord_109966
  simp only [CollatzResearch.WordTrace]
  refine ⟨501348689952429692837719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2673859679746291695134501 501348689952429692837719)
  ·
    refine ⟨752023034928644539256579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 501348689952429692837719 752023034928644539256579)
    ·
      refine ⟨1128034552392966808884869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752023034928644539256579 1128034552392966808884869)
      ·
        refine ⟨211506478573681276665913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1128034552392966808884869 211506478573681276665913)
        ·
          refine ⟨158629858930260957499435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211506478573681276665913 158629858930260957499435)
          ·
            refine ⟨237944788395391436249153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158629858930260957499435 237944788395391436249153)
            ·
              refine ⟨178458591296543577186865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237944788395391436249153 178458591296543577186865)
              ·
                refine ⟨133843943472407682890149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178458591296543577186865 133843943472407682890149)
                ·
                  refine ⟨25095739401076440541903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133843943472407682890149 25095739401076440541903)
                  ·
                    rfl

theorem cell21_109966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_109966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_109966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_109966 prefixEnd_109966 := by exact prefixLift 109966
  have htrace : WordTrace (prefixWord ++ tailWord_109966) baseStart_109966 baseEnd_109966 := by
    simpa [prefixWord, tailWord_109966, baseEnd_109966] using wordTrace_append hprefix tailTrace_109966
  have hstable : (prefixWord ++ tailWord_109966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_109966).length < 2 ^ (prefixWord ++ tailWord_109966).sum := by decide
  have hdescent : baseEnd_109966 < baseStart_109966 := by decide
  rcases family_descends (prefixWord ++ tailWord_109966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110093 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 4]
def baseStart_110093 : Nat := 118140960795 + 110093 * 2 ^ 59
def prefixEnd_110093 : Nat := 4983230072969 + 3 ^ 40 * 110093 * 2
def baseEnd_110093 : Nat := 25124722531352441924977

theorem tailTrace_110093 : CollatzResearch.WordTrace tailWord_110093 prefixEnd_110093 25124722531352441924977 := by
  unfold tailWord_110093
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015421590159338232574933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2676947726772892155049955 4015421590159338232574933)
  ·
    refine ⟨94111443519359489825975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4015421590159338232574933 94111443519359489825975)
    ·
      refine ⟨141167165279039234738963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94111443519359489825975 141167165279039234738963)
      ·
        refine ⟨211750747918558852108445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141167165279039234738963 211750747918558852108445)
        ·
          refine ⟨79406530469459569540667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211750747918558852108445 79406530469459569540667)
          ·
            refine ⟨119109795704189354311001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79406530469459569540667 119109795704189354311001)
            ·
              refine ⟨89332346778142015733251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119109795704189354311001 89332346778142015733251)
              ·
                refine ⟨133998520167213023599877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89332346778142015733251 133998520167213023599877)
                ·
                  refine ⟨25124722531352441924977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133998520167213023599877 25124722531352441924977)
                  ·
                    rfl

theorem cell21_110093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_110093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110093 prefixEnd_110093 := by exact prefixLift 110093
  have htrace : WordTrace (prefixWord ++ tailWord_110093) baseStart_110093 baseEnd_110093 := by
    simpa [prefixWord, tailWord_110093, baseEnd_110093] using wordTrace_append hprefix tailTrace_110093
  have hstable : (prefixWord ++ tailWord_110093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110093).length < 2 ^ (prefixWord ++ tailWord_110093).sum := by decide
  have hdescent : baseEnd_110093 < baseStart_110093 := by decide
  rcases family_descends (prefixWord ++ tailWord_110093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110101 : List Nat := [1, 3, 2, 1, 3, 2, 4, 1, 4]
def baseStart_110101 : Nat := 118140960795 + 110101 * 2 ^ 59
def prefixEnd_110101 : Nat := 4983230072969 + 3 ^ 40 * 110101 * 2
def baseEnd_110101 : Nat := 25126548240346205791627

theorem tailTrace_110101 : CollatzResearch.WordTrace tailWord_110101 prefixEnd_110101 25126548240346205791627 := by
  unfold tailWord_110101
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015713374130355598866157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2677142249420237065910771 4015713374130355598866157)
  ·
    refine ⟨1505892515298883349574809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4015713374130355598866157 1505892515298883349574809)
    ·
      refine ⟨1129419386474162512181107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1505892515298883349574809 1129419386474162512181107)
      ·
        refine ⟨1694129079711243768271661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129419386474162512181107 1694129079711243768271661)
        ·
          refine ⟨635298404891716413101873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1694129079711243768271661 635298404891716413101873)
          ·
            refine ⟨476473803668787309826405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635298404891716413101873 476473803668787309826405)
            ·
              refine ⟨89338838187897620592451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476473803668787309826405 89338838187897620592451)
              ·
                refine ⟨134008257281846430888677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89338838187897620592451 134008257281846430888677)
                ·
                  refine ⟨25126548240346205791627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134008257281846430888677 25126548240346205791627)
                  ·
                    rfl

theorem cell21_110101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 1, 4].length) (baseStart_110101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110101 prefixEnd_110101 := by exact prefixLift 110101
  have htrace : WordTrace (prefixWord ++ tailWord_110101) baseStart_110101 baseEnd_110101 := by
    simpa [prefixWord, tailWord_110101, baseEnd_110101] using wordTrace_append hprefix tailTrace_110101
  have hstable : (prefixWord ++ tailWord_110101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110101).length < 2 ^ (prefixWord ++ tailWord_110101).sum := by decide
  have hdescent : baseEnd_110101 < baseStart_110101 := by decide
  rcases family_descends (prefixWord ++ tailWord_110101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110166 : List Nat := [5, 2, 2, 2, 1, 1, 3, 5]
def baseStart_110166 : Nat := 118140960795 + 110166 * 2 ^ 59
def prefixEnd_110166 : Nat := 4983230072969 + 3 ^ 40 * 110166 * 2
def baseEnd_110166 : Nat := 8380460708640179069387

theorem tailTrace_110166 : CollatzResearch.WordTrace tailWord_110166 prefixEnd_110166 8380460708640179069387 := by
  unfold tailWord_110166
  simp only [CollatzResearch.WordTrace]
  refine ⟨251130257430929481248897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2678722745929914466654901 251130257430929481248897)
  ·
    refine ⟨188347693073197110936673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251130257430929481248897 188347693073197110936673)
    ·
      refine ⟨141260769804897833202505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188347693073197110936673 141260769804897833202505)
      ·
        refine ⟨105945577353673374901879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141260769804897833202505 105945577353673374901879)
        ·
          refine ⟨158918366030510062352819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105945577353673374901879 158918366030510062352819)
          ·
            refine ⟨238377549045765093529229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158918366030510062352819 238377549045765093529229)
            ·
              refine ⟨89391580892161910073461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238377549045765093529229 89391580892161910073461)
              ·
                refine ⟨8380460708640179069387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89391580892161910073461 8380460708640179069387)
                ·
                  rfl

theorem cell21_110166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_110166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110166 prefixEnd_110166 := by exact prefixLift 110166
  have htrace : WordTrace (prefixWord ++ tailWord_110166) baseStart_110166 baseEnd_110166 := by
    simpa [prefixWord, tailWord_110166, baseEnd_110166] using wordTrace_append hprefix tailTrace_110166
  have hstable : (prefixWord ++ tailWord_110166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110166).length < 2 ^ (prefixWord ++ tailWord_110166).sum := by decide
  have hdescent : baseEnd_110166 < baseStart_110166 := by decide
  rcases family_descends (prefixWord ++ tailWord_110166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110188 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_110188 : Nat := 118140960795 + 110188 * 2 ^ 59
def prefixEnd_110188 : Nat := 4983230072969 + 3 ^ 40 * 110188 * 2
def baseEnd_110188 : Nat := 25146402825653387841449

theorem tailTrace_110188 : CollatzResearch.WordTrace tailWord_110188 prefixEnd_110188 25146402825653387841449 := by
  unfold tailWord_110188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009443262407584728641609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2679257683210112971522145 2009443262407584728641609)
  ·
    refine ⟨1507082446805688546481207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2009443262407584728641609 1507082446805688546481207)
    ·
      refine ⟨2260623670208532819721811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507082446805688546481207 2260623670208532819721811)
      ·
        refine ⟨3390935505312799229582717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260623670208532819721811 3390935505312799229582717)
        ·
          refine ⟨1271600814492299711093519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3390935505312799229582717 1271600814492299711093519)
          ·
            refine ⟨1907401221738449566640279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271600814492299711093519 1907401221738449566640279)
            ·
              refine ⟨2861101832607674349960419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907401221738449566640279 2861101832607674349960419)
              ·
                refine ⟨4291652748911511524940629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861101832607674349960419 4291652748911511524940629)
                ·
                  refine ⟨25146402825653387841449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4291652748911511524940629 25146402825653387841449)
                  ·
                    rfl

theorem cell21_110188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_110188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110188 prefixEnd_110188 := by exact prefixLift 110188
  have htrace : WordTrace (prefixWord ++ tailWord_110188) baseStart_110188 baseEnd_110188 := by
    simpa [prefixWord, tailWord_110188, baseEnd_110188] using wordTrace_append hprefix tailTrace_110188
  have hstable : (prefixWord ++ tailWord_110188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110188).length < 2 ^ (prefixWord ++ tailWord_110188).sum := by decide
  have hdescent : baseEnd_110188 < baseStart_110188 := by decide
  rcases family_descends (prefixWord ++ tailWord_110188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110205 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_110205 : Nat := 118140960795 + 110205 * 2 ^ 59
def prefixEnd_110205 : Nat := 4983230072969 + 3 ^ 40 * 110205 * 2
def baseEnd_110205 : Nat := 25150282457265136058081

theorem tailTrace_110205 : CollatzResearch.WordTrace tailWord_110205 prefixEnd_110205 25150282457265136058081 := by
  unfold tailWord_110205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019506565753581360652069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2679671043835720907101379 4019506565753581360652069)
  ·
    refine ⟨753657481078796505122263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4019506565753581360652069 753657481078796505122263)
    ·
      refine ⟨1130486221618194757683395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753657481078796505122263 1130486221618194757683395)
      ·
        refine ⟨1695729332427292136525093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130486221618194757683395 1695729332427292136525093)
        ·
          refine ⟨317949249830117275598455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1695729332427292136525093 317949249830117275598455)
          ·
            refine ⟨476923874745175913397683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317949249830117275598455 476923874745175913397683)
            ·
              refine ⟨715385812117763870096525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476923874745175913397683 715385812117763870096525)
              ·
                refine ⟨268269679544161451286197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715385812117763870096525 268269679544161451286197)
                ·
                  refine ⟨25150282457265136058081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268269679544161451286197 25150282457265136058081)
                  ·
                    rfl

theorem cell21_110205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_110205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110205 prefixEnd_110205 := by exact prefixLift 110205
  have htrace : WordTrace (prefixWord ++ tailWord_110205) baseStart_110205 baseEnd_110205 := by
    simpa [prefixWord, tailWord_110205, baseEnd_110205] using wordTrace_append hprefix tailTrace_110205
  have hstable : (prefixWord ++ tailWord_110205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110205).length < 2 ^ (prefixWord ++ tailWord_110205).sum := by decide
  have hdescent : baseEnd_110205 < baseStart_110205 := by decide
  rcases family_descends (prefixWord ++ tailWord_110205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110270 : List Nat := [4, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_110270 : Nat := 118140960795 + 110270 * 2 ^ 59
def prefixEnd_110270 : Nat := 4983230072969 + 3 ^ 40 * 110270 * 2
def baseEnd_110270 : Nat := 25165116342839467474615

theorem tailTrace_110270 : CollatzResearch.WordTrace tailWord_110270 prefixEnd_110270 25165116342839467474615 := by
  unfold tailWord_110270
  simp only [CollatzResearch.WordTrace]
  refine ⟨502734663814762182721033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2681251540345398307845509 502734663814762182721033)
  ·
    refine ⟨377050997861071637040775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 502734663814762182721033 377050997861071637040775)
    ·
      refine ⟨565576496791607455561163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377050997861071637040775 565576496791607455561163)
      ·
        refine ⟨848364745187411183341745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565576496791607455561163 848364745187411183341745)
        ·
          refine ⟨636273558890558387506309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848364745187411183341745 636273558890558387506309)
          ·
            refine ⟨119301292291979697657433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 636273558890558387506309 119301292291979697657433)
            ·
              refine ⟨89475969218984773243075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119301292291979697657433 89475969218984773243075)
              ·
                refine ⟨134213953828477159864613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89475969218984773243075 134213953828477159864613)
                ·
                  refine ⟨25165116342839467474615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134213953828477159864613 25165116342839467474615)
                  ·
                    rfl

theorem cell21_110270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_110270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110270 prefixEnd_110270 := by exact prefixLift 110270
  have htrace : WordTrace (prefixWord ++ tailWord_110270) baseStart_110270 baseEnd_110270 := by
    simpa [prefixWord, tailWord_110270, baseEnd_110270] using wordTrace_append hprefix tailTrace_110270
  have hstable : (prefixWord ++ tailWord_110270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110270).length < 2 ^ (prefixWord ++ tailWord_110270).sum := by decide
  have hdescent : baseEnd_110270 < baseStart_110270 := by decide
  rcases family_descends (prefixWord ++ tailWord_110270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110312 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_110312 : Nat := 118140960795 + 110312 * 2 ^ 59
def prefixEnd_110312 : Nat := 4983230072969 + 3 ^ 40 * 110312 * 2
def baseEnd_110312 : Nat := 25174701315056727774529

theorem tailTrace_110312 : CollatzResearch.WordTrace tailWord_110312 prefixEnd_110312 25174701315056727774529 := by
  unfold tailWord_110312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011704588182969317398595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2682272784243959089864793 2011704588182969317398595)
  ·
    refine ⟨3017556882274453976097893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011704588182969317398595 3017556882274453976097893)
    ·
      refine ⟨565791915426460120518355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3017556882274453976097893 565791915426460120518355)
      ·
        refine ⟨848687873139690180777533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565791915426460120518355 848687873139690180777533)
        ·
          refine ⟨318257952427383817791575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 848687873139690180777533 318257952427383817791575)
          ·
            refine ⟨477386928641075726687363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318257952427383817791575 477386928641075726687363)
            ·
              refine ⟨716080392961613590031045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477386928641075726687363 716080392961613590031045)
              ·
                refine ⟨134265073680302548130821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716080392961613590031045 134265073680302548130821)
                ·
                  refine ⟨25174701315056727774529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134265073680302548130821 25174701315056727774529)
                  ·
                    rfl

theorem cell21_110312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_110312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110312 prefixEnd_110312 := by exact prefixLift 110312
  have htrace : WordTrace (prefixWord ++ tailWord_110312) baseStart_110312 baseEnd_110312 := by
    simpa [prefixWord, tailWord_110312, baseEnd_110312] using wordTrace_append hprefix tailTrace_110312
  have hstable : (prefixWord ++ tailWord_110312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110312).length < 2 ^ (prefixWord ++ tailWord_110312).sum := by decide
  have hdescent : baseEnd_110312 < baseStart_110312 := by decide
  rcases family_descends (prefixWord ++ tailWord_110312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110478 : List Nat := [4, 1, 1, 5, 10]
def baseStart_110478 : Nat := 118140960795 + 110478 * 2 ^ 59
def prefixEnd_110478 : Nat := 4983230072969 + 3 ^ 40 * 110478 * 2
def baseEnd_110478 : Nat := 311266478724411456883

theorem tailTrace_110478 : CollatzResearch.WordTrace tailWord_110478 prefixEnd_110478 311266478724411456883 := by
  unfold tailWord_110478
  simp only [CollatzResearch.WordTrace]
  refine ⟨503682961720568623167511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2686309129176365990226725 503682961720568623167511)
  ·
    refine ⟨755524442580852934751267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503682961720568623167511 755524442580852934751267)
    ·
      refine ⟨1133286663871279402126901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755524442580852934751267 1133286663871279402126901)
      ·
        refine ⟨106245624737932443949397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1133286663871279402126901 106245624737932443949397)
        ·
          refine ⟨311266478724411456883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 106245624737932443949397 311266478724411456883)
          ·
            rfl

theorem cell21_110478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 10].length) (baseStart_110478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110478 prefixEnd_110478 := by exact prefixLift 110478
  have htrace : WordTrace (prefixWord ++ tailWord_110478) baseStart_110478 baseEnd_110478 := by
    simpa [prefixWord, tailWord_110478, baseEnd_110478] using wordTrace_append hprefix tailTrace_110478
  have hstable : (prefixWord ++ tailWord_110478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110478).length < 2 ^ (prefixWord ++ tailWord_110478).sum := by decide
  have hdescent : baseEnd_110478 < baseStart_110478 := by decide
  rcases family_descends (prefixWord ++ tailWord_110478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110484 : List Nat := [2, 4, 2, 1, 1, 4, 2, 2, 3]
def baseStart_110484 : Nat := 118140960795 + 110484 * 2 ^ 59
def prefixEnd_110484 : Nat := 4983230072969 + 3 ^ 40 * 110484 * 2
def baseEnd_110484 : Nat := 25213954058422650907511

theorem tailTrace_110484 : CollatzResearch.WordTrace tailWord_110484 prefixEnd_110484 25213954058422650907511 := by
  unfold tailWord_110484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014841265871406005029253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2686455021161874673372337 2014841265871406005029253)
  ·
    refine ⟨377782737350888625942985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2014841265871406005029253 377782737350888625942985)
    ·
      refine ⟨283337053013166469457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377782737350888625942985 283337053013166469457239)
      ·
        refine ⟨425005579519749704185859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283337053013166469457239 425005579519749704185859)
        ·
          refine ⟨637508369279624556278789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425005579519749704185859 637508369279624556278789)
          ·
            refine ⟨119532819239929604302273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 637508369279624556278789 119532819239929604302273)
            ·
              refine ⟨89649614429947203226705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119532819239929604302273 89649614429947203226705)
              ·
                refine ⟨67237210822460402420029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89649614429947203226705 67237210822460402420029)
                ·
                  refine ⟨25213954058422650907511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67237210822460402420029 25213954058422650907511)
                  ·
                    rfl

theorem cell21_110484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_110484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110484 prefixEnd_110484 := by exact prefixLift 110484
  have htrace : WordTrace (prefixWord ++ tailWord_110484) baseStart_110484 baseEnd_110484 := by
    simpa [prefixWord, tailWord_110484, baseEnd_110484] using wordTrace_append hprefix tailTrace_110484
  have hstable : (prefixWord ++ tailWord_110484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110484).length < 2 ^ (prefixWord ++ tailWord_110484).sum := by decide
  have hdescent : baseEnd_110484 < baseStart_110484 := by decide
  rcases family_descends (prefixWord ++ tailWord_110484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110495 : List Nat := [1, 1, 2, 5, 3, 2, 1, 6]
def baseStart_110495 : Nat := 118140960795 + 110495 * 2 ^ 59
def prefixEnd_110495 : Nat := 4983230072969 + 3 ^ 40 * 110495 * 2
def baseEnd_110495 : Nat := 8405488136096358741385

theorem tailTrace_110495 : CollatzResearch.WordTrace tailWord_110495 prefixEnd_110495 8405488136096358741385 := by
  unfold tailWord_110495
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030083734702960888708939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2686722489801973925805959 4030083734702960888708939)
  ·
    refine ⟨6045125602054441333063409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030083734702960888708939 6045125602054441333063409)
    ·
      refine ⟨4533844201540830999797557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6045125602054441333063409 4533844201540830999797557)
      ·
        refine ⟨425047893894452906231021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4533844201540830999797557 425047893894452906231021)
        ·
          refine ⟨159392960210419839836633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425047893894452906231021 159392960210419839836633)
          ·
            refine ⟨119544720157814879877475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159392960210419839836633 119544720157814879877475)
            ·
              refine ⟨179317080236722319816213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119544720157814879877475 179317080236722319816213)
              ·
                refine ⟨8405488136096358741385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179317080236722319816213 8405488136096358741385)
                ·
                  rfl

theorem cell21_110495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_110495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110495 prefixEnd_110495 := by exact prefixLift 110495
  have htrace : WordTrace (prefixWord ++ tailWord_110495) baseStart_110495 baseEnd_110495 := by
    simpa [prefixWord, tailWord_110495, baseEnd_110495] using wordTrace_append hprefix tailTrace_110495
  have hstable : (prefixWord ++ tailWord_110495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110495).length < 2 ^ (prefixWord ++ tailWord_110495).sum := by decide
  have hdescent : baseEnd_110495 < baseStart_110495 := by decide
  rcases family_descends (prefixWord ++ tailWord_110495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110526 : List Nat := [4, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_110526 : Nat := 118140960795 + 110526 * 2 ^ 59
def prefixEnd_110526 : Nat := 4983230072969 + 3 ^ 40 * 110526 * 2
def baseEnd_110526 : Nat := 25223539030639911207425

theorem tailTrace_110526 : CollatzResearch.WordTrace tailWord_110526 prefixEnd_110526 25223539030639911207425 := by
  unfold tailWord_110526
  simp only [CollatzResearch.WordTrace]
  refine ⟨503901799698831647885929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2687476265060435455391621 503901799698831647885929)
  ·
    refine ⟨377926349774123735914447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 503901799698831647885929 377926349774123735914447)
    ·
      refine ⟨566889524661185603871671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 377926349774123735914447 566889524661185603871671)
      ·
        refine ⟨850334286991778405807507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566889524661185603871671 850334286991778405807507)
        ·
          refine ⟨1275501430487667608711261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850334286991778405807507 1275501430487667608711261)
          ·
            refine ⟨478313036432875353266723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1275501430487667608711261 478313036432875353266723)
            ·
              refine ⟨717469554649313029900085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478313036432875353266723 717469554649313029900085)
              ·
                refine ⟨67262770748373096553133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717469554649313029900085 67262770748373096553133)
                ·
                  refine ⟨25223539030639911207425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67262770748373096553133 25223539030639911207425)
                  ·
                    rfl

theorem cell21_110526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_110526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110526 prefixEnd_110526 := by exact prefixLift 110526
  have htrace : WordTrace (prefixWord ++ tailWord_110526) baseStart_110526 baseEnd_110526 := by
    simpa [prefixWord, tailWord_110526, baseEnd_110526] using wordTrace_append hprefix tailTrace_110526
  have hstable : (prefixWord ++ tailWord_110526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110526).length < 2 ^ (prefixWord ++ tailWord_110526).sum := by decide
  have hdescent : baseEnd_110526 < baseStart_110526 := by decide
  rcases family_descends (prefixWord ++ tailWord_110526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110540 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_110540 : Nat := 118140960795 + 110540 * 2 ^ 59
def prefixEnd_110540 : Nat := 4983230072969 + 3 ^ 40 * 110540 * 2
def baseEnd_110540 : Nat := 25226734021378997974063

theorem tailTrace_110540 : CollatzResearch.WordTrace tailWord_110540 prefixEnd_110540 25226734021378997974063 := by
  unfold tailWord_110540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015862509769966787048537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2687816679693289049398049 2015862509769966787048537)
  ·
    refine ⟨1511896882327475090286403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2015862509769966787048537 1511896882327475090286403)
    ·
      refine ⟨2267845323491212635429605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1511896882327475090286403 2267845323491212635429605)
      ·
        refine ⟨425220998154602369143051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2267845323491212635429605 425220998154602369143051)
        ·
          refine ⟨637831497231903553714577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425220998154602369143051 637831497231903553714577)
          ·
            refine ⟨478373622923927665285933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637831497231903553714577 478373622923927665285933)
            ·
              refine ⟨179390108596472874482225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478373622923927665285933 179390108596472874482225)
              ·
                refine ⟨134542581447354655861669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179390108596472874482225 134542581447354655861669)
                ·
                  refine ⟨25226734021378997974063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134542581447354655861669 25226734021378997974063)
                  ·
                    rfl

theorem cell21_110540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_110540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110540 prefixEnd_110540 := by exact prefixLift 110540
  have htrace : WordTrace (prefixWord ++ tailWord_110540) baseStart_110540 baseEnd_110540 := by
    simpa [prefixWord, tailWord_110540, baseEnd_110540] using wordTrace_append hprefix tailTrace_110540
  have hstable : (prefixWord ++ tailWord_110540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110540).length < 2 ^ (prefixWord ++ tailWord_110540).sum := by decide
  have hdescent : baseEnd_110540 < baseStart_110540 := by decide
  rcases family_descends (prefixWord ++ tailWord_110540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110599 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 6]
def baseStart_110599 : Nat := 118140960795 + 110599 * 2 ^ 59
def prefixEnd_110599 : Nat := 4983230072969 + 3 ^ 40 * 110599 * 2
def baseEnd_110599 : Nat := 25240198625208006490609

theorem tailTrace_110599 : CollatzResearch.WordTrace tailWord_110599 prefixEnd_110599 25240198625208006490609 := by
  unfold tailWord_110599
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033876926326186650494851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2689251284217457766996567 4033876926326186650494851)
  ·
    refine ⟨6050815389489279975742277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033876926326186650494851 6050815389489279975742277)
    ·
      refine ⟨1134527885529239995451677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6050815389489279975742277 1134527885529239995451677)
      ·
        refine ⟨425447957073464998294379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1134527885529239995451677 425447957073464998294379)
        ·
          refine ⟨638171935610197497441569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425447957073464998294379 638171935610197497441569)
          ·
            refine ⟨478628951707648123081177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 638171935610197497441569 478628951707648123081177)
            ·
              refine ⟨358971713780736092310883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478628951707648123081177 358971713780736092310883)
              ·
                refine ⟨538457570671104138466325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358971713780736092310883 538457570671104138466325)
                ·
                  refine ⟨25240198625208006490609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 538457570671104138466325 25240198625208006490609)
                  ·
                    rfl

theorem cell21_110599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_110599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110599 prefixEnd_110599 := by exact prefixLift 110599
  have htrace : WordTrace (prefixWord ++ tailWord_110599) baseStart_110599 baseEnd_110599 := by
    simpa [prefixWord, tailWord_110599, baseEnd_110599] using wordTrace_append hprefix tailTrace_110599
  have hstable : (prefixWord ++ tailWord_110599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110599).length < 2 ^ (prefixWord ++ tailWord_110599).sum := by decide
  have hdescent : baseEnd_110599 < baseStart_110599 := by decide
  rcases family_descends (prefixWord ++ tailWord_110599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110602 : List Nat := [3, 1, 2, 2, 4, 2, 1, 1, 5]
def baseStart_110602 : Nat := 118140960795 + 110602 * 2 ^ 59
def prefixEnd_110602 : Nat := 4983230072969 + 3 ^ 40 * 110602 * 2
def baseEnd_110602 : Nat := 25240883266080667940603

theorem tailTrace_110602 : CollatzResearch.WordTrace tailWord_110602 prefixEnd_110602 25240883266080667940603 := by
  unfold tailWord_110602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1008496586328829540713515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2689324230210212108569373 1008496586328829540713515)
  ·
    refine ⟨1512744879493244311070273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1008496586328829540713515 1512744879493244311070273)
    ·
      refine ⟨1134558659619933233302705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1512744879493244311070273 1134558659619933233302705)
      ·
        refine ⟨850918994714949924977029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134558659619933233302705 850918994714949924977029)
        ·
          refine ⟨159547311509053110933193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 850918994714949924977029 159547311509053110933193)
          ·
            refine ⟨119660483631789833199895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159547311509053110933193 119660483631789833199895)
            ·
              refine ⟨179490725447684749799843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119660483631789833199895 179490725447684749799843)
              ·
                refine ⟨269236088171527124699765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179490725447684749799843 269236088171527124699765)
                ·
                  refine ⟨25240883266080667940603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269236088171527124699765 25240883266080667940603)
                  ·
                    rfl

theorem cell21_110602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_110602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110602 prefixEnd_110602 := by exact prefixLift 110602
  have htrace : WordTrace (prefixWord ++ tailWord_110602) baseStart_110602 baseEnd_110602 := by
    simpa [prefixWord, tailWord_110602, baseEnd_110602] using wordTrace_append hprefix tailTrace_110602
  have hstable : (prefixWord ++ tailWord_110602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110602).length < 2 ^ (prefixWord ++ tailWord_110602).sum := by decide
  have hdescent : baseEnd_110602 < baseStart_110602 := by decide
  rcases family_descends (prefixWord ++ tailWord_110602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110605 : List Nat := [1, 7, 1, 2, 1, 1, 2, 6]
def baseStart_110605 : Nat := 118140960795 + 110605 * 2 ^ 59
def prefixEnd_110605 : Nat := 4983230072969 + 3 ^ 40 * 110605 * 2
def baseEnd_110605 : Nat := 8413855968984443130199

theorem tailTrace_110605 : CollatzResearch.WordTrace tailWord_110605 prefixEnd_110605 8413855968984443130199 := by
  unfold tailWord_110605
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034095764304449675213269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2689397176202966450142179 4034095764304449675213269)
  ·
    refine ⟨94549119475885539262811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4034095764304449675213269 94549119475885539262811)
    ·
      refine ⟨141823679213828308894217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94549119475885539262811 141823679213828308894217)
      ·
        refine ⟨106367759410371231670663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141823679213828308894217 106367759410371231670663)
        ·
          refine ⟨159551639115556847505995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106367759410371231670663 159551639115556847505995)
          ·
            refine ⟨239327458673335271258993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159551639115556847505995 239327458673335271258993)
            ·
              refine ⟨179495594005001453444245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239327458673335271258993 179495594005001453444245)
              ·
                refine ⟨8413855968984443130199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179495594005001453444245 8413855968984443130199)
                ·
                  rfl

theorem cell21_110605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 6].length) (baseStart_110605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110605 prefixEnd_110605 := by exact prefixLift 110605
  have htrace : WordTrace (prefixWord ++ tailWord_110605) baseStart_110605 baseEnd_110605 := by
    simpa [prefixWord, tailWord_110605, baseEnd_110605] using wordTrace_append hprefix tailTrace_110605
  have hstable : (prefixWord ++ tailWord_110605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110605).length < 2 ^ (prefixWord ++ tailWord_110605).sum := by decide
  have hdescent : baseEnd_110605 < baseStart_110605 := by decide
  rcases family_descends (prefixWord ++ tailWord_110605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110678 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_110678 : Nat := 118140960795 + 110678 * 2 ^ 59
def prefixEnd_110678 : Nat := 4983230072969 + 3 ^ 40 * 110678 * 2
def baseEnd_110678 : Nat := 25258227501521424673781

theorem tailTrace_110678 : CollatzResearch.WordTrace tailWord_110678 prefixEnd_110678 25258227501521424673781 := by
  unfold tailWord_110678
  simp only [CollatzResearch.WordTrace]
  refine ⟨252297393314998946413793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2691172195359988761747125 252297393314998946413793)
  ·
    refine ⟨189223044986249209810345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252297393314998946413793 189223044986249209810345)
    ·
      refine ⟨141917283739686907357759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189223044986249209810345 141917283739686907357759)
      ·
        refine ⟨212875925609530361036639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141917283739686907357759 212875925609530361036639)
        ·
          refine ⟨319313888414295541554959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212875925609530361036639 319313888414295541554959)
          ·
            refine ⟨478970832621443312332439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319313888414295541554959 478970832621443312332439)
            ·
              refine ⟨718456248932164968498659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478970832621443312332439 718456248932164968498659)
              ·
                refine ⟨1077684373398247452747989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 718456248932164968498659 1077684373398247452747989)
                ·
                  refine ⟨25258227501521424673781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1077684373398247452747989 25258227501521424673781)
                  ·
                    rfl

theorem cell21_110678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_110678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110678 prefixEnd_110678 := by exact prefixLift 110678
  have htrace : WordTrace (prefixWord ++ tailWord_110678) baseStart_110678 baseEnd_110678 := by
    simpa [prefixWord, tailWord_110678, baseEnd_110678] using wordTrace_append hprefix tailTrace_110678
  have hstable : (prefixWord ++ tailWord_110678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110678).length < 2 ^ (prefixWord ++ tailWord_110678).sum := by decide
  have hdescent : baseEnd_110678 < baseStart_110678 := by decide
  rcases family_descends (prefixWord ++ tailWord_110678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110751 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 6]
def baseStart_110751 : Nat := 118140960795 + 110751 * 2 ^ 59
def prefixEnd_110751 : Nat := 4983230072969 + 3 ^ 40 * 110751 * 2
def baseEnd_110751 : Nat := 25274887096089519956965

theorem tailTrace_110751 : CollatzResearch.WordTrace tailWord_110751 prefixEnd_110751 25274887096089519956965 := by
  unfold tailWord_110751
  simp only [CollatzResearch.WordTrace]
  refine ⟨4039420821775516610028107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2692947214517011073352071 4039420821775516610028107)
  ·
    refine ⟨6059131232663274915042161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4039420821775516610028107 6059131232663274915042161)
    ·
      refine ⟨4544348424497456186281621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6059131232663274915042161 4544348424497456186281621)
      ·
        refine ⟨213016332398318258731951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4544348424497456186281621 213016332398318258731951)
        ·
          refine ⟨319524498597477388097927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213016332398318258731951 319524498597477388097927)
          ·
            refine ⟨479286747896216082146891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319524498597477388097927 479286747896216082146891)
            ·
              refine ⟨718930121844324123220337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479286747896216082146891 718930121844324123220337)
              ·
                refine ⟨539197591383243092415253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 718930121844324123220337 539197591383243092415253)
                ·
                  refine ⟨25274887096089519956965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 539197591383243092415253 25274887096089519956965)
                  ·
                    rfl

theorem cell21_110751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_110751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110751 prefixEnd_110751 := by exact prefixLift 110751
  have htrace : WordTrace (prefixWord ++ tailWord_110751) baseStart_110751 baseEnd_110751 := by
    simpa [prefixWord, tailWord_110751, baseEnd_110751] using wordTrace_append hprefix tailTrace_110751
  have hstable : (prefixWord ++ tailWord_110751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110751).length < 2 ^ (prefixWord ++ tailWord_110751).sum := by decide
  have hdescent : baseEnd_110751 < baseStart_110751 := by decide
  rcases family_descends (prefixWord ++ tailWord_110751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110785 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 4]
def baseStart_110785 : Nat := 118140960795 + 110785 * 2 ^ 59
def prefixEnd_110785 : Nat := 4983230072969 + 3 ^ 40 * 110785 * 2
def baseEnd_110785 : Nat := 25282646359313016390229

theorem tailTrace_110785 : CollatzResearch.WordTrace tailWord_110785 prefixEnd_110785 25282646359313016390229 := by
  unfold tailWord_110785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4040660903652340416765809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2693773935768226944510539 4040660903652340416765809)
  ·
    refine ⟨3030495677739255312574357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4040660903652340416765809 3030495677739255312574357)
    ·
      refine ⟨142054484894027592776923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3030495677739255312574357 142054484894027592776923)
      ·
        refine ⟨213081727341041389165385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142054484894027592776923 213081727341041389165385)
        ·
          refine ⟨159811295505781041874039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213081727341041389165385 159811295505781041874039)
          ·
            refine ⟨239716943258671562811059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159811295505781041874039 239716943258671562811059)
            ·
              refine ⟨359575414888007344216589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239716943258671562811059 359575414888007344216589)
              ·
                refine ⟨134840780583002754081221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359575414888007344216589 134840780583002754081221)
                ·
                  refine ⟨25282646359313016390229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134840780583002754081221 25282646359313016390229)
                  ·
                    rfl

theorem cell21_110785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 4].length) (baseStart_110785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110785 prefixEnd_110785 := by exact prefixLift 110785
  have htrace : WordTrace (prefixWord ++ tailWord_110785) baseStart_110785 baseEnd_110785 := by
    simpa [prefixWord, tailWord_110785, baseEnd_110785] using wordTrace_append hprefix tailTrace_110785
  have hstable : (prefixWord ++ tailWord_110785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110785).length < 2 ^ (prefixWord ++ tailWord_110785).sum := by decide
  have hdescent : baseEnd_110785 < baseStart_110785 := by decide
  rcases family_descends (prefixWord ++ tailWord_110785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110810 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_110810 : Nat := 118140960795 + 110810 * 2 ^ 59
def prefixEnd_110810 : Nat := 4983230072969 + 3 ^ 40 * 110810 * 2
def baseEnd_110810 : Nat := 25288351699918528473511

theorem tailTrace_110810 : CollatzResearch.WordTrace tailWord_110810 prefixEnd_110810 25288351699918528473511 := by
  unfold tailWord_110810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010393182140442421606471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2694381819041179790950589 1010393182140442421606471)
  ·
    refine ⟨1515589773210663632409707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010393182140442421606471 1515589773210663632409707)
    ·
      refine ⟨2273384659815995448614561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515589773210663632409707 2273384659815995448614561)
      ·
        refine ⟨1705038494861996586460921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2273384659815995448614561 1705038494861996586460921)
        ·
          refine ⟨1278778871146497439845691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1705038494861996586460921 1278778871146497439845691)
          ·
            refine ⟨1918168306719746159768537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1278778871146497439845691 1918168306719746159768537)
            ·
              refine ⟨1438626230039809619826403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1918168306719746159768537 1438626230039809619826403)
              ·
                refine ⟨2157939345059714429739605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1438626230039809619826403 2157939345059714429739605)
                ·
                  refine ⟨25288351699918528473511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2157939345059714429739605 25288351699918528473511)
                  ·
                    rfl

theorem cell21_110810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_110810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110810 prefixEnd_110810 := by exact prefixLift 110810
  have htrace : WordTrace (prefixWord ++ tailWord_110810) baseStart_110810 baseEnd_110810 := by
    simpa [prefixWord, tailWord_110810, baseEnd_110810] using wordTrace_append hprefix tailTrace_110810
  have hstable : (prefixWord ++ tailWord_110810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110810).length < 2 ^ (prefixWord ++ tailWord_110810).sum := by decide
  have hdescent : baseEnd_110810 < baseStart_110810 := by decide
  rcases family_descends (prefixWord ++ tailWord_110810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110827 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 4]
def baseStart_110827 : Nat := 118140960795 + 110827 * 2 ^ 59
def prefixEnd_110827 : Nat := 4983230072969 + 3 ^ 40 * 110827 * 2
def baseEnd_110827 : Nat := 25292231331530276690143

theorem tailTrace_110827 : CollatzResearch.WordTrace tailWord_110827 prefixEnd_110827 25292231331530276690143 := by
  unfold tailWord_110827
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042192769500181589794735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2694795179666787726529823 4042192769500181589794735)
  ·
    refine ⟨6063289154250272384692103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042192769500181589794735 6063289154250272384692103)
    ·
      refine ⟨9094933731375408577038155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6063289154250272384692103 9094933731375408577038155)
      ·
        refine ⟨13642400597063112865557233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9094933731375408577038155 13642400597063112865557233)
        ·
          refine ⟨10231800447797334649167925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13642400597063112865557233 10231800447797334649167925)
          ·
            refine ⟨959231291981000123359493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10231800447797334649167925 959231291981000123359493)
            ·
              refine ⟨179855867246437523129905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 959231291981000123359493 179855867246437523129905)
              ·
                refine ⟨134891900434828142347429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179855867246437523129905 134891900434828142347429)
                ·
                  refine ⟨25292231331530276690143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134891900434828142347429 25292231331530276690143)
                  ·
                    rfl

theorem cell21_110827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 4].length) (baseStart_110827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110827 prefixEnd_110827 := by exact prefixLift 110827
  have htrace : WordTrace (prefixWord ++ tailWord_110827) baseStart_110827 baseEnd_110827 := by
    simpa [prefixWord, tailWord_110827, baseEnd_110827] using wordTrace_append hprefix tailTrace_110827
  have hstable : (prefixWord ++ tailWord_110827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110827).length < 2 ^ (prefixWord ++ tailWord_110827).sum := by decide
  have hdescent : baseEnd_110827 < baseStart_110827 := by decide
  rcases family_descends (prefixWord ++ tailWord_110827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110878 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_110878 : Nat := 118140960795 + 110878 * 2 ^ 59
def prefixEnd_110878 : Nat := 4983230072969 + 3 ^ 40 * 110878 * 2
def baseEnd_110878 : Nat := 25303870226365521340039

theorem tailTrace_110878 : CollatzResearch.WordTrace tailWord_110878 prefixEnd_110878 25303870226365521340039 := by
  unfold tailWord_110878
  simp only [CollatzResearch.WordTrace]
  refine ⟨505506611539427162487661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2696035261543611533267525 505506611539427162487661)
  ·
    refine ⟨189564979327285185932873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 505506611539427162487661 189564979327285185932873)
    ·
      refine ⟨142173734495463889449655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189564979327285185932873 142173734495463889449655)
      ·
        refine ⟨213260601743195834174483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142173734495463889449655 213260601743195834174483)
        ·
          refine ⟨319890902614793751261725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213260601743195834174483 319890902614793751261725)
          ·
            refine ⟨119959088480547656723147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319890902614793751261725 119959088480547656723147)
            ·
              refine ⟨179938632720821485084721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119959088480547656723147 179938632720821485084721)
              ·
                refine ⟨134953974540616113813541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179938632720821485084721 134953974540616113813541)
                ·
                  refine ⟨25303870226365521340039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134953974540616113813541 25303870226365521340039)
                  ·
                    rfl

theorem cell21_110878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_110878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110878 prefixEnd_110878 := by exact prefixLift 110878
  have htrace : WordTrace (prefixWord ++ tailWord_110878) baseStart_110878 baseEnd_110878 := by
    simpa [prefixWord, tailWord_110878, baseEnd_110878] using wordTrace_append hprefix tailTrace_110878
  have hstable : (prefixWord ++ tailWord_110878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110878).length < 2 ^ (prefixWord ++ tailWord_110878).sum := by decide
  have hdescent : baseEnd_110878 < baseStart_110878 := by decide
  rcases family_descends (prefixWord ++ tailWord_110878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_110940 : List Nat := [2, 2, 4, 3, 1, 1, 3, 2, 3]
def baseStart_110940 : Nat := 118140960795 + 110940 * 2 ^ 59
def prefixEnd_110940 : Nat := 4983230072969 + 3 ^ 40 * 110940 * 2
def baseEnd_110940 : Nat := 25318019471067191306579

theorem tailTrace_110940 : CollatzResearch.WordTrace tailWord_110940 prefixEnd_110940 25318019471067191306579 := by
  unfold tailWord_110940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2023157109045400944329137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2697542812060534592438849 2023157109045400944329137)
  ·
    refine ⟨1517367831784050708246853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2023157109045400944329137 1517367831784050708246853)
    ·
      refine ⟨284506468459509507796285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1517367831784050708246853 284506468459509507796285)
      ·
        refine ⟨106689925672316065423607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284506468459509507796285 106689925672316065423607)
        ·
          refine ⟨160034888508474098135411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106689925672316065423607 160034888508474098135411)
          ·
            refine ⟨240052332762711147203117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160034888508474098135411 240052332762711147203117)
            ·
              refine ⟨90019624786016680201169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240052332762711147203117 90019624786016680201169)
              ·
                refine ⟨67514718589512510150877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90019624786016680201169 67514718589512510150877)
                ·
                  refine ⟨25318019471067191306579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67514718589512510150877 25318019471067191306579)
                  ·
                    rfl

theorem cell21_110940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_110940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_110940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_110940 prefixEnd_110940 := by exact prefixLift 110940
  have htrace : WordTrace (prefixWord ++ tailWord_110940) baseStart_110940 baseEnd_110940 := by
    simpa [prefixWord, tailWord_110940, baseEnd_110940] using wordTrace_append hprefix tailTrace_110940
  have hstable : (prefixWord ++ tailWord_110940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_110940).length < 2 ^ (prefixWord ++ tailWord_110940).sum := by decide
  have hdescent : baseEnd_110940 < baseStart_110940 := by decide
  rcases family_descends (prefixWord ++ tailWord_110940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111058 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 5]
def baseStart_111058 : Nat := 118140960795 + 111058 * 2 ^ 59
def prefixEnd_111058 : Nat := 4983230072969 + 3 ^ 40 * 111058 * 2
def baseEnd_111058 : Nat := 25344948678725208339671

theorem tailTrace_111058 : CollatzResearch.WordTrace tailWord_111058 prefixEnd_111058 25344948678725208339671 := by
  unfold tailWord_111058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1012654507915827010363457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2700412021108872027635885 1012654507915827010363457)
  ·
    refine ⟨759490880936870257772593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1012654507915827010363457 759490880936870257772593)
    ·
      refine ⟨569618160702652693329445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759490880936870257772593 569618160702652693329445)
      ·
        refine ⟨106803405131747379999271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 569618160702652693329445 106803405131747379999271)
        ·
          refine ⟨160205107697621069998907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106803405131747379999271 160205107697621069998907)
          ·
            refine ⟨240307661546431604998361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160205107697621069998907 240307661546431604998361)
            ·
              refine ⟨180230746159823703748771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240307661546431604998361 180230746159823703748771)
              ·
                refine ⟨270346119239735555623157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180230746159823703748771 270346119239735555623157)
                ·
                  refine ⟨25344948678725208339671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270346119239735555623157 25344948678725208339671)
                  ·
                    rfl

theorem cell21_111058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_111058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111058 prefixEnd_111058 := by exact prefixLift 111058
  have htrace : WordTrace (prefixWord ++ tailWord_111058) baseStart_111058 baseEnd_111058 := by
    simpa [prefixWord, tailWord_111058, baseEnd_111058] using wordTrace_append hprefix tailTrace_111058
  have hstable : (prefixWord ++ tailWord_111058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111058).length < 2 ^ (prefixWord ++ tailWord_111058).sum := by decide
  have hdescent : baseEnd_111058 < baseStart_111058 := by decide
  rcases family_descends (prefixWord ++ tailWord_111058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111069 : List Nat := [1, 4, 3, 1, 1, 1, 2, 8]
def baseStart_111069 : Nat := 118140960795 + 111069 * 2 ^ 59
def prefixEnd_111069 : Nat := 4983230072969 + 3 ^ 40 * 111069 * 2
def baseEnd_111069 : Nat := 8449153009530544552105

theorem tailTrace_111069 : CollatzResearch.WordTrace tailWord_111069 prefixEnd_111069 8449153009530544552105 := by
  unfold tailWord_111069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051019234623456920104261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2700679489748971280069507 4051019234623456920104261)
  ·
    refine ⟨759566106491898172519549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4051019234623456920104261 759566106491898172519549)
    ·
      refine ⟨284837289934461814694831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 759566106491898172519549 284837289934461814694831)
      ·
        refine ⟨427255934901692722042247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284837289934461814694831 427255934901692722042247)
        ·
          refine ⟨640883902352539083063371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427255934901692722042247 640883902352539083063371)
          ·
            refine ⟨961325853528808624595057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640883902352539083063371 961325853528808624595057)
            ·
              refine ⟨720994390146606468446293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961325853528808624595057 720994390146606468446293)
              ·
                refine ⟨8449153009530544552105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 720994390146606468446293 8449153009530544552105)
                ·
                  rfl

theorem cell21_111069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 8].length) (baseStart_111069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111069 prefixEnd_111069 := by exact prefixLift 111069
  have htrace : WordTrace (prefixWord ++ tailWord_111069) baseStart_111069 baseEnd_111069 := by
    simpa [prefixWord, tailWord_111069, baseEnd_111069] using wordTrace_append hprefix tailTrace_111069
  have hstable : (prefixWord ++ tailWord_111069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111069).length < 2 ^ (prefixWord ++ tailWord_111069).sum := by decide
  have hdescent : baseEnd_111069 < baseStart_111069 := by decide
  rcases family_descends (prefixWord ++ tailWord_111069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111083 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_111083 : Nat := 118140960795 + 111083 * 2 ^ 59
def prefixEnd_111083 : Nat := 4983230072969 + 3 ^ 40 * 111083 * 2
def baseEnd_111083 : Nat := 25350654019330720422953

theorem tailTrace_111083 : CollatzResearch.WordTrace tailWord_111083 prefixEnd_111083 25350654019330720422953 := by
  unfold tailWord_111083
  simp only [CollatzResearch.WordTrace]
  refine ⟨4051529856572737311113903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2701019904381824874075935 4051529856572737311113903)
  ·
    refine ⟨6077294784859105966670855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4051529856572737311113903 6077294784859105966670855)
    ·
      refine ⟨9115942177288658950006283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6077294784859105966670855 9115942177288658950006283)
      ·
        refine ⟨13673913265932988425009425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9115942177288658950006283 13673913265932988425009425)
        ·
          refine ⟨10255434949449741318757069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13673913265932988425009425 10255434949449741318757069)
          ·
            refine ⟨3845788106043652994533901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10255434949449741318757069 3845788106043652994533901)
            ·
              refine ⟨1442170539766369872950213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3845788106043652994533901 1442170539766369872950213)
              ·
                refine ⟨270406976206194351178165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1442170539766369872950213 270406976206194351178165)
                ·
                  refine ⟨25350654019330720422953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270406976206194351178165 25350654019330720422953)
                  ·
                    rfl

theorem cell21_111083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_111083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111083 prefixEnd_111083 := by exact prefixLift 111083
  have htrace : WordTrace (prefixWord ++ tailWord_111083) baseStart_111083 baseEnd_111083 := by
    simpa [prefixWord, tailWord_111083, baseEnd_111083] using wordTrace_append hprefix tailTrace_111083
  have hstable : (prefixWord ++ tailWord_111083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111083).length < 2 ^ (prefixWord ++ tailWord_111083).sum := by decide
  have hdescent : baseEnd_111083 < baseStart_111083 := by decide
  rcases family_descends (prefixWord ++ tailWord_111083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111086 : List Nat := [4, 1, 2, 1, 2, 2, 4, 5]
def baseStart_111086 : Nat := 118140960795 + 111086 * 2 ^ 59
def prefixEnd_111086 : Nat := 4983230072969 + 3 ^ 40 * 111086 * 2
def baseEnd_111086 : Nat := 8450446220067793957649

theorem tailTrace_111086 : CollatzResearch.WordTrace tailWord_111086 prefixEnd_111086 8450446220067793957649 := by
  unfold tailWord_111086
  simp only [CollatzResearch.WordTrace]
  refine ⟨506454909445233602934139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2701092850374579215648741 506454909445233602934139)
  ·
    refine ⟨759682364167850404401209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506454909445233602934139 759682364167850404401209)
    ·
      refine ⟨569761773125887803300907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 759682364167850404401209 569761773125887803300907)
      ·
        refine ⟨854642659688831704951361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569761773125887803300907 854642659688831704951361)
        ·
          refine ⟨640981994766623778713521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854642659688831704951361 640981994766623778713521)
          ·
            refine ⟨480736496074967834035141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640981994766623778713521 480736496074967834035141)
            ·
              refine ⟨90138093014056468881589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480736496074967834035141 90138093014056468881589)
              ·
                refine ⟨8450446220067793957649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90138093014056468881589 8450446220067793957649)
                ·
                  rfl

theorem cell21_111086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_111086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111086 prefixEnd_111086 := by exact prefixLift 111086
  have htrace : WordTrace (prefixWord ++ tailWord_111086) baseStart_111086 baseEnd_111086 := by
    simpa [prefixWord, tailWord_111086, baseEnd_111086] using wordTrace_append hprefix tailTrace_111086
  have hstable : (prefixWord ++ tailWord_111086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111086).length < 2 ^ (prefixWord ++ tailWord_111086).sum := by decide
  have hdescent : baseEnd_111086 < baseStart_111086 := by decide
  rcases family_descends (prefixWord ++ tailWord_111086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111114 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 6]
def baseStart_111114 : Nat := 118140960795 + 111114 * 2 ^ 59
def prefixEnd_111114 : Nat := 4983230072969 + 3 ^ 40 * 111114 * 2
def baseEnd_111114 : Nat := 25357728641681555406223

theorem tailTrace_111114 : CollatzResearch.WordTrace tailWord_111114 prefixEnd_111114 25357728641681555406223 := by
  unfold tailWord_111114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013165129865107401373099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2701773679640286403661597 1013165129865107401373099)
  ·
    refine ⟨1519747694797661102059649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013165129865107401373099 1519747694797661102059649)
    ·
      refine ⟨1139810771098245826544737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1519747694797661102059649 1139810771098245826544737)
      ·
        refine ⟨854858078323684369908553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1139810771098245826544737 854858078323684369908553)
        ·
          refine ⟨641143558742763277431415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854858078323684369908553 641143558742763277431415)
          ·
            refine ⟨961715338114144916147123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641143558742763277431415 961715338114144916147123)
            ·
              refine ⟨1442573007171217374220685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 961715338114144916147123 1442573007171217374220685)
              ·
                refine ⟨540964877689206515332757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1442573007171217374220685 540964877689206515332757)
                ·
                  refine ⟨25357728641681555406223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 540964877689206515332757 25357728641681555406223)
                  ·
                    rfl

theorem cell21_111114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_111114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111114 prefixEnd_111114 := by exact prefixLift 111114
  have htrace : WordTrace (prefixWord ++ tailWord_111114) baseStart_111114 baseEnd_111114 := by
    simpa [prefixWord, tailWord_111114, baseEnd_111114] using wordTrace_append hprefix tailTrace_111114
  have hstable : (prefixWord ++ tailWord_111114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111114).length < 2 ^ (prefixWord ++ tailWord_111114).sum := by decide
  have hdescent : baseEnd_111114 < baseStart_111114 := by decide
  rcases family_descends (prefixWord ++ tailWord_111114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111235 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 5]
def baseStart_111235 : Nat := 118140960795 + 111235 * 2 ^ 59
def prefixEnd_111235 : Nat := 4983230072969 + 3 ^ 40 * 111235 * 2
def baseEnd_111235 : Nat := 25385342490212233889309

theorem tailTrace_111235 : CollatzResearch.WordTrace tailWord_111235 prefixEnd_111235 25385342490212233889309 := by
  unfold tailWord_111235
  simp only [CollatzResearch.WordTrace]
  refine ⟨4057073752022067270647159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2704715834681378180431439 4057073752022067270647159)
  ·
    refine ⟨6085610628033100905970739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4057073752022067270647159 6085610628033100905970739)
    ·
      refine ⟨9128415942049651358956109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6085610628033100905970739 9128415942049651358956109)
      ·
        refine ⟨3423155978268619259608541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9128415942049651358956109 3423155978268619259608541)
        ·
          refine ⟨1283683491850732222353203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3423155978268619259608541 1283683491850732222353203)
          ·
            refine ⟨1925525237776098333529805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283683491850732222353203 1925525237776098333529805)
            ·
              refine ⟨722071964166036875073677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1925525237776098333529805 722071964166036875073677)
              ·
                refine ⟨270776986562263828152629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722071964166036875073677 270776986562263828152629)
                ·
                  refine ⟨25385342490212233889309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270776986562263828152629 25385342490212233889309)
                  ·
                    rfl

theorem cell21_111235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_111235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111235 prefixEnd_111235 := by exact prefixLift 111235
  have htrace : WordTrace (prefixWord ++ tailWord_111235) baseStart_111235 baseEnd_111235 := by
    simpa [prefixWord, tailWord_111235, baseEnd_111235] using wordTrace_append hprefix tailTrace_111235
  have hstable : (prefixWord ++ tailWord_111235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111235).length < 2 ^ (prefixWord ++ tailWord_111235).sum := by decide
  have hdescent : baseEnd_111235 < baseStart_111235 := by decide
  rcases family_descends (prefixWord ++ tailWord_111235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111300 : List Nat := [2, 3, 3, 1, 1, 2, 4, 1, 4]
def baseStart_111300 : Nat := 118140960795 + 111300 * 2 ^ 59
def prefixEnd_111300 : Nat := 4983230072969 + 3 ^ 40 * 111300 * 2
def baseEnd_111300 : Nat := 25400176375786565305843

theorem tailTrace_111300 : CollatzResearch.WordTrace tailWord_111300 prefixEnd_111300 25400176375786565305843 := by
  unfold tailWord_111300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2029722248393291685881677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2706296331191055581175569 2029722248393291685881677)
  ·
    refine ⟨761145843147484382205629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2029722248393291685881677 761145843147484382205629)
    ·
      refine ⟨285429691180306643327111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 761145843147484382205629 285429691180306643327111)
      ·
        refine ⟨428144536770459964990667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285429691180306643327111 428144536770459964990667)
        ·
          refine ⟨642216805155689947486001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428144536770459964990667 642216805155689947486001)
          ·
            refine ⟨481662603866767460614501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642216805155689947486001 481662603866767460614501)
            ·
              refine ⟨90311738225018898865219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 481662603866767460614501 90311738225018898865219)
              ·
                refine ⟨135467607337528348297829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90311738225018898865219 135467607337528348297829)
                ·
                  refine ⟨25400176375786565305843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135467607337528348297829 25400176375786565305843)
                  ·
                    rfl

theorem cell21_111300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_111300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111300 prefixEnd_111300 := by exact prefixLift 111300
  have htrace : WordTrace (prefixWord ++ tailWord_111300) baseStart_111300 baseEnd_111300 := by
    simpa [prefixWord, tailWord_111300, baseEnd_111300] using wordTrace_append hprefix tailTrace_111300
  have hstable : (prefixWord ++ tailWord_111300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111300).length < 2 ^ (prefixWord ++ tailWord_111300).sum := by decide
  have hdescent : baseEnd_111300 < baseStart_111300 := by decide
  rcases family_descends (prefixWord ++ tailWord_111300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111328 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 3]
def baseStart_111328 : Nat := 118140960795 + 111328 * 2 ^ 59
def prefixEnd_111328 : Nat := 4983230072969 + 3 ^ 40 * 111328 * 2
def baseEnd_111328 : Nat := 25406566357264738839119

theorem tailTrace_111328 : CollatzResearch.WordTrace tailWord_111328 prefixEnd_111328 25406566357264738839119 := by
  unfold tailWord_111328
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030232870342572076891319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2706977160456762769188425 2030232870342572076891319)
  ·
    refine ⟨3045349305513858115336979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030232870342572076891319 3045349305513858115336979)
    ·
      refine ⟨4568023958270787173005469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045349305513858115336979 4568023958270787173005469)
      ·
        refine ⟨1713008984351545189877051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4568023958270787173005469 1713008984351545189877051)
        ·
          refine ⟨2569513476527317784815577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1713008984351545189877051 2569513476527317784815577)
          ·
            refine ⟨1927135107395488338611683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2569513476527317784815577 1927135107395488338611683)
            ·
              refine ⟨2890702661093232507917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1927135107395488338611683 2890702661093232507917525)
              ·
                refine ⟨67750843619372636904317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2890702661093232507917525 67750843619372636904317)
                ·
                  refine ⟨25406566357264738839119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67750843619372636904317 25406566357264738839119)
                  ·
                    rfl

theorem cell21_111328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 3].length) (baseStart_111328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111328 prefixEnd_111328 := by exact prefixLift 111328
  have htrace : WordTrace (prefixWord ++ tailWord_111328) baseStart_111328 baseEnd_111328 := by
    simpa [prefixWord, tailWord_111328, baseEnd_111328] using wordTrace_append hprefix tailTrace_111328
  have hstable : (prefixWord ++ tailWord_111328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111328).length < 2 ^ (prefixWord ++ tailWord_111328).sum := by decide
  have hdescent : baseEnd_111328 < baseStart_111328 := by decide
  rcases family_descends (prefixWord ++ tailWord_111328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111348 : List Nat := [2, 6, 1, 1, 2, 2, 1, 6]
def baseStart_111348 : Nat := 118140960795 + 111348 * 2 ^ 59
def prefixEnd_111348 : Nat := 4983230072969 + 3 ^ 40 * 111348 * 2
def baseEnd_111348 : Nat := 8470376876583049501915

theorem tailTrace_111348 : CollatzResearch.WordTrace tailWord_111348 prefixEnd_111348 8470376876583049501915 := by
  unfold tailWord_111348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030597600306343784755349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2707463467075125046340465 2030597600306343784755349)
  ·
    refine ⟨95184262514359864910407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2030597600306343784755349 95184262514359864910407)
    ·
      refine ⟨142776393771539797365611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95184262514359864910407 142776393771539797365611)
      ·
        refine ⟨214164590657309696048417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142776393771539797365611 214164590657309696048417)
        ·
          refine ⟨160623442992982272036313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 214164590657309696048417 160623442992982272036313)
          ·
            refine ⟨120467582244736704027235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160623442992982272036313 120467582244736704027235)
            ·
              refine ⟨180701373367105056040853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120467582244736704027235 180701373367105056040853)
              ·
                refine ⟨8470376876583049501915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180701373367105056040853 8470376876583049501915)
                ·
                  rfl

theorem cell21_111348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 6].length) (baseStart_111348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111348 prefixEnd_111348 := by exact prefixLift 111348
  have htrace : WordTrace (prefixWord ++ tailWord_111348) baseStart_111348 baseEnd_111348 := by
    simpa [prefixWord, tailWord_111348, baseEnd_111348] using wordTrace_append hprefix tailTrace_111348
  have hstable : (prefixWord ++ tailWord_111348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111348).length < 2 ^ (prefixWord ++ tailWord_111348).sum := by decide
  have hdescent : baseEnd_111348 < baseStart_111348 := by decide
  rcases family_descends (prefixWord ++ tailWord_111348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111401 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_111401 : Nat := 118140960795 + 111401 * 2 ^ 59
def prefixEnd_111401 : Nat := 4983230072969 + 3 ^ 40 * 111401 * 2
def baseEnd_111401 : Nat := 25423225951832834122303

theorem tailTrace_111401 : CollatzResearch.WordTrace tailWord_111401 prefixEnd_111401 25423225951832834122303 := by
  unfold tailWord_111401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063128269420677621190057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2708752179613785080793371 4063128269420677621190057)
  ·
    refine ⟨3047346202065508215892543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063128269420677621190057 3047346202065508215892543)
    ·
      refine ⟨4571019303098262323838815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047346202065508215892543 4571019303098262323838815)
      ·
        refine ⟨6856528954647393485758223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4571019303098262323838815 6856528954647393485758223)
        ·
          refine ⟨10284793431971090228637335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6856528954647393485758223 10284793431971090228637335)
          ·
            refine ⟨15427190147956635342956003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10284793431971090228637335 15427190147956635342956003)
            ·
              refine ⟨23140785221934953014434005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15427190147956635342956003 23140785221934953014434005)
              ·
                refine ⟨542362153639100461275797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23140785221934953014434005 542362153639100461275797)
                ·
                  refine ⟨25423225951832834122303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 542362153639100461275797 25423225951832834122303)
                  ·
                    rfl

theorem cell21_111401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_111401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111401 prefixEnd_111401 := by exact prefixLift 111401
  have htrace : WordTrace (prefixWord ++ tailWord_111401) baseStart_111401 baseEnd_111401 := by
    simpa [prefixWord, tailWord_111401, baseEnd_111401] using wordTrace_append hprefix tailTrace_111401
  have hstable : (prefixWord ++ tailWord_111401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111401).length < 2 ^ (prefixWord ++ tailWord_111401).sum := by decide
  have hdescent : baseEnd_111401 < baseStart_111401 := by decide
  rcases family_descends (prefixWord ++ tailWord_111401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111404 : List Nat := [2, 2, 1, 1, 1, 4, 1, 6, 3]
def baseStart_111404 : Nat := 118140960795 + 111404 * 2 ^ 59
def prefixEnd_111404 : Nat := 4983230072969 + 3 ^ 40 * 111404 * 2
def baseEnd_111404 : Nat := 25423910592705495572297

theorem tailTrace_111404 : CollatzResearch.WordTrace tailWord_111404 prefixEnd_111404 25423910592705495572297 := by
  unfold tailWord_111404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031618844204904566774633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2708825125606539422366177 2031618844204904566774633)
  ·
    refine ⟨1523714133153678425080975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2031618844204904566774633 1523714133153678425080975)
    ·
      refine ⟨2285571199730517637621463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523714133153678425080975 2285571199730517637621463)
      ·
        refine ⟨3428356799595776456432195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2285571199730517637621463 3428356799595776456432195)
        ·
          refine ⟨5142535199393664684648293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3428356799595776456432195 5142535199393664684648293)
          ·
            refine ⟨964225349886312128371555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5142535199393664684648293 964225349886312128371555)
            ·
              refine ⟨1446338024829468192557333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964225349886312128371555 1446338024829468192557333)
              ·
                refine ⟨67797094913881321526125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1446338024829468192557333 67797094913881321526125)
                ·
                  refine ⟨25423910592705495572297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67797094913881321526125 25423910592705495572297)
                  ·
                    rfl

theorem cell21_111404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 6, 3].length) (baseStart_111404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111404 prefixEnd_111404 := by exact prefixLift 111404
  have htrace : WordTrace (prefixWord ++ tailWord_111404) baseStart_111404 baseEnd_111404 := by
    simpa [prefixWord, tailWord_111404, baseEnd_111404] using wordTrace_append hprefix tailTrace_111404
  have hstable : (prefixWord ++ tailWord_111404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111404).length < 2 ^ (prefixWord ++ tailWord_111404).sum := by decide
  have hdescent : baseEnd_111404 < baseStart_111404 := by decide
  rcases family_descends (prefixWord ++ tailWord_111404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111432 : List Nat := [2, 1, 3, 1, 1, 3, 3, 7]
def baseStart_111432 : Nat := 118140960795 + 111432 * 2 ^ 59
def prefixEnd_111432 : Nat := 4983230072969 + 3 ^ 40 * 111432 * 2
def baseEnd_111432 : Nat := 8476766858061223035191

theorem tailTrace_111432 : CollatzResearch.WordTrace tailWord_111432 prefixEnd_111432 8476766858061223035191 := by
  unfold tailWord_111432
  simp only [CollatzResearch.WordTrace]
  refine ⟨2032129466154184957784275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2709505954872246610379033 2032129466154184957784275)
  ·
    refine ⟨3048194199231277436676413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2032129466154184957784275 3048194199231277436676413)
    ·
      refine ⟨1143072824711729038753655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3048194199231277436676413 1143072824711729038753655)
      ·
        refine ⟨1714609237067593558130483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143072824711729038753655 1714609237067593558130483)
        ·
          refine ⟨2571913855601390337195725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714609237067593558130483 2571913855601390337195725)
          ·
            refine ⟨964467695850521376448397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2571913855601390337195725 964467695850521376448397)
            ·
              refine ⟨361675385943945516168149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964467695850521376448397 361675385943945516168149)
              ·
                refine ⟨8476766858061223035191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 361675385943945516168149 8476766858061223035191)
                ·
                  rfl

theorem cell21_111432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 7].length) (baseStart_111432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111432 prefixEnd_111432 := by exact prefixLift 111432
  have htrace : WordTrace (prefixWord ++ tailWord_111432) baseStart_111432 baseEnd_111432 := by
    simpa [prefixWord, tailWord_111432, baseEnd_111432] using wordTrace_append hprefix tailTrace_111432
  have hstable : (prefixWord ++ tailWord_111432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111432).length < 2 ^ (prefixWord ++ tailWord_111432).sum := by decide
  have hdescent : baseEnd_111432 < baseStart_111432 := by decide
  rcases family_descends (prefixWord ++ tailWord_111432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111587 : List Nat := [1, 1, 1, 6, 1, 1, 5, 1, 4]
def baseStart_111587 : Nat := 118140960795 + 111587 * 2 ^ 59
def prefixEnd_111587 : Nat := 4983230072969 + 3 ^ 40 * 111587 * 2
def baseEnd_111587 : Nat := 25465673685937844021923

theorem tailTrace_111587 : CollatzResearch.WordTrace tailWord_111587 prefixEnd_111587 25465673685937844021923 := by
  unfold tailWord_111587
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069912246746831387461015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2713274831164554258307343 4069912246746831387461015)
  ·
    refine ⟨6104868370120247081191523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4069912246746831387461015 6104868370120247081191523)
    ·
      refine ⟨9157302555180370621787285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6104868370120247081191523 9157302555180370621787285)
      ·
        refine ⟨429248557274079872896279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9157302555180370621787285 429248557274079872896279)
        ·
          refine ⟨643872835911119809344419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429248557274079872896279 643872835911119809344419)
          ·
            refine ⟨965809253866679714016629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643872835911119809344419 965809253866679714016629)
            ·
              refine ⟨90544617550001223189059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 965809253866679714016629 90544617550001223189059)
              ·
                refine ⟨135816926325001834783589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90544617550001223189059 135816926325001834783589)
                ·
                  refine ⟨25465673685937844021923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135816926325001834783589 25465673685937844021923)
                  ·
                    rfl

theorem cell21_111587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_111587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111587 prefixEnd_111587 := by exact prefixLift 111587
  have htrace : WordTrace (prefixWord ++ tailWord_111587) baseStart_111587 baseEnd_111587 := by
    simpa [prefixWord, tailWord_111587, baseEnd_111587] using wordTrace_append hprefix tailTrace_111587
  have hstable : (prefixWord ++ tailWord_111587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111587).length < 2 ^ (prefixWord ++ tailWord_111587).sum := by decide
  have hdescent : baseEnd_111587 < baseStart_111587 := by decide
  rcases family_descends (prefixWord ++ tailWord_111587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111601 : List Nat := [1, 2, 2, 2, 4, 1, 4, 5]
def baseStart_111601 : Nat := 118140960795 + 111601 * 2 ^ 59
def prefixEnd_111601 : Nat := 4983230072969 + 3 ^ 40 * 111601 * 2
def baseEnd_111601 : Nat := 8489622892225643596187

theorem tailTrace_111601 : CollatzResearch.WordTrace tailWord_111601 prefixEnd_111601 8489622892225643596187 := by
  unfold tailWord_111601
  simp only [CollatzResearch.WordTrace]
  refine ⟨4070422868696111778470657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2713615245797407852313771 4070422868696111778470657)
  ·
    refine ⟨3052817151522083833852993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4070422868696111778470657 3052817151522083833852993)
    ·
      refine ⟨2289612863641562875389745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3052817151522083833852993 2289612863641562875389745)
      ·
        refine ⟨1717209647731172156542309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2289612863641562875389745 1717209647731172156542309)
        ·
          refine ⟨321976808949594779351683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1717209647731172156542309 321976808949594779351683)
          ·
            refine ⟨482965213424392169027525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321976808949594779351683 482965213424392169027525)
            ·
              refine ⟨90555977517073531692661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 482965213424392169027525 90555977517073531692661)
              ·
                refine ⟨8489622892225643596187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90555977517073531692661 8489622892225643596187)
                ·
                  rfl

theorem cell21_111601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 5].length) (baseStart_111601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111601 prefixEnd_111601 := by exact prefixLift 111601
  have htrace : WordTrace (prefixWord ++ tailWord_111601) baseStart_111601 baseEnd_111601 := by
    simpa [prefixWord, tailWord_111601, baseEnd_111601] using wordTrace_append hprefix tailTrace_111601
  have hstable : (prefixWord ++ tailWord_111601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111601).length < 2 ^ (prefixWord ++ tailWord_111601).sum := by decide
  have hdescent : baseEnd_111601 < baseStart_111601 := by decide
  rcases family_descends (prefixWord ++ tailWord_111601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111725 : List Nat := [1, 5, 1, 1, 2, 3, 2, 3, 3]
def baseStart_111725 : Nat := 118140960795 + 111725 * 2 ^ 59
def prefixEnd_111725 : Nat := 4983230072969 + 3 ^ 40 * 111725 * 2
def baseEnd_111725 : Nat := 25497167166080270721641

theorem tailTrace_111725 : CollatzResearch.WordTrace tailWord_111725 prefixEnd_111725 25497167166080270721641 := by
  unfold tailWord_111725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074945520246880955984629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2716630346831253970656419 4074945520246880955984629)
  ·
    refine ⟨382026142523145089623559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4074945520246880955984629 382026142523145089623559)
    ·
      refine ⟨573039213784717634435339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382026142523145089623559 573039213784717634435339)
      ·
        refine ⟨859558820677076451653009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573039213784717634435339 859558820677076451653009)
        ·
          refine ⟨644669115507807338739757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859558820677076451653009 644669115507807338739757)
          ·
            refine ⟨241750918315427752027409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644669115507807338739757 241750918315427752027409)
            ·
              refine ⟨181313188736570814020557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241750918315427752027409 181313188736570814020557)
              ·
                refine ⟨67992445776214055257709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 181313188736570814020557 67992445776214055257709)
                ·
                  refine ⟨25497167166080270721641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67992445776214055257709 25497167166080270721641)
                  ·
                    rfl

theorem cell21_111725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_111725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111725 prefixEnd_111725 := by exact prefixLift 111725
  have htrace : WordTrace (prefixWord ++ tailWord_111725) baseStart_111725 baseEnd_111725 := by
    simpa [prefixWord, tailWord_111725, baseEnd_111725] using wordTrace_append hprefix tailTrace_111725
  have hstable : (prefixWord ++ tailWord_111725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111725).length < 2 ^ (prefixWord ++ tailWord_111725).sum := by decide
  have hdescent : baseEnd_111725 < baseStart_111725 := by decide
  rcases family_descends (prefixWord ++ tailWord_111725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111767 : List Nat := [1, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_111767 : Nat := 118140960795 + 111767 * 2 ^ 59
def prefixEnd_111767 : Nat := 4983230072969 + 3 ^ 40 * 111767 * 2
def baseEnd_111767 : Nat := 25506752138297531021555

theorem tailTrace_111767 : CollatzResearch.WordTrace tailWord_111767 prefixEnd_111767 25506752138297531021555 := by
  unfold tailWord_111767
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076477386094722129013555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2717651590729814752675703 4076477386094722129013555)
  ·
    refine ⟨6114716079142083193520333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4076477386094722129013555 6114716079142083193520333)
    ·
      refine ⟨2293018529678281197570125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6114716079142083193520333 2293018529678281197570125)
      ·
        refine ⟨859881948629355449088797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2293018529678281197570125 859881948629355449088797)
        ·
          refine ⟨322455730736008293408299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 859881948629355449088797 322455730736008293408299)
          ·
            refine ⟨483683596104012440112449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322455730736008293408299 483683596104012440112449)
            ·
              refine ⟨362762697078009330084337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483683596104012440112449 362762697078009330084337)
              ·
                refine ⟨272072022808506997563253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 362762697078009330084337 272072022808506997563253)
                ·
                  refine ⟨25506752138297531021555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272072022808506997563253 25506752138297531021555)
                  ·
                    rfl

theorem cell21_111767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_111767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111767 prefixEnd_111767 := by exact prefixLift 111767
  have htrace : WordTrace (prefixWord ++ tailWord_111767) baseStart_111767 baseEnd_111767 := by
    simpa [prefixWord, tailWord_111767, baseEnd_111767] using wordTrace_append hprefix tailTrace_111767
  have hstable : (prefixWord ++ tailWord_111767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111767).length < 2 ^ (prefixWord ++ tailWord_111767).sum := by decide
  have hdescent : baseEnd_111767 < baseStart_111767 := by decide
  rcases family_descends (prefixWord ++ tailWord_111767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111770 : List Nat := [3, 1, 1, 5, 1, 3, 2, 5]
def baseStart_111770 : Nat := 118140960795 + 111770 * 2 ^ 59
def prefixEnd_111770 : Nat := 4983230072969 + 3 ^ 40 * 111770 * 2
def baseEnd_111770 : Nat := 8502478926390064157183

theorem tailTrace_111770 : CollatzResearch.WordTrace tailWord_111770 prefixEnd_111770 8502478926390064157183 := by
  unfold tailWord_111770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019146701270963410343191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2717724536722569094248509 1019146701270963410343191)
  ·
    refine ⟨1528720051906445115514787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1019146701270963410343191 1528720051906445115514787)
    ·
      refine ⟨2293080077859667673272181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528720051906445115514787 2293080077859667673272181)
      ·
        refine ⟨214976257299343844369267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2293080077859667673272181 214976257299343844369267)
        ·
          refine ⟨322464385949015766553901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214976257299343844369267 322464385949015766553901)
          ·
            refine ⟨120924144730880912457713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322464385949015766553901 120924144730880912457713)
            ·
              refine ⟨90693108548160684343285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120924144730880912457713 90693108548160684343285)
              ·
                refine ⟨8502478926390064157183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90693108548160684343285 8502478926390064157183)
                ·
                  rfl

theorem cell21_111770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_111770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111770 prefixEnd_111770 := by exact prefixLift 111770
  have htrace : WordTrace (prefixWord ++ tailWord_111770) baseStart_111770 baseEnd_111770 := by
    simpa [prefixWord, tailWord_111770, baseEnd_111770] using wordTrace_append hprefix tailTrace_111770
  have hstable : (prefixWord ++ tailWord_111770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111770).length < 2 ^ (prefixWord ++ tailWord_111770).sum := by decide
  have hdescent : baseEnd_111770 < baseStart_111770 := by decide
  rcases family_descends (prefixWord ++ tailWord_111770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111781 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 6]
def baseStart_111781 : Nat := 118140960795 + 111781 * 2 ^ 59
def prefixEnd_111781 : Nat := 4983230072969 + 3 ^ 40 * 111781 * 2
def baseEnd_111781 : Nat := 25509947129036617788193

theorem tailTrace_111781 : CollatzResearch.WordTrace tailWord_111781 prefixEnd_111781 25509947129036617788193 := by
  unfold tailWord_111781
  simp only [CollatzResearch.WordTrace]
  refine ⟨4076988008044002520023197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2717992005362668346682131 4076988008044002520023197)
  ·
    refine ⟨1528870503016500945008699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4076988008044002520023197 1528870503016500945008699)
    ·
      refine ⟨2293305754524751417513049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1528870503016500945008699 2293305754524751417513049)
      ·
        refine ⟨1719979315893563563134787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2293305754524751417513049 1719979315893563563134787)
        ·
          refine ⟨2579968973840345344702181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1719979315893563563134787 2579968973840345344702181)
          ·
            refine ⟨483744182595064752131659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2579968973840345344702181 483744182595064752131659)
            ·
              refine ⟨725616273892597128197489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483744182595064752131659 725616273892597128197489)
              ·
                refine ⟨544212205419447846148117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 725616273892597128197489 544212205419447846148117)
                ·
                  refine ⟨25509947129036617788193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 544212205419447846148117 25509947129036617788193)
                  ·
                    rfl

theorem cell21_111781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_111781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111781 prefixEnd_111781 := by exact prefixLift 111781
  have htrace : WordTrace (prefixWord ++ tailWord_111781) baseStart_111781 baseEnd_111781 := by
    simpa [prefixWord, tailWord_111781, baseEnd_111781] using wordTrace_append hprefix tailTrace_111781
  have hstable : (prefixWord ++ tailWord_111781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111781).length < 2 ^ (prefixWord ++ tailWord_111781).sum := by decide
  have hdescent : baseEnd_111781 < baseStart_111781 := by decide
  rcases family_descends (prefixWord ++ tailWord_111781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111795 : List Nat := [1, 1, 1, 2, 3, 2, 11]
def baseStart_111795 : Nat := 118140960795 + 111795 * 2 ^ 59
def prefixEnd_111795 : Nat := 4983230072969 + 3 ^ 40 * 111795 * 2
def baseEnd_111795 : Nat := 2834793568863967172759

theorem tailTrace_111795 : CollatzResearch.WordTrace tailWord_111795 prefixEnd_111795 2834793568863967172759 := by
  unfold tailWord_111795
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077498629993282911032839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718332419995521940688559 4077498629993282911032839)
  ·
    refine ⟨6116247944989924366549259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4077498629993282911032839 6116247944989924366549259)
    ·
      refine ⟨9174371917484886549823889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116247944989924366549259 9174371917484886549823889)
      ·
        refine ⟨6880778938113664912367917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9174371917484886549823889 6880778938113664912367917)
        ·
          refine ⟨2580292101792624342137969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6880778938113664912367917 2580292101792624342137969)
          ·
            refine ⟨1935219076344468256603477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2580292101792624342137969 1935219076344468256603477)
            ·
              refine ⟨2834793568863967172759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1935219076344468256603477 2834793568863967172759)
              ·
                rfl

theorem cell21_111795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_111795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111795 prefixEnd_111795 := by exact prefixLift 111795
  have htrace : WordTrace (prefixWord ++ tailWord_111795) baseStart_111795 baseEnd_111795 := by
    simpa [prefixWord, tailWord_111795, baseEnd_111795] using wordTrace_append hprefix tailTrace_111795
  have hstable : (prefixWord ++ tailWord_111795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111795).length < 2 ^ (prefixWord ++ tailWord_111795).sum := by decide
  have hdescent : baseEnd_111795 < baseStart_111795 := by decide
  rcases family_descends (prefixWord ++ tailWord_111795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111801 : List Nat := [1, 2, 1, 4, 1, 4, 3, 2, 3]
def baseStart_111801 : Nat := 118140960795 + 111801 * 2 ^ 59
def prefixEnd_111801 : Nat := 4983230072969 + 3 ^ 40 * 111801 * 2
def baseEnd_111801 : Nat := 25514511401521027454819

theorem tailTrace_111801 : CollatzResearch.WordTrace tailWord_111801 prefixEnd_111801 25514511401521027454819 := by
  unfold tailWord_111801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4077717467971545935751257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718478311981030623834171 4077717467971545935751257)
  ·
    refine ⟨3058288100978659451813443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4077717467971545935751257 3058288100978659451813443)
    ·
      refine ⟨4587432151467989177720165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058288100978659451813443 4587432151467989177720165)
      ·
        refine ⟨860143528400247970822531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4587432151467989177720165 860143528400247970822531)
        ·
          refine ⟨1290215292600371956233797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860143528400247970822531 1290215292600371956233797)
          ·
            refine ⟨241915367362569741793837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1290215292600371956233797 241915367362569741793837)
            ·
              refine ⟨90718262760963653172689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241915367362569741793837 90718262760963653172689)
              ·
                refine ⟨68038697070722739879517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90718262760963653172689 68038697070722739879517)
                ·
                  refine ⟨25514511401521027454819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68038697070722739879517 25514511401521027454819)
                  ·
                    rfl

theorem cell21_111801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 3].length) (baseStart_111801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_111801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_111801 prefixEnd_111801 := by exact prefixLift 111801
  have htrace : WordTrace (prefixWord ++ tailWord_111801) baseStart_111801 baseEnd_111801 := by
    simpa [prefixWord, tailWord_111801, baseEnd_111801] using wordTrace_append hprefix tailTrace_111801
  have hstable : (prefixWord ++ tailWord_111801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111801).length < 2 ^ (prefixWord ++ tailWord_111801).sum := by decide
  have hdescent : baseEnd_111801 < baseStart_111801 := by decide
  rcases family_descends (prefixWord ++ tailWord_111801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112026 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_112026 : Nat := 118140960795 + 112026 * 2 ^ 59
def prefixEnd_112026 : Nat := 4983230072969 + 3 ^ 40 * 112026 * 2
def baseEnd_112026 : Nat := 25565859466970636204359

theorem tailTrace_112026 : CollatzResearch.WordTrace tailWord_112026 prefixEnd_112026 25565859466970636204359 := by
  unfold tailWord_112026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021480973039102340672983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2723949261437606241794621 1021480973039102340672983)
  ·
    refine ⟨1532221459558653511009475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1021480973039102340672983 1532221459558653511009475)
    ·
      refine ⟨2298332189337980266514213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532221459558653511009475 2298332189337980266514213)
      ·
        refine ⟨430937285500871299971415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2298332189337980266514213 430937285500871299971415)
        ·
          refine ⟨646405928251306949957123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430937285500871299971415 646405928251306949957123)
          ·
            refine ⟨969608892376960424935685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646405928251306949957123 969608892376960424935685)
            ·
              refine ⟨181801667320680079675441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 969608892376960424935685 181801667320680079675441)
              ·
                refine ⟨136351250490510059756581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181801667320680079675441 136351250490510059756581)
                ·
                  refine ⟨25565859466970636204359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136351250490510059756581 25565859466970636204359)
                  ·
                    rfl

theorem cell21_112026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_112026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112026 prefixEnd_112026 := by exact prefixLift 112026
  have htrace : WordTrace (prefixWord ++ tailWord_112026) baseStart_112026 baseEnd_112026 := by
    simpa [prefixWord, tailWord_112026, baseEnd_112026] using wordTrace_append hprefix tailTrace_112026
  have hstable : (prefixWord ++ tailWord_112026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112026).length < 2 ^ (prefixWord ++ tailWord_112026).sum := by decide
  have hdescent : baseEnd_112026 < baseStart_112026 := by decide
  rcases family_descends (prefixWord ++ tailWord_112026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112029 : List Nat := [1, 4, 2, 1, 3, 1, 4, 2, 3]
def baseStart_112029 : Nat := 118140960795 + 112029 * 2 ^ 59
def prefixEnd_112029 : Nat := 4983230072969 + 3 ^ 40 * 112029 * 2
def baseEnd_112029 : Nat := 25566544107843297654353

theorem tailTrace_112029 : CollatzResearch.WordTrace tailWord_112029 prefixEnd_112029 25566544107843297654353 := by
  unfold tailWord_112029
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086033311145540875051141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2724022207430360583367427 4086033311145540875051141)
  ·
    refine ⟨766131245839788914072089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4086033311145540875051141 766131245839788914072089)
    ·
      refine ⟨574598434379841685554067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766131245839788914072089 574598434379841685554067)
      ·
        refine ⟨861897651569762528331101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574598434379841685554067 861897651569762528331101)
        ·
          refine ⟨323211619338660948124163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861897651569762528331101 323211619338660948124163)
          ·
            refine ⟨484817429007991422186245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323211619338660948124163 484817429007991422186245)
            ·
              refine ⟨90903267938998391659921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 484817429007991422186245 90903267938998391659921)
              ·
                refine ⟨68177450954248793744941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90903267938998391659921 68177450954248793744941)
                ·
                  refine ⟨25566544107843297654353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68177450954248793744941 25566544107843297654353)
                  ·
                    rfl

theorem cell21_112029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_112029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112029 prefixEnd_112029 := by exact prefixLift 112029
  have htrace : WordTrace (prefixWord ++ tailWord_112029) baseStart_112029 baseEnd_112029 := by
    simpa [prefixWord, tailWord_112029, baseEnd_112029] using wordTrace_append hprefix tailTrace_112029
  have hstable : (prefixWord ++ tailWord_112029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112029).length < 2 ^ (prefixWord ++ tailWord_112029).sum := by decide
  have hdescent : baseEnd_112029 < baseStart_112029 := by decide
  rcases family_descends (prefixWord ++ tailWord_112029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112057 : List Nat := [1, 2, 1, 4, 4, 1, 3, 5]
def baseStart_112057 : Nat := 118140960795 + 112057 * 2 ^ 59
def prefixEnd_112057 : Nat := 4983230072969 + 3 ^ 40 * 112057 * 2
def baseEnd_112057 : Nat := 8524311363107157062543

theorem tailTrace_112057 : CollatzResearch.WordTrace tailWord_112057 prefixEnd_112057 8524311363107157062543 := by
  unfold tailWord_112057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4087054555044101657070425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2724703036696067771380283 4087054555044101657070425)
  ·
    refine ⟨3065290916283076242802819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4087054555044101657070425 3065290916283076242802819)
    ·
      refine ⟨4597936374424614364204229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3065290916283076242802819 4597936374424614364204229)
      ·
        refine ⟨862113070204615193288293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4597936374424614364204229 862113070204615193288293)
        ·
          refine ⟨161646200663365348741555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862113070204615193288293 161646200663365348741555)
          ·
            refine ⟨242469300995048023112333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161646200663365348741555 242469300995048023112333)
            ·
              refine ⟨90925987873143008667125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242469300995048023112333 90925987873143008667125)
              ·
                refine ⟨8524311363107157062543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90925987873143008667125 8524311363107157062543)
                ·
                  rfl

theorem cell21_112057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 5].length) (baseStart_112057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112057 prefixEnd_112057 := by exact prefixLift 112057
  have htrace : WordTrace (prefixWord ++ tailWord_112057) baseStart_112057 baseEnd_112057 := by
    simpa [prefixWord, tailWord_112057, baseEnd_112057] using wordTrace_append hprefix tailTrace_112057
  have hstable : (prefixWord ++ tailWord_112057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112057).length < 2 ^ (prefixWord ++ tailWord_112057).sum := by decide
  have hdescent : baseEnd_112057 < baseStart_112057 := by decide
  rcases family_descends (prefixWord ++ tailWord_112057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112085 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_112085 : Nat := 118140960795 + 112085 * 2 ^ 59
def prefixEnd_112085 : Nat := 4983230072969 + 3 ^ 40 * 112085 * 2
def baseEnd_112085 : Nat := 25579324070799644720905

theorem tailTrace_112085 : CollatzResearch.WordTrace tailWord_112085 prefixEnd_112085 25579324070799644720905 := by
  unfold tailWord_112085
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088075798942662439089709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2725383865961774959393139 4088075798942662439089709)
  ·
    refine ⟨1533028424603498414658641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4088075798942662439089709 1533028424603498414658641)
    ·
      refine ⟨1149771318452623810993981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533028424603498414658641 1149771318452623810993981)
      ·
        refine ⟨431164244419733929122743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1149771318452623810993981 431164244419733929122743)
        ·
          refine ⟨646746366629600893684115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431164244419733929122743 646746366629600893684115)
          ·
            refine ⟨970119549944401340526173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 646746366629600893684115 970119549944401340526173)
            ·
              refine ⟨363794831229150502697315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 970119549944401340526173 363794831229150502697315)
              ·
                refine ⟨545692246843725754045973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363794831229150502697315 545692246843725754045973)
                ·
                  refine ⟨25579324070799644720905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 545692246843725754045973 25579324070799644720905)
                  ·
                    rfl

theorem cell21_112085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_112085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112085 prefixEnd_112085 := by exact prefixLift 112085
  have htrace : WordTrace (prefixWord ++ tailWord_112085) baseStart_112085 baseEnd_112085 := by
    simpa [prefixWord, tailWord_112085, baseEnd_112085] using wordTrace_append hprefix tailTrace_112085
  have hstable : (prefixWord ++ tailWord_112085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112085).length < 2 ^ (prefixWord ++ tailWord_112085).sum := by decide
  have hdescent : baseEnd_112085 < baseStart_112085 := by decide
  rcases family_descends (prefixWord ++ tailWord_112085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112147 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 5]
def baseStart_112147 : Nat := 118140960795 + 112147 * 2 ^ 59
def prefixEnd_112147 : Nat := 4983230072969 + 3 ^ 40 * 112147 * 2
def baseEnd_112147 : Nat := 25593473315501314687445

theorem tailTrace_112147 : CollatzResearch.WordTrace tailWord_112147 prefixEnd_112147 25593473315501314687445 := by
  unfold tailWord_112147
  simp only [CollatzResearch.WordTrace]
  refine ⟨4090337124718047027846695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2726891416478698018564463 4090337124718047027846695)
  ·
    refine ⟨6135505687077070541770043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4090337124718047027846695 6135505687077070541770043)
    ·
      refine ⟨9203258530615605812655065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6135505687077070541770043 9203258530615605812655065)
      ·
        refine ⟨6902443897961704359491299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9203258530615605812655065 6902443897961704359491299)
        ·
          refine ⟨10353665846942556539236949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6902443897961704359491299 10353665846942556539236949)
          ·
            refine ⟨121332021643858084444183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 10353665846942556539236949 121332021643858084444183)
            ·
              refine ⟨181998032465787126666275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121332021643858084444183 181998032465787126666275)
              ·
                refine ⟨272997048698680689999413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 181998032465787126666275 272997048698680689999413)
                ·
                  refine ⟨25593473315501314687445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 272997048698680689999413 25593473315501314687445)
                  ·
                    rfl

theorem cell21_112147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 5].length) (baseStart_112147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112147 prefixEnd_112147 := by exact prefixLift 112147
  have htrace : WordTrace (prefixWord ++ tailWord_112147) baseStart_112147 baseEnd_112147 := by
    simpa [prefixWord, tailWord_112147, baseEnd_112147] using wordTrace_append hprefix tailTrace_112147
  have hstable : (prefixWord ++ tailWord_112147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112147).length < 2 ^ (prefixWord ++ tailWord_112147).sum := by decide
  have hdescent : baseEnd_112147 < baseStart_112147 := by decide
  rcases family_descends (prefixWord ++ tailWord_112147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112198 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_112198 : Nat := 118140960795 + 112198 * 2 ^ 59
def prefixEnd_112198 : Nat := 4983230072969 + 3 ^ 40 * 112198 * 2
def baseEnd_112198 : Nat := 25605112210336559337341

theorem tailTrace_112198 : CollatzResearch.WordTrace tailWord_112198 prefixEnd_112198 25605112210336559337341 := by
  unfold tailWord_112198
  simp only [CollatzResearch.WordTrace]
  refine ⟨127881163985415085561039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2728131498355521825302165 127881163985415085561039)
  ·
    refine ⟨191821745978122628341559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 127881163985415085561039 191821745978122628341559)
    ·
      refine ⟨287732618967183942512339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191821745978122628341559 287732618967183942512339)
      ·
        refine ⟨431598928450775913768509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287732618967183942512339 431598928450775913768509)
        ·
          refine ⟨161849598169040967663191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431598928450775913768509 161849598169040967663191)
          ·
            refine ⟨242774397253561451494787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161849598169040967663191 242774397253561451494787)
            ·
              refine ⟨364161595880342177242181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242774397253561451494787 364161595880342177242181)
              ·
                refine ⟨68280299227564158232909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 364161595880342177242181 68280299227564158232909)
                ·
                  refine ⟨25605112210336559337341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68280299227564158232909 25605112210336559337341)
                  ·
                    rfl

theorem cell21_112198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_112198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112198 prefixEnd_112198 := by exact prefixLift 112198
  have htrace : WordTrace (prefixWord ++ tailWord_112198) baseStart_112198 baseEnd_112198 := by
    simpa [prefixWord, tailWord_112198, baseEnd_112198] using wordTrace_append hprefix tailTrace_112198
  have hstable : (prefixWord ++ tailWord_112198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112198).length < 2 ^ (prefixWord ++ tailWord_112198).sum := by decide
  have hdescent : baseEnd_112198 < baseStart_112198 := by decide
  rcases family_descends (prefixWord ++ tailWord_112198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112206 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_112206 : Nat := 118140960795 + 112206 * 2 ^ 59
def prefixEnd_112206 : Nat := 4983230072969 + 3 ^ 40 * 112206 * 2
def baseEnd_112206 : Nat := 25606937919330323203991

theorem tailTrace_112206 : CollatzResearch.WordTrace tailWord_112206 prefixEnd_112206 25606937919330323203991 := by
  unfold tailWord_112206
  simp only [CollatzResearch.WordTrace]
  refine ⟨511561128938037513030559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2728326021002866736162981 511561128938037513030559)
  ·
    refine ⟨767341693407056269545839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511561128938037513030559 767341693407056269545839)
    ·
      refine ⟨1151012540110584404318759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 767341693407056269545839 1151012540110584404318759)
      ·
        refine ⟨1726518810165876606478139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1151012540110584404318759 1726518810165876606478139)
        ·
          refine ⟨2589778215248814909717209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726518810165876606478139 2589778215248814909717209)
          ·
            refine ⟨1942333661436611182287907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2589778215248814909717209 1942333661436611182287907)
            ·
              refine ⟨2913500492154916773431861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1942333661436611182287907 2913500492154916773431861)
              ·
                refine ⟨273140671139523447509237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2913500492154916773431861 273140671139523447509237)
                ·
                  refine ⟨25606937919330323203991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273140671139523447509237 25606937919330323203991)
                  ·
                    rfl

theorem cell21_112206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_112206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112206 prefixEnd_112206 := by exact prefixLift 112206
  have htrace : WordTrace (prefixWord ++ tailWord_112206) baseStart_112206 baseEnd_112206 := by
    simpa [prefixWord, tailWord_112206, baseEnd_112206] using wordTrace_append hprefix tailTrace_112206
  have hstable : (prefixWord ++ tailWord_112206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112206).length < 2 ^ (prefixWord ++ tailWord_112206).sum := by decide
  have hdescent : baseEnd_112206 < baseStart_112206 := by decide
  rcases family_descends (prefixWord ++ tailWord_112206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112240 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 3]
def baseStart_112240 : Nat := 118140960795 + 112240 * 2 ^ 59
def prefixEnd_112240 : Nat := 4983230072969 + 3 ^ 40 * 112240 * 2
def baseEnd_112240 : Nat := 25614697182553819637255

theorem tailTrace_112240 : CollatzResearch.WordTrace tailWord_112240 prefixEnd_112240 25614697182553819637255 := by
  unfold tailWord_112240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046864556690561955491087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2729152742254082607321449 2046864556690561955491087)
  ·
    refine ⟨3070296835035842933236631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046864556690561955491087 3070296835035842933236631)
    ·
      refine ⟨4605445252553764399854947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070296835035842933236631 4605445252553764399854947)
      ·
        refine ⟨6908167878830646599782421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605445252553764399854947 6908167878830646599782421)
        ·
          refine ⟨323820369320186559364801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6908167878830646599782421 323820369320186559364801)
          ·
            refine ⟨242865276990139919523601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323820369320186559364801 242865276990139919523601)
            ·
              refine ⟨182148957742604939642701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242865276990139919523601 182148957742604939642701)
              ·
                refine ⟨68305859153476852366013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182148957742604939642701 68305859153476852366013)
                ·
                  refine ⟨25614697182553819637255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68305859153476852366013 25614697182553819637255)
                  ·
                    rfl

theorem cell21_112240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 3].length) (baseStart_112240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112240 prefixEnd_112240 := by exact prefixLift 112240
  have htrace : WordTrace (prefixWord ++ tailWord_112240) baseStart_112240 baseEnd_112240 := by
    simpa [prefixWord, tailWord_112240, baseEnd_112240] using wordTrace_append hprefix tailTrace_112240
  have hstable : (prefixWord ++ tailWord_112240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112240).length < 2 ^ (prefixWord ++ tailWord_112240).sum := by decide
  have hdescent : baseEnd_112240 < baseStart_112240 := by decide
  rcases family_descends (prefixWord ++ tailWord_112240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112302 : List Nat := [4, 1, 4, 1, 3, 1, 7]
def baseStart_112302 : Nat := 118140960795 + 112302 * 2 ^ 59
def prefixEnd_112302 : Nat := 4983230072969 + 3 ^ 40 * 112302 * 2
def baseEnd_112302 : Nat := 2847649603028387733755

theorem tailTrace_112302 : CollatzResearch.WordTrace tailWord_112302 prefixEnd_112302 2847649603028387733755 := by
  unfold tailWord_112302
  simp only [CollatzResearch.WordTrace]
  refine ⟨511998804894563562467395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2730660292771005666492773 511998804894563562467395)
  ·
    refine ⟨767998207341845343701093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 511998804894563562467395 767998207341845343701093)
    ·
      refine ⟨143999663876596001943955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 767998207341845343701093 143999663876596001943955)
      ·
        refine ⟨215999495814894002915933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143999663876596001943955 215999495814894002915933)
        ·
          refine ⟨80999810930585251093475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215999495814894002915933 80999810930585251093475)
          ·
            refine ⟨121499716395877876640213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80999810930585251093475 121499716395877876640213)
            ·
              refine ⟨2847649603028387733755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121499716395877876640213 2847649603028387733755)
              ·
                rfl

theorem cell21_112302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 7].length) (baseStart_112302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112302 prefixEnd_112302 := by exact prefixLift 112302
  have htrace : WordTrace (prefixWord ++ tailWord_112302) baseStart_112302 baseEnd_112302 := by
    simpa [prefixWord, tailWord_112302, baseEnd_112302] using wordTrace_append hprefix tailTrace_112302
  have hstable : (prefixWord ++ tailWord_112302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112302).length < 2 ^ (prefixWord ++ tailWord_112302).sum := by decide
  have hdescent : baseEnd_112302 < baseStart_112302 := by decide
  rcases family_descends (prefixWord ++ tailWord_112302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112322 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 4]
def baseStart_112322 : Nat := 118140960795 + 112322 * 2 ^ 59
def prefixEnd_112322 : Nat := 4983230072969 + 3 ^ 40 * 112322 * 2
def baseEnd_112322 : Nat := 25633410699739899270421

theorem tailTrace_112322 : CollatzResearch.WordTrace tailWord_112322 prefixEnd_112322 25633410699739899270421 := by
  unfold tailWord_112322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024179974771012978866805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2731146599389367943644813 1024179974771012978866805)
  ·
    refine ⟨96016872634782466768763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1024179974771012978866805 96016872634782466768763)
    ·
      refine ⟨144025308952173700153145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96016872634782466768763 144025308952173700153145)
      ·
        refine ⟨108018981714130275114859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144025308952173700153145 108018981714130275114859)
        ·
          refine ⟨162028472571195412672289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108018981714130275114859 162028472571195412672289)
          ·
            refine ⟨121521354428396559504217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162028472571195412672289 121521354428396559504217)
            ·
              refine ⟨91141015821297419628163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121521354428396559504217 91141015821297419628163)
              ·
                refine ⟨136711523731946129442245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91141015821297419628163 136711523731946129442245)
                ·
                  refine ⟨25633410699739899270421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136711523731946129442245 25633410699739899270421)
                  ·
                    rfl

theorem cell21_112322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_112322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112322 prefixEnd_112322 := by exact prefixLift 112322
  have htrace : WordTrace (prefixWord ++ tailWord_112322) baseStart_112322 baseEnd_112322 := by
    simpa [prefixWord, tailWord_112322, baseEnd_112322] using wordTrace_append hprefix tailTrace_112322
  have hstable : (prefixWord ++ tailWord_112322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112322).length < 2 ^ (prefixWord ++ tailWord_112322).sum := by decide
  have hdescent : baseEnd_112322 < baseStart_112322 := by decide
  rcases family_descends (prefixWord ++ tailWord_112322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112327 : List Nat := [1, 1, 4, 1, 1, 1, 6, 6]
def baseStart_112327 : Nat := 118140960795 + 112327 * 2 ^ 59
def prefixEnd_112327 : Nat := 4983230072969 + 3 ^ 40 * 112327 * 2
def baseEnd_112327 : Nat := 8544850589287000562359

theorem tailTrace_112327 : CollatzResearch.WordTrace tailWord_112327 prefixEnd_112327 8544850589287000562359 := by
  unfold tailWord_112327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4096902264065937769399235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2731268176043958512932823 4096902264065937769399235)
  ·
    refine ⟨6145353396098906654098853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4096902264065937769399235 6145353396098906654098853)
    ·
      refine ⟨1152253761768544997643535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6145353396098906654098853 1152253761768544997643535)
      ·
        refine ⟨1728380642652817496465303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152253761768544997643535 1728380642652817496465303)
        ·
          refine ⟨2592570963979226244697955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728380642652817496465303 2592570963979226244697955)
          ·
            refine ⟨3888856445968839367046933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592570963979226244697955 3888856445968839367046933)
            ·
              refine ⟨182290145904789345330325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3888856445968839367046933 182290145904789345330325)
              ·
                refine ⟨8544850589287000562359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 182290145904789345330325 8544850589287000562359)
                ·
                  rfl

theorem cell21_112327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_112327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112327 prefixEnd_112327 := by exact prefixLift 112327
  have htrace : WordTrace (prefixWord ++ tailWord_112327) baseStart_112327 baseEnd_112327 := by
    simpa [prefixWord, tailWord_112327, baseEnd_112327] using wordTrace_append hprefix tailTrace_112327
  have hstable : (prefixWord ++ tailWord_112327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112327).length < 2 ^ (prefixWord ++ tailWord_112327).sum := by decide
  have hdescent : baseEnd_112327 < baseStart_112327 := by decide
  rcases family_descends (prefixWord ++ tailWord_112327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112330 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 4]
def baseStart_112330 : Nat := 118140960795 + 112330 * 2 ^ 59
def prefixEnd_112330 : Nat := 4983230072969 + 3 ^ 40 * 112330 * 2
def baseEnd_112330 : Nat := 25635236408733663137071

theorem tailTrace_112330 : CollatzResearch.WordTrace tailWord_112330 prefixEnd_112330 25635236408733663137071 := by
  unfold tailWord_112330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024252920763767320439611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2731341122036712854505629 1024252920763767320439611)
  ·
    refine ⟨1536379381145650980659417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024252920763767320439611 1536379381145650980659417)
    ·
      refine ⟨1152284535859238235494563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1536379381145650980659417 1152284535859238235494563)
      ·
        refine ⟨1728426803788857353241845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1152284535859238235494563 1728426803788857353241845)
        ·
          refine ⟨162040012855205376866423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1728426803788857353241845 162040012855205376866423)
          ·
            refine ⟨243060019282808065299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162040012855205376866423 243060019282808065299635)
            ·
              refine ⟨364590028924212097949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243060019282808065299635 364590028924212097949453)
              ·
                refine ⟨136721260846579536731045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364590028924212097949453 136721260846579536731045)
                ·
                  refine ⟨25635236408733663137071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136721260846579536731045 25635236408733663137071)
                  ·
                    rfl

theorem cell21_112330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_112330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112330 prefixEnd_112330 := by exact prefixLift 112330
  have htrace : WordTrace (prefixWord ++ tailWord_112330) baseStart_112330 baseEnd_112330 := by
    simpa [prefixWord, tailWord_112330, baseEnd_112330] using wordTrace_append hprefix tailTrace_112330
  have hstable : (prefixWord ++ tailWord_112330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112330).length < 2 ^ (prefixWord ++ tailWord_112330).sum := by decide
  have hdescent : baseEnd_112330 < baseStart_112330 := by decide
  rcases family_descends (prefixWord ++ tailWord_112330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112434 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 5]
def baseStart_112434 : Nat := 118140960795 + 112434 * 2 ^ 59
def prefixEnd_112434 : Nat := 4983230072969 + 3 ^ 40 * 112434 * 2
def baseEnd_112434 : Nat := 25658970625652593403525

theorem tailTrace_112434 : CollatzResearch.WordTrace tailWord_112434 prefixEnd_112434 25658970625652593403525 := by
  unfold tailWord_112434
  simp only [CollatzResearch.WordTrace]
  refine ⟨1025201218669573760886089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2733869916452196695696237 1025201218669573760886089)
  ·
    refine ⟨768900914002180320664567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1025201218669573760886089 768900914002180320664567)
    ·
      refine ⟨1153351371003270480996851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768900914002180320664567 1153351371003270480996851)
      ·
        refine ⟨1730027056504905721495277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1153351371003270480996851 1730027056504905721495277)
        ·
          refine ⟨648760146189339645560729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1730027056504905721495277 648760146189339645560729)
          ·
            refine ⟨486570109642004734170547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648760146189339645560729 486570109642004734170547)
            ·
              refine ⟨729855164463007101255821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486570109642004734170547 729855164463007101255821)
              ·
                refine ⟨273695686673627662970933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729855164463007101255821 273695686673627662970933)
                ·
                  refine ⟨25658970625652593403525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 273695686673627662970933 25658970625652593403525)
                  ·
                    rfl

theorem cell21_112434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_112434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112434 prefixEnd_112434 := by exact prefixLift 112434
  have htrace : WordTrace (prefixWord ++ tailWord_112434) baseStart_112434 baseEnd_112434 := by
    simpa [prefixWord, tailWord_112434, baseEnd_112434] using wordTrace_append hprefix tailTrace_112434
  have hstable : (prefixWord ++ tailWord_112434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112434).length < 2 ^ (prefixWord ++ tailWord_112434).sum := by decide
  have hdescent : baseEnd_112434 < baseStart_112434 := by decide
  rcases family_descends (prefixWord ++ tailWord_112434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112454 : List Nat := [6, 1, 1, 2, 1, 1, 4, 5]
def baseStart_112454 : Nat := 118140960795 + 112454 * 2 ^ 59
def prefixEnd_112454 : Nat := 4983230072969 + 3 ^ 40 * 112454 * 2
def baseEnd_112454 : Nat := 8554511632712334356717

theorem tailTrace_112454 : CollatzResearch.WordTrace tailWord_112454 prefixEnd_112454 8554511632712334356717 := by
  unfold tailWord_112454
  simp only [CollatzResearch.WordTrace]
  refine ⟨128172947956432451852263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2734356223070558972848277 128172947956432451852263)
  ·
    refine ⟨192259421934648677778395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128172947956432451852263 192259421934648677778395)
    ·
      refine ⟨288389132901973016667593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192259421934648677778395 288389132901973016667593)
      ·
        refine ⟨216291849676479762500695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288389132901973016667593 216291849676479762500695)
        ·
          refine ⟨324437774514719643751043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216291849676479762500695 324437774514719643751043)
          ·
            refine ⟨486656661772079465626565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324437774514719643751043 486656661772079465626565)
            ·
              refine ⟨91248124082264899804981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 486656661772079465626565 91248124082264899804981)
              ·
                refine ⟨8554511632712334356717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91248124082264899804981 8554511632712334356717)
                ·
                  rfl

theorem cell21_112454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_112454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112454 prefixEnd_112454 := by exact prefixLift 112454
  have htrace : WordTrace (prefixWord ++ tailWord_112454) baseStart_112454 baseEnd_112454 := by
    simpa [prefixWord, tailWord_112454, baseEnd_112454] using wordTrace_append hprefix tailTrace_112454
  have hstable : (prefixWord ++ tailWord_112454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112454).length < 2 ^ (prefixWord ++ tailWord_112454).sum := by decide
  have hdescent : baseEnd_112454 < baseStart_112454 := by decide
  rcases family_descends (prefixWord ++ tailWord_112454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112468 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 3]
def baseStart_112468 : Nat := 118140960795 + 112468 * 2 ^ 59
def prefixEnd_112468 : Nat := 4983230072969 + 3 ^ 40 * 112468 * 2
def baseEnd_112468 : Nat := 25666729888876089836789

theorem tailTrace_112468 : CollatzResearch.WordTrace tailWord_112468 prefixEnd_112468 25666729888876089836789 := by
  unfold tailWord_112468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051022478277559425141029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2734696637703412566854705 2051022478277559425141029)
  ·
    refine ⟨384566714677042392213943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2051022478277559425141029 384566714677042392213943)
    ·
      refine ⟨576850072015563588320915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 384566714677042392213943 576850072015563588320915)
      ·
        refine ⟨865275108023345382481373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576850072015563588320915 865275108023345382481373)
        ·
          refine ⟨324478165508754518430515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 865275108023345382481373 324478165508754518430515)
          ·
            refine ⟨486717248263131777645773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324478165508754518430515 486717248263131777645773)
            ·
              refine ⟨182518968098674416617165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486717248263131777645773 182518968098674416617165)
              ·
                refine ⟨68444613037002906231437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 182518968098674416617165 68444613037002906231437)
                ·
                  refine ⟨25666729888876089836789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68444613037002906231437 25666729888876089836789)
                  ·
                    rfl

theorem cell21_112468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_112468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112468 prefixEnd_112468 := by exact prefixLift 112468
  have htrace : WordTrace (prefixWord ++ tailWord_112468) baseStart_112468 baseEnd_112468 := by
    simpa [prefixWord, tailWord_112468, baseEnd_112468] using wordTrace_append hprefix tailTrace_112468
  have hstable : (prefixWord ++ tailWord_112468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112468).length < 2 ^ (prefixWord ++ tailWord_112468).sum := by decide
  have hdescent : baseEnd_112468 < baseStart_112468 := by decide
  rcases family_descends (prefixWord ++ tailWord_112468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112479 : List Nat := [1, 1, 2, 3, 1, 6, 7]
def baseStart_112479 : Nat := 118140960795 + 112479 * 2 ^ 59
def prefixEnd_112479 : Nat := 4983230072969 + 3 ^ 40 * 112479 * 2
def baseEnd_112479 : Nat := 2852137804304723905937

theorem tailTrace_112479 : CollatzResearch.WordTrace tailWord_112479 prefixEnd_112479 2852137804304723905937 := by
  unfold tailWord_112479
  simp only [CollatzResearch.WordTrace]
  refine ⟨4102446159515267728932491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2734964106343511819288327 4102446159515267728932491)
  ·
    refine ⟨6153669239272901593398737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4102446159515267728932491 6153669239272901593398737)
    ·
      refine ⟨4615251929454676195049053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6153669239272901593398737 4615251929454676195049053)
      ·
        refine ⟨1730719473545503573143395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4615251929454676195049053 1730719473545503573143395)
        ·
          refine ⟨2596079210318255359715093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1730719473545503573143395 2596079210318255359715093)
          ·
            refine ⟨121691212983668219986645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2596079210318255359715093 121691212983668219986645)
            ·
              refine ⟨2852137804304723905937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 121691212983668219986645 2852137804304723905937)
              ·
                rfl

theorem cell21_112479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 7].length) (baseStart_112479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112479 prefixEnd_112479 := by exact prefixLift 112479
  have htrace : WordTrace (prefixWord ++ tailWord_112479) baseStart_112479 baseEnd_112479 := by
    simpa [prefixWord, tailWord_112479, baseEnd_112479] using wordTrace_append hprefix tailTrace_112479
  have hstable : (prefixWord ++ tailWord_112479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112479).length < 2 ^ (prefixWord ++ tailWord_112479).sum := by decide
  have hdescent : baseEnd_112479 < baseStart_112479 := by decide
  rcases family_descends (prefixWord ++ tailWord_112479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112541 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 4]
def baseStart_112541 : Nat := 118140960795 + 112541 * 2 ^ 59
def prefixEnd_112541 : Nat := 4983230072969 + 3 ^ 40 * 112541 * 2
def baseEnd_112541 : Nat := 25683389483444185119973

theorem tailTrace_112541 : CollatzResearch.WordTrace tailWord_112541 prefixEnd_112541 25683389483444185119973 := by
  unfold tailWord_112541
  simp only [CollatzResearch.WordTrace]
  refine ⟨4104707485290652317689477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2736471656860434878459651 4104707485290652317689477)
  ·
    refine ⟨769632653491997309566777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4104707485290652317689477 769632653491997309566777)
    ·
      refine ⟨577224490118997982175083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 769632653491997309566777 577224490118997982175083)
      ·
        refine ⟨865836735178496973262625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577224490118997982175083 865836735178496973262625)
        ·
          refine ⟨649377551383872729946969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 865836735178496973262625 649377551383872729946969)
          ·
            refine ⟨487033163537904547460227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649377551383872729946969 487033163537904547460227)
            ·
              refine ⟨730549745306856821190341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487033163537904547460227 730549745306856821190341)
              ·
                refine ⟨136978077245035653973189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730549745306856821190341 136978077245035653973189)
                ·
                  refine ⟨25683389483444185119973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 136978077245035653973189 25683389483444185119973)
                  ·
                    rfl

theorem cell21_112541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_112541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112541 prefixEnd_112541 := by exact prefixLift 112541
  have htrace : WordTrace (prefixWord ++ tailWord_112541) baseStart_112541 baseEnd_112541 := by
    simpa [prefixWord, tailWord_112541, baseEnd_112541] using wordTrace_append hprefix tailTrace_112541
  have hstable : (prefixWord ++ tailWord_112541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112541).length < 2 ^ (prefixWord ++ tailWord_112541).sum := by decide
  have hdescent : baseEnd_112541 < baseStart_112541 := by decide
  rcases family_descends (prefixWord ++ tailWord_112541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112600 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 6]
def baseStart_112600 : Nat := 118140960795 + 112600 * 2 ^ 59
def prefixEnd_112600 : Nat := 4983230072969 + 3 ^ 40 * 112600 * 2
def baseEnd_112600 : Nat := 25696854087273193636519

theorem tailTrace_112600 : CollatzResearch.WordTrace tailWord_112600 prefixEnd_112600 25696854087273193636519 := by
  unfold tailWord_112600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2053429696038452697043627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2737906261384603596058169 2053429696038452697043627)
  ·
    refine ⟨3080144544057679045565441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2053429696038452697043627 3080144544057679045565441)
    ·
      refine ⟨2310108408043259284174081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3080144544057679045565441 2310108408043259284174081)
      ·
        refine ⟨1732581306032444463130561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2310108408043259284174081 1732581306032444463130561)
        ·
          refine ⟨1299435979524333347347921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1732581306032444463130561 1299435979524333347347921)
          ·
            refine ⟨974576984643250010510941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299435979524333347347921 974576984643250010510941)
            ·
              refine ⟨365466369241218753941603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974576984643250010510941 365466369241218753941603)
              ·
                refine ⟨548199553861828130912405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365466369241218753941603 548199553861828130912405)
                ·
                  refine ⟨25696854087273193636519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 548199553861828130912405 25696854087273193636519)
                  ·
                    rfl

theorem cell21_112600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 6].length) (baseStart_112600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112600 prefixEnd_112600 := by exact prefixLift 112600
  have htrace : WordTrace (prefixWord ++ tailWord_112600) baseStart_112600 baseEnd_112600 := by
    simpa [prefixWord, tailWord_112600, baseEnd_112600] using wordTrace_append hprefix tailTrace_112600
  have hstable : (prefixWord ++ tailWord_112600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112600).length < 2 ^ (prefixWord ++ tailWord_112600).sum := by decide
  have hdescent : baseEnd_112600 < baseStart_112600 := by decide
  rcases family_descends (prefixWord ++ tailWord_112600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112721 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 5]
def baseStart_112721 : Nat := 118140960795 + 112721 * 2 ^ 59
def prefixEnd_112721 : Nat := 4983230072969 + 3 ^ 40 * 112721 * 2
def baseEnd_112721 : Nat := 25724467935803872119605

theorem tailTrace_112721 : CollatzResearch.WordTrace tailWord_112721 prefixEnd_112721 25724467935803872119605 := by
  unfold tailWord_112721
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111272624638543059242017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2740848416425695372828011 4111272624638543059242017)
  ·
    refine ⟨3083454468478907294431513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4111272624638543059242017 3083454468478907294431513)
    ·
      refine ⟨2312590851359180470823635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3083454468478907294431513 2312590851359180470823635)
      ·
        refine ⟨3468886277038770706235453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312590851359180470823635 3468886277038770706235453)
        ·
          refine ⟨1300832353889539014838295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3468886277038770706235453 1300832353889539014838295)
          ·
            refine ⟨1951248530834308522257443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300832353889539014838295 1951248530834308522257443)
            ·
              refine ⟨2926872796251462783386165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1951248530834308522257443 2926872796251462783386165)
              ·
                refine ⟨274394324648574635942453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2926872796251462783386165 274394324648574635942453)
                ·
                  refine ⟨25724467935803872119605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 274394324648574635942453 25724467935803872119605)
                  ·
                    rfl

theorem cell21_112721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_112721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112721 prefixEnd_112721 := by exact prefixLift 112721
  have htrace : WordTrace (prefixWord ++ tailWord_112721) baseStart_112721 baseEnd_112721 := by
    simpa [prefixWord, tailWord_112721, baseEnd_112721] using wordTrace_append hprefix tailTrace_112721
  have hstable : (prefixWord ++ tailWord_112721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112721).length < 2 ^ (prefixWord ++ tailWord_112721).sum := by decide
  have hdescent : baseEnd_112721 < baseStart_112721 := by decide
  rcases family_descends (prefixWord ++ tailWord_112721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112769 : List Nat := [1, 2, 4, 2, 3, 1, 1, 1, 6]
def baseStart_112769 : Nat := 118140960795 + 112769 * 2 ^ 59
def prefixEnd_112769 : Nat := 4983230072969 + 3 ^ 40 * 112769 * 2
def baseEnd_112769 : Nat := 25735422189766455319507

theorem tailTrace_112769 : CollatzResearch.WordTrace tailWord_112769 prefixEnd_112769 25735422189766455319507 := by
  unfold tailWord_112769
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113023328464647256989361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742015552309764837992907 4113023328464647256989361)
  ·
    refine ⟨3084767496348485442742021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4113023328464647256989361 3084767496348485442742021)
    ·
      refine ⟨578393905565341020514129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3084767496348485442742021 578393905565341020514129)
      ·
        refine ⟨433795429174005765385597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578393905565341020514129 433795429174005765385597)
        ·
          refine ⟨162673285940252162019599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 433795429174005765385597 162673285940252162019599)
          ·
            refine ⟨244009928910378243029399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162673285940252162019599 244009928910378243029399)
            ·
              refine ⟨366014893365567364544099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244009928910378243029399 366014893365567364544099)
              ·
                refine ⟨549022340048351046816149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366014893365567364544099 549022340048351046816149)
                ·
                  refine ⟨25735422189766455319507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 549022340048351046816149 25735422189766455319507)
                  ·
                    rfl

theorem cell21_112769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 6].length) (baseStart_112769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112769 prefixEnd_112769 := by exact prefixLift 112769
  have htrace : WordTrace (prefixWord ++ tailWord_112769) baseStart_112769 baseEnd_112769 := by
    simpa [prefixWord, tailWord_112769, baseEnd_112769] using wordTrace_append hprefix tailTrace_112769
  have hstable : (prefixWord ++ tailWord_112769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112769).length < 2 ^ (prefixWord ++ tailWord_112769).sum := by decide
  have hdescent : baseEnd_112769 < baseStart_112769 := by decide
  rcases family_descends (prefixWord ++ tailWord_112769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112786 : List Nat := [3, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_112786 : Nat := 118140960795 + 112786 * 2 ^ 59
def prefixEnd_112786 : Nat := 4983230072969 + 3 ^ 40 * 112786 * 2
def baseEnd_112786 : Nat := 25739301821378203536139

theorem tailTrace_112786 : CollatzResearch.WordTrace tailWord_112786 prefixEnd_112786 25739301821378203536139 := by
  unfold tailWord_112786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028410842350764790089553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2742428912935372773572141 1028410842350764790089553)
  ·
    refine ⟨771308131763073592567165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1028410842350764790089553 771308131763073592567165)
    ·
      refine ⟨289240549411152597212687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 771308131763073592567165 289240549411152597212687)
      ·
        refine ⟨433860824116728895819031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289240549411152597212687 433860824116728895819031)
        ·
          refine ⟨650791236175093343728547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433860824116728895819031 650791236175093343728547)
          ·
            refine ⟨976186854262640015592821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650791236175093343728547 976186854262640015592821)
            ·
              refine ⟨91517517587122501461827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 976186854262640015592821 91517517587122501461827)
              ·
                refine ⟨137276276380683752192741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91517517587122501461827 137276276380683752192741)
                ·
                  refine ⟨25739301821378203536139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137276276380683752192741 25739301821378203536139)
                  ·
                    rfl

theorem cell21_112786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_112786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112786 prefixEnd_112786 := by exact prefixLift 112786
  have htrace : WordTrace (prefixWord ++ tailWord_112786) baseStart_112786 baseEnd_112786 := by
    simpa [prefixWord, tailWord_112786, baseEnd_112786] using wordTrace_append hprefix tailTrace_112786
  have hstable : (prefixWord ++ tailWord_112786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112786).length < 2 ^ (prefixWord ++ tailWord_112786).sum := by decide
  have hdescent : baseEnd_112786 < baseStart_112786 := by decide
  rcases family_descends (prefixWord ++ tailWord_112786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112800 : List Nat := [2, 1, 1, 4, 2, 4, 2, 5]
def baseStart_112800 : Nat := 118140960795 + 112800 * 2 ^ 59
def prefixEnd_112800 : Nat := 4983230072969 + 3 ^ 40 * 112800 * 2
def baseEnd_112800 : Nat := 8580832270705763434259

theorem tailTrace_112800 : CollatzResearch.WordTrace tailWord_112800 prefixEnd_112800 8580832270705763434259 := by
  unfold tailWord_112800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2057076995676169775683927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2742769327568226367578569 2057076995676169775683927)
  ·
    refine ⟨3085615493514254663525891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2057076995676169775683927 3085615493514254663525891)
    ·
      refine ⟨4628423240271381995288837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3085615493514254663525891 4628423240271381995288837)
      ·
        refine ⟨867829357550884124116657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4628423240271381995288837 867829357550884124116657)
        ·
          refine ⟨650872018163163093087493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867829357550884124116657 650872018163163093087493)
          ·
            refine ⟨122038503405593079953905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 650872018163163093087493 122038503405593079953905)
            ·
              refine ⟨91528877554194809965429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122038503405593079953905 91528877554194809965429)
              ·
                refine ⟨8580832270705763434259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91528877554194809965429 8580832270705763434259)
                ·
                  rfl

theorem cell21_112800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_112800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112800 prefixEnd_112800 := by exact prefixLift 112800
  have htrace : WordTrace (prefixWord ++ tailWord_112800) baseStart_112800 baseEnd_112800 := by
    simpa [prefixWord, tailWord_112800, baseEnd_112800] using wordTrace_append hprefix tailTrace_112800
  have hstable : (prefixWord ++ tailWord_112800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112800).length < 2 ^ (prefixWord ++ tailWord_112800).sum := by decide
  have hdescent : baseEnd_112800 < baseStart_112800 := by decide
  rcases family_descends (prefixWord ++ tailWord_112800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112980 : List Nat := [2, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_112980 : Nat := 118140960795 + 112980 * 2 ^ 59
def prefixEnd_112980 : Nat := 4983230072969 + 3 ^ 40 * 112980 * 2
def baseEnd_112980 : Nat := 25783575264476977302409

theorem tailTrace_112980 : CollatzResearch.WordTrace tailWord_112980 prefixEnd_112980 25783575264476977302409 := by
  unfold tailWord_112980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060359565350115146460197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2747146087133486861946929 2060359565350115146460197)
  ·
    refine ⟨386317418503146589961287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2060359565350115146460197 386317418503146589961287)
    ·
      refine ⟨579476127754719884941931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 386317418503146589961287 579476127754719884941931)
      ·
        refine ⟨869214191632079827412897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 579476127754719884941931 869214191632079827412897)
        ·
          refine ⟨651910643724059870559673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 869214191632079827412897 651910643724059870559673)
          ·
            refine ⟨488932982793044902919755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 651910643724059870559673 488932982793044902919755)
            ·
              refine ⟨733399474189567354379633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488932982793044902919755 733399474189567354379633)
              ·
                refine ⟨550049605642175515784725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 733399474189567354379633 550049605642175515784725)
                ·
                  refine ⟨25783575264476977302409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 550049605642175515784725 25783575264476977302409)
                  ·
                    rfl

theorem cell21_112980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_112980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_112980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_112980 prefixEnd_112980 := by exact prefixLift 112980
  have htrace : WordTrace (prefixWord ++ tailWord_112980) baseStart_112980 baseEnd_112980 := by
    simpa [prefixWord, tailWord_112980, baseEnd_112980] using wordTrace_append hprefix tailTrace_112980
  have hstable : (prefixWord ++ tailWord_112980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112980).length < 2 ^ (prefixWord ++ tailWord_112980).sum := by decide
  have hdescent : baseEnd_112980 < baseStart_112980 := by decide
  rcases family_descends (prefixWord ++ tailWord_112980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113000 : List Nat := [2, 1, 4, 2, 2, 2, 3, 2, 3]
def baseStart_113000 : Nat := 118140960795 + 113000 * 2 ^ 59
def prefixEnd_113000 : Nat := 4983230072969 + 3 ^ 40 * 113000 * 2
def baseEnd_113000 : Nat := 25788139536961386969035

theorem tailTrace_113000 : CollatzResearch.WordTrace tailWord_113000 prefixEnd_113000 25788139536961386969035 := by
  unfold tailWord_113000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2060724295313886854324227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2747632393751849139098969 2060724295313886854324227)
  ·
    refine ⟨3091086442970830281486341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2060724295313886854324227 3091086442970830281486341)
    ·
      refine ⟨579578708057030677778689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3091086442970830281486341 579578708057030677778689)
      ·
        refine ⟨434684031042773008334017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 579578708057030677778689 434684031042773008334017)
        ·
          refine ⟨326013023282079756250513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434684031042773008334017 326013023282079756250513)
          ·
            refine ⟨244509767461559817187885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326013023282079756250513 244509767461559817187885)
            ·
              refine ⟨91691162798084931445457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244509767461559817187885 91691162798084931445457)
              ·
                refine ⟨68768372098563698584093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91691162798084931445457 68768372098563698584093)
                ·
                  refine ⟨25788139536961386969035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68768372098563698584093 25788139536961386969035)
                  ·
                    rfl

theorem cell21_113000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 3].length) (baseStart_113000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113000 prefixEnd_113000 := by exact prefixLift 113000
  have htrace : WordTrace (prefixWord ++ tailWord_113000) baseStart_113000 baseEnd_113000 := by
    simpa [prefixWord, tailWord_113000, baseEnd_113000] using wordTrace_append hprefix tailTrace_113000
  have hstable : (prefixWord ++ tailWord_113000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113000).length < 2 ^ (prefixWord ++ tailWord_113000).sum := by decide
  have hdescent : baseEnd_113000 < baseStart_113000 := by decide
  rcases family_descends (prefixWord ++ tailWord_113000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113056 : List Nat := [2, 1, 1, 4, 1, 3, 1, 4, 4]
def baseStart_113056 : Nat := 118140960795 + 113056 * 2 ^ 59
def prefixEnd_113056 : Nat := 4983230072969 + 3 ^ 40 * 113056 * 2
def baseEnd_113056 : Nat := 25800919499917734035587

theorem tailTrace_113056 : CollatzResearch.WordTrace tailWord_113056 prefixEnd_113056 25800919499917734035587 := by
  unfold tailWord_113056
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061745539212447636343511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2748994052283263515124681 2061745539212447636343511)
  ·
    refine ⟨3092618308818671454515267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2061745539212447636343511 3092618308818671454515267)
    ·
      refine ⟨4638927463228007181772901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3092618308818671454515267 4638927463228007181772901)
      ·
        refine ⟨869798899355251346582419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4638927463228007181772901 869798899355251346582419)
        ·
          refine ⟨1304698349032877019873629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 869798899355251346582419 1304698349032877019873629)
          ·
            refine ⟨489261880887328882452611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1304698349032877019873629 489261880887328882452611)
            ·
              refine ⟨733892821330993323678917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 489261880887328882452611 733892821330993323678917)
              ·
                refine ⟨137604903999561248189797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 733892821330993323678917 137604903999561248189797)
                ·
                  refine ⟨25800919499917734035587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 137604903999561248189797 25800919499917734035587)
                  ·
                    rfl

theorem cell21_113056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4, 4].length) (baseStart_113056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113056 prefixEnd_113056 := by exact prefixLift 113056
  have htrace : WordTrace (prefixWord ++ tailWord_113056) baseStart_113056 baseEnd_113056 := by
    simpa [prefixWord, tailWord_113056, baseEnd_113056] using wordTrace_append hprefix tailTrace_113056
  have hstable : (prefixWord ++ tailWord_113056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113056).length < 2 ^ (prefixWord ++ tailWord_113056).sum := by decide
  have hdescent : baseEnd_113056 < baseStart_113056 := by decide
  rcases family_descends (prefixWord ++ tailWord_113056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113059 : List Nat := [1, 1, 1, 4, 1, 4, 4, 2, 3]
def baseStart_113059 : Nat := 118140960795 + 113059 * 2 ^ 59
def prefixEnd_113059 : Nat := 4983230072969 + 3 ^ 40 * 113059 * 2
def baseEnd_113059 : Nat := 25801604140790395485581

theorem tailTrace_113059 : CollatzResearch.WordTrace tailWord_113059 prefixEnd_113059 25801604140790395485581 := by
  unfold tailWord_113059
  simp only [CollatzResearch.WordTrace]
  refine ⟨4123600497414026785046231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2749066998276017856697487 4123600497414026785046231)
  ·
    refine ⟨6185400746121040177569347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4123600497414026785046231 6185400746121040177569347)
    ·
      refine ⟨9278101119181560266354021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6185400746121040177569347 9278101119181560266354021)
      ·
        refine ⟨1739643959846542549941379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9278101119181560266354021 1739643959846542549941379)
        ·
          refine ⟨2609465939769813824912069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1739643959846542549941379 2609465939769813824912069)
          ·
            refine ⟨489274863706840092171013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2609465939769813824912069 489274863706840092171013)
            ·
              refine ⟨91739036945032517282065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 489274863706840092171013 91739036945032517282065)
              ·
                refine ⟨68804277708774387961549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91739036945032517282065 68804277708774387961549)
                ·
                  refine ⟨25801604140790395485581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68804277708774387961549 25801604140790395485581)
                  ·
                    rfl

theorem cell21_113059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 2, 3].length) (baseStart_113059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113059 prefixEnd_113059 := by exact prefixLift 113059
  have htrace : WordTrace (prefixWord ++ tailWord_113059) baseStart_113059 baseEnd_113059 := by
    simpa [prefixWord, tailWord_113059, baseEnd_113059] using wordTrace_append hprefix tailTrace_113059
  have hstable : (prefixWord ++ tailWord_113059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113059).length < 2 ^ (prefixWord ++ tailWord_113059).sum := by decide
  have hdescent : baseEnd_113059 < baseStart_113059 := by decide
  rcases family_descends (prefixWord ++ tailWord_113059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113076 : List Nat := [2, 5, 2, 2, 1, 1, 1, 2, 5]
def baseStart_113076 : Nat := 118140960795 + 113076 * 2 ^ 59
def prefixEnd_113076 : Nat := 4983230072969 + 3 ^ 40 * 113076 * 2
def baseEnd_113076 : Nat := 25805483772402143702213

theorem tailTrace_113076 : CollatzResearch.WordTrace tailWord_113076 prefixEnd_113076 25805483772402143702213 := by
  unfold tailWord_113076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2062110269176219344207541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2749480358901625792276721 2062110269176219344207541)
  ·
    refine ⟨193322837735270563519457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2062110269176219344207541 193322837735270563519457)
    ·
      refine ⟨144992128301452922639593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193322837735270563519457 144992128301452922639593)
      ·
        refine ⟨108744096226089691979695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144992128301452922639593 108744096226089691979695)
        ·
          refine ⟨163116144339134537969543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108744096226089691979695 163116144339134537969543)
          ·
            refine ⟨244674216508701806954315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163116144339134537969543 244674216508701806954315)
            ·
              refine ⟨367011324763052710431473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244674216508701806954315 367011324763052710431473)
              ·
                refine ⟨275258493572289532823605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 367011324763052710431473 275258493572289532823605)
                ·
                  refine ⟨25805483772402143702213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 275258493572289532823605 25805483772402143702213)
                  ·
                    rfl

theorem cell21_113076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_113076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113076 prefixEnd_113076 := by exact prefixLift 113076
  have htrace : WordTrace (prefixWord ++ tailWord_113076) baseStart_113076 baseEnd_113076 := by
    simpa [prefixWord, tailWord_113076, baseEnd_113076] using wordTrace_append hprefix tailTrace_113076
  have hstable : (prefixWord ++ tailWord_113076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113076).length < 2 ^ (prefixWord ++ tailWord_113076).sum := by decide
  have hdescent : baseEnd_113076 < baseStart_113076 := by decide
  rcases family_descends (prefixWord ++ tailWord_113076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113256 : List Nat := [2, 1, 4, 3, 2, 1, 3, 5]
def baseStart_113256 : Nat := 118140960795 + 113256 * 2 ^ 59
def prefixEnd_113256 : Nat := 4983230072969 + 3 ^ 40 * 113256 * 2
def baseEnd_113256 : Nat := 8615520741587276900615

theorem tailTrace_113256 : CollatzResearch.WordTrace tailWord_113256 prefixEnd_113256 8615520741587276900615 := by
  unfold tailWord_113256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065392838850164714983811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2753857118466886286645081 2065392838850164714983811)
  ·
    refine ⟨3098089258275247072475717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065392838850164714983811 3098089258275247072475717)
    ·
      refine ⟨580891735926608826089197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3098089258275247072475717 580891735926608826089197)
      ·
        refine ⟨217834400972478309783449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 580891735926608826089197 217834400972478309783449)
        ·
          refine ⟨163375800729358732337587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217834400972478309783449 163375800729358732337587)
          ·
            refine ⟨245063701094038098506381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163375800729358732337587 245063701094038098506381)
            ·
              refine ⟨91898887910264286939893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245063701094038098506381 91898887910264286939893)
              ·
                refine ⟨8615520741587276900615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91898887910264286939893 8615520741587276900615)
                ·
                  rfl

theorem cell21_113256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 3, 5].length) (baseStart_113256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113256 prefixEnd_113256 := by exact prefixLift 113256
  have htrace : WordTrace (prefixWord ++ tailWord_113256) baseStart_113256 baseEnd_113256 := by
    simpa [prefixWord, tailWord_113256, baseEnd_113256] using wordTrace_append hprefix tailTrace_113256
  have hstable : (prefixWord ++ tailWord_113256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113256).length < 2 ^ (prefixWord ++ tailWord_113256).sum := by decide
  have hdescent : baseEnd_113256 < baseStart_113256 := by decide
  rcases family_descends (prefixWord ++ tailWord_113256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113284 : List Nat := [2, 3, 2, 1, 3, 2, 1, 1, 6]
def baseStart_113284 : Nat := 118140960795 + 113284 * 2 ^ 59
def prefixEnd_113284 : Nat := 4983230072969 + 3 ^ 40 * 113284 * 2
def baseEnd_113284 : Nat := 25852952206240004235121

theorem tailTrace_113284 : CollatzResearch.WordTrace tailWord_113284 prefixEnd_113284 25852952206240004235121 := by
  unfold tailWord_113284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065903460799445105993453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2754537947732593474657937 2065903460799445105993453)
  ·
    refine ⟨774713797799791914747545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2065903460799445105993453 774713797799791914747545)
    ·
      refine ⟨581035348349843936060659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 774713797799791914747545 581035348349843936060659)
      ·
        refine ⟨871553022524765904090989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581035348349843936060659 871553022524765904090989)
        ·
          refine ⟨326832383446787214034121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 871553022524765904090989 326832383446787214034121)
          ·
            refine ⟨245124287585090410525591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326832383446787214034121 245124287585090410525591)
            ·
              refine ⟨367686431377635615788387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245124287585090410525591 367686431377635615788387)
              ·
                refine ⟨551529647066453423682581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367686431377635615788387 551529647066453423682581)
                ·
                  refine ⟨25852952206240004235121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 551529647066453423682581 25852952206240004235121)
                  ·
                    rfl

theorem cell21_113284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_113284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113284 prefixEnd_113284 := by exact prefixLift 113284
  have htrace : WordTrace (prefixWord ++ tailWord_113284) baseStart_113284 baseEnd_113284 := by
    simpa [prefixWord, tailWord_113284, baseEnd_113284] using wordTrace_append hprefix tailTrace_113284
  have hstable : (prefixWord ++ tailWord_113284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113284).length < 2 ^ (prefixWord ++ tailWord_113284).sum := by decide
  have hdescent : baseEnd_113284 < baseStart_113284 := by decide
  rcases family_descends (prefixWord ++ tailWord_113284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113343 : List Nat := [1, 1, 2, 2, 2, 4, 2, 1, 6]
def baseStart_113343 : Nat := 118140960795 + 113343 * 2 ^ 59
def prefixEnd_113343 : Nat := 4983230072969 + 3 ^ 40 * 113343 * 2
def baseEnd_113343 : Nat := 25866416810069012751667

theorem tailTrace_113343 : CollatzResearch.WordTrace tailWord_113343 prefixEnd_113343 25866416810069012751667 := by
  unfold tailWord_113343
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133958828385143288384683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2755972552256762192256455 4133958828385143288384683)
  ·
    refine ⟨6200938242577714932577025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133958828385143288384683 6200938242577714932577025)
    ·
      refine ⟨4650703681933286199432769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6200938242577714932577025 4650703681933286199432769)
      ·
        refine ⟨3488027761449964649574577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4650703681933286199432769 3488027761449964649574577)
        ·
          refine ⟨2616020821087473487180933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488027761449964649574577 2616020821087473487180933)
          ·
            refine ⟨490503903953901278846425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2616020821087473487180933 490503903953901278846425)
            ·
              refine ⟨367877927965425959134819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490503903953901278846425 367877927965425959134819)
              ·
                refine ⟨551816891948138938702229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 367877927965425959134819 551816891948138938702229)
                ·
                  refine ⟨25866416810069012751667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 551816891948138938702229 25866416810069012751667)
                  ·
                    rfl

theorem cell21_113343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_113343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113343 prefixEnd_113343 := by exact prefixLift 113343
  have htrace : WordTrace (prefixWord ++ tailWord_113343) baseStart_113343 baseEnd_113343 := by
    simpa [prefixWord, tailWord_113343, baseEnd_113343] using wordTrace_append hprefix tailTrace_113343
  have hstable : (prefixWord ++ tailWord_113343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113343).length < 2 ^ (prefixWord ++ tailWord_113343).sum := by decide
  have hdescent : baseEnd_113343 < baseStart_113343 := by decide
  rcases family_descends (prefixWord ++ tailWord_113343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113397 : List Nat := [1, 3, 6, 1, 1, 1, 1, 4, 3]
def baseStart_113397 : Nat := 118140960795 + 113397 * 2 ^ 59
def prefixEnd_113397 : Nat := 4983230072969 + 3 ^ 40 * 113397 * 2
def baseEnd_113397 : Nat := 25878740345776918851557

theorem tailTrace_113397 : CollatzResearch.WordTrace tailWord_113397 prefixEnd_113397 25878740345776918851557 := by
  unfold tailWord_113397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135928370189510510850445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2757285580126340340566963 4135928370189510510850445)
  ·
    refine ⟨1550973138821066441568917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4135928370189510510850445 1550973138821066441568917)
    ·
      refine ⟨72701865882237489448543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1550973138821066441568917 72701865882237489448543)
      ·
        refine ⟨109052798823356234172815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72701865882237489448543 109052798823356234172815)
        ·
          refine ⟨163579198235034351259223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109052798823356234172815 163579198235034351259223)
          ·
            refine ⟨245368797352551526888835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163579198235034351259223 245368797352551526888835)
            ·
              refine ⟨368053196028827290333253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245368797352551526888835 368053196028827290333253)
              ·
                refine ⟨69009974255405116937485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 368053196028827290333253 69009974255405116937485)
                ·
                  refine ⟨25878740345776918851557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69009974255405116937485 25878740345776918851557)
                  ·
                    rfl

theorem cell21_113397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_113397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113397 prefixEnd_113397 := by exact prefixLift 113397
  have htrace : WordTrace (prefixWord ++ tailWord_113397) baseStart_113397 baseEnd_113397 := by
    simpa [prefixWord, tailWord_113397, baseEnd_113397] using wordTrace_append hprefix tailTrace_113397
  have hstable : (prefixWord ++ tailWord_113397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113397).length < 2 ^ (prefixWord ++ tailWord_113397).sum := by decide
  have hdescent : baseEnd_113397 < baseStart_113397 := by decide
  rcases family_descends (prefixWord ++ tailWord_113397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113470 : List Nat := [4, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_113470 : Nat := 118140960795 + 113470 * 2 ^ 59
def prefixEnd_113470 : Nat := 4983230072969 + 3 ^ 40 * 113470 * 2
def baseEnd_113470 : Nat := 25895399940345014134741

theorem tailTrace_113470 : CollatzResearch.WordTrace tailWord_113470 prefixEnd_113470 25895399940345014134741 := by
  unfold tailWord_113470
  simp only [CollatzResearch.WordTrace]
  refine ⟨517323862365630497282233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2759060599283362652171909 517323862365630497282233)
  ·
    refine ⟨387992896774222872961675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 517323862365630497282233 387992896774222872961675)
    ·
      refine ⟨581989345161334309442513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 387992896774222872961675 581989345161334309442513)
      ·
        refine ⟨436492008871000732081885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 581989345161334309442513 436492008871000732081885)
        ·
          refine ⟨163684503326625274530707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 436492008871000732081885 163684503326625274530707)
          ·
            refine ⟨245526754989937911796061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163684503326625274530707 245526754989937911796061)
            ·
              refine ⟨92072533121226716923523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245526754989937911796061 92072533121226716923523)
              ·
                refine ⟨138108799681840075385285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92072533121226716923523 138108799681840075385285)
                ·
                  refine ⟨25895399940345014134741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138108799681840075385285 25895399940345014134741)
                  ·
                    rfl

theorem cell21_113470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_113470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113470 prefixEnd_113470 := by exact prefixLift 113470
  have htrace : WordTrace (prefixWord ++ tailWord_113470) baseStart_113470 baseEnd_113470 := by
    simpa [prefixWord, tailWord_113470, baseEnd_113470] using wordTrace_append hprefix tailTrace_113470
  have hstable : (prefixWord ++ tailWord_113470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113470).length < 2 ^ (prefixWord ++ tailWord_113470).sum := by decide
  have hdescent : baseEnd_113470 < baseStart_113470 := by decide
  rcases family_descends (prefixWord ++ tailWord_113470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113495 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 6]
def baseStart_113495 : Nat := 118140960795 + 113495 * 2 ^ 59
def prefixEnd_113495 : Nat := 4983230072969 + 3 ^ 40 * 113495 * 2
def baseEnd_113495 : Nat := 25901105280950526218023

theorem tailTrace_113495 : CollatzResearch.WordTrace tailWord_113495 prefixEnd_113495 25901105280950526218023 := by
  unfold tailWord_113495
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139502723834473247917939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2759668482556315498611959 4139502723834473247917939)
  ·
    refine ⟨6209254085751709871876909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139502723834473247917939 6209254085751709871876909)
    ·
      refine ⟨2328470282156891201953841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6209254085751709871876909 2328470282156891201953841)
      ·
        refine ⟨1746352711617668401465381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2328470282156891201953841 1746352711617668401465381)
        ·
          refine ⟨327441133428312825274759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1746352711617668401465381 327441133428312825274759)
          ·
            refine ⟨491161700142469237912139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327441133428312825274759 491161700142469237912139)
            ·
              refine ⟨736742550213703856868209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 491161700142469237912139 736742550213703856868209)
              ·
                refine ⟨552556912660277892651157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736742550213703856868209 552556912660277892651157)
                ·
                  refine ⟨25901105280950526218023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 552556912660277892651157 25901105280950526218023)
                  ·
                    rfl

theorem cell21_113495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_113495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113495 prefixEnd_113495 := by exact prefixLift 113495
  have htrace : WordTrace (prefixWord ++ tailWord_113495) baseStart_113495 baseEnd_113495 := by
    simpa [prefixWord, tailWord_113495, baseEnd_113495] using wordTrace_append hprefix tailTrace_113495
  have hstable : (prefixWord ++ tailWord_113495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113495).length < 2 ^ (prefixWord ++ tailWord_113495).sum := by decide
  have hdescent : baseEnd_113495 < baseStart_113495 := by decide
  rcases family_descends (prefixWord ++ tailWord_113495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113498 : List Nat := [3, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_113498 : Nat := 118140960795 + 113498 * 2 ^ 59
def prefixEnd_113498 : Nat := 4983230072969 + 3 ^ 40 * 113498 * 2
def baseEnd_113498 : Nat := 25901789921823187668017

theorem tailTrace_113498 : CollatzResearch.WordTrace tailWord_113498 prefixEnd_113498 25901789921823187668017 := by
  unfold tailWord_113498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034903035705901190069287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2759741428549069840184765 1034903035705901190069287)
  ·
    refine ⟨1552354553558851785103931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1034903035705901190069287 1552354553558851785103931)
    ·
      refine ⟨2328531830338277677655897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552354553558851785103931 2328531830338277677655897)
      ·
        refine ⟨1746398872753708258241923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2328531830338277677655897 1746398872753708258241923)
        ·
          refine ⟨2619598309130562387362885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746398872753708258241923 2619598309130562387362885)
          ·
            refine ⟨491174682961980447630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2619598309130562387362885 491174682961980447630541)
            ·
              refine ⟨184190506110742667861453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 491174682961980447630541 184190506110742667861453)
              ·
                refine ⟨69071439791528500448045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 184190506110742667861453 69071439791528500448045)
                ·
                  refine ⟨25901789921823187668017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69071439791528500448045 25901789921823187668017)
                  ·
                    rfl

theorem cell21_113498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_113498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113498 prefixEnd_113498 := by exact prefixLift 113498
  have htrace : WordTrace (prefixWord ++ tailWord_113498) baseStart_113498 baseEnd_113498 := by
    simpa [prefixWord, tailWord_113498, baseEnd_113498] using wordTrace_append hprefix tailTrace_113498
  have hstable : (prefixWord ++ tailWord_113498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113498).length < 2 ^ (prefixWord ++ tailWord_113498).sum := by decide
  have hdescent : baseEnd_113498 < baseStart_113498 := by decide
  rcases family_descends (prefixWord ++ tailWord_113498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113509 : List Nat := [1, 3, 1, 3, 1, 1, 11]
def baseStart_113509 : Nat := 118140960795 + 113509 * 2 ^ 59
def prefixEnd_113509 : Nat := 4983230072969 + 3 ^ 40 * 113509 * 2
def baseEnd_113509 : Nat := 2878255585743290331629

theorem tailTrace_113509 : CollatzResearch.WordTrace tailWord_113509 prefixEnd_113509 2878255585743290331629 := by
  unfold tailWord_113509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140013345783753638927581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760008897189169092618387 4140013345783753638927581)
  ·
    refine ⟨1552505004668907614597843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4140013345783753638927581 1552505004668907614597843)
    ·
      refine ⟨2328757507003361421896765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552505004668907614597843 2328757507003361421896765)
      ·
        refine ⟨873284065126260533211287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2328757507003361421896765 873284065126260533211287)
        ·
          refine ⟨1309926097689390799816931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873284065126260533211287 1309926097689390799816931)
          ·
            refine ⟨1964889146534086199725397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309926097689390799816931 1964889146534086199725397)
            ·
              refine ⟨2878255585743290331629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1964889146534086199725397 2878255585743290331629)
              ·
                rfl

theorem cell21_113509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 11].length) (baseStart_113509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113509 prefixEnd_113509 := by exact prefixLift 113509
  have htrace : WordTrace (prefixWord ++ tailWord_113509) baseStart_113509 baseEnd_113509 := by
    simpa [prefixWord, tailWord_113509, baseEnd_113509] using wordTrace_append hprefix tailTrace_113509
  have hstable : (prefixWord ++ tailWord_113509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113509).length < 2 ^ (prefixWord ++ tailWord_113509).sum := by decide
  have hdescent : baseEnd_113509 < baseStart_113509 := by decide
  rcases family_descends (prefixWord ++ tailWord_113509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113529 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 4]
def baseStart_113529 : Nat := 118140960795 + 113529 * 2 ^ 59
def prefixEnd_113529 : Nat := 4983230072969 + 3 ^ 40 * 113529 * 2
def baseEnd_113529 : Nat := 25908864544174022651287

theorem tailTrace_113529 : CollatzResearch.WordTrace tailWord_113529 prefixEnd_113529 25908864544174022651287 := by
  unfold tailWord_113529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140742805711297054655641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760495203807531369770427 4140742805711297054655641)
  ·
    refine ⟨3105557104283472790991731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4140742805711297054655641 3105557104283472790991731)
    ·
      refine ⟨4658335656425209186487597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3105557104283472790991731 4658335656425209186487597)
      ·
        refine ⟨1746875871159453444932849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4658335656425209186487597 1746875871159453444932849)
        ·
          refine ⟨1310156903369590083699637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746875871159453444932849 1310156903369590083699637)
          ·
            refine ⟨122827209690899070346841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1310156903369590083699637 122827209690899070346841)
            ·
              refine ⟨92120407268174302760131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122827209690899070346841 92120407268174302760131)
              ·
                refine ⟨138180610902261454140197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92120407268174302760131 138180610902261454140197)
                ·
                  refine ⟨25908864544174022651287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138180610902261454140197 25908864544174022651287)
                  ·
                    rfl

theorem cell21_113529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 4].length) (baseStart_113529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113529 prefixEnd_113529 := by exact prefixLift 113529
  have htrace : WordTrace (prefixWord ++ tailWord_113529) baseStart_113529 baseEnd_113529 := by
    simpa [prefixWord, tailWord_113529, baseEnd_113529] using wordTrace_append hprefix tailTrace_113529
  have hstable : (prefixWord ++ tailWord_113529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113529).length < 2 ^ (prefixWord ++ tailWord_113529).sum := by decide
  have hdescent : baseEnd_113529 < baseStart_113529 := by decide
  rcases family_descends (prefixWord ++ tailWord_113529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113540 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 7]
def baseStart_113540 : Nat := 118140960795 + 113540 * 2 ^ 59
def prefixEnd_113540 : Nat := 4983230072969 + 3 ^ 40 * 113540 * 2
def baseEnd_113540 : Nat := 25911374894040447967931

theorem tailTrace_113540 : CollatzResearch.WordTrace tailWord_113540 prefixEnd_113540 25911374894040447967931 := by
  unfold tailWord_113540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2070572004335722966653037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2760762672447630622204049 2070572004335722966653037)
  ·
    refine ⟨776464501625896112494889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2070572004335722966653037 776464501625896112494889)
    ·
      refine ⟨582348376219422084371167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776464501625896112494889 582348376219422084371167)
      ·
        refine ⟨873522564329133126556751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582348376219422084371167 873522564329133126556751)
        ·
          refine ⟨1310283846493699689835127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873522564329133126556751 1310283846493699689835127)
          ·
            refine ⟨1965425769740549534752691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310283846493699689835127 1965425769740549534752691)
            ·
              refine ⟨2948138654610824302129037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965425769740549534752691 2948138654610824302129037)
              ·
                refine ⟨1105551995479059113298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2948138654610824302129037 1105551995479059113298389)
                ·
                  refine ⟨25911374894040447967931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1105551995479059113298389 25911374894040447967931)
                  ·
                    rfl

theorem cell21_113540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_113540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113540 prefixEnd_113540 := by exact prefixLift 113540
  have htrace : WordTrace (prefixWord ++ tailWord_113540) baseStart_113540 baseEnd_113540 := by
    simpa [prefixWord, tailWord_113540, baseEnd_113540] using wordTrace_append hprefix tailTrace_113540
  have hstable : (prefixWord ++ tailWord_113540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113540).length < 2 ^ (prefixWord ++ tailWord_113540).sum := by decide
  have hdescent : baseEnd_113540 < baseStart_113540 := by decide
  rcases family_descends (prefixWord ++ tailWord_113540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113571 : List Nat := [1, 1, 1, 4, 1, 2, 3, 4, 4]
def baseStart_113571 : Nat := 118140960795 + 113571 * 2 ^ 59
def prefixEnd_113571 : Nat := 4983230072969 + 3 ^ 40 * 113571 * 2
def baseEnd_113571 : Nat := 25918449516391282951201

theorem tailTrace_113571 : CollatzResearch.WordTrace tailWord_113571 prefixEnd_113571 25918449516391282951201 := by
  unfold tailWord_113571
  simp only [CollatzResearch.WordTrace]
  refine ⟨4142274671559138227684567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2761516447706092151789711 4142274671559138227684567)
  ·
    refine ⟨6213412007338707341526851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4142274671559138227684567 6213412007338707341526851)
    ·
      refine ⟨9320118011008061012290277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6213412007338707341526851 9320118011008061012290277)
      ·
        refine ⟨1747522127064011439804427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9320118011008061012290277 1747522127064011439804427)
        ·
          refine ⟨2621283190596017159706641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747522127064011439804427 2621283190596017159706641)
          ·
            refine ⟨1965962392947012869779981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621283190596017159706641 1965962392947012869779981)
            ·
              refine ⟨737235897355129826167493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1965962392947012869779981 737235897355129826167493)
              ·
                refine ⟨138231730754086842406405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737235897355129826167493 138231730754086842406405)
                ·
                  refine ⟨25918449516391282951201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138231730754086842406405 25918449516391282951201)
                  ·
                    rfl

theorem cell21_113571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 4].length) (baseStart_113571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113571 prefixEnd_113571 := by exact prefixLift 113571
  have htrace : WordTrace (prefixWord ++ tailWord_113571) baseStart_113571 baseEnd_113571 := by
    simpa [prefixWord, tailWord_113571, baseEnd_113571] using wordTrace_append hprefix tailTrace_113571
  have hstable : (prefixWord ++ tailWord_113571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113571).length < 2 ^ (prefixWord ++ tailWord_113571).sum := by decide
  have hdescent : baseEnd_113571 < baseStart_113571 := by decide
  rcases family_descends (prefixWord ++ tailWord_113571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113622 : List Nat := [5, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_113622 : Nat := 118140960795 + 113622 * 2 ^ 59
def prefixEnd_113622 : Nat := 4983230072969 + 3 ^ 40 * 113622 * 2
def baseEnd_113622 : Nat := 25930088411226527601097

theorem tailTrace_113622 : CollatzResearch.WordTrace tailWord_113622 prefixEnd_113622 25930088411226527601097 := by
  unfold tailWord_113622
  simp only [CollatzResearch.WordTrace]
  refine ⟨259008424648398371111945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2762756529582915958527413 259008424648398371111945)
  ·
    refine ⟨194256318486298778333959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 259008424648398371111945 194256318486298778333959)
    ·
      refine ⟨291384477729448167500939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194256318486298778333959 291384477729448167500939)
      ·
        refine ⟨437076716594172251251409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291384477729448167500939 437076716594172251251409)
        ·
          refine ⟨327807537445629188438557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437076716594172251251409 327807537445629188438557)
          ·
            refine ⟨122927826542110945664459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 327807537445629188438557 122927826542110945664459)
            ·
              refine ⟨184391739813166418496689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122927826542110945664459 184391739813166418496689)
              ·
                refine ⟨138293804859874813872517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 184391739813166418496689 138293804859874813872517)
                ·
                  refine ⟨25930088411226527601097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138293804859874813872517 25930088411226527601097)
                  ·
                    rfl

theorem cell21_113622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_113622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113622 prefixEnd_113622 := by exact prefixLift 113622
  have htrace : WordTrace (prefixWord ++ tailWord_113622) baseStart_113622 baseEnd_113622 := by
    simpa [prefixWord, tailWord_113622, baseEnd_113622] using wordTrace_append hprefix tailTrace_113622
  have hstable : (prefixWord ++ tailWord_113622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113622).length < 2 ^ (prefixWord ++ tailWord_113622).sum := by decide
  have hdescent : baseEnd_113622 < baseStart_113622 := by decide
  rcases family_descends (prefixWord ++ tailWord_113622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113653 : List Nat := [1, 3, 5, 2, 1, 2, 2, 5]
def baseStart_113653 : Nat := 118140960795 + 113653 * 2 ^ 59
def prefixEnd_113653 : Nat := 4983230072969 + 3 ^ 40 * 113653 * 2
def baseEnd_113653 : Nat := 8645721011192454194789

theorem tailTrace_113653 : CollatzResearch.WordTrace tailWord_113653 prefixEnd_113653 8645721011192454194789 := by
  unfold tailWord_113653
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145265457262066232169613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2763510304841377488113075 4145265457262066232169613)
  ·
    refine ⟨1554474546473274837063605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4145265457262066232169613 1554474546473274837063605)
    ·
      refine ⟨145731988731869515974713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1554474546473274837063605 145731988731869515974713)
      ·
        refine ⟨109298991548902136981035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145731988731869515974713 109298991548902136981035)
        ·
          refine ⟨163948487323353205471553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109298991548902136981035 163948487323353205471553)
          ·
            refine ⟨122961365492514904103665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163948487323353205471553 122961365492514904103665)
            ·
              refine ⟨92221024119386178077749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122961365492514904103665 92221024119386178077749)
              ·
                refine ⟨8645721011192454194789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92221024119386178077749 8645721011192454194789)
                ·
                  rfl

theorem cell21_113653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 5].length) (baseStart_113653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113653 prefixEnd_113653 := by exact prefixLift 113653
  have htrace : WordTrace (prefixWord ++ tailWord_113653) baseStart_113653 baseEnd_113653 := by
    simpa [prefixWord, tailWord_113653, baseEnd_113653] using wordTrace_append hprefix tailTrace_113653
  have hstable : (prefixWord ++ tailWord_113653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113653).length < 2 ^ (prefixWord ++ tailWord_113653).sum := by decide
  have hdescent : baseEnd_113653 < baseStart_113653 := by decide
  rcases family_descends (prefixWord ++ tailWord_113653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113678 : List Nat := [4, 1, 1, 2, 2, 4, 7]
def baseStart_113678 : Nat := 118140960795 + 113678 * 2 ^ 59
def prefixEnd_113678 : Nat := 4983230072969 + 3 ^ 40 * 113678 * 2
def baseEnd_113678 : Nat := 2882540930464763851961

theorem tailTrace_113678 : CollatzResearch.WordTrace tailWord_113678 prefixEnd_113678 2882540930464763851961 := by
  unfold tailWord_113678
  simp only [CollatzResearch.WordTrace]
  refine ⟨518272160271436937728711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2764118188114330334553125 518272160271436937728711)
  ·
    refine ⟨777408240407155406593067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 518272160271436937728711 777408240407155406593067)
    ·
      refine ⟨1166112360610733109889601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 777408240407155406593067 1166112360610733109889601)
      ·
        refine ⟨874584270458049832417201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166112360610733109889601 874584270458049832417201)
        ·
          refine ⟨655938202843537374312901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 874584270458049832417201 655938202843537374312901)
          ·
            refine ⟨122988413033163257683669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 655938202843537374312901 122988413033163257683669)
            ·
              refine ⟨2882540930464763851961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 122988413033163257683669 2882540930464763851961)
              ·
                rfl

theorem cell21_113678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 7].length) (baseStart_113678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113678 prefixEnd_113678 := by exact prefixLift 113678
  have htrace : WordTrace (prefixWord ++ tailWord_113678) baseStart_113678 baseEnd_113678 := by
    simpa [prefixWord, tailWord_113678, baseEnd_113678] using wordTrace_append hprefix tailTrace_113678
  have hstable : (prefixWord ++ tailWord_113678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113678).length < 2 ^ (prefixWord ++ tailWord_113678).sum := by decide
  have hdescent : baseEnd_113678 < baseStart_113678 := by decide
  rcases family_descends (prefixWord ++ tailWord_113678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113889 : List Nat := [1, 2, 3, 1, 3, 2, 2, 7]
def baseStart_113889 : Nat := 118140960795 + 113889 * 2 ^ 59
def prefixEnd_113889 : Nat := 4983230072969 + 3 ^ 40 * 113889 * 2
def baseEnd_113889 : Nat := 8663673816297798883517

theorem tailTrace_113889 : CollatzResearch.WordTrace tailWord_113889 prefixEnd_113889 8663673816297798883517 := by
  unfold tailWord_113889
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153873084407078537760721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2769248722938052358507147 4153873084407078537760721)
  ·
    refine ⟨3115404813305308903320541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153873084407078537760721 3115404813305308903320541)
    ·
      refine ⟨1168276804989490838745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3115404813305308903320541 1168276804989490838745203)
      ·
        refine ⟨1752415207484236258117805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168276804989490838745203 1752415207484236258117805)
        ·
          refine ⟨657155702806588596794177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1752415207484236258117805 657155702806588596794177)
          ·
            refine ⟨492866777104941447595633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657155702806588596794177 492866777104941447595633)
            ·
              refine ⟨369650082828706085696725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 492866777104941447595633 369650082828706085696725)
              ·
                refine ⟨8663673816297798883517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 369650082828706085696725 8663673816297798883517)
                ·
                  rfl

theorem cell21_113889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 7].length) (baseStart_113889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113889 prefixEnd_113889 := by exact prefixLift 113889
  have htrace : WordTrace (prefixWord ++ tailWord_113889) baseStart_113889 baseEnd_113889 := by
    simpa [prefixWord, tailWord_113889, baseEnd_113889] using wordTrace_append hprefix tailTrace_113889
  have hstable : (prefixWord ++ tailWord_113889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113889).length < 2 ^ (prefixWord ++ tailWord_113889).sum := by decide
  have hdescent : baseEnd_113889 < baseStart_113889 := by decide
  rcases family_descends (prefixWord ++ tailWord_113889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113906 : List Nat := [3, 2, 1, 3, 4, 8]
def baseStart_113906 : Nat := 118140960795 + 113906 * 2 ^ 59
def prefixEnd_113906 : Nat := 4983230072969 + 3 ^ 40 * 113906 * 2
def baseEnd_113906 : Nat := 962774114092783143229

theorem tailTrace_113906 : CollatzResearch.WordTrace tailWord_113906 prefixEnd_113906 962774114092783143229 := by
  unfold tailWord_113906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038623281336372610282393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2769662083563660294086381 1038623281336372610282393)
  ·
    refine ⟨778967461002279457711795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1038623281336372610282393 778967461002279457711795)
    ·
      refine ⟨1168451191503419186567693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778967461002279457711795 1168451191503419186567693)
      ·
        refine ⟨438169196813782194962885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1168451191503419186567693 438169196813782194962885)
        ·
          refine ⟨82156724402584161555541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 438169196813782194962885 82156724402584161555541)
          ·
            refine ⟨962774114092783143229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 82156724402584161555541 962774114092783143229)
            ·
              rfl

theorem cell21_113906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 8].length) (baseStart_113906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113906 prefixEnd_113906 := by exact prefixLift 113906
  have htrace : WordTrace (prefixWord ++ tailWord_113906) baseStart_113906 baseEnd_113906 := by
    simpa [prefixWord, tailWord_113906, baseEnd_113906] using wordTrace_append hprefix tailTrace_113906
  have hstable : (prefixWord ++ tailWord_113906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113906).length < 2 ^ (prefixWord ++ tailWord_113906).sum := by decide
  have hdescent : baseEnd_113906 < baseStart_113906 := by decide
  rcases family_descends (prefixWord ++ tailWord_113906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113985 : List Nat := [1, 2, 5, 2, 1, 2, 3, 1, 4]
def baseStart_113985 : Nat := 118140960795 + 113985 * 2 ^ 59
def prefixEnd_113985 : Nat := 4983230072969 + 3 ^ 40 * 113985 * 2
def baseEnd_113985 : Nat := 26012929956818563050355

theorem tailTrace_113985 : CollatzResearch.WordTrace tailWord_113985 prefixEnd_113985 26012929956818563050355 := by
  unfold tailWord_113985
  simp only [CollatzResearch.WordTrace]
  refine ⟨4157374492059286933255409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2771582994706191288836939 4157374492059286933255409)
  ·
    refine ⟨3118030869044465199941557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4157374492059286933255409 3118030869044465199941557)
    ·
      refine ⟨292315393972918612494521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3118030869044465199941557 292315393972918612494521)
      ·
        refine ⟨219236545479688959370891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292315393972918612494521 219236545479688959370891)
        ·
          refine ⟨328854818219533439056337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219236545479688959370891 328854818219533439056337)
          ·
            refine ⟨246641113664650079292253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328854818219533439056337 246641113664650079292253)
            ·
              refine ⟨92490417624243779734595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 246641113664650079292253 92490417624243779734595)
              ·
                refine ⟨138735626436365669601893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92490417624243779734595 138735626436365669601893)
                ·
                  refine ⟨26012929956818563050355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 138735626436365669601893 26012929956818563050355)
                  ·
                    rfl

theorem cell21_113985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 4].length) (baseStart_113985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113985 prefixEnd_113985 := by exact prefixLift 113985
  have htrace : WordTrace (prefixWord ++ tailWord_113985) baseStart_113985 baseEnd_113985 := by
    simpa [prefixWord, tailWord_113985, baseEnd_113985] using wordTrace_append hprefix tailTrace_113985
  have hstable : (prefixWord ++ tailWord_113985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113985).length < 2 ^ (prefixWord ++ tailWord_113985).sum := by decide
  have hdescent : baseEnd_113985 < baseStart_113985 := by decide
  rcases family_descends (prefixWord ++ tailWord_113985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113996 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 5]
def baseStart_113996 : Nat := 118140960795 + 113996 * 2 ^ 59
def prefixEnd_113996 : Nat := 4983230072969 + 3 ^ 40 * 113996 * 2
def baseEnd_113996 : Nat := 26015440306684988366999

theorem tailTrace_113996 : CollatzResearch.WordTrace tailWord_113996 prefixEnd_113996 26015440306684988366999 := by
  unfold tailWord_113996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078887847509717905952921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2771850463346290541270561 2078887847509717905952921)
  ·
    refine ⟨1559165885632288429464691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2078887847509717905952921 1559165885632288429464691)
    ·
      refine ⟨2338748828448432644197037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559165885632288429464691 2338748828448432644197037)
      ·
        refine ⟨877030810668162241573889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2338748828448432644197037 877030810668162241573889)
        ·
          refine ⟨657773108001121681180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 877030810668162241573889 657773108001121681180417)
          ·
            refine ⟨493329831000841260885313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 657773108001121681180417 493329831000841260885313)
            ·
              refine ⟨369997373250630945663985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 493329831000841260885313 369997373250630945663985)
              ·
                refine ⟨277498029937973209247989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 369997373250630945663985 277498029937973209247989)
                ·
                  refine ⟨26015440306684988366999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277498029937973209247989 26015440306684988366999)
                  ·
                    rfl

theorem cell21_113996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_113996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_113996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_113996 prefixEnd_113996 := by exact prefixLift 113996
  have htrace : WordTrace (prefixWord ++ tailWord_113996) baseStart_113996 baseEnd_113996 := by
    simpa [prefixWord, tailWord_113996, baseEnd_113996] using wordTrace_append hprefix tailTrace_113996
  have hstable : (prefixWord ++ tailWord_113996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113996).length < 2 ^ (prefixWord ++ tailWord_113996).sum := by decide
  have hdescent : baseEnd_113996 < baseStart_113996 := by decide
  rcases family_descends (prefixWord ++ tailWord_113996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114010 : List Nat := [3, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_114010 : Nat := 118140960795 + 114010 * 2 ^ 59
def prefixEnd_114010 : Nat := 4983230072969 + 3 ^ 40 * 114010 * 2
def baseEnd_114010 : Nat := 26018635297424075133637

theorem tailTrace_114010 : CollatzResearch.WordTrace tailWord_114010 prefixEnd_114010 26018635297424075133637 := by
  unfold tailWord_114010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1039571579242179050728871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2772190877979144135276989 1039571579242179050728871)
  ·
    refine ⟨1559357368863268576093307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1039571579242179050728871 1559357368863268576093307)
    ·
      refine ⟨2339036053294902864139961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559357368863268576093307 2339036053294902864139961)
      ·
        refine ⟨1754277039971177148104971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339036053294902864139961 1754277039971177148104971)
        ·
          refine ⟨2631415559956765722157457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754277039971177148104971 2631415559956765722157457)
          ·
            refine ⟨1973561669967574291618093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2631415559956765722157457 1973561669967574291618093)
            ·
              refine ⟨740085626237840359356785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1973561669967574291618093 740085626237840359356785)
              ·
                refine ⟨555064219678380269517589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740085626237840359356785 555064219678380269517589)
                ·
                  refine ⟨26018635297424075133637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 555064219678380269517589 26018635297424075133637)
                  ·
                    rfl

theorem cell21_114010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_114010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114010 prefixEnd_114010 := by exact prefixLift 114010
  have htrace : WordTrace (prefixWord ++ tailWord_114010) baseStart_114010 baseEnd_114010 := by
    simpa [prefixWord, tailWord_114010, baseEnd_114010] using wordTrace_append hprefix tailTrace_114010
  have hstable : (prefixWord ++ tailWord_114010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114010).length < 2 ^ (prefixWord ++ tailWord_114010).sum := by decide
  have hdescent : baseEnd_114010 < baseStart_114010 := by decide
  rcases family_descends (prefixWord ++ tailWord_114010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114134 : List Nat := [5, 2, 1, 1, 1, 3, 8]
def baseStart_114134 : Nat := 118140960795 + 114134 * 2 ^ 59
def prefixEnd_114134 : Nat := 4983230072969 + 3 ^ 40 * 114134 * 2
def baseEnd_114134 : Nat := 2894103754091935007413

theorem tailTrace_114134 : CollatzResearch.WordTrace tailWord_114134 prefixEnd_114134 2894103754091935007413 := by
  unfold tailWord_114134
  simp only [CollatzResearch.WordTrace]
  refine ⟨260175560532467836276841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2775205979012990253619637 260175560532467836276841)
  ·
    refine ⟨195131670399350877207631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260175560532467836276841 195131670399350877207631)
    ·
      refine ⟨292697505599026315811447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195131670399350877207631 292697505599026315811447)
      ·
        refine ⟨439046258398539473717171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292697505599026315811447 439046258398539473717171)
        ·
          refine ⟨658569387597809210575757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439046258398539473717171 658569387597809210575757)
          ·
            refine ⟨246963520349178453965909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658569387597809210575757 246963520349178453965909)
            ·
              refine ⟨2894103754091935007413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 246963520349178453965909 2894103754091935007413)
              ·
                rfl

theorem cell21_114134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 8].length) (baseStart_114134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114134 prefixEnd_114134 := by exact prefixLift 114134
  have htrace : WordTrace (prefixWord ++ tailWord_114134) baseStart_114134 baseEnd_114134 := by
    simpa [prefixWord, tailWord_114134, baseEnd_114134] using wordTrace_append hprefix tailTrace_114134
  have hstable : (prefixWord ++ tailWord_114134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114134).length < 2 ^ (prefixWord ++ tailWord_114134).sum := by decide
  have hdescent : baseEnd_114134 < baseStart_114134 := by decide
  rcases family_descends (prefixWord ++ tailWord_114134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114165 : List Nat := [1, 3, 5, 1, 1, 1, 2, 2, 5]
def baseStart_114165 : Nat := 118140960795 + 114165 * 2 ^ 59
def prefixEnd_114165 : Nat := 4983230072969 + 3 ^ 40 * 114165 * 2
def baseEnd_114165 : Nat := 26054008409178250049987

theorem tailTrace_114165 : CollatzResearch.WordTrace tailWord_114165 prefixEnd_114165 26054008409178250049987 := by
  unfold tailWord_114165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4163939631407177674807949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2775959754271451783205299 4163939631407177674807949)
  ·
    refine ⟨1561477361777691628052981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4163939631407177674807949 1561477361777691628052981)
    ·
      refine ⟨146388502666658590129967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1561477361777691628052981 146388502666658590129967)
      ·
        refine ⟨219582753999987885194951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146388502666658590129967 219582753999987885194951)
        ·
          refine ⟨329374130999981827792427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 219582753999987885194951 329374130999981827792427)
          ·
            refine ⟨494061196499972741688641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329374130999981827792427 494061196499972741688641)
            ·
              refine ⟨370545897374979556266481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494061196499972741688641 370545897374979556266481)
              ·
                refine ⟨277909423031234667199861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 370545897374979556266481 277909423031234667199861)
                ·
                  refine ⟨26054008409178250049987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 277909423031234667199861 26054008409178250049987)
                  ·
                    rfl

theorem cell21_114165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_114165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114165 prefixEnd_114165 := by exact prefixLift 114165
  have htrace : WordTrace (prefixWord ++ tailWord_114165) baseStart_114165 baseEnd_114165 := by
    simpa [prefixWord, tailWord_114165, baseEnd_114165] using wordTrace_append hprefix tailTrace_114165
  have hstable : (prefixWord ++ tailWord_114165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114165).length < 2 ^ (prefixWord ++ tailWord_114165).sum := by decide
  have hdescent : baseEnd_114165 < baseStart_114165 := by decide
  rcases family_descends (prefixWord ++ tailWord_114165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114241 : List Nat := [1, 2, 5, 1, 1, 1, 2, 5, 3]
def baseStart_114241 : Nat := 118140960795 + 114241 * 2 ^ 59
def prefixEnd_114241 : Nat := 4983230072969 + 3 ^ 40 * 114241 * 2
def baseEnd_114241 : Nat := 26071352644619006783165

theorem tailTrace_114241 : CollatzResearch.WordTrace tailWord_114241 prefixEnd_114241 26071352644619006783165 := by
  unfold tailWord_114241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4166711579131842654574577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2777807719421228436383051 4166711579131842654574577)
  ·
    refine ⟨3125033684348881990930933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4166711579131842654574577 3125033684348881990930933)
    ·
      refine ⟨292971907907707686649775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3125033684348881990930933 292971907907707686649775)
      ·
        refine ⟨439457861861561529974663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292971907907707686649775 439457861861561529974663)
        ·
          refine ⟨659186792792342294961995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 439457861861561529974663 659186792792342294961995)
          ·
            refine ⟨988780189188513442442993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 659186792792342294961995 988780189188513442442993)
            ·
              refine ⟨741585141891385081832245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 988780189188513442442993 741585141891385081832245)
              ·
                refine ⟨69523607052317351421773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 741585141891385081832245 69523607052317351421773)
                ·
                  refine ⟨26071352644619006783165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69523607052317351421773 26071352644619006783165)
                  ·
                    rfl

theorem cell21_114241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 5, 3].length) (baseStart_114241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114241 prefixEnd_114241 := by exact prefixLift 114241
  have htrace : WordTrace (prefixWord ++ tailWord_114241) baseStart_114241 baseEnd_114241 := by
    simpa [prefixWord, tailWord_114241, baseEnd_114241] using wordTrace_append hprefix tailTrace_114241
  have hstable : (prefixWord ++ tailWord_114241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114241).length < 2 ^ (prefixWord ++ tailWord_114241).sum := by decide
  have hdescent : baseEnd_114241 < baseStart_114241 := by decide
  rcases family_descends (prefixWord ++ tailWord_114241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114252 : List Nat := [2, 2, 1, 3, 1, 12]
def baseStart_114252 : Nat := 118140960795 + 114252 * 2 ^ 59
def prefixEnd_114252 : Nat := 4983230072969 + 3 ^ 40 * 114252 * 2
def baseEnd_114252 : Nat := 965698629425386374067

theorem tailTrace_114252 : CollatzResearch.WordTrace tailWord_114252 prefixEnd_114252 965698629425386374067 := by
  unfold tailWord_114252
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083556391045995766612505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2778075188061327688816673 2083556391045995766612505)
  ·
    refine ⟨1562667293284496824959379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2083556391045995766612505 1562667293284496824959379)
    ·
      refine ⟨2344000939926745237439069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1562667293284496824959379 2344000939926745237439069)
      ·
        refine ⟨879000352472529464039651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2344000939926745237439069 879000352472529464039651)
        ·
          refine ⟨1318500528708794196059477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 879000352472529464039651 1318500528708794196059477)
          ·
            refine ⟨965698629425386374067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1318500528708794196059477 965698629425386374067)
            ·
              rfl

theorem cell21_114252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 12].length) (baseStart_114252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114252 prefixEnd_114252 := by exact prefixLift 114252
  have htrace : WordTrace (prefixWord ++ tailWord_114252) baseStart_114252 baseEnd_114252 := by
    simpa [prefixWord, tailWord_114252, baseEnd_114252] using wordTrace_append hprefix tailTrace_114252
  have hstable : (prefixWord ++ tailWord_114252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114252).length < 2 ^ (prefixWord ++ tailWord_114252).sum := by decide
  have hdescent : baseEnd_114252 < baseStart_114252 := by decide
  rcases family_descends (prefixWord ++ tailWord_114252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114258 : List Nat := [3, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_114258 : Nat := 118140960795 + 114258 * 2 ^ 59
def prefixEnd_114258 : Nat := 4983230072969 + 3 ^ 40 * 114258 * 2
def baseEnd_114258 : Nat := 26075232276230754999797

theorem tailTrace_114258 : CollatzResearch.WordTrace tailWord_114258 prefixEnd_114258 26075232276230754999797 := by
  unfold tailWord_114258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1041832905017563639485857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2778221080046836371962285 1041832905017563639485857)
  ·
    refine ⟨781374678763172729614393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1041832905017563639485857 781374678763172729614393)
    ·
      refine ⟨586031009072379547210795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 781374678763172729614393 586031009072379547210795)
      ·
        refine ⟨879046513608569320816193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586031009072379547210795 879046513608569320816193)
        ·
          refine ⟨659284885206426990612145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 879046513608569320816193 659284885206426990612145)
          ·
            refine ⟨494463663904820242959109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659284885206426990612145 494463663904820242959109)
            ·
              refine ⟨92711936982153795554833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494463663904820242959109 92711936982153795554833)
              ·
                refine ⟨69533952736615346666125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92711936982153795554833 69533952736615346666125)
                ·
                  refine ⟨26075232276230754999797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69533952736615346666125 26075232276230754999797)
                  ·
                    rfl

theorem cell21_114258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_114258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114258 prefixEnd_114258 := by exact prefixLift 114258
  have htrace : WordTrace (prefixWord ++ tailWord_114258) baseStart_114258 baseEnd_114258 := by
    simpa [prefixWord, tailWord_114258, baseEnd_114258] using wordTrace_append hprefix tailTrace_114258
  have hstable : (prefixWord ++ tailWord_114258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114258).length < 2 ^ (prefixWord ++ tailWord_114258).sum := by decide
  have hdescent : baseEnd_114258 < baseStart_114258 := by decide
  rcases family_descends (prefixWord ++ tailWord_114258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114404 : List Nat := [2, 3, 1, 1, 1, 3, 1, 9]
def baseStart_114404 : Nat := 118140960795 + 114404 * 2 ^ 59
def prefixEnd_114404 : Nat := 4983230072969 + 3 ^ 40 * 114404 * 2
def baseEnd_114404 : Nat := 8702850488455648522055

theorem tailTrace_114404 : CollatzResearch.WordTrace tailWord_114404 prefixEnd_114404 8702850488455648522055 := by
  unfold tailWord_114404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2086328338770660746379133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2781771118360880995172177 2086328338770660746379133)
  ·
    refine ⟨782373127038997779892175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2086328338770660746379133 782373127038997779892175)
    ·
      refine ⟨1173559690558496669838263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 782373127038997779892175 1173559690558496669838263)
      ·
        refine ⟨1760339535837745004757395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1173559690558496669838263 1760339535837745004757395)
        ·
          refine ⟨2640509303756617507136093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1760339535837745004757395 2640509303756617507136093)
          ·
            refine ⟨990190988908731565176035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2640509303756617507136093 990190988908731565176035)
            ·
              refine ⟨1485286483363097347764053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 990190988908731565176035 1485286483363097347764053)
              ·
                refine ⟨8702850488455648522055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1485286483363097347764053 8702850488455648522055)
                ·
                  rfl

theorem cell21_114404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 9].length) (baseStart_114404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114404 prefixEnd_114404 := by exact prefixLift 114404
  have htrace : WordTrace (prefixWord ++ tailWord_114404) baseStart_114404 baseEnd_114404 := by
    simpa [prefixWord, tailWord_114404, baseEnd_114404] using wordTrace_append hprefix tailTrace_114404
  have hstable : (prefixWord ++ tailWord_114404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114404).length < 2 ^ (prefixWord ++ tailWord_114404).sum := by decide
  have hdescent : baseEnd_114404 < baseStart_114404 := by decide
  rcases family_descends (prefixWord ++ tailWord_114404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114421 : List Nat := [1, 3, 6, 11]
def baseStart_114421 : Nat := 118140960795 + 114421 * 2 ^ 59
def prefixEnd_114421 : Nat := 4983230072969 + 3 ^ 40 * 114421 * 2
def baseEnd_114421 : Nat := 107458564185097505279

theorem tailTrace_114421 : CollatzResearch.WordTrace tailWord_114421 prefixEnd_114421 107458564185097505279 := by
  unfold tailWord_114421
  simp only [CollatzResearch.WordTrace]
  refine ⟨4173276718479733396127117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2782184478986488930751411 4173276718479733396127117)
  ·
    refine ⟨1564978769429900023547669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4173276718479733396127117 1564978769429900023547669)
    ·
      refine ⟨73358379817026563603797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1564978769429900023547669 73358379817026563603797)
      ·
        refine ⟨107458564185097505279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 73358379817026563603797 107458564185097505279)
        ·
          rfl

theorem cell21_114421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 11].length) (baseStart_114421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114421 prefixEnd_114421 := by exact prefixLift 114421
  have htrace : WordTrace (prefixWord ++ tailWord_114421) baseStart_114421 baseEnd_114421 := by
    simpa [prefixWord, tailWord_114421, baseEnd_114421] using wordTrace_append hprefix tailTrace_114421
  have hstable : (prefixWord ++ tailWord_114421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114421).length < 2 ^ (prefixWord ++ tailWord_114421).sum := by decide
  have hdescent : baseEnd_114421 < baseStart_114421 := by decide
  rcases family_descends (prefixWord ++ tailWord_114421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114449 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 8]
def baseStart_114449 : Nat := 118140960795 + 114449 * 2 ^ 59
def prefixEnd_114449 : Nat := 4983230072969 + 3 ^ 40 * 114449 * 2
def baseEnd_114449 : Nat := 26118821078456867316073

theorem tailTrace_114449 : CollatzResearch.WordTrace tailWord_114449 prefixEnd_114449 26118821078456867316073 := by
  unfold tailWord_114449
  simp only [CollatzResearch.WordTrace]
  refine ⟨4174297962378294178146401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2782865308252196118764267 4174297962378294178146401)
  ·
    refine ⟨3130723471783720633609801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4174297962378294178146401 3130723471783720633609801)
    ·
      refine ⟨2348042603837790475207351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3130723471783720633609801 2348042603837790475207351)
      ·
        refine ⟨3522063905756685712811027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2348042603837790475207351 3522063905756685712811027)
        ·
          refine ⟨5283095858635028569216541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3522063905756685712811027 5283095858635028569216541)
          ·
            refine ⟨1981160946988135713456203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5283095858635028569216541 1981160946988135713456203)
            ·
              refine ⟨2971741420482203570184305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1981160946988135713456203 2971741420482203570184305)
              ·
                refine ⟨2228806065361652677638229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2971741420482203570184305 2228806065361652677638229)
                ·
                  refine ⟨26118821078456867316073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2228806065361652677638229 26118821078456867316073)
                  ·
                    rfl

theorem cell21_114449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_114449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114449 prefixEnd_114449 := by exact prefixLift 114449
  have htrace : WordTrace (prefixWord ++ tailWord_114449) baseStart_114449 baseEnd_114449 := by
    simpa [prefixWord, tailWord_114449, baseEnd_114449] using wordTrace_append hprefix tailTrace_114449
  have hstable : (prefixWord ++ tailWord_114449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114449).length < 2 ^ (prefixWord ++ tailWord_114449).sum := by decide
  have hdescent : baseEnd_114449 < baseStart_114449 := by decide
  rcases family_descends (prefixWord ++ tailWord_114449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114466 : List Nat := [3, 3, 1, 1, 2, 1, 2, 2, 6]
def baseStart_114466 : Nat := 118140960795 + 114466 * 2 ^ 59
def prefixEnd_114466 : Nat := 4983230072969 + 3 ^ 40 * 114466 * 2
def baseEnd_114466 : Nat := 26122700710068615532705

theorem tailTrace_114466 : CollatzResearch.WordTrace tailWord_114466 prefixEnd_114466 26122700710068615532705 := by
  unfold tailWord_114466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043729500829176520378813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2783278668877804054343501 1043729500829176520378813)
  ·
    refine ⟨391398562810941195142055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1043729500829176520378813 391398562810941195142055)
    ·
      refine ⟨587097844216411792713083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391398562810941195142055 587097844216411792713083)
      ·
        refine ⟨880646766324617689069625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587097844216411792713083 880646766324617689069625)
        ·
          refine ⟨660485074743463266802219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880646766324617689069625 660485074743463266802219)
          ·
            refine ⟨990727612115194900203329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660485074743463266802219 990727612115194900203329)
            ·
              refine ⟨743045709086396175152497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 990727612115194900203329 743045709086396175152497)
              ·
                refine ⟨557284281814797131364373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743045709086396175152497 557284281814797131364373)
                ·
                  refine ⟨26122700710068615532705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557284281814797131364373 26122700710068615532705)
                  ·
                    rfl

theorem cell21_114466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_114466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114466 prefixEnd_114466 := by exact prefixLift 114466
  have htrace : WordTrace (prefixWord ++ tailWord_114466) baseStart_114466 baseEnd_114466 := by
    simpa [prefixWord, tailWord_114466, baseEnd_114466] using wordTrace_append hprefix tailTrace_114466
  have hstable : (prefixWord ++ tailWord_114466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114466).length < 2 ^ (prefixWord ++ tailWord_114466).sum := by decide
  have hdescent : baseEnd_114466 < baseStart_114466 := by decide
  rcases family_descends (prefixWord ++ tailWord_114466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114469 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 3]
def baseStart_114469 : Nat := 118140960795 + 114469 * 2 ^ 59
def prefixEnd_114469 : Nat := 4983230072969 + 3 ^ 40 * 114469 * 2
def baseEnd_114469 : Nat := 26123385350941276982699

theorem tailTrace_114469 : CollatzResearch.WordTrace tailWord_114469 prefixEnd_114469 26123385350941276982699 := by
  unfold tailWord_114469
  simp only [CollatzResearch.WordTrace]
  refine ⟨4175027422305837593874461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2783351614870558395916307 4175027422305837593874461)
  ·
    refine ⟨1565635283364689097702923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4175027422305837593874461 1565635283364689097702923)
    ·
      refine ⟨2348452925047033646554385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565635283364689097702923 2348452925047033646554385)
      ·
        refine ⟨1761339693785275234915789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2348452925047033646554385 1761339693785275234915789)
        ·
          refine ⟨660502385169478213093421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1761339693785275234915789 660502385169478213093421)
          ·
            refine ⟨247688394438554329910033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660502385169478213093421 247688394438554329910033)
            ·
              refine ⟨185766295828915747432525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247688394438554329910033 185766295828915747432525)
              ·
                refine ⟨69662360935843405287197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185766295828915747432525 69662360935843405287197)
                ·
                  refine ⟨26123385350941276982699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69662360935843405287197 26123385350941276982699)
                  ·
                    rfl

theorem cell21_114469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_114469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114469 prefixEnd_114469 := by exact prefixLift 114469
  have htrace : WordTrace (prefixWord ++ tailWord_114469) baseStart_114469 baseEnd_114469 := by
    simpa [prefixWord, tailWord_114469, baseEnd_114469] using wordTrace_append hprefix tailTrace_114469
  have hstable : (prefixWord ++ tailWord_114469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114469).length < 2 ^ (prefixWord ++ tailWord_114469).sum := by decide
  have hdescent : baseEnd_114469 < baseStart_114469 := by decide
  rcases family_descends (prefixWord ++ tailWord_114469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114486 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 3]
def baseStart_114486 : Nat := 118140960795 + 114486 * 2 ^ 59
def prefixEnd_114486 : Nat := 4983230072969 + 3 ^ 40 * 114486 * 2
def baseEnd_114486 : Nat := 26127264982553025199331

theorem tailTrace_114486 : CollatzResearch.WordTrace tailWord_114486 prefixEnd_114486 26127264982553025199331 := by
  unfold tailWord_114486
  simp only [CollatzResearch.WordTrace]
  refine ⟨260977966452765593577707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2783764975496166331495541 260977966452765593577707)
  ·
    refine ⟨391466949679148390366561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260977966452765593577707 391466949679148390366561)
    ·
      refine ⟨293600212259361292774921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 391466949679148390366561 293600212259361292774921)
      ·
        refine ⟨220200159194520969581191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293600212259361292774921 220200159194520969581191)
        ·
          refine ⟨330300238791781454371787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220200159194520969581191 330300238791781454371787)
          ·
            refine ⟨495450358187672181557681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330300238791781454371787 495450358187672181557681)
            ·
              refine ⟨371587768640754136168261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 495450358187672181557681 371587768640754136168261)
              ·
                refine ⟨69672706620141400531549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 371587768640754136168261 69672706620141400531549)
                ·
                  refine ⟨26127264982553025199331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69672706620141400531549 26127264982553025199331)
                  ·
                    rfl

theorem cell21_114486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_114486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114486 prefixEnd_114486 := by exact prefixLift 114486
  have htrace : WordTrace (prefixWord ++ tailWord_114486) baseStart_114486 baseEnd_114486 := by
    simpa [prefixWord, tailWord_114486, baseEnd_114486] using wordTrace_append hprefix tailTrace_114486
  have hstable : (prefixWord ++ tailWord_114486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114486).length < 2 ^ (prefixWord ++ tailWord_114486).sum := by decide
  have hdescent : baseEnd_114486 < baseStart_114486 := by decide
  rcases family_descends (prefixWord ++ tailWord_114486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114514 : List Nat := [3, 2, 2, 1, 1, 5, 2, 5]
def baseStart_114514 : Nat := 118140960795 + 114514 * 2 ^ 59
def prefixEnd_114514 : Nat := 4983230072969 + 3 ^ 40 * 114514 * 2
def baseEnd_114514 : Nat := 8711218321343732910869

theorem tailTrace_114514 : CollatzResearch.WordTrace tailWord_114514 prefixEnd_114514 8711218321343732910869 := by
  unfold tailWord_114514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1044167176785702569815649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2784445804761873519508397 1044167176785702569815649)
  ·
    refine ⟨783125382589276927361737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1044167176785702569815649 783125382589276927361737)
    ·
      refine ⟨587344036941957695521303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 783125382589276927361737 587344036941957695521303)
      ·
        refine ⟨881016055412936543281955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 587344036941957695521303 881016055412936543281955)
        ·
          refine ⟨1321524083119404814922933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 881016055412936543281955 1321524083119404814922933)
          ·
            refine ⟨123892882792444201399025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1321524083119404814922933 123892882792444201399025)
            ·
              refine ⟨92919662094333151049269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123892882792444201399025 92919662094333151049269)
              ·
                refine ⟨8711218321343732910869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 92919662094333151049269 8711218321343732910869)
                ·
                  rfl

theorem cell21_114514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_114514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114514 prefixEnd_114514 := by exact prefixLift 114514
  have htrace : WordTrace (prefixWord ++ tailWord_114514) baseStart_114514 baseEnd_114514 := by
    simpa [prefixWord, tailWord_114514, baseEnd_114514] using wordTrace_append hprefix tailTrace_114514
  have hstable : (prefixWord ++ tailWord_114514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114514).length < 2 ^ (prefixWord ++ tailWord_114514).sum := by decide
  have hdescent : baseEnd_114514 < baseStart_114514 := by decide
  rcases family_descends (prefixWord ++ tailWord_114514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114545 : List Nat := [1, 2, 2, 2, 1, 3, 5, 2, 3]
def baseStart_114545 : Nat := 118140960795 + 114545 * 2 ^ 59
def prefixEnd_114545 : Nat := 4983230072969 + 3 ^ 40 * 114545 * 2
def baseEnd_114545 : Nat := 26140729586382033715877

theorem tailTrace_114545 : CollatzResearch.WordTrace tailWord_114545 prefixEnd_114545 26140729586382033715877 := by
  unfold tailWord_114545
  simp only [CollatzResearch.WordTrace]
  refine ⟨4177799370030502573641089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2785199580020335049094059 4177799370030502573641089)
  ·
    refine ⟨3133349527522876930230817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4177799370030502573641089 3133349527522876930230817)
    ·
      refine ⟨2350012145642157697673113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3133349527522876930230817 2350012145642157697673113)
      ·
        refine ⟨1762509109231618273254835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2350012145642157697673113 1762509109231618273254835)
        ·
          refine ⟨2643763663847427409882253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762509109231618273254835 2643763663847427409882253)
          ·
            refine ⟨991411373942785278705845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2643763663847427409882253 991411373942785278705845)
            ·
              refine ⟨92944816307136119878673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 991411373942785278705845 92944816307136119878673)
              ·
                refine ⟨69708612230352089909005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92944816307136119878673 69708612230352089909005)
                ·
                  refine ⟨26140729586382033715877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69708612230352089909005 26140729586382033715877)
                  ·
                    rfl

theorem cell21_114545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 3].length) (baseStart_114545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114545 prefixEnd_114545 := by exact prefixLift 114545
  have htrace : WordTrace (prefixWord ++ tailWord_114545) baseStart_114545 baseEnd_114545 := by
    simpa [prefixWord, tailWord_114545, baseEnd_114545] using wordTrace_append hprefix tailTrace_114545
  have hstable : (prefixWord ++ tailWord_114545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114545).length < 2 ^ (prefixWord ++ tailWord_114545).sum := by decide
  have hdescent : baseEnd_114545 < baseStart_114545 := by decide
  rcases family_descends (prefixWord ++ tailWord_114545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114590 : List Nat := [4, 3, 1, 3, 1, 9]
def baseStart_114590 : Nat := 118140960795 + 114590 * 2 ^ 59
def prefixEnd_114590 : Nat := 4983230072969 + 3 ^ 40 * 114590 * 2
def baseEnd_114590 : Nat := 968555525906368720955

theorem tailTrace_114590 : CollatzResearch.WordTrace tailWord_114590 prefixEnd_114590 968555525906368720955 := by
  unfold tailWord_114590
  simp only [CollatzResearch.WordTrace]
  refine ⟨522430081858434407378653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2786293769911650172686149 522430081858434407378653)
  ·
    refine ⟨195911280696912902766995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 522430081858434407378653 195911280696912902766995)
    ·
      refine ⟨293866921045369354150493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195911280696912902766995 293866921045369354150493)
      ·
        refine ⟨110200095392013507806435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293866921045369354150493 110200095392013507806435)
        ·
          refine ⟨165300143088020261709653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110200095392013507806435 165300143088020261709653)
          ·
            refine ⟨968555525906368720955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 165300143088020261709653 968555525906368720955)
            ·
              rfl

theorem cell21_114590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 9].length) (baseStart_114590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114590 prefixEnd_114590 := by exact prefixLift 114590
  have htrace : WordTrace (prefixWord ++ tailWord_114590) baseStart_114590 baseEnd_114590 := by
    simpa [prefixWord, tailWord_114590, baseEnd_114590] using wordTrace_append hprefix tailTrace_114590
  have hstable : (prefixWord ++ tailWord_114590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114590).length < 2 ^ (prefixWord ++ tailWord_114590).sum := by decide
  have hdescent : baseEnd_114590 < baseStart_114590 := by decide
  rcases family_descends (prefixWord ++ tailWord_114590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114669 : List Nat := [1, 5, 1, 4, 1, 1, 3, 1, 4]
def baseStart_114669 : Nat := 118140960795 + 114669 * 2 ^ 59
def prefixEnd_114669 : Nat := 4983230072969 + 3 ^ 40 * 114669 * 2
def baseEnd_114669 : Nat := 26169028075785373648957

theorem tailTrace_114669 : CollatzResearch.WordTrace tailWord_114669 prefixEnd_114669 26169028075785373648957 := by
  unfold tailWord_114669
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182322021581271751155061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2788214681054181167436707 4182322021581271751155061)
  ·
    refine ⟨392092689523244226670787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4182322021581271751155061 392092689523244226670787)
    ·
      refine ⟨588139034284866340006181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392092689523244226670787 588139034284866340006181)
      ·
        refine ⟨110276068928412438751159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 588139034284866340006181 110276068928412438751159)
        ·
          refine ⟨165414103392618658126739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110276068928412438751159 165414103392618658126739)
          ·
            refine ⟨248121155088927987190109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165414103392618658126739 248121155088927987190109)
            ·
              refine ⟨93045433158347995196291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248121155088927987190109 93045433158347995196291)
              ·
                refine ⟨139568149737521992794437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93045433158347995196291 139568149737521992794437)
                ·
                  refine ⟨26169028075785373648957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139568149737521992794437 26169028075785373648957)
                  ·
                    rfl

theorem cell21_114669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_114669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114669 prefixEnd_114669 := by exact prefixLift 114669
  have htrace : WordTrace (prefixWord ++ tailWord_114669) baseStart_114669 baseEnd_114669 := by
    simpa [prefixWord, tailWord_114669, baseEnd_114669] using wordTrace_append hprefix tailTrace_114669
  have hstable : (prefixWord ++ tailWord_114669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114669).length < 2 ^ (prefixWord ++ tailWord_114669).sum := by decide
  have hdescent : baseEnd_114669 < baseStart_114669 := by decide
  rcases family_descends (prefixWord ++ tailWord_114669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114728 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 4]
def baseStart_114728 : Nat := 118140960795 + 114728 * 2 ^ 59
def prefixEnd_114728 : Nat := 4983230072969 + 3 ^ 40 * 114728 * 2
def baseEnd_114728 : Nat := 26182492679614382165503

theorem tailTrace_114728 : CollatzResearch.WordTrace tailWord_114728 prefixEnd_114728 26182492679614382165503 := by
  unfold tailWord_114728
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092236964183762413776419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2789649285578349885035225 2092236964183762413776419)
  ·
    refine ⟨3138355446275643620664629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092236964183762413776419 3138355446275643620664629)
    ·
      refine ⟨294220823088341589437309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3138355446275643620664629 294220823088341589437309)
      ·
        refine ⟨110332808658128096038991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294220823088341589437309 110332808658128096038991)
        ·
          refine ⟨165499212987192144058487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110332808658128096038991 165499212987192144058487)
          ·
            refine ⟨248248819480788216087731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165499212987192144058487 248248819480788216087731)
            ·
              refine ⟨372373229221182324131597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248248819480788216087731 372373229221182324131597)
              ·
                refine ⟨139639960957943371549349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372373229221182324131597 139639960957943371549349)
                ·
                  refine ⟨26182492679614382165503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139639960957943371549349 26182492679614382165503)
                  ·
                    rfl

theorem cell21_114728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_114728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114728 prefixEnd_114728 := by exact prefixLift 114728
  have htrace : WordTrace (prefixWord ++ tailWord_114728) baseStart_114728 baseEnd_114728 := by
    simpa [prefixWord, tailWord_114728, baseEnd_114728] using wordTrace_append hprefix tailTrace_114728
  have hstable : (prefixWord ++ tailWord_114728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114728).length < 2 ^ (prefixWord ++ tailWord_114728).sum := by decide
  have hdescent : baseEnd_114728 < baseStart_114728 := by decide
  rcases family_descends (prefixWord ++ tailWord_114728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114773 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 3]
def baseStart_114773 : Nat := 118140960795 + 114773 * 2 ^ 59
def prefixEnd_114773 : Nat := 4983230072969 + 3 ^ 40 * 114773 * 2
def baseEnd_114773 : Nat := 26192762292704303915411

theorem tailTrace_114773 : CollatzResearch.WordTrace tailWord_114773 prefixEnd_114773 26192762292704303915411 := by
  unfold tailWord_114773
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186115213204497512940973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2790743475469665008627315 4186115213204497512940973)
  ·
    refine ⟨1569793204951686567352865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4186115213204497512940973 1569793204951686567352865)
    ·
      refine ⟨1177344903713764925514649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1569793204951686567352865 1177344903713764925514649)
      ·
        refine ⟨883008677785323694135987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177344903713764925514649 883008677785323694135987)
        ·
          refine ⟨1324513016677985541203981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 883008677785323694135987 1324513016677985541203981)
          ·
            refine ⟨496692381254244577951493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324513016677985541203981 496692381254244577951493)
            ·
              refine ⟨93129821485170858365905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 496692381254244577951493 93129821485170858365905)
              ·
                refine ⟨69847366113878143774429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93129821485170858365905 69847366113878143774429)
                ·
                  refine ⟨26192762292704303915411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69847366113878143774429 26192762292704303915411)
                  ·
                    rfl

theorem cell21_114773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_114773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114773 prefixEnd_114773 := by exact prefixLift 114773
  have htrace : WordTrace (prefixWord ++ tailWord_114773) baseStart_114773 baseEnd_114773 := by
    simpa [prefixWord, tailWord_114773, baseEnd_114773] using wordTrace_append hprefix tailTrace_114773
  have hstable : (prefixWord ++ tailWord_114773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114773).length < 2 ^ (prefixWord ++ tailWord_114773).sum := by decide
  have hdescent : baseEnd_114773 < baseStart_114773 := by decide
  rcases family_descends (prefixWord ++ tailWord_114773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114784 : List Nat := [2, 1, 1, 3, 2, 3, 3, 6]
def baseStart_114784 : Nat := 118140960795 + 114784 * 2 ^ 59
def prefixEnd_114784 : Nat := 4983230072969 + 3 ^ 40 * 114784 * 2
def baseEnd_114784 : Nat := 8731757547523576410685

theorem tailTrace_114784 : CollatzResearch.WordTrace tailWord_114784 prefixEnd_114784 8731757547523576410685 := by
  unfold tailWord_114784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2093258208082323195795703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2791010944109764261060937 2093258208082323195795703)
  ·
    refine ⟨3139887312123484793693555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2093258208082323195795703 3139887312123484793693555)
    ·
      refine ⟨4709830968185227190540333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3139887312123484793693555 4709830968185227190540333)
      ·
        refine ⟨1766186613069460196452625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4709830968185227190540333 1766186613069460196452625)
        ·
          refine ⟨1324639959802095147339469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766186613069460196452625 1324639959802095147339469)
          ·
            refine ⟨496739984925785680252301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1324639959802095147339469 496739984925785680252301)
            ·
              refine ⟨186277494347169630094613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496739984925785680252301 186277494347169630094613)
              ·
                refine ⟨8731757547523576410685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186277494347169630094613 8731757547523576410685)
                ·
                  rfl

theorem cell21_114784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 6].length) (baseStart_114784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114784 prefixEnd_114784 := by exact prefixLift 114784
  have htrace : WordTrace (prefixWord ++ tailWord_114784) baseStart_114784 baseEnd_114784 := by
    simpa [prefixWord, tailWord_114784, baseEnd_114784] using wordTrace_append hprefix tailTrace_114784
  have hstable : (prefixWord ++ tailWord_114784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114784).length < 2 ^ (prefixWord ++ tailWord_114784).sum := by decide
  have hdescent : baseEnd_114784 < baseStart_114784 := by decide
  rcases family_descends (prefixWord ++ tailWord_114784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114874 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_114874 : Nat := 118140960795 + 114874 * 2 ^ 59
def prefixEnd_114874 : Nat := 4983230072969 + 3 ^ 40 * 114874 * 2
def baseEnd_114874 : Nat := 26215811868750572731871

theorem tailTrace_114874 : CollatzResearch.WordTrace tailWord_114874 prefixEnd_114874 26215811868750572731871 := by
  unfold tailWord_114874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1047449746459647940591919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2793199323892394508245117 1047449746459647940591919)
  ·
    refine ⟨1571174619689471910887879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1047449746459647940591919 1571174619689471910887879)
    ·
      refine ⟨2356761929534207866331819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571174619689471910887879 2356761929534207866331819)
      ·
        refine ⟨3535142894301311799497729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356761929534207866331819 3535142894301311799497729)
        ·
          refine ⟨2651357170725983849623297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535142894301311799497729 2651357170725983849623297)
          ·
            refine ⟨1988517878044487887217473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2651357170725983849623297 1988517878044487887217473)
            ·
              refine ⟨1491388408533365915413105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988517878044487887217473 1491388408533365915413105)
              ·
                refine ⟨1118541306400024436559829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491388408533365915413105 1118541306400024436559829)
                ·
                  refine ⟨26215811868750572731871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1118541306400024436559829 26215811868750572731871)
                  ·
                    rfl

theorem cell21_114874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_114874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114874 prefixEnd_114874 := by exact prefixLift 114874
  have htrace : WordTrace (prefixWord ++ tailWord_114874) baseStart_114874 baseEnd_114874 := by
    simpa [prefixWord, tailWord_114874, baseEnd_114874] using wordTrace_append hprefix tailTrace_114874
  have hstable : (prefixWord ++ tailWord_114874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114874).length < 2 ^ (prefixWord ++ tailWord_114874).sum := by decide
  have hdescent : baseEnd_114874 < baseStart_114874 := by decide
  rcases family_descends (prefixWord ++ tailWord_114874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114967 : List Nat := [1, 1, 3, 4, 1, 3, 1, 2, 5]
def baseStart_114967 : Nat := 118140960795 + 114967 * 2 ^ 59
def prefixEnd_114967 : Nat := 4983230072969 + 3 ^ 40 * 114967 * 2
def baseEnd_114967 : Nat := 26237035735803077681681

theorem tailTrace_114967 : CollatzResearch.WordTrace tailWord_114967 prefixEnd_114967 26237035735803077681681 := by
  unfold tailWord_114967
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193190974501668645503155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2795460649667779097002103 4193190974501668645503155)
  ·
    refine ⟨6289786461752502968254733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193190974501668645503155 6289786461752502968254733)
    ·
      refine ⟨2358669923157188613095525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6289786461752502968254733 2358669923157188613095525)
      ·
        refine ⟨442250610591972864955411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2358669923157188613095525 442250610591972864955411)
        ·
          refine ⟨663375915887959297433117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442250610591972864955411 663375915887959297433117)
          ·
            refine ⟨248765968457984736537419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663375915887959297433117 248765968457984736537419)
            ·
              refine ⟨373148952686977104806129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248765968457984736537419 373148952686977104806129)
              ·
                refine ⟨279861714515232828604597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373148952686977104806129 279861714515232828604597)
                ·
                  refine ⟨26237035735803077681681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279861714515232828604597 26237035735803077681681)
                  ·
                    rfl

theorem cell21_114967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_114967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114967 prefixEnd_114967 := by exact prefixLift 114967
  have htrace : WordTrace (prefixWord ++ tailWord_114967) baseStart_114967 baseEnd_114967 := by
    simpa [prefixWord, tailWord_114967, baseEnd_114967] using wordTrace_append hprefix tailTrace_114967
  have hstable : (prefixWord ++ tailWord_114967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114967).length < 2 ^ (prefixWord ++ tailWord_114967).sum := by decide
  have hdescent : baseEnd_114967 < baseStart_114967 := by decide
  rcases family_descends (prefixWord ++ tailWord_114967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114995 : List Nat := [1, 1, 1, 2, 5, 1, 10]
def baseStart_114995 : Nat := 118140960795 + 114995 * 2 ^ 59
def prefixEnd_114995 : Nat := 4983230072969 + 3 ^ 40 * 114995 * 2
def baseEnd_114995 : Nat := 2915936190809027912773

theorem tailTrace_114995 : CollatzResearch.WordTrace tailWord_114995 prefixEnd_114995 2915936190809027912773 := by
  unfold tailWord_114995
  simp only [CollatzResearch.WordTrace]
  refine ⟨4194212218400229427522439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2796141478933486285014959 4194212218400229427522439)
  ·
    refine ⟨6291318327600344141283659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4194212218400229427522439 6291318327600344141283659)
    ·
      refine ⟨9436977491400516211925489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291318327600344141283659 9436977491400516211925489)
      ·
        refine ⟨7077733118550387158944117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9436977491400516211925489 7077733118550387158944117)
        ·
          refine ⟨663537479864098796151011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7077733118550387158944117 663537479864098796151011)
          ·
            refine ⟨995306219796148194226517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663537479864098796151011 995306219796148194226517)
            ·
              refine ⟨2915936190809027912773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 995306219796148194226517 2915936190809027912773)
              ·
                rfl

theorem cell21_114995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 10].length) (baseStart_114995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_114995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_114995 prefixEnd_114995 := by exact prefixLift 114995
  have htrace : WordTrace (prefixWord ++ tailWord_114995) baseStart_114995 baseEnd_114995 := by
    simpa [prefixWord, tailWord_114995, baseEnd_114995] using wordTrace_append hprefix tailTrace_114995
  have hstable : (prefixWord ++ tailWord_114995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114995).length < 2 ^ (prefixWord ++ tailWord_114995).sum := by decide
  have hdescent : baseEnd_114995 < baseStart_114995 := by decide
  rcases family_descends (prefixWord ++ tailWord_114995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115057 : List Nat := [1, 2, 2, 2, 1, 2, 1, 6, 4]
def baseStart_115057 : Nat := 118140960795 + 115057 * 2 ^ 59
def prefixEnd_115057 : Nat := 4983230072969 + 3 ^ 40 * 115057 * 2
def baseEnd_115057 : Nat := 26257574961982921181497

theorem tailTrace_115057 : CollatzResearch.WordTrace tailWord_115057 prefixEnd_115057 26257574961982921181497 := by
  unfold tailWord_115057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4196473544175614016279425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2797649029450409344186283 4196473544175614016279425)
  ·
    refine ⟨3147355158131710512209569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4196473544175614016279425 3147355158131710512209569)
    ·
      refine ⟨2360516368598782884157177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3147355158131710512209569 2360516368598782884157177)
      ·
        refine ⟨1770387276449087163117883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2360516368598782884157177 1770387276449087163117883)
        ·
          refine ⟨2655580914673630744676825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1770387276449087163117883 2655580914673630744676825)
          ·
            refine ⟨1991685686005223058507619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655580914673630744676825 1991685686005223058507619)
            ·
              refine ⟨2987528529007834587761429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991685686005223058507619 2987528529007834587761429)
              ·
                refine ⟨140040399797242246301317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2987528529007834587761429 140040399797242246301317)
                ·
                  refine ⟨26257574961982921181497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140040399797242246301317 26257574961982921181497)
                  ·
                    rfl

theorem cell21_115057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 6, 4].length) (baseStart_115057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115057 prefixEnd_115057 := by exact prefixLift 115057
  have htrace : WordTrace (prefixWord ++ tailWord_115057) baseStart_115057 baseEnd_115057 := by
    simpa [prefixWord, tailWord_115057, baseEnd_115057] using wordTrace_append hprefix tailTrace_115057
  have hstable : (prefixWord ++ tailWord_115057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115057).length < 2 ^ (prefixWord ++ tailWord_115057).sum := by decide
  have hdescent : baseEnd_115057 < baseStart_115057 := by decide
  rcases family_descends (prefixWord ++ tailWord_115057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115105 : List Nat := [1, 2, 3, 5, 2, 8]
def baseStart_115105 : Nat := 118140960795 + 115105 * 2 ^ 59
def prefixEnd_115105 : Nat := 4983230072969 + 3 ^ 40 * 115105 * 2
def baseEnd_115105 : Nat := 972908489479463125237

theorem tailTrace_115105 : CollatzResearch.WordTrace tailWord_115105 prefixEnd_115105 972908489479463125237 := by
  unfold tailWord_115105
  simp only [CollatzResearch.WordTrace]
  refine ⟨4198224248001718214026769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2798816165334478809351179 4198224248001718214026769)
  ·
    refine ⟨3148668186001288660520077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4198224248001718214026769 3148668186001288660520077)
    ·
      refine ⟨1180750569750483247695029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3148668186001288660520077 1180750569750483247695029)
      ·
        refine ⟨110695365914107804471409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1180750569750483247695029 110695365914107804471409)
        ·
          refine ⟨83021524435580853353557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110695365914107804471409 83021524435580853353557)
          ·
            refine ⟨972908489479463125237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 83021524435580853353557 972908489479463125237)
            ·
              rfl

theorem cell21_115105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 8].length) (baseStart_115105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115105 prefixEnd_115105 := by exact prefixLift 115105
  have htrace : WordTrace (prefixWord ++ tailWord_115105) baseStart_115105 baseEnd_115105 := by
    simpa [prefixWord, tailWord_115105, baseEnd_115105] using wordTrace_append hprefix tailTrace_115105
  have hstable : (prefixWord ++ tailWord_115105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115105).length < 2 ^ (prefixWord ++ tailWord_115105).sum := by decide
  have hdescent : baseEnd_115105 < baseStart_115105 := by decide
  rcases family_descends (prefixWord ++ tailWord_115105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115212 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_115212 : Nat := 118140960795 + 115212 * 2 ^ 59
def prefixEnd_115212 : Nat := 4983230072969 + 3 ^ 40 * 115212 * 2
def baseEnd_115212 : Nat := 26292948073737096097847

theorem tailTrace_115212 : CollatzResearch.WordTrace tailWord_115212 prefixEnd_115212 26292948073737096097847 := by
  unfold tailWord_115212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101063429307037744085945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2801417905742716992114593 2101063429307037744085945)
  ·
    refine ⟨1575797571980278308064459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101063429307037744085945 1575797571980278308064459)
    ·
      refine ⟨2363696357970417462096689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575797571980278308064459 2363696357970417462096689)
      ·
        refine ⟨1772772268477813096572517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2363696357970417462096689 1772772268477813096572517)
        ·
          refine ⟨332394800339589955607347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1772772268477813096572517 332394800339589955607347)
          ·
            refine ⟨498592200509384933411021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332394800339589955607347 498592200509384933411021)
            ·
              refine ⟨186972075191019350029133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498592200509384933411021 186972075191019350029133)
              ·
                refine ⟨70114528196632256260925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186972075191019350029133 70114528196632256260925)
                ·
                  refine ⟨26292948073737096097847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70114528196632256260925 26292948073737096097847)
                  ·
                    rfl

theorem cell21_115212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_115212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115212 prefixEnd_115212 := by exact prefixLift 115212
  have htrace : WordTrace (prefixWord ++ tailWord_115212) baseStart_115212 baseEnd_115212 := by
    simpa [prefixWord, tailWord_115212, baseEnd_115212] using wordTrace_append hprefix tailTrace_115212
  have hstable : (prefixWord ++ tailWord_115212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115212).length < 2 ^ (prefixWord ++ tailWord_115212).sum := by decide
  have hdescent : baseEnd_115212 < baseStart_115212 := by decide
  rcases family_descends (prefixWord ++ tailWord_115212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115229 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 3]
def baseStart_115229 : Nat := 118140960795 + 115229 * 2 ^ 59
def prefixEnd_115229 : Nat := 4983230072969 + 3 ^ 40 * 115229 * 2
def baseEnd_115229 : Nat := 26296827705348844314479

theorem tailTrace_115229 : CollatzResearch.WordTrace tailWord_115229 prefixEnd_115229 26296827705348844314479 := by
  unfold tailWord_115229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202746899552487391540741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2801831266368324927693827 4202746899552487391540741)
  ·
    refine ⟨788015043666091385913889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4202746899552487391540741 788015043666091385913889)
    ·
      refine ⟨591011282749568539435417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 788015043666091385913889 591011282749568539435417)
      ·
        refine ⟨443258462062176404576563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591011282749568539435417 443258462062176404576563)
        ·
          refine ⟨664887693093264606864845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443258462062176404576563 664887693093264606864845)
          ·
            refine ⟨249332884909974227574317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664887693093264606864845 249332884909974227574317)
            ·
              refine ⟨93499831841240335340369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249332884909974227574317 93499831841240335340369)
              ·
                refine ⟨70124873880930251505277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93499831841240335340369 70124873880930251505277)
                ·
                  refine ⟨26296827705348844314479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70124873880930251505277 26296827705348844314479)
                  ·
                    rfl

theorem cell21_115229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 3].length) (baseStart_115229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115229 prefixEnd_115229 := by exact prefixLift 115229
  have htrace : WordTrace (prefixWord ++ tailWord_115229) baseStart_115229 baseEnd_115229 := by
    simpa [prefixWord, tailWord_115229, baseEnd_115229] using wordTrace_append hprefix tailTrace_115229
  have hstable : (prefixWord ++ tailWord_115229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115229).length < 2 ^ (prefixWord ++ tailWord_115229).sum := by decide
  have hdescent : baseEnd_115229 < baseStart_115229 := by decide
  rcases family_descends (prefixWord ++ tailWord_115229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115240 : List Nat := [2, 1, 5, 2, 1, 1, 1, 8]
def baseStart_115240 : Nat := 118140960795 + 115240 * 2 ^ 59
def prefixEnd_115240 : Nat := 4983230072969 + 3 ^ 40 * 115240 * 2
def baseEnd_115240 : Nat := 8766446018405089877041

theorem tailTrace_115240 : CollatzResearch.WordTrace tailWord_115240 prefixEnd_115240 8766446018405089877041 := by
  unfold tailWord_115240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101574051256318135095587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2802098735008424180127449 2101574051256318135095587)
  ·
    refine ⟨3152361076884477202643381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2101574051256318135095587 3152361076884477202643381)
    ·
      refine ⟨295533850957919737747817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3152361076884477202643381 295533850957919737747817)
      ·
        refine ⟨221650388218439803310863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 295533850957919737747817 221650388218439803310863)
        ·
          refine ⟨332475582327659704966295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221650388218439803310863 332475582327659704966295)
          ·
            refine ⟨498713373491489557449443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332475582327659704966295 498713373491489557449443)
            ·
              refine ⟨748070060237234336174165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 498713373491489557449443 748070060237234336174165)
              ·
                refine ⟨8766446018405089877041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 748070060237234336174165 8766446018405089877041)
                ·
                  rfl

theorem cell21_115240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 8].length) (baseStart_115240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115240 prefixEnd_115240 := by exact prefixLift 115240
  have htrace : WordTrace (prefixWord ++ tailWord_115240) baseStart_115240 baseEnd_115240 := by
    simpa [prefixWord, tailWord_115240, baseEnd_115240] using wordTrace_append hprefix tailTrace_115240
  have hstable : (prefixWord ++ tailWord_115240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115240).length < 2 ^ (prefixWord ++ tailWord_115240).sum := by decide
  have hdescent : baseEnd_115240 < baseStart_115240 := by decide
  rcases family_descends (prefixWord ++ tailWord_115240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115285 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 4]
def baseStart_115285 : Nat := 118140960795 + 115285 * 2 ^ 59
def prefixEnd_115285 : Nat := 4983230072969 + 3 ^ 40 * 115285 * 2
def baseEnd_115285 : Nat := 26309607668305191381031

theorem tailTrace_115285 : CollatzResearch.WordTrace tailWord_115285 prefixEnd_115285 26309607668305191381031 := by
  unfold tailWord_115285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204789387349608955579309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2803192924899739303719539 4204789387349608955579309)
  ·
    refine ⟨1576796020256103358342241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4204789387349608955579309 1576796020256103358342241)
    ·
      refine ⟨1182597015192077518756681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576796020256103358342241 1182597015192077518756681)
      ·
        refine ⟨886947761394058139067511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182597015192077518756681 886947761394058139067511)
        ·
          refine ⟨1330421642091087208601267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886947761394058139067511 1330421642091087208601267)
          ·
            refine ⟨1995632463136630812901901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330421642091087208601267 1995632463136630812901901)
            ·
              refine ⟨748362173676236554838213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995632463136630812901901 748362173676236554838213)
              ·
                refine ⟨140317907564294354032165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 748362173676236554838213 140317907564294354032165)
                ·
                  refine ⟨26309607668305191381031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140317907564294354032165 26309607668305191381031)
                  ·
                    rfl

theorem cell21_115285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_115285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115285 prefixEnd_115285 := by exact prefixLift 115285
  have htrace : WordTrace (prefixWord ++ tailWord_115285) baseStart_115285 baseEnd_115285 := by
    simpa [prefixWord, tailWord_115285, baseEnd_115285] using wordTrace_append hprefix tailTrace_115285
  have hstable : (prefixWord ++ tailWord_115285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115285).length < 2 ^ (prefixWord ++ tailWord_115285).sum := by decide
  have hdescent : baseEnd_115285 < baseStart_115285 := by decide
  rcases family_descends (prefixWord ++ tailWord_115285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115288 : List Nat := [2, 1, 2, 2, 1, 2, 6, 2, 3]
def baseStart_115288 : Nat := 118140960795 + 115288 * 2 ^ 59
def prefixEnd_115288 : Nat := 4983230072969 + 3 ^ 40 * 115288 * 2
def baseEnd_115288 : Nat := 26310292309177852831025

theorem tailTrace_115288 : CollatzResearch.WordTrace tailWord_115288 prefixEnd_115288 26310292309177852831025 := by
  unfold tailWord_115288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2102449403169370233969259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2803265870892493645292345 2102449403169370233969259)
  ·
    refine ⟨3153674104754055350953889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2102449403169370233969259 3153674104754055350953889)
    ·
      refine ⟨2365255578565541513215417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3153674104754055350953889 2365255578565541513215417)
      ·
        refine ⟨1773941683924156134911563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2365255578565541513215417 1773941683924156134911563)
        ·
          refine ⟨2660912525886234202367345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773941683924156134911563 2660912525886234202367345)
          ·
            refine ⟨1995684394414675651775509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2660912525886234202367345 1995684394414675651775509)
            ·
              refine ⟨93547705988187921176977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1995684394414675651775509 93547705988187921176977)
              ·
                refine ⟨70160779491140940882733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93547705988187921176977 70160779491140940882733)
                ·
                  refine ⟨26310292309177852831025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70160779491140940882733 26310292309177852831025)
                  ·
                    rfl

theorem cell21_115288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 2, 3].length) (baseStart_115288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115288 prefixEnd_115288 := by exact prefixLift 115288
  have htrace : WordTrace (prefixWord ++ tailWord_115288) baseStart_115288 baseEnd_115288 := by
    simpa [prefixWord, tailWord_115288, baseEnd_115288] using wordTrace_append hprefix tailTrace_115288
  have hstable : (prefixWord ++ tailWord_115288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115288).length < 2 ^ (prefixWord ++ tailWord_115288).sum := by decide
  have hdescent : baseEnd_115288 < baseStart_115288 := by decide
  rcases family_descends (prefixWord ++ tailWord_115288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115367 : List Nat := [1, 1, 6, 3, 2, 1, 2, 5]
def baseStart_115367 : Nat := 118140960795 + 115367 * 2 ^ 59
def prefixEnd_115367 : Nat := 4983230072969 + 3 ^ 40 * 115367 * 2
def baseEnd_115367 : Nat := 8776107061830423671399

theorem tailTrace_115367 : CollatzResearch.WordTrace tailWord_115367 prefixEnd_115367 8776107061830423671399 := by
  unfold tailWord_115367
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207780173052536960064355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2805186782035024640042903 4207780173052536960064355)
  ·
    refine ⟨6311670259578805440096533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207780173052536960064355 6311670259578805440096533)
    ·
      refine ⟨295859543417756505004525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6311670259578805440096533 295859543417756505004525)
      ·
        refine ⟨110947328781658689376697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 295859543417756505004525 110947328781658689376697)
        ·
          refine ⟨83210496586244017032523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110947328781658689376697 83210496586244017032523)
          ·
            refine ⟨124815744879366025548785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83210496586244017032523 124815744879366025548785)
            ·
              refine ⟨93611808659524519161589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124815744879366025548785 93611808659524519161589)
              ·
                refine ⟨8776107061830423671399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93611808659524519161589 8776107061830423671399)
                ·
                  rfl

theorem cell21_115367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 2, 5].length) (baseStart_115367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115367 prefixEnd_115367 := by exact prefixLift 115367
  have htrace : WordTrace (prefixWord ++ tailWord_115367) baseStart_115367 baseEnd_115367 := by
    simpa [prefixWord, tailWord_115367, baseEnd_115367] using wordTrace_append hprefix tailTrace_115367
  have hstable : (prefixWord ++ tailWord_115367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115367).length < 2 ^ (prefixWord ++ tailWord_115367).sum := by decide
  have hdescent : baseEnd_115367 < baseStart_115367 := by decide
  rcases family_descends (prefixWord ++ tailWord_115367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115375 : List Nat := [1, 1, 2, 1, 2, 6, 1, 7]
def baseStart_115375 : Nat := 118140960795 + 115375 * 2 ^ 59
def prefixEnd_115375 : Nat := 4983230072969 + 3 ^ 40 * 115375 * 2
def baseEnd_115375 : Nat := 8776715631495011626949

theorem tailTrace_115375 : CollatzResearch.WordTrace tailWord_115375 prefixEnd_115375 8776715631495011626949 := by
  unfold tailWord_115375
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208071957023554326355579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2805381304682369550903719 4208071957023554326355579)
  ·
    refine ⟨6312107935535331489533369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4208071957023554326355579 6312107935535331489533369)
    ·
      refine ⟨4734080951651498617150027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6312107935535331489533369 4734080951651498617150027)
      ·
        refine ⟨7101121427477247925725041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4734080951651498617150027 7101121427477247925725041)
        ·
          refine ⟨5325841070607935944293781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7101121427477247925725041 5325841070607935944293781)
          ·
            refine ⟨249648800184746997388771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5325841070607935944293781 249648800184746997388771)
            ·
              refine ⟨374473200277120496083157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249648800184746997388771 374473200277120496083157)
              ·
                refine ⟨8776715631495011626949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 374473200277120496083157 8776715631495011626949)
                ·
                  rfl

theorem cell21_115375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 7].length) (baseStart_115375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115375 prefixEnd_115375 := by exact prefixLift 115375
  have htrace : WordTrace (prefixWord ++ tailWord_115375) baseStart_115375 baseEnd_115375 := by
    simpa [prefixWord, tailWord_115375, baseEnd_115375] using wordTrace_append hprefix tailTrace_115375
  have hstable : (prefixWord ++ tailWord_115375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115375).length < 2 ^ (prefixWord ++ tailWord_115375).sum := by decide
  have hdescent : baseEnd_115375 < baseStart_115375 := by decide
  rcases family_descends (prefixWord ++ tailWord_115375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115381 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 3]
def baseStart_115381 : Nat := 118140960795 + 115381 * 2 ^ 59
def prefixEnd_115381 : Nat := 4983230072969 + 3 ^ 40 * 115381 * 2
def baseEnd_115381 : Nat := 26331516176230357780835

theorem tailTrace_115381 : CollatzResearch.WordTrace tailWord_115381 prefixEnd_115381 26331516176230357780835 := by
  unfold tailWord_115381
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208290795001817351073997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2805527196667878234049331 4208290795001817351073997)
  ·
    refine ⟨1578109048125681506652749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4208290795001817351073997 1578109048125681506652749)
    ·
      refine ⟨591790893047130564994781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1578109048125681506652749 591790893047130564994781)
      ·
        refine ⟨221921584892673961873043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591790893047130564994781 221921584892673961873043)
        ·
          refine ⟨332882377339010942809565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221921584892673961873043 332882377339010942809565)
          ·
            refine ⟨124830891502129103553587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 332882377339010942809565 124830891502129103553587)
            ·
              refine ⟨187246337253193655330381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124830891502129103553587 187246337253193655330381)
              ·
                refine ⟨70217376469947620748893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187246337253193655330381 70217376469947620748893)
                ·
                  refine ⟨26331516176230357780835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70217376469947620748893 26331516176230357780835)
                  ·
                    rfl

theorem cell21_115381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 3].length) (baseStart_115381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115381 prefixEnd_115381 := by exact prefixLift 115381
  have htrace : WordTrace (prefixWord ++ tailWord_115381) baseStart_115381 baseEnd_115381 := by
    simpa [prefixWord, tailWord_115381, baseEnd_115381] using wordTrace_append hprefix tailTrace_115381
  have hstable : (prefixWord ++ tailWord_115381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115381).length < 2 ^ (prefixWord ++ tailWord_115381).sum := by decide
  have hdescent : baseEnd_115381 < baseStart_115381 := by decide
  rcases family_descends (prefixWord ++ tailWord_115381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115398 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_115398 : Nat := 118140960795 + 115398 * 2 ^ 59
def prefixEnd_115398 : Nat := 4983230072969 + 3 ^ 40 * 115398 * 2
def baseEnd_115398 : Nat := 26335395807842105997467

theorem tailTrace_115398 : CollatzResearch.WordTrace tailWord_115398 prefixEnd_115398 26335395807842105997467 := by
  unfold tailWord_115398
  simp only [CollatzResearch.WordTrace]
  refine ⟨131528463623132164201339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2805940557293486169628565 131528463623132164201339)
  ·
    refine ⟨197292695434698246302009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131528463623132164201339 197292695434698246302009)
    ·
      refine ⟨147969521576023684726507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197292695434698246302009 147969521576023684726507)
      ·
        refine ⟨221954282364035527089761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147969521576023684726507 221954282364035527089761)
        ·
          refine ⟨166465711773026645317321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221954282364035527089761 166465711773026645317321)
          ·
            refine ⟨124849283829769983987991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166465711773026645317321 124849283829769983987991)
            ·
              refine ⟨187273925744654975981987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124849283829769983987991 187273925744654975981987)
              ·
                refine ⟨280910888616982463972981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187273925744654975981987 280910888616982463972981)
                ·
                  refine ⟨26335395807842105997467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 280910888616982463972981 26335395807842105997467)
                  ·
                    rfl

theorem cell21_115398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_115398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115398 prefixEnd_115398 := by exact prefixLift 115398
  have htrace : WordTrace (prefixWord ++ tailWord_115398) baseStart_115398 baseEnd_115398 := by
    simpa [prefixWord, tailWord_115398, baseEnd_115398] using wordTrace_append hprefix tailTrace_115398
  have hstable : (prefixWord ++ tailWord_115398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115398).length < 2 ^ (prefixWord ++ tailWord_115398).sum := by decide
  have hdescent : baseEnd_115398 < baseStart_115398 := by decide
  rcases family_descends (prefixWord ++ tailWord_115398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115412 : List Nat := [2, 4, 1, 3, 2, 2, 2, 1, 4]
def baseStart_115412 : Nat := 118140960795 + 115412 * 2 ^ 59
def prefixEnd_115412 : Nat := 4983230072969 + 3 ^ 40 * 115412 * 2
def baseEnd_115412 : Nat := 26338590798581192764105

theorem tailTrace_115412 : CollatzResearch.WordTrace tailWord_115412 prefixEnd_115412 26338590798581192764105 := by
  unfold tailWord_115412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104710728944754822726245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2806280971926339763634993 2104710728944754822726245)
  ·
    refine ⟨394633261677141529261171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2104710728944754822726245 394633261677141529261171)
    ·
      refine ⟨591949892515712293891757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 394633261677141529261171 591949892515712293891757)
      ·
        refine ⟨221981209693392110209409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 591949892515712293891757 221981209693392110209409)
        ·
          refine ⟨166485907270044082657057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221981209693392110209409 166485907270044082657057)
          ·
            refine ⟨124864430452533061992793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166485907270044082657057 124864430452533061992793)
            ·
              refine ⟨93648322839399796494595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124864430452533061992793 93648322839399796494595)
              ·
                refine ⟨140472484259099694741893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93648322839399796494595 140472484259099694741893)
                ·
                  refine ⟨26338590798581192764105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140472484259099694741893 26338590798581192764105)
                  ·
                    rfl

theorem cell21_115412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_115412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115412 prefixEnd_115412 := by exact prefixLift 115412
  have htrace : WordTrace (prefixWord ++ tailWord_115412) baseStart_115412 baseEnd_115412 := by
    simpa [prefixWord, tailWord_115412, baseEnd_115412] using wordTrace_append hprefix tailTrace_115412
  have hstable : (prefixWord ++ tailWord_115412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115412).length < 2 ^ (prefixWord ++ tailWord_115412).sum := by decide
  have hdescent : baseEnd_115412 < baseStart_115412 := by decide
  rcases family_descends (prefixWord ++ tailWord_115412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115454 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_115454 : Nat := 118140960795 + 115454 * 2 ^ 59
def prefixEnd_115454 : Nat := 4983230072969 + 3 ^ 40 * 115454 * 2
def baseEnd_115454 : Nat := 26348175770798453064019

theorem tailTrace_115454 : CollatzResearch.WordTrace tailWord_115454 prefixEnd_115454 26348175770798453064019 := by
  unfold tailWord_115454
  simp only [CollatzResearch.WordTrace]
  refine ⟨526369165467168852310177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2807302215824900545654277 526369165467168852310177)
  ·
    refine ⟨394776874100376639232633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 526369165467168852310177 394776874100376639232633)
    ·
      refine ⟨296082655575282479424475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 394776874100376639232633 296082655575282479424475)
      ·
        refine ⟨444123983362923719136713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296082655575282479424475 444123983362923719136713)
        ·
          refine ⟨333092987522192789352535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 444123983362923719136713 333092987522192789352535)
          ·
            refine ⟨499639481283289184028803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 333092987522192789352535 499639481283289184028803)
            ·
              refine ⟨749459221924933776043205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 499639481283289184028803 749459221924933776043205)
              ·
                refine ⟨140523604110925083008101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 749459221924933776043205 140523604110925083008101)
                ·
                  refine ⟨26348175770798453064019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140523604110925083008101 26348175770798453064019)
                  ·
                    rfl

theorem cell21_115454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_115454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115454 prefixEnd_115454 := by exact prefixLift 115454
  have htrace : WordTrace (prefixWord ++ tailWord_115454) baseStart_115454 baseEnd_115454 := by
    simpa [prefixWord, tailWord_115454, baseEnd_115454] using wordTrace_append hprefix tailTrace_115454
  have hstable : (prefixWord ++ tailWord_115454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115454).length < 2 ^ (prefixWord ++ tailWord_115454).sum := by decide
  have hdescent : baseEnd_115454 < baseStart_115454 := by decide
  rcases family_descends (prefixWord ++ tailWord_115454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115482 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_115482 : Nat := 118140960795 + 115482 * 2 ^ 59
def prefixEnd_115482 : Nat := 4983230072969 + 3 ^ 40 * 115482 * 2
def baseEnd_115482 : Nat := 26354565752276626597295

theorem tailTrace_115482 : CollatzResearch.WordTrace tailWord_115482 prefixEnd_115482 26354565752276626597295 := by
  unfold tailWord_115482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052993641908977900125175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2807983045090607733667133 1052993641908977900125175)
  ·
    refine ⟨1579490462863466850187763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1052993641908977900125175 1579490462863466850187763)
    ·
      refine ⟨2369235694295200275281645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1579490462863466850187763 2369235694295200275281645)
      ·
        refine ⟨888463385360700103230617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2369235694295200275281645 888463385360700103230617)
        ·
          refine ⟨666347539020525077422963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 888463385360700103230617 666347539020525077422963)
          ·
            refine ⟨999521308530787616134445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666347539020525077422963 999521308530787616134445)
            ·
              refine ⟨374820490699045356050417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 999521308530787616134445 374820490699045356050417)
              ·
                refine ⟨281115368024284017037813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 374820490699045356050417 281115368024284017037813)
                ·
                  refine ⟨26354565752276626597295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281115368024284017037813 26354565752276626597295)
                  ·
                    rfl

theorem cell21_115482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_115482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115482 prefixEnd_115482 := by exact prefixLift 115482
  have htrace : WordTrace (prefixWord ++ tailWord_115482) baseStart_115482 baseEnd_115482 := by
    simpa [prefixWord, tailWord_115482, baseEnd_115482] using wordTrace_append hprefix tailTrace_115482
  have hstable : (prefixWord ++ tailWord_115482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115482).length < 2 ^ (prefixWord ++ tailWord_115482).sum := by decide
  have hdescent : baseEnd_115482 < baseStart_115482 := by decide
  rcases family_descends (prefixWord ++ tailWord_115482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115589 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 4]
def baseStart_115589 : Nat := 118140960795 + 115589 * 2 ^ 59
def prefixEnd_115589 : Nat := 4983230072969 + 3 ^ 40 * 115589 * 2
def baseEnd_115589 : Nat := 26378984610068218313743

theorem tailTrace_115589 : CollatzResearch.WordTrace tailWord_115589 prefixEnd_115589 26378984610068218313743 := by
  unfold tailWord_115589
  simp only [CollatzResearch.WordTrace]
  refine ⟨4215877178248268874645821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2810584785498845916430547 4215877178248268874645821)
  ·
    refine ⟨1580953941843100827992183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4215877178248268874645821 1580953941843100827992183)
    ·
      refine ⟨2371430912764651241988275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580953941843100827992183 2371430912764651241988275)
      ·
        refine ⟨3557146369146976862982413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371430912764651241988275 3557146369146976862982413)
        ·
          refine ⟨1333929888430116323618405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3557146369146976862982413 1333929888430116323618405)
          ·
            refine ⟨250111854080646810678451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1333929888430116323618405 250111854080646810678451)
            ·
              refine ⟨375167781120970216017677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250111854080646810678451 375167781120970216017677)
              ·
                refine ⟨140687917920363831006629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 375167781120970216017677 140687917920363831006629)
                ·
                  refine ⟨26378984610068218313743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 140687917920363831006629 26378984610068218313743)
                  ·
                    rfl

theorem cell21_115589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_115589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115589 prefixEnd_115589 := by exact prefixLift 115589
  have htrace : WordTrace (prefixWord ++ tailWord_115589) baseStart_115589 baseEnd_115589 := by
    simpa [prefixWord, tailWord_115589, baseEnd_115589] using wordTrace_append hprefix tailTrace_115589
  have hstable : (prefixWord ++ tailWord_115589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115589).length < 2 ^ (prefixWord ++ tailWord_115589).sum := by decide
  have hdescent : baseEnd_115589 < baseStart_115589 := by decide
  rcases family_descends (prefixWord ++ tailWord_115589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115668 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 3]
def baseStart_115668 : Nat := 118140960795 + 115668 * 2 ^ 59
def prefixEnd_115668 : Nat := 4983230072969 + 3 ^ 40 * 115668 * 2
def baseEnd_115668 : Nat := 26397013486381636496915

theorem tailTrace_115668 : CollatzResearch.WordTrace tailWord_115668 prefixEnd_115668 26397013486381636496915 := by
  unfold tailWord_115668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2109379272481032683385829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2812505696641376911181105 2109379272481032683385829)
  ·
    refine ⟨395508613590193628134843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2109379272481032683385829 395508613590193628134843)
    ·
      refine ⟨593262920385290442202265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 395508613590193628134843 593262920385290442202265)
      ·
        refine ⟨444947190288967831651699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 593262920385290442202265 444947190288967831651699)
        ·
          refine ⟨667420785433451747477549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 444947190288967831651699 667420785433451747477549)
          ·
            refine ⟨250282794537544405304081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 667420785433451747477549 250282794537544405304081)
            ·
              refine ⟨187712095903158303978061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250282794537544405304081 187712095903158303978061)
              ·
                refine ⟨70392035963684363991773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 187712095903158303978061 70392035963684363991773)
                ·
                  refine ⟨26397013486381636496915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70392035963684363991773 26397013486381636496915)
                  ·
                    rfl

theorem cell21_115668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_115668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115668 prefixEnd_115668 := by exact prefixLift 115668
  have htrace : WordTrace (prefixWord ++ tailWord_115668) baseStart_115668 baseEnd_115668 := by
    simpa [prefixWord, tailWord_115668, baseEnd_115668] using wordTrace_append hprefix tailTrace_115668
  have hstable : (prefixWord ++ tailWord_115668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115668).length < 2 ^ (prefixWord ++ tailWord_115668).sum := by decide
  have hdescent : baseEnd_115668 < baseStart_115668 := by decide
  rcases family_descends (prefixWord ++ tailWord_115668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115679 : List Nat := [1, 1, 2, 3, 5, 1, 8]
def baseStart_115679 : Nat := 118140960795 + 115679 * 2 ^ 59
def prefixEnd_115679 : Nat := 4983230072969 + 3 ^ 40 * 115679 * 2
def baseEnd_115679 : Nat := 2933280426249784645951

theorem tailTrace_115679 : CollatzResearch.WordTrace tailWord_115679 prefixEnd_115679 2933280426249784645951 := by
  unfold tailWord_115679
  simp only [CollatzResearch.WordTrace]
  refine ⟨4219159747922214245422091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2812773165281476163614727 4219159747922214245422091)
  ·
    refine ⟨6328739621883321368133137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4219159747922214245422091 6328739621883321368133137)
    ·
      refine ⟨4746554716412491026099853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6328739621883321368133137 4746554716412491026099853)
      ·
        refine ⟨1779958018654684134787445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4746554716412491026099853 1779958018654684134787445)
        ·
          refine ⟨166871064248876637636323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1779958018654684134787445 166871064248876637636323)
          ·
            refine ⟨250306596373314956454485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166871064248876637636323 250306596373314956454485)
            ·
              refine ⟨2933280426249784645951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 250306596373314956454485 2933280426249784645951)
              ·
                rfl

theorem cell21_115679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 8].length) (baseStart_115679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115679 prefixEnd_115679 := by exact prefixLift 115679
  have htrace : WordTrace (prefixWord ++ tailWord_115679) baseStart_115679 baseEnd_115679 := by
    simpa [prefixWord, tailWord_115679, baseEnd_115679] using wordTrace_append hprefix tailTrace_115679
  have hstable : (prefixWord ++ tailWord_115679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115679).length < 2 ^ (prefixWord ++ tailWord_115679).sum := by decide
  have hdescent : baseEnd_115679 < baseStart_115679 := by decide
  rcases family_descends (prefixWord ++ tailWord_115679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115682 : List Nat := [3, 3, 3, 1, 1, 2, 1, 1, 6]
def baseStart_115682 : Nat := 118140960795 + 115682 * 2 ^ 59
def prefixEnd_115682 : Nat := 4983230072969 + 3 ^ 40 * 115682 * 2
def baseEnd_115682 : Nat := 26400208477120723263553

theorem tailTrace_115682 : CollatzResearch.WordTrace tailWord_115682 prefixEnd_115682 26400208477120723263553 := by
  unfold tailWord_115682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054817291727836439445325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2812846111274230505187533 1054817291727836439445325)
  ·
    refine ⟨395556484397938664791997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1054817291727836439445325 395556484397938664791997)
    ·
      refine ⟨148333681649226999296999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 395556484397938664791997 148333681649226999296999)
      ·
        refine ⟨222500522473840498945499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148333681649226999296999 222500522473840498945499)
        ·
          refine ⟨333750783710760748418249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222500522473840498945499 333750783710760748418249)
          ·
            refine ⟨250313087783070561313687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 333750783710760748418249 250313087783070561313687)
            ·
              refine ⟨375469631674605841970531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 250313087783070561313687 375469631674605841970531)
              ·
                refine ⟨563204447511908762955797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 375469631674605841970531 563204447511908762955797)
                ·
                  refine ⟨26400208477120723263553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 563204447511908762955797 26400208477120723263553)
                  ·
                    rfl

theorem cell21_115682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_115682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115682 prefixEnd_115682 := by exact prefixLift 115682
  have htrace : WordTrace (prefixWord ++ tailWord_115682) baseStart_115682 baseEnd_115682 := by
    simpa [prefixWord, tailWord_115682, baseEnd_115682] using wordTrace_append hprefix tailTrace_115682
  have hstable : (prefixWord ++ tailWord_115682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115682).length < 2 ^ (prefixWord ++ tailWord_115682).sum := by decide
  have hdescent : baseEnd_115682 < baseStart_115682 := by decide
  rcases family_descends (prefixWord ++ tailWord_115682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115724 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 6]
def baseStart_115724 : Nat := 118140960795 + 115724 * 2 ^ 59
def prefixEnd_115724 : Nat := 4983230072969 + 3 ^ 40 * 115724 * 2
def baseEnd_115724 : Nat := 26409793449337983563467

theorem tailTrace_115724 : CollatzResearch.WordTrace tailWord_115724 prefixEnd_115724 26409793449337983563467 := by
  unfold tailWord_115724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110400516379593465405113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2813867355172791287206817 2110400516379593465405113)
  ·
    refine ⟨1582800387284695099053835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2110400516379593465405113 1582800387284695099053835)
    ·
      refine ⟨2374200580927042648580753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1582800387284695099053835 2374200580927042648580753)
      ·
        refine ⟨1780650435695281986435565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2374200580927042648580753 1780650435695281986435565)
        ·
          refine ⟨667743913385730744913337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1780650435695281986435565 667743913385730744913337)
          ·
            refine ⟨500807935039298058685003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 667743913385730744913337 500807935039298058685003)
            ·
              refine ⟨751211902558947088027505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 500807935039298058685003 751211902558947088027505)
              ·
                refine ⟨563408926919210316020629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751211902558947088027505 563408926919210316020629)
                ·
                  refine ⟨26409793449337983563467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 563408926919210316020629 26409793449337983563467)
                  ·
                    rfl

theorem cell21_115724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_115724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115724 prefixEnd_115724 := by exact prefixLift 115724
  have htrace : WordTrace (prefixWord ++ tailWord_115724) baseStart_115724 baseEnd_115724 := by
    simpa [prefixWord, tailWord_115724, baseEnd_115724] using wordTrace_append hprefix tailTrace_115724
  have hstable : (prefixWord ++ tailWord_115724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115724).length < 2 ^ (prefixWord ++ tailWord_115724).sum := by decide
  have hdescent : baseEnd_115724 < baseStart_115724 := by decide
  rcases family_descends (prefixWord ++ tailWord_115724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115730 : List Nat := [3, 2, 5, 1, 1, 2, 7]
def baseStart_115730 : Nat := 118140960795 + 115730 * 2 ^ 59
def prefixEnd_115730 : Nat := 4983230072969 + 3 ^ 40 * 115730 * 2
def baseEnd_115730 : Nat := 2934573636787034051495

theorem tailTrace_115730 : CollatzResearch.WordTrace tailWord_115730 prefixEnd_115730 2934573636787034051495 := by
  unfold tailWord_115730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055254967684362488882161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2814013247158299970352429 1055254967684362488882161)
  ·
    refine ⟨791441225763271866661621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055254967684362488882161 791441225763271866661621)
    ·
      refine ⟨74197614915306737499527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 791441225763271866661621 74197614915306737499527)
      ·
        refine ⟨111296422372960106249291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74197614915306737499527 111296422372960106249291)
        ·
          refine ⟨166944633559440159373937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111296422372960106249291 166944633559440159373937)
          ·
            refine ⟨125208475169580119530453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166944633559440159373937 125208475169580119530453)
            ·
              refine ⟨2934573636787034051495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 125208475169580119530453 2934573636787034051495)
              ·
                rfl

theorem cell21_115730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 7].length) (baseStart_115730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115730 prefixEnd_115730 := by exact prefixLift 115730
  have htrace : WordTrace (prefixWord ++ tailWord_115730) baseStart_115730 baseEnd_115730 := by
    simpa [prefixWord, tailWord_115730, baseEnd_115730] using wordTrace_append hprefix tailTrace_115730
  have hstable : (prefixWord ++ tailWord_115730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115730).length < 2 ^ (prefixWord ++ tailWord_115730).sum := by decide
  have hdescent : baseEnd_115730 < baseStart_115730 := by decide
  rcases family_descends (prefixWord ++ tailWord_115730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115744 : List Nat := [2, 1, 1, 7, 1, 2, 1, 1, 5]
def baseStart_115744 : Nat := 118140960795 + 115744 * 2 ^ 59
def prefixEnd_115744 : Nat := 4983230072969 + 3 ^ 40 * 115744 * 2
def baseEnd_115744 : Nat := 26414357721822393230093

theorem tailTrace_115744 : CollatzResearch.WordTrace tailWord_115744 prefixEnd_115744 26414357721822393230093 := by
  unfold tailWord_115744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110765246343365173269143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2814353661791153564358857 2110765246343365173269143)
  ·
    refine ⟨3166147869515047759903715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2110765246343365173269143 3166147869515047759903715)
    ·
      refine ⟨4749221804272571639855573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166147869515047759903715 4749221804272571639855573)
      ·
        refine ⟨111309886037638397809115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4749221804272571639855573 111309886037638397809115)
        ·
          refine ⟨166964829056457596713673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111309886037638397809115 166964829056457596713673)
          ·
            refine ⟨125223621792343197535255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 166964829056457596713673 125223621792343197535255)
            ·
              refine ⟨187835432688514796302883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125223621792343197535255 187835432688514796302883)
              ·
                refine ⟨281753149032772194454325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 187835432688514796302883 281753149032772194454325)
                ·
                  refine ⟨26414357721822393230093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 281753149032772194454325 26414357721822393230093)
                  ·
                    rfl

theorem cell21_115744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 1, 5].length) (baseStart_115744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115744 prefixEnd_115744 := by exact prefixLift 115744
  have htrace : WordTrace (prefixWord ++ tailWord_115744) baseStart_115744 baseEnd_115744 := by
    simpa [prefixWord, tailWord_115744, baseEnd_115744] using wordTrace_append hprefix tailTrace_115744
  have hstable : (prefixWord ++ tailWord_115744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115744).length < 2 ^ (prefixWord ++ tailWord_115744).sum := by decide
  have hdescent : baseEnd_115744 < baseStart_115744 := by decide
  rcases family_descends (prefixWord ++ tailWord_115744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115806 : List Nat := [4, 4, 1, 1, 1, 3, 1, 6]
def baseStart_115806 : Nat := 118140960795 + 115806 * 2 ^ 59
def prefixEnd_115806 : Nat := 4983230072969 + 3 ^ 40 * 115806 * 2
def baseEnd_115806 : Nat := 8809502322174687732211

theorem tailTrace_115806 : CollatzResearch.WordTrace tailWord_115806 prefixEnd_115806 8809502322174687732211 := by
  unfold tailWord_115806
  simp only [CollatzResearch.WordTrace]
  refine ⟨527973977307764366911909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2815861212308076623530181 527973977307764366911909)
  ·
    refine ⟨98995120745205818795983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 527973977307764366911909 98995120745205818795983)
    ·
      refine ⟨148492681117808728193975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98995120745205818795983 148492681117808728193975)
      ·
        refine ⟨222739021676713092290963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148492681117808728193975 222739021676713092290963)
        ·
          refine ⟨334108532515069638436445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222739021676713092290963 334108532515069638436445)
          ·
            refine ⟨125290699693151114413667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 334108532515069638436445 125290699693151114413667)
            ·
              refine ⟨187936049539726671620501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125290699693151114413667 187936049539726671620501)
              ·
                refine ⟨8809502322174687732211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 187936049539726671620501 8809502322174687732211)
                ·
                  rfl

theorem cell21_115806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_115806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115806 prefixEnd_115806 := by exact prefixLift 115806
  have htrace : WordTrace (prefixWord ++ tailWord_115806) baseStart_115806 baseEnd_115806 := by
    simpa [prefixWord, tailWord_115806, baseEnd_115806] using wordTrace_append hprefix tailTrace_115806
  have hstable : (prefixWord ++ tailWord_115806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115806).length < 2 ^ (prefixWord ++ tailWord_115806).sum := by decide
  have hdescent : baseEnd_115806 < baseStart_115806 := by decide
  rcases family_descends (prefixWord ++ tailWord_115806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115831 : List Nat := [1, 1, 3, 1, 1, 4, 5, 5]
def baseStart_115831 : Nat := 118140960795 + 115831 * 2 ^ 59
def prefixEnd_115831 : Nat := 4983230072969 + 3 ^ 40 * 115831 * 2
def baseEnd_115831 : Nat := 8811404102376525093305

theorem tailTrace_115831 : CollatzResearch.WordTrace tailWord_115831 prefixEnd_115831 8811404102376525093305 := by
  unfold tailWord_115831
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224703643371544204955347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2816469095581029469970231 4224703643371544204955347)
  ·
    refine ⟨6337055465057316307433021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4224703643371544204955347 6337055465057316307433021)
    ·
      refine ⟨2376395799396493615287383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6337055465057316307433021 2376395799396493615287383)
      ·
        refine ⟨3564593699094740422931075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2376395799396493615287383 3564593699094740422931075)
        ·
          refine ⟨5346890548642110634396613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3564593699094740422931075 5346890548642110634396613)
          ·
            refine ⟨1002541977870395743949365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5346890548642110634396613 1002541977870395743949365)
            ·
              refine ⟨93988310425349600995253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1002541977870395743949365 93988310425349600995253)
              ·
                refine ⟨8811404102376525093305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93988310425349600995253 8811404102376525093305)
                ·
                  rfl

theorem cell21_115831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 5, 5].length) (baseStart_115831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115831 prefixEnd_115831 := by exact prefixLift 115831
  have htrace : WordTrace (prefixWord ++ tailWord_115831) baseStart_115831 baseEnd_115831 := by
    simpa [prefixWord, tailWord_115831, baseEnd_115831] using wordTrace_append hprefix tailTrace_115831
  have hstable : (prefixWord ++ tailWord_115831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115831).length < 2 ^ (prefixWord ++ tailWord_115831).sum := by decide
  have hdescent : baseEnd_115831 < baseStart_115831 := by decide
  rcases family_descends (prefixWord ++ tailWord_115831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115969 : List Nat := [1, 2, 4, 1, 1, 4, 2, 2, 4]
def baseStart_115969 : Nat := 118140960795 + 115969 * 2 ^ 59
def prefixEnd_115969 : Nat := 4983230072969 + 3 ^ 40 * 115969 * 2
def baseEnd_115969 : Nat := 26465705787272001979633

theorem tailTrace_115969 : CollatzResearch.WordTrace tailWord_115969 prefixEnd_115969 26465705787272001979633 := by
  unfold tailWord_115969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229736916871593773478961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2819824611247729182319307 4229736916871593773478961)
  ·
    refine ⟨3172302687653695330109221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4229736916871593773478961 3172302687653695330109221)
    ·
      refine ⟨594806753935067874395479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3172302687653695330109221 594806753935067874395479)
      ·
        refine ⟨892210130902601811593219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594806753935067874395479 892210130902601811593219)
        ·
          refine ⟨1338315196353902717389829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892210130902601811593219 1338315196353902717389829)
          ·
            refine ⟨250934099316356759510593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1338315196353902717389829 250934099316356759510593)
            ·
              refine ⟨188200574487267569632945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250934099316356759510593 188200574487267569632945)
              ·
                refine ⟨141150430865450677224709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188200574487267569632945 141150430865450677224709)
                ·
                  refine ⟨26465705787272001979633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141150430865450677224709 26465705787272001979633)
                  ·
                    rfl

theorem cell21_115969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 2, 4].length) (baseStart_115969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115969 prefixEnd_115969 := by exact prefixLift 115969
  have htrace : WordTrace (prefixWord ++ tailWord_115969) baseStart_115969 baseEnd_115969 := by
    simpa [prefixWord, tailWord_115969, baseEnd_115969] using wordTrace_append hprefix tailTrace_115969
  have hstable : (prefixWord ++ tailWord_115969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115969).length < 2 ^ (prefixWord ++ tailWord_115969).sum := by decide
  have hdescent : baseEnd_115969 < baseStart_115969 := by decide
  rcases family_descends (prefixWord ++ tailWord_115969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115972 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 3]
def baseStart_115972 : Nat := 118140960795 + 115972 * 2 ^ 59
def prefixEnd_115972 : Nat := 4983230072969 + 3 ^ 40 * 115972 * 2
def baseEnd_115972 : Nat := 26466390428144663429627

theorem tailTrace_115972 : CollatzResearch.WordTrace tailWord_115972 prefixEnd_115972 26466390428144663429627 := by
  unfold tailWord_115972
  simp only [CollatzResearch.WordTrace]
  refine ⟨2114923167930362642919085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2819897557240483523892113 2114923167930362642919085)
  ·
    refine ⟨793096187973885991094657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2114923167930362642919085 793096187973885991094657)
    ·
      refine ⟨594822140980414493320993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 793096187973885991094657 594822140980414493320993)
      ·
        refine ⟨446116605735310869990745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 594822140980414493320993 446116605735310869990745)
        ·
          refine ⟨334587454301483152493059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446116605735310869990745 334587454301483152493059)
          ·
            refine ⟨501881181452224728739589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 334587454301483152493059 501881181452224728739589)
            ·
              refine ⟨94102721522292136638673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 501881181452224728739589 94102721522292136638673)
              ·
                refine ⟨70577041141719102479005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94102721522292136638673 70577041141719102479005)
                ·
                  refine ⟨26466390428144663429627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70577041141719102479005 26466390428144663429627)
                  ·
                    rfl

theorem cell21_115972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_115972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_115972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_115972 prefixEnd_115972 := by exact prefixLift 115972
  have htrace : WordTrace (prefixWord ++ tailWord_115972) baseStart_115972 baseEnd_115972 := by
    simpa [prefixWord, tailWord_115972, baseEnd_115972] using wordTrace_append hprefix tailTrace_115972
  have hstable : (prefixWord ++ tailWord_115972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115972).length < 2 ^ (prefixWord ++ tailWord_115972).sum := by decide
  have hdescent : baseEnd_115972 < baseStart_115972 := by decide
  rcases family_descends (prefixWord ++ tailWord_115972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116000 : List Nat := [2, 1, 1, 5, 3, 1, 3, 5]
def baseStart_116000 : Nat := 118140960795 + 116000 * 2 ^ 59
def prefixEnd_116000 : Nat := 4983230072969 + 3 ^ 40 * 116000 * 2
def baseEnd_116000 : Nat := 8824260136540945654301

theorem tailTrace_116000 : CollatzResearch.WordTrace tailWord_116000 prefixEnd_116000 8824260136540945654301 := by
  unfold tailWord_116000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115433789879643033928727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2820578386506190711904969 2115433789879643033928727)
  ·
    refine ⟨3173150684819464550893091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2115433789879643033928727 3173150684819464550893091)
    ·
      refine ⟨4759726027229196826339637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173150684819464550893091 4759726027229196826339637)
      ·
        refine ⟨446224315052737202469341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4759726027229196826339637 446224315052737202469341)
        ·
          refine ⟨167334118144776450926003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446224315052737202469341 167334118144776450926003)
          ·
            refine ⟨251001177217164676389005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167334118144776450926003 251001177217164676389005)
            ·
              refine ⟨94125441456436753645877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251001177217164676389005 94125441456436753645877)
              ·
                refine ⟨8824260136540945654301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94125441456436753645877 8824260136540945654301)
                ·
                  rfl

theorem cell21_116000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 5].length) (baseStart_116000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116000 prefixEnd_116000 := by exact prefixLift 116000
  have htrace : WordTrace (prefixWord ++ tailWord_116000) baseStart_116000 baseEnd_116000 := by
    simpa [prefixWord, tailWord_116000, baseEnd_116000] using wordTrace_append hprefix tailTrace_116000
  have hstable : (prefixWord ++ tailWord_116000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116000).length < 2 ^ (prefixWord ++ tailWord_116000).sum := by decide
  have hdescent : baseEnd_116000 < baseStart_116000 := by decide
  rcases family_descends (prefixWord ++ tailWord_116000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116028 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 6]
def baseStart_116028 : Nat := 118140960795 + 116028 * 2 ^ 59
def prefixEnd_116028 : Nat := 4983230072969 + 3 ^ 40 * 116028 * 2
def baseEnd_116028 : Nat := 26479170391101010496179

theorem tailTrace_116028 : CollatzResearch.WordTrace tailWord_116028 prefixEnd_116028 26479170391101010496179 := by
  unfold tailWord_116028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2115944411828923424938369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2821259215771897899917825 2115944411828923424938369)
  ·
    refine ⟨1586958308871692568703777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2115944411828923424938369 1586958308871692568703777)
    ·
      refine ⟨1190218731653769426527833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1586958308871692568703777 1190218731653769426527833)
      ·
        refine ⟨892664048740327069895875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1190218731653769426527833 892664048740327069895875)
        ·
          refine ⟨1338996073110490604843813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892664048740327069895875 1338996073110490604843813)
          ·
            refine ⟨251061763708216988408215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1338996073110490604843813 251061763708216988408215)
            ·
              refine ⟨376592645562325482612323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251061763708216988408215 376592645562325482612323)
              ·
                refine ⟨564888968343488223918485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376592645562325482612323 564888968343488223918485)
                ·
                  refine ⟨26479170391101010496179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 564888968343488223918485 26479170391101010496179)
                  ·
                    rfl

theorem cell21_116028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_116028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116028 prefixEnd_116028 := by exact prefixLift 116028
  have htrace : WordTrace (prefixWord ++ tailWord_116028) baseStart_116028 baseEnd_116028 := by
    simpa [prefixWord, tailWord_116028, baseEnd_116028] using wordTrace_append hprefix tailTrace_116028
  have hstable : (prefixWord ++ tailWord_116028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116028).length < 2 ^ (prefixWord ++ tailWord_116028).sum := by decide
  have hdescent : baseEnd_116028 < baseStart_116028 := by decide
  rcases family_descends (prefixWord ++ tailWord_116028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116087 : List Nat := [1, 1, 3, 1, 1, 2, 3, 3, 6]
def baseStart_116087 : Nat := 118140960795 + 116087 * 2 ^ 59
def prefixEnd_116087 : Nat := 4983230072969 + 3 ^ 40 * 116087 * 2
def baseEnd_116087 : Nat := 26492634994930019012725

theorem tailTrace_116087 : CollatzResearch.WordTrace tailWord_116087 prefixEnd_116087 26492634994930019012725 := by
  unfold tailWord_116087
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234040730444099926274515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822693820296066617516343 4234040730444099926274515)
  ·
    refine ⟨6351061095666149889411773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4234040730444099926274515 6351061095666149889411773)
    ·
      refine ⟨2381647910874806208529415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6351061095666149889411773 2381647910874806208529415)
      ·
        refine ⟨3572471866312209312794123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381647910874806208529415 3572471866312209312794123)
        ·
          refine ⟨5358707799468313969191185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3572471866312209312794123 5358707799468313969191185)
          ·
            refine ⟨4019030849601235476893389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5358707799468313969191185 4019030849601235476893389)
            ·
              refine ⟨1507136568600463303835021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4019030849601235476893389 1507136568600463303835021)
              ·
                refine ⟨565176213225173738938133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507136568600463303835021 565176213225173738938133)
                ·
                  refine ⟨26492634994930019012725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 565176213225173738938133 26492634994930019012725)
                  ·
                    rfl

theorem cell21_116087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_116087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116087 prefixEnd_116087 := by exact prefixLift 116087
  have htrace : WordTrace (prefixWord ++ tailWord_116087) baseStart_116087 baseEnd_116087 := by
    simpa [prefixWord, tailWord_116087, baseEnd_116087] using wordTrace_append hprefix tailTrace_116087
  have hstable : (prefixWord ++ tailWord_116087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116087).length < 2 ^ (prefixWord ++ tailWord_116087).sum := by decide
  have hdescent : baseEnd_116087 < baseStart_116087 := by decide
  rcases family_descends (prefixWord ++ tailWord_116087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116141 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 3]
def baseStart_116141 : Nat := 118140960795 + 116141 * 2 ^ 59
def prefixEnd_116141 : Nat := 4983230072969 + 3 ^ 40 * 116141 * 2
def baseEnd_116141 : Nat := 26504958530637925112615

theorem tailTrace_116141 : CollatzResearch.WordTrace tailWord_116141 prefixEnd_116141 26504958530637925112615 := by
  unfold tailWord_116141
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236010272248467148740277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2824006848165644765826851 4236010272248467148740277)
  ·
    refine ⟨397125963023293795194401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4236010272248467148740277 397125963023293795194401)
    ·
      refine ⟨297844472267470346395801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397125963023293795194401 297844472267470346395801)
      ·
        refine ⟨223383354200602759796851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297844472267470346395801 223383354200602759796851)
        ·
          refine ⟨335075031300904139695277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223383354200602759796851 335075031300904139695277)
          ·
            refine ⟨125653136737839052385729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335075031300904139695277 125653136737839052385729)
            ·
              refine ⟨94239852553379289289297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125653136737839052385729 94239852553379289289297)
              ·
                refine ⟨70679889415034466966973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94239852553379289289297 70679889415034466966973)
                ·
                  refine ⟨26504958530637925112615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70679889415034466966973 26504958530637925112615)
                  ·
                    rfl

theorem cell21_116141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_116141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116141 prefixEnd_116141 := by exact prefixLift 116141
  have htrace : WordTrace (prefixWord ++ tailWord_116141) baseStart_116141 baseEnd_116141 := by
    simpa [prefixWord, tailWord_116141, baseEnd_116141] using wordTrace_append hprefix tailTrace_116141
  have hstable : (prefixWord ++ tailWord_116141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116141).length < 2 ^ (prefixWord ++ tailWord_116141).sum := by decide
  have hdescent : baseEnd_116141 < baseStart_116141 := by decide
  rcases family_descends (prefixWord ++ tailWord_116141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116197 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 4]
def baseStart_116197 : Nat := 118140960795 + 116197 * 2 ^ 59
def prefixEnd_116197 : Nat := 4983230072969 + 3 ^ 40 * 116197 * 2
def baseEnd_116197 : Nat := 26517738493594272179167

theorem tailTrace_116197 : CollatzResearch.WordTrace tailWord_116197 prefixEnd_116197 26517738493594272179167 := by
  unfold tailWord_116197
  simp only [CollatzResearch.WordTrace]
  refine ⟨4238052760045588712778845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2825368506697059141852563 4238052760045588712778845)
  ·
    refine ⟨1589269785017095767292067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4238052760045588712778845 1589269785017095767292067)
    ·
      refine ⟨2383904677525643650938101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589269785017095767292067 2383904677525643650938101)
      ·
        refine ⟨223491063518029092275447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2383904677525643650938101 223491063518029092275447)
        ·
          refine ⟨335236595277043638413171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223491063518029092275447 335236595277043638413171)
          ·
            refine ⟨502854892915565457619757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335236595277043638413171 502854892915565457619757)
            ·
              refine ⟨188570584843337046607409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502854892915565457619757 188570584843337046607409)
              ·
                refine ⟨141427938632502784955557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188570584843337046607409 141427938632502784955557)
                ·
                  refine ⟨26517738493594272179167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141427938632502784955557 26517738493594272179167)
                  ·
                    rfl

theorem cell21_116197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_116197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116197 prefixEnd_116197 := by exact prefixLift 116197
  have htrace : WordTrace (prefixWord ++ tailWord_116197) baseStart_116197 baseEnd_116197 := by
    simpa [prefixWord, tailWord_116197, baseEnd_116197] using wordTrace_append hprefix tailTrace_116197
  have hstable : (prefixWord ++ tailWord_116197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116197).length < 2 ^ (prefixWord ++ tailWord_116197).sum := by decide
  have hdescent : baseEnd_116197 < baseStart_116197 := by decide
  rcases family_descends (prefixWord ++ tailWord_116197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116214 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_116214 : Nat := 118140960795 + 116214 * 2 ^ 59
def prefixEnd_116214 : Nat := 4983230072969 + 3 ^ 40 * 116214 * 2
def baseEnd_116214 : Nat := 26521618125206020395799

theorem tailTrace_116214 : CollatzResearch.WordTrace tailWord_116214 prefixEnd_116214 26521618125206020395799 := by
  unfold tailWord_116214
  simp only [CollatzResearch.WordTrace]
  refine ⟨264917050061500038509231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2825781867322667077431797 264917050061500038509231)
  ·
    refine ⟨397375575092250057763847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264917050061500038509231 397375575092250057763847)
    ·
      refine ⟨596063362638375086645771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397375575092250057763847 596063362638375086645771)
      ·
        refine ⟨894095043957562629968657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596063362638375086645771 894095043957562629968657)
        ·
          refine ⟨670571282968171972476493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894095043957562629968657 670571282968171972476493)
          ·
            refine ⟨251464231113064489678685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670571282968171972476493 251464231113064489678685)
            ·
              refine ⟨94299086667399183629507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251464231113064489678685 94299086667399183629507)
              ·
                refine ⟨141448630001098775444261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94299086667399183629507 141448630001098775444261)
                ·
                  refine ⟨26521618125206020395799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141448630001098775444261 26521618125206020395799)
                  ·
                    rfl

theorem cell21_116214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_116214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116214 prefixEnd_116214 := by exact prefixLift 116214
  have htrace : WordTrace (prefixWord ++ tailWord_116214) baseStart_116214 baseEnd_116214 := by
    simpa [prefixWord, tailWord_116214, baseEnd_116214] using wordTrace_append hprefix tailTrace_116214
  have hstable : (prefixWord ++ tailWord_116214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116214).length < 2 ^ (prefixWord ++ tailWord_116214).sum := by decide
  have hdescent : baseEnd_116214 < baseStart_116214 := by decide
  rcases family_descends (prefixWord ++ tailWord_116214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116256 : List Nat := [2, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_116256 : Nat := 118140960795 + 116256 * 2 ^ 59
def prefixEnd_116256 : Nat := 4983230072969 + 3 ^ 40 * 116256 * 2
def baseEnd_116256 : Nat := 26531203097423280695713

theorem tailTrace_116256 : CollatzResearch.WordTrace tailWord_116256 prefixEnd_116256 26531203097423280695713 := by
  unfold tailWord_116256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120102333415920894588311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2826803111221227859451081 2120102333415920894588311)
  ·
    refine ⟨3180153500123881341882467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120102333415920894588311 3180153500123881341882467)
    ·
      refine ⟨4770230250185822012823701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180153500123881341882467 4770230250185822012823701)
      ·
        refine ⟨223604542977460406851111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4770230250185822012823701 223604542977460406851111)
        ·
          refine ⟨335406814466190610276667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223604542977460406851111 335406814466190610276667)
          ·
            refine ⟨503110221699285915415001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335406814466190610276667 503110221699285915415001)
            ·
              refine ⟨377332666274464436561251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503110221699285915415001 377332666274464436561251)
              ·
                refine ⟨565998999411696654841877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377332666274464436561251 565998999411696654841877)
                ·
                  refine ⟨26531203097423280695713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 565998999411696654841877 26531203097423280695713)
                  ·
                    rfl

theorem cell21_116256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_116256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116256 prefixEnd_116256 := by exact prefixLift 116256
  have htrace : WordTrace (prefixWord ++ tailWord_116256) baseStart_116256 baseEnd_116256 := by
    simpa [prefixWord, tailWord_116256, baseEnd_116256] using wordTrace_append hprefix tailTrace_116256
  have hstable : (prefixWord ++ tailWord_116256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116256).length < 2 ^ (prefixWord ++ tailWord_116256).sum := by decide
  have hdescent : baseEnd_116256 < baseStart_116256 := by decide
  rcases family_descends (prefixWord ++ tailWord_116256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116259 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 5]
def baseStart_116259 : Nat := 118140960795 + 116259 * 2 ^ 59
def prefixEnd_116259 : Nat := 4983230072969 + 3 ^ 40 * 116259 * 2
def baseEnd_116259 : Nat := 26531887738295942145707

theorem tailTrace_116259 : CollatzResearch.WordTrace tailWord_116259 prefixEnd_116259 26531887738295942145707 := by
  unfold tailWord_116259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240314085820973301535831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2826876057213982201023887 4240314085820973301535831)
  ·
    refine ⟨6360471128731459952303747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4240314085820973301535831 6360471128731459952303747)
    ·
      refine ⟨9540706693097189928455621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6360471128731459952303747 9540706693097189928455621)
      ·
        refine ⟨1788882504955723111585429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9540706693097189928455621 1788882504955723111585429)
        ·
          refine ⟨83853867419799520855567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1788882504955723111585429 83853867419799520855567)
          ·
            refine ⟨125780801129699281283351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83853867419799520855567 125780801129699281283351)
            ·
              refine ⟨188671201694548921925027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125780801129699281283351 188671201694548921925027)
              ·
                refine ⟨283006802541823382887541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188671201694548921925027 283006802541823382887541)
                ·
                  refine ⟨26531887738295942145707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283006802541823382887541 26531887738295942145707)
                  ·
                    rfl

theorem cell21_116259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 5].length) (baseStart_116259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116259 prefixEnd_116259 := by exact prefixLift 116259
  have htrace : WordTrace (prefixWord ++ tailWord_116259) baseStart_116259 baseEnd_116259 := by
    simpa [prefixWord, tailWord_116259, baseEnd_116259] using wordTrace_append hprefix tailTrace_116259
  have hstable : (prefixWord ++ tailWord_116259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116259).length < 2 ^ (prefixWord ++ tailWord_116259).sum := by decide
  have hdescent : baseEnd_116259 < baseStart_116259 := by decide
  rcases family_descends (prefixWord ++ tailWord_116259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116428 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 3]
def baseStart_116428 : Nat := 118140960795 + 116428 * 2 ^ 59
def prefixEnd_116428 : Nat := 4983230072969 + 3 ^ 40 * 116428 * 2
def baseEnd_116428 : Nat := 26570455840789203828695

theorem tailTrace_116428 : CollatzResearch.WordTrace tailWord_116428 prefixEnd_116428 26570455840789203828695 := by
  unfold tailWord_116428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2123239011104357582218969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2830985348139143442958625 2123239011104357582218969)
  ·
    refine ⟨1592429258328268186664227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2123239011104357582218969 1592429258328268186664227)
    ·
      refine ⟨2388643887492402279996341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592429258328268186664227 2388643887492402279996341)
      ·
        refine ⟨223935364452412713749657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2388643887492402279996341 223935364452412713749657)
        ·
          refine ⟨167951523339309535312243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223935364452412713749657 167951523339309535312243)
          ·
            refine ⟨251927285008964302968365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167951523339309535312243 251927285008964302968365)
            ·
              refine ⟨94472731878361613613137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251927285008964302968365 94472731878361613613137)
              ·
                refine ⟨70854548908771210209853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94472731878361613613137 70854548908771210209853)
                ·
                  refine ⟨26570455840789203828695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70854548908771210209853 26570455840789203828695)
                  ·
                    rfl

theorem cell21_116428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 3].length) (baseStart_116428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116428 prefixEnd_116428 := by exact prefixLift 116428
  have htrace : WordTrace (prefixWord ++ tailWord_116428) baseStart_116428 baseEnd_116428 := by
    simpa [prefixWord, tailWord_116428, baseEnd_116428] using wordTrace_append hprefix tailTrace_116428
  have hstable : (prefixWord ++ tailWord_116428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116428).length < 2 ^ (prefixWord ++ tailWord_116428).sum := by decide
  have hdescent : baseEnd_116428 < baseStart_116428 := by decide
  rcases family_descends (prefixWord ++ tailWord_116428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116484 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 4]
def baseStart_116484 : Nat := 118140960795 + 116484 * 2 ^ 59
def prefixEnd_116484 : Nat := 4983230072969 + 3 ^ 40 * 116484 * 2
def baseEnd_116484 : Nat := 26583235803745550895247

theorem tailTrace_116484 : CollatzResearch.WordTrace tailWord_116484 prefixEnd_116484 26583235803745550895247 := by
  unfold tailWord_116484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2124260255002918364238253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2832347006670557818984337 2124260255002918364238253)
  ·
    refine ⟨796597595626094386589345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2124260255002918364238253 796597595626094386589345)
    ·
      refine ⟨597448196719570789942009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 796597595626094386589345 597448196719570789942009)
      ·
        refine ⟨448086147539678092456507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 597448196719570789942009 448086147539678092456507)
        ·
          refine ⟨672129221309517138684761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 448086147539678092456507 672129221309517138684761)
          ·
            refine ⟨504096915982137854013571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 672129221309517138684761 504096915982137854013571)
            ·
              refine ⟨756145373973206781020357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 504096915982137854013571 756145373973206781020357)
              ·
                refine ⟨141777257619976271441317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 756145373973206781020357 141777257619976271441317)
                ·
                  refine ⟨26583235803745550895247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141777257619976271441317 26583235803745550895247)
                  ·
                    rfl

theorem cell21_116484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_116484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116484 prefixEnd_116484 := by exact prefixLift 116484
  have htrace : WordTrace (prefixWord ++ tailWord_116484) baseStart_116484 baseEnd_116484 := by
    simpa [prefixWord, tailWord_116484, baseEnd_116484] using wordTrace_append hprefix tailTrace_116484
  have hstable : (prefixWord ++ tailWord_116484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116484).length < 2 ^ (prefixWord ++ tailWord_116484).sum := by decide
  have hdescent : baseEnd_116484 < baseStart_116484 := by decide
  rcases family_descends (prefixWord ++ tailWord_116484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116487 : List Nat := [1, 1, 4, 4, 2, 1, 1, 4, 3]
def baseStart_116487 : Nat := 118140960795 + 116487 * 2 ^ 59
def prefixEnd_116487 : Nat := 4983230072969 + 3 ^ 40 * 116487 * 2
def baseEnd_116487 : Nat := 26583920444618212345241

theorem tailTrace_116487 : CollatzResearch.WordTrace tailWord_116487 prefixEnd_116487 26583920444618212345241 := by
  unfold tailWord_116487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4248629928994968240835715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2832419952663312160557143 4248629928994968240835715)
  ·
    refine ⟨6372944893492452361253573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4248629928994968240835715 6372944893492452361253573)
    ·
      refine ⟨1194927167529834817735045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6372944893492452361253573 1194927167529834817735045)
      ·
        refine ⟨224048843911844028325321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1194927167529834817735045 224048843911844028325321)
        ·
          refine ⟨168036632933883021243991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224048843911844028325321 168036632933883021243991)
          ·
            refine ⟨252054949400824531865987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168036632933883021243991 252054949400824531865987)
            ·
              refine ⟨378082424101236797798981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252054949400824531865987 378082424101236797798981)
              ·
                refine ⟨70890454518981899587309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 378082424101236797798981 70890454518981899587309)
                ·
                  refine ⟨26583920444618212345241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70890454518981899587309 26583920444618212345241)
                  ·
                    rfl

theorem cell21_116487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 3].length) (baseStart_116487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116487 prefixEnd_116487 := by exact prefixLift 116487
  have htrace : WordTrace (prefixWord ++ tailWord_116487) baseStart_116487 baseEnd_116487 := by
    simpa [prefixWord, tailWord_116487, baseEnd_116487] using wordTrace_append hprefix tailTrace_116487
  have hstable : (prefixWord ++ tailWord_116487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116487).length < 2 ^ (prefixWord ++ tailWord_116487).sum := by decide
  have hdescent : baseEnd_116487 < baseStart_116487 := by decide
  rcases family_descends (prefixWord ++ tailWord_116487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116580 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_116580 : Nat := 118140960795 + 116580 * 2 ^ 59
def prefixEnd_116580 : Nat := 4983230072969 + 3 ^ 40 * 116580 * 2
def baseEnd_116580 : Nat := 26605144311670717295051

theorem tailTrace_116580 : CollatzResearch.WordTrace tailWord_116580 prefixEnd_116580 26605144311670717295051 := by
  unfold tailWord_116580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126010958829022561985597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2834681278438696749314129 2126010958829022561985597)
  ·
    refine ⟨797254109560883460744599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2126010958829022561985597 797254109560883460744599)
    ·
      refine ⟨1195881164341325191116899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 797254109560883460744599 1195881164341325191116899)
      ·
        refine ⟨1793821746511987786675349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1195881164341325191116899 1793821746511987786675349)
        ·
          refine ⟨84085394367749427500407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1793821746511987786675349 84085394367749427500407)
          ·
            refine ⟨126128091551624141250611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84085394367749427500407 126128091551624141250611)
            ·
              refine ⟨189192137327436211875917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126128091551624141250611 189192137327436211875917)
              ·
                refine ⟨70947051497788579453469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 189192137327436211875917 70947051497788579453469)
                ·
                  refine ⟨26605144311670717295051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70947051497788579453469 26605144311670717295051)
                  ·
                    rfl

theorem cell21_116580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_116580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116580 prefixEnd_116580 := by exact prefixLift 116580
  have htrace : WordTrace (prefixWord ++ tailWord_116580) baseStart_116580 baseEnd_116580 := by
    simpa [prefixWord, tailWord_116580, baseEnd_116580] using wordTrace_append hprefix tailTrace_116580
  have hstable : (prefixWord ++ tailWord_116580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116580).length < 2 ^ (prefixWord ++ tailWord_116580).sum := by decide
  have hdescent : baseEnd_116580 < baseStart_116580 := by decide
  rcases family_descends (prefixWord ++ tailWord_116580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116633 : List Nat := [1, 2, 1, 2, 1, 3, 4, 7]
def baseStart_116633 : Nat := 118140960795 + 116633 * 2 ^ 59
def prefixEnd_116633 : Nat := 4983230072969 + 3 ^ 40 * 116633 * 2
def baseEnd_116633 : Nat := 8872413211251467637203

theorem tailTrace_116633 : CollatzResearch.WordTrace tailWord_116633 prefixEnd_116633 8872413211251467637203 := by
  unfold tailWord_116633
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253954986466035175650553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2835969990977356783767035 4253954986466035175650553)
  ·
    refine ⟨3190466239849526381737915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4253954986466035175650553 3190466239849526381737915)
    ·
      refine ⟨4785699359774289572606873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3190466239849526381737915 4785699359774289572606873)
      ·
        refine ⟨3589274519830717179455155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4785699359774289572606873 3589274519830717179455155)
        ·
          refine ⟨5383911779746075769182733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3589274519830717179455155 5383911779746075769182733)
          ·
            refine ⟨2018966917404778413443525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5383911779746075769182733 2018966917404778413443525)
            ·
              refine ⟨378556297013395952520661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2018966917404778413443525 378556297013395952520661)
              ·
                refine ⟨8872413211251467637203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 378556297013395952520661 8872413211251467637203)
                ·
                  rfl

theorem cell21_116633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_116633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116633 prefixEnd_116633 := by exact prefixLift 116633
  have htrace : WordTrace (prefixWord ++ tailWord_116633) baseStart_116633 baseEnd_116633 := by
    simpa [prefixWord, tailWord_116633, baseEnd_116633] using wordTrace_append hprefix tailTrace_116633
  have hstable : (prefixWord ++ tailWord_116633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116633).length < 2 ^ (prefixWord ++ tailWord_116633).sum := by decide
  have hdescent : baseEnd_116633 < baseStart_116633 := by decide
  rcases family_descends (prefixWord ++ tailWord_116633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116664 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 5]
def baseStart_116664 : Nat := 118140960795 + 116664 * 2 ^ 59
def prefixEnd_116664 : Nat := 4983230072969 + 3 ^ 40 * 116664 * 2
def baseEnd_116664 : Nat := 26624314256105237894879

theorem tailTrace_116664 : CollatzResearch.WordTrace tailWord_116664 prefixEnd_116664 26624314256105237894879 := by
  unfold tailWord_116664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2127542824676863735014523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2836723766235818313352697 2127542824676863735014523)
  ·
    refine ⟨3191314237015295602521785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2127542824676863735014523 3191314237015295602521785)
    ·
      refine ⟨2393485677761471701891339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3191314237015295602521785 2393485677761471701891339)
      ·
        refine ⟨3590228516642207552837009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2393485677761471701891339 3590228516642207552837009)
        ·
          refine ⟨2692671387481655664627757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3590228516642207552837009 2692671387481655664627757)
          ·
            refine ⟨1009751770305620874235409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2692671387481655664627757 1009751770305620874235409)
            ·
              refine ⟨757313827729215655676557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1009751770305620874235409 757313827729215655676557)
              ·
                refine ⟨283992685398455870878709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 757313827729215655676557 283992685398455870878709)
                ·
                  refine ⟨26624314256105237894879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 283992685398455870878709 26624314256105237894879)
                  ·
                    rfl

theorem cell21_116664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_116664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116664 prefixEnd_116664 := by exact prefixLift 116664
  have htrace : WordTrace (prefixWord ++ tailWord_116664) baseStart_116664 baseEnd_116664 := by
    simpa [prefixWord, tailWord_116664, baseEnd_116664] using wordTrace_append hprefix tailTrace_116664
  have hstable : (prefixWord ++ tailWord_116664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116664).length < 2 ^ (prefixWord ++ tailWord_116664).sum := by decide
  have hdescent : baseEnd_116664 < baseStart_116664 := by decide
  rcases family_descends (prefixWord ++ tailWord_116664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116743 : List Nat := [1, 1, 4, 3, 1, 4, 2, 5]
def baseStart_116743 : Nat := 118140960795 + 116743 * 2 ^ 59
def prefixEnd_116743 : Nat := 4983230072969 + 3 ^ 40 * 116743 * 2
def baseEnd_116743 : Nat := 8880781044139552026017

theorem tailTrace_116743 : CollatzResearch.WordTrace tailWord_116743 prefixEnd_116743 8880781044139552026017 := by
  unfold tailWord_116743
  simp only [CollatzResearch.WordTrace]
  refine ⟨4257967016067523962154883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2838644677378349308103255 4257967016067523962154883)
  ·
    refine ⟨6386950524101285943232325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4257967016067523962154883 6386950524101285943232325)
    ·
      refine ⟨1197553223268991114356061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6386950524101285943232325 1197553223268991114356061)
      ·
        refine ⟨449082458725871667883523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1197553223268991114356061 449082458725871667883523)
        ·
          refine ⟨673623688088807501825285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449082458725871667883523 673623688088807501825285)
          ·
            refine ⟨126304441516651406592241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 673623688088807501825285 126304441516651406592241)
            ·
              refine ⟨94728331137488554944181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126304441516651406592241 94728331137488554944181)
              ·
                refine ⟨8880781044139552026017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94728331137488554944181 8880781044139552026017)
                ·
                  rfl

theorem cell21_116743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 2, 5].length) (baseStart_116743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116743 prefixEnd_116743 := by exact prefixLift 116743
  have htrace : WordTrace (prefixWord ++ tailWord_116743) baseStart_116743 baseEnd_116743 := by
    simpa [prefixWord, tailWord_116743, baseEnd_116743] using wordTrace_append hprefix tailTrace_116743
  have hstable : (prefixWord ++ tailWord_116743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116743).length < 2 ^ (prefixWord ++ tailWord_116743).sum := by decide
  have hdescent : baseEnd_116743 < baseStart_116743 := by decide
  rcases family_descends (prefixWord ++ tailWord_116743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116771 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_116771 : Nat := 118140960795 + 116771 * 2 ^ 59
def prefixEnd_116771 : Nat := 4983230072969 + 3 ^ 40 * 116771 * 2
def baseEnd_116771 : Nat := 26648733113896829611327

theorem tailTrace_116771 : CollatzResearch.WordTrace tailWord_116771 prefixEnd_116771 26648733113896829611327 := by
  unfold tailWord_116771
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258988259966084744174167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839325506644056496116111 4258988259966084744174167)
  ·
    refine ⟨6388482389949127116261251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4258988259966084744174167 6388482389949127116261251)
    ·
      refine ⟨9582723584923690674391877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6388482389949127116261251 9582723584923690674391877)
      ·
        refine ⟨1796760672173192001448477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9582723584923690674391877 1796760672173192001448477)
        ·
          refine ⟨673785252064947000543179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1796760672173192001448477 673785252064947000543179)
          ·
            refine ⟨1010677878097420500814769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 673785252064947000543179 1010677878097420500814769)
            ·
              refine ⟨758008408573065375611077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1010677878097420500814769 758008408573065375611077)
              ·
                refine ⟨142126576607449757927077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 758008408573065375611077 142126576607449757927077)
                ·
                  refine ⟨26648733113896829611327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142126576607449757927077 26648733113896829611327)
                  ·
                    rfl

theorem cell21_116771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_116771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116771 prefixEnd_116771 := by exact prefixLift 116771
  have htrace : WordTrace (prefixWord ++ tailWord_116771) baseStart_116771 baseEnd_116771 := by
    simpa [prefixWord, tailWord_116771, baseEnd_116771] using wordTrace_append hprefix tailTrace_116771
  have hstable : (prefixWord ++ tailWord_116771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116771).length < 2 ^ (prefixWord ++ tailWord_116771).sum := by decide
  have hdescent : baseEnd_116771 < baseStart_116771 := by decide
  rcases family_descends (prefixWord ++ tailWord_116771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116785 : List Nat := [1, 2, 2, 3, 1, 3, 1, 8]
def baseStart_116785 : Nat := 118140960795 + 116785 * 2 ^ 59
def prefixEnd_116785 : Nat := 4983230072969 + 3 ^ 40 * 116785 * 2
def baseEnd_116785 : Nat := 8883976034878638792655

theorem tailTrace_116785 : CollatzResearch.WordTrace tailWord_116785 prefixEnd_116785 8883976034878638792655 := by
  unfold tailWord_116785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4259498881915365135183809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839665921276910090122539 4259498881915365135183809)
  ·
    refine ⟨3194624161436523851387857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4259498881915365135183809 3194624161436523851387857)
    ·
      refine ⟨2395968121077392888540893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3194624161436523851387857 2395968121077392888540893)
      ·
        refine ⟨898488045404022333202835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2395968121077392888540893 898488045404022333202835)
        ·
          refine ⟨1347732068106033499804253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 898488045404022333202835 1347732068106033499804253)
          ·
            refine ⟨505399525539762562426595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1347732068106033499804253 505399525539762562426595)
            ·
              refine ⟨758099288309643843639893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 505399525539762562426595 758099288309643843639893)
              ·
                refine ⟨8883976034878638792655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 758099288309643843639893 8883976034878638792655)
                ·
                  rfl

theorem cell21_116785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 8].length) (baseStart_116785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116785 prefixEnd_116785 := by exact prefixLift 116785
  have htrace : WordTrace (prefixWord ++ tailWord_116785) baseStart_116785 baseEnd_116785 := by
    simpa [prefixWord, tailWord_116785, baseEnd_116785] using wordTrace_append hprefix tailTrace_116785
  have hstable : (prefixWord ++ tailWord_116785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116785).length < 2 ^ (prefixWord ++ tailWord_116785).sum := by decide
  have hdescent : baseEnd_116785 < baseStart_116785 := by decide
  rcases family_descends (prefixWord ++ tailWord_116785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116822 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_116822 : Nat := 118140960795 + 116822 * 2 ^ 59
def prefixEnd_116822 : Nat := 4983230072969 + 3 ^ 40 * 116822 * 2
def baseEnd_116822 : Nat := 26660372008732074261223

theorem tailTrace_116822 : CollatzResearch.WordTrace tailWord_116822 prefixEnd_116822 26660372008732074261223 := by
  unfold tailWord_116822
  simp only [CollatzResearch.WordTrace]
  refine ⟨266303023923832528392545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2840565588520880302853813 266303023923832528392545)
  ·
    refine ⟨199727267942874396294409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 266303023923832528392545 199727267942874396294409)
    ·
      refine ⟨149795450957155797220807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199727267942874396294409 149795450957155797220807)
      ·
        refine ⟨224693176435733695831211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149795450957155797220807 224693176435733695831211)
        ·
          refine ⟨337039764653600543746817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224693176435733695831211 337039764653600543746817)
          ·
            refine ⟨252779823490200407810113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337039764653600543746817 252779823490200407810113)
            ·
              refine ⟨189584867617650305857585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252779823490200407810113 189584867617650305857585)
              ·
                refine ⟨142188650713237729393189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189584867617650305857585 142188650713237729393189)
                ·
                  refine ⟨26660372008732074261223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142188650713237729393189 26660372008732074261223)
                  ·
                    rfl

theorem cell21_116822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_116822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116822 prefixEnd_116822 := by exact prefixLift 116822
  have htrace : WordTrace (prefixWord ++ tailWord_116822) baseStart_116822 baseEnd_116822 := by
    simpa [prefixWord, tailWord_116822, baseEnd_116822] using wordTrace_append hprefix tailTrace_116822
  have hstable : (prefixWord ++ tailWord_116822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116822).length < 2 ^ (prefixWord ++ tailWord_116822).sum := by decide
  have hdescent : baseEnd_116822 < baseStart_116822 := by decide
  rcases family_descends (prefixWord ++ tailWord_116822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116847 : List Nat := [1, 1, 2, 1, 3, 4, 2, 3, 4]
def baseStart_116847 : Nat := 118140960795 + 116847 * 2 ^ 59
def prefixEnd_116847 : Nat := 4983230072969 + 3 ^ 40 * 116847 * 2
def baseEnd_116847 : Nat := 26666077349337586344505

theorem tailTrace_116847 : CollatzResearch.WordTrace tailWord_116847 prefixEnd_116847 26666077349337586344505 := by
  unfold tailWord_116847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261760207690749723940795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2841173471793833149293863 4261760207690749723940795)
  ·
    refine ⟨6392640311536124585911193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261760207690749723940795 6392640311536124585911193)
    ·
      refine ⟨4794480233652093439433395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392640311536124585911193 4794480233652093439433395)
      ·
        refine ⟨7191720350478140159150093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794480233652093439433395 7191720350478140159150093)
        ·
          refine ⟨2696895131429302559681285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7191720350478140159150093 2696895131429302559681285)
          ·
            refine ⟨505667837142994229940241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2696895131429302559681285 505667837142994229940241)
            ·
              refine ⟨379250877857245672455181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505667837142994229940241 379250877857245672455181)
              ·
                refine ⟨142219079196467127170693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 379250877857245672455181 142219079196467127170693)
                ·
                  refine ⟨26666077349337586344505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142219079196467127170693 26666077349337586344505)
                  ·
                    rfl

theorem cell21_116847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 4].length) (baseStart_116847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116847 prefixEnd_116847 := by exact prefixLift 116847
  have htrace : WordTrace (prefixWord ++ tailWord_116847) baseStart_116847 baseEnd_116847 := by
    simpa [prefixWord, tailWord_116847, baseEnd_116847] using wordTrace_append hprefix tailTrace_116847
  have hstable : (prefixWord ++ tailWord_116847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116847).length < 2 ^ (prefixWord ++ tailWord_116847).sum := by decide
  have hdescent : baseEnd_116847 < baseStart_116847 := by decide
  rcases family_descends (prefixWord ++ tailWord_116847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116878 : List Nat := [4, 1, 1, 3, 3, 1, 8]
def baseStart_116878 : Nat := 118140960795 + 116878 * 2 ^ 59
def prefixEnd_116878 : Nat := 4983230072969 + 3 ^ 40 * 116878 * 2
def baseEnd_116878 : Nat := 2963683552409824591975

theorem tailTrace_116878 : CollatzResearch.WordTrace tailWord_116878 prefixEnd_116878 2963683552409824591975 := by
  unfold tailWord_116878
  simp only [CollatzResearch.WordTrace]
  refine ⟨532861358822305252289911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2841927247052294678879525 532861358822305252289911)
  ·
    refine ⟨799292038233457878434867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532861358822305252289911 799292038233457878434867)
    ·
      refine ⟨1198938057350186817652301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 799292038233457878434867 1198938057350186817652301)
      ·
        refine ⟨449601771506320056619613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1198938057350186817652301 449601771506320056619613)
        ·
          refine ⟨168600664314870021232355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449601771506320056619613 168600664314870021232355)
          ·
            refine ⟨252900996472305031848533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168600664314870021232355 252900996472305031848533)
            ·
              refine ⟨2963683552409824591975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 252900996472305031848533 2963683552409824591975)
              ·
                rfl

theorem cell21_116878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 8].length) (baseStart_116878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116878 prefixEnd_116878 := by exact prefixLift 116878
  have htrace : WordTrace (prefixWord ++ tailWord_116878) baseStart_116878 baseEnd_116878 := by
    simpa [prefixWord, tailWord_116878, baseEnd_116878] using wordTrace_append hprefix tailTrace_116878
  have hstable : (prefixWord ++ tailWord_116878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116878).length < 2 ^ (prefixWord ++ tailWord_116878).sum := by decide
  have hdescent : baseEnd_116878 < baseStart_116878 := by decide
  rcases family_descends (prefixWord ++ tailWord_116878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116909 : List Nat := [1, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_116909 : Nat := 118140960795 + 116909 * 2 ^ 59
def prefixEnd_116909 : Nat := 4983230072969 + 3 ^ 40 * 116909 * 2
def baseEnd_116909 : Nat := 26680226594039256311045

theorem tailTrace_116909 : CollatzResearch.WordTrace tailWord_116909 prefixEnd_116909 26680226594039256311045 := by
  unfold tailWord_116909
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264021533466134312697781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2842681022310756208465187 4264021533466134312697781)
  ·
    refine ⟨399752018762450091815417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4264021533466134312697781 399752018762450091815417)
    ·
      refine ⟨299814014071837568861563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 399752018762450091815417 299814014071837568861563)
      ·
        refine ⟨449721021107756353292345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299814014071837568861563 449721021107756353292345)
        ·
          refine ⟨337290765830817264969259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449721021107756353292345 337290765830817264969259)
          ·
            refine ⟨505936148746225897453889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337290765830817264969259 505936148746225897453889)
            ·
              refine ⟨379452111559669423090417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505936148746225897453889 379452111559669423090417)
              ·
                refine ⟨284589083669752067317813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379452111559669423090417 284589083669752067317813)
                ·
                  refine ⟨26680226594039256311045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284589083669752067317813 26680226594039256311045)
                  ·
                    rfl

theorem cell21_116909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_116909 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116909 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116909 prefixEnd_116909 := by exact prefixLift 116909
  have htrace : WordTrace (prefixWord ++ tailWord_116909) baseStart_116909 baseEnd_116909 := by
    simpa [prefixWord, tailWord_116909, baseEnd_116909] using wordTrace_append hprefix tailTrace_116909
  have hstable : (prefixWord ++ tailWord_116909).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116909).length < 2 ^ (prefixWord ++ tailWord_116909).sum := by decide
  have hdescent : baseEnd_116909 < baseStart_116909 := by decide
  rcases family_descends (prefixWord ++ tailWord_116909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116957 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 4]
def baseStart_116957 : Nat := 118140960795 + 116957 * 2 ^ 59
def prefixEnd_116957 : Nat := 4983230072969 + 3 ^ 40 * 116957 * 2
def baseEnd_116957 : Nat := 26691180848001839510947

theorem tailTrace_116957 : CollatzResearch.WordTrace tailWord_116957 prefixEnd_116957 26691180848001839510947 := by
  unfold tailWord_116957
  simp only [CollatzResearch.WordTrace]
  refine ⟨4265772237292238510445125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2843848158194825673630083 4265772237292238510445125)
  ·
    refine ⟨799832294492294720708461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4265772237292238510445125 799832294492294720708461)
    ·
      refine ⟨299937110434610520265673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 799832294492294720708461 299937110434610520265673)
      ·
        refine ⟨224952832825957890199255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299937110434610520265673 224952832825957890199255)
        ·
          refine ⟨337429249238936835298883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224952832825957890199255 337429249238936835298883)
          ·
            refine ⟨506143873858405252948325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337429249238936835298883 506143873858405252948325)
            ·
              refine ⟨94901976348450984927811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506143873858405252948325 94901976348450984927811)
              ·
                refine ⟨142352964522676477391717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94901976348450984927811 142352964522676477391717)
                ·
                  refine ⟨26691180848001839510947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142352964522676477391717 26691180848001839510947)
                  ·
                    rfl

theorem cell21_116957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_116957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_116957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_116957 prefixEnd_116957 := by exact prefixLift 116957
  have htrace : WordTrace (prefixWord ++ tailWord_116957) baseStart_116957 baseEnd_116957 := by
    simpa [prefixWord, tailWord_116957, baseEnd_116957] using wordTrace_append hprefix tailTrace_116957
  have hstable : (prefixWord ++ tailWord_116957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116957).length < 2 ^ (prefixWord ++ tailWord_116957).sum := by decide
  have hdescent : baseEnd_116957 < baseStart_116957 := by decide
  rcases family_descends (prefixWord ++ tailWord_116957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117002 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 3]
def baseStart_117002 : Nat := 118140960795 + 117002 * 2 ^ 59
def prefixEnd_117002 : Nat := 4983230072969 + 3 ^ 40 * 117002 * 2
def baseEnd_117002 : Nat := 26701450461091761260855

theorem tailTrace_117002 : CollatzResearch.WordTrace tailWord_117002 prefixEnd_117002 26701450461091761260855 := by
  unfold tailWord_117002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1066853380532302798958315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2844942348086140797222173 1066853380532302798958315)
  ·
    refine ⟨1600280070798454198437473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1066853380532302798958315 1600280070798454198437473)
    ·
      refine ⟨1200210053098840648828105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600280070798454198437473 1200210053098840648828105)
      ·
        refine ⟨900157539824130486621079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200210053098840648828105 900157539824130486621079)
        ·
          refine ⟨1350236309736195729931619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900157539824130486621079 1350236309736195729931619)
          ·
            refine ⟨2025354464604293594897429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350236309736195729931619 2025354464604293594897429)
            ·
              refine ⟨94938490528326262260817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2025354464604293594897429 94938490528326262260817)
              ·
                refine ⟨71203867896244696695613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94938490528326262260817 71203867896244696695613)
                ·
                  refine ⟨26701450461091761260855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71203867896244696695613 26701450461091761260855)
                  ·
                    rfl

theorem cell21_117002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_117002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117002 prefixEnd_117002 := by exact prefixLift 117002
  have htrace : WordTrace (prefixWord ++ tailWord_117002) baseStart_117002 baseEnd_117002 := by
    simpa [prefixWord, tailWord_117002, baseEnd_117002] using wordTrace_append hprefix tailTrace_117002
  have hstable : (prefixWord ++ tailWord_117002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117002).length < 2 ^ (prefixWord ++ tailWord_117002).sum := by decide
  have hdescent : baseEnd_117002 < baseStart_117002 := by decide
  rcases family_descends (prefixWord ++ tailWord_117002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117013 : List Nat := [1, 3, 2, 1, 2, 1, 5, 6]
def baseStart_117013 : Nat := 118140960795 + 117013 * 2 ^ 59
def prefixEnd_117013 : Nat := 4983230072969 + 3 ^ 40 * 117013 * 2
def baseEnd_117013 : Nat := 8901320270319395525833

theorem tailTrace_117013 : CollatzResearch.WordTrace tailWord_117013 prefixEnd_117013 8901320270319395525833 := by
  unfold tailWord_117013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267814725089360074483693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2845209816726240049655795 4267814725089360074483693)
  ·
    refine ⟨1600430521908510027931385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4267814725089360074483693 1600430521908510027931385)
    ·
      refine ⟨1200322891431382520948539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600430521908510027931385 1200322891431382520948539)
      ·
        refine ⟨1800484337147073781422809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200322891431382520948539 1800484337147073781422809)
        ·
          refine ⟨1350363252860305336067107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800484337147073781422809 1350363252860305336067107)
          ·
            refine ⟨2025544879290458004100661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350363252860305336067107 2025544879290458004100661)
            ·
              refine ⟨189894832433480437884437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2025544879290458004100661 189894832433480437884437)
              ·
                refine ⟨8901320270319395525833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 189894832433480437884437 8901320270319395525833)
                ·
                  rfl

theorem cell21_117013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_117013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117013 prefixEnd_117013 := by exact prefixLift 117013
  have htrace : WordTrace (prefixWord ++ tailWord_117013) baseStart_117013 baseEnd_117013 := by
    simpa [prefixWord, tailWord_117013, baseEnd_117013] using wordTrace_append hprefix tailTrace_117013
  have hstable : (prefixWord ++ tailWord_117013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117013).length < 2 ^ (prefixWord ++ tailWord_117013).sum := by decide
  have hdescent : baseEnd_117013 < baseStart_117013 := by decide
  rcases family_descends (prefixWord ++ tailWord_117013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117165 : List Nat := [1, 5, 2, 2, 11]
def baseStart_117165 : Nat := 118140960795 + 117165 * 2 ^ 59
def prefixEnd_117165 : Nat := 4983230072969 + 3 ^ 40 * 117165 * 2
def baseEnd_117165 : Nat := 330106781257280247455

theorem tailTrace_117165 : CollatzResearch.WordTrace tailWord_117165 prefixEnd_117165 330106781257280247455 := by
  unfold tailWord_117165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273358620538690034016949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2848905747025793356011299 4273358620538690034016949)
  ·
    refine ⟨400627370675502190689089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4273358620538690034016949 400627370675502190689089)
    ·
      refine ⟨300470528006626643016817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400627370675502190689089 300470528006626643016817)
      ·
        refine ⟨225352896004969982262613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300470528006626643016817 225352896004969982262613)
        ·
          refine ⟨330106781257280247455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 225352896004969982262613 330106781257280247455)
          ·
            rfl

theorem cell21_117165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 11].length) (baseStart_117165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117165 prefixEnd_117165 := by exact prefixLift 117165
  have htrace : WordTrace (prefixWord ++ tailWord_117165) baseStart_117165 baseEnd_117165 := by
    simpa [prefixWord, tailWord_117165, baseEnd_117165] using wordTrace_append hprefix tailTrace_117165
  have hstable : (prefixWord ++ tailWord_117165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117165).length < 2 ^ (prefixWord ++ tailWord_117165).sum := by decide
  have hdescent : baseEnd_117165 < baseStart_117165 := by decide
  rcases family_descends (prefixWord ++ tailWord_117165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117210 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_117210 : Nat := 118140960795 + 117210 * 2 ^ 59
def prefixEnd_117210 : Nat := 4983230072969 + 3 ^ 40 * 117210 * 2
def baseEnd_117210 : Nat := 26748918894929621793763

theorem tailTrace_117210 : CollatzResearch.WordTrace tailWord_117210 prefixEnd_117210 26748918894929621793763 := by
  unfold tailWord_117210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068749976343915679851271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2849999936917108479603389 1068749976343915679851271)
  ·
    refine ⟨1603124964515873519776907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068749976343915679851271 1603124964515873519776907)
    ·
      refine ⟨2404687446773810279665361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603124964515873519776907 2404687446773810279665361)
      ·
        refine ⟨1803515585080357709749021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404687446773810279665361 1803515585080357709749021)
        ·
          refine ⟨676318344405134141155883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1803515585080357709749021 676318344405134141155883)
          ·
            refine ⟨1014477516607701211733825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676318344405134141155883 1014477516607701211733825)
            ·
              refine ⟨760858137455775908800369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014477516607701211733825 760858137455775908800369)
              ·
                refine ⟨570643603091831931600277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 760858137455775908800369 570643603091831931600277)
                ·
                  refine ⟨26748918894929621793763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 570643603091831931600277 26748918894929621793763)
                  ·
                    rfl

theorem cell21_117210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_117210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117210 prefixEnd_117210 := by exact prefixLift 117210
  have htrace : WordTrace (prefixWord ++ tailWord_117210) baseStart_117210 baseEnd_117210 := by
    simpa [prefixWord, tailWord_117210, baseEnd_117210] using wordTrace_append hprefix tailTrace_117210
  have hstable : (prefixWord ++ tailWord_117210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117210).length < 2 ^ (prefixWord ++ tailWord_117210).sum := by decide
  have hdescent : baseEnd_117210 < baseStart_117210 := by decide
  rcases family_descends (prefixWord ++ tailWord_117210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117340 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 3]
def baseStart_117340 : Nat := 118140960795 + 117340 * 2 ^ 59
def prefixEnd_117340 : Nat := 4983230072969 + 3 ^ 40 * 117340 * 2
def baseEnd_117340 : Nat := 26778586666078284626831

theorem tailTrace_117340 : CollatzResearch.WordTrace tailWord_117340 prefixEnd_117340 26778586666078284626831 := by
  unfold tailWord_117340
  simp only [CollatzResearch.WordTrace]
  refine ⟨2139870697452347460818737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2853160929936463281091649 2139870697452347460818737)
  ·
    refine ⟨1604903023089260595614053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2139870697452347460818737 1604903023089260595614053)
    ·
      refine ⟨300919316829236361677635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1604903023089260595614053 300919316829236361677635)
      ·
        refine ⟨451378975243854542516453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300919316829236361677635 451378975243854542516453)
        ·
          refine ⟨84633557858222726721835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451378975243854542516453 84633557858222726721835)
          ·
            refine ⟨126950336787334090082753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84633557858222726721835 126950336787334090082753)
            ·
              refine ⟨95212752590500567562065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126950336787334090082753 95212752590500567562065)
              ·
                refine ⟨71409564442875425671549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95212752590500567562065 71409564442875425671549)
                ·
                  refine ⟨26778586666078284626831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71409564442875425671549 26778586666078284626831)
                  ·
                    rfl

theorem cell21_117340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 3].length) (baseStart_117340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117340 prefixEnd_117340 := by exact prefixLift 117340
  have htrace : WordTrace (prefixWord ++ tailWord_117340) baseStart_117340 baseEnd_117340 := by
    simpa [prefixWord, tailWord_117340, baseEnd_117340] using wordTrace_append hprefix tailTrace_117340
  have hstable : (prefixWord ++ tailWord_117340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117340).length < 2 ^ (prefixWord ++ tailWord_117340).sum := by decide
  have hdescent : baseEnd_117340 < baseStart_117340 := by decide
  rcases family_descends (prefixWord ++ tailWord_117340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117365 : List Nat := [1, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_117365 : Nat := 118140960795 + 117365 * 2 ^ 59
def prefixEnd_117365 : Nat := 4983230072969 + 3 ^ 40 * 117365 * 2
def baseEnd_117365 : Nat := 26784292006683796710113

theorem tailTrace_117365 : CollatzResearch.WordTrace tailWord_117365 prefixEnd_117365 26784292006683796710113 := by
  unfold tailWord_117365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280653219814124191297549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2853768813209416127531699 4280653219814124191297549)
  ·
    refine ⟨1605244957430296571736581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4280653219814124191297549 1605244957430296571736581)
    ·
      refine ⟨300983429518180607200609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1605244957430296571736581 300983429518180607200609)
      ·
        refine ⟨225737572138635455400457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300983429518180607200609 225737572138635455400457)
        ·
          refine ⟨169303179103976591550343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225737572138635455400457 169303179103976591550343)
          ·
            refine ⟨253954768655964887325515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169303179103976591550343 253954768655964887325515)
            ·
              refine ⟨380932152983947330988273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253954768655964887325515 380932152983947330988273)
              ·
                refine ⟨285699114737960498241205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380932152983947330988273 285699114737960498241205)
                ·
                  refine ⟨26784292006683796710113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285699114737960498241205 26784292006683796710113)
                  ·
                    rfl

theorem cell21_117365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_117365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117365 prefixEnd_117365 := by exact prefixLift 117365
  have htrace : WordTrace (prefixWord ++ tailWord_117365) baseStart_117365 baseEnd_117365 := by
    simpa [prefixWord, tailWord_117365, baseEnd_117365] using wordTrace_append hprefix tailTrace_117365
  have hstable : (prefixWord ++ tailWord_117365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117365).length < 2 ^ (prefixWord ++ tailWord_117365).sum := by decide
  have hdescent : baseEnd_117365 < baseStart_117365 := by decide
  rcases family_descends (prefixWord ++ tailWord_117365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117396 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 4]
def baseStart_117396 : Nat := 118140960795 + 117396 * 2 ^ 59
def prefixEnd_117396 : Nat := 4983230072969 + 3 ^ 40 * 117396 * 2
def baseEnd_117396 : Nat := 26791366629034631693383

theorem tailTrace_117396 : CollatzResearch.WordTrace tailWord_117396 prefixEnd_117396 26791366629034631693383 := by
  unfold tailWord_117396
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140891941350908242838021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2854522588467877657117361 2140891941350908242838021)
  ·
    refine ⟨401417239003295295532129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2140891941350908242838021 401417239003295295532129)
    ·
      refine ⟨301062929252471471649097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401417239003295295532129 301062929252471471649097)
      ·
        refine ⟨225797196939353603736823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301062929252471471649097 225797196939353603736823)
        ·
          refine ⟨338695795409030405605235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225797196939353603736823 338695795409030405605235)
          ·
            refine ⟨508043693113545608407853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338695795409030405605235 508043693113545608407853)
            ·
              refine ⟨190516384917579603152945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508043693113545608407853 190516384917579603152945)
              ·
                refine ⟨142887288688184702364709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190516384917579603152945 142887288688184702364709)
                ·
                  refine ⟨26791366629034631693383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142887288688184702364709 26791366629034631693383)
                  ·
                    rfl

theorem cell21_117396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_117396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117396 prefixEnd_117396 := by exact prefixLift 117396
  have htrace : WordTrace (prefixWord ++ tailWord_117396) baseStart_117396 baseEnd_117396 := by
    simpa [prefixWord, tailWord_117396, baseEnd_117396] using wordTrace_append hprefix tailTrace_117396
  have hstable : (prefixWord ++ tailWord_117396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117396).length < 2 ^ (prefixWord ++ tailWord_117396).sum := by decide
  have hdescent : baseEnd_117396 < baseStart_117396 := by decide
  rcases family_descends (prefixWord ++ tailWord_117396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117438 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_117438 : Nat := 118140960795 + 117438 * 2 ^ 59
def prefixEnd_117438 : Nat := 4983230072969 + 3 ^ 40 * 117438 * 2
def baseEnd_117438 : Nat := 26800951601251891993297

theorem tailTrace_117438 : CollatzResearch.WordTrace tailWord_117438 prefixEnd_117438 26800951601251891993297 := by
  unfold tailWord_117438
  simp only [CollatzResearch.WordTrace]
  refine ⟨535414468568707207338121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2855543832366438439136645 535414468568707207338121)
  ·
    refine ⟨401560851426530405503591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 535414468568707207338121 401560851426530405503591)
    ·
      refine ⟨602341277139795608255387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401560851426530405503591 602341277139795608255387)
      ·
        refine ⟨903511915709693412383081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602341277139795608255387 903511915709693412383081)
        ·
          refine ⟨677633936782270059287311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903511915709693412383081 677633936782270059287311)
          ·
            refine ⟨1016450905173405088930967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677633936782270059287311 1016450905173405088930967)
            ·
              refine ⟨1524676357760107633396451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016450905173405088930967 1524676357760107633396451)
              ·
                refine ⟨2287014536640161450094677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524676357760107633396451 2287014536640161450094677)
                ·
                  refine ⟨26800951601251891993297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2287014536640161450094677 26800951601251891993297)
                  ·
                    rfl

theorem cell21_117438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_117438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117438 prefixEnd_117438 := by exact prefixLift 117438
  have htrace : WordTrace (prefixWord ++ tailWord_117438) baseStart_117438 baseEnd_117438 := by
    simpa [prefixWord, tailWord_117438, baseEnd_117438] using wordTrace_append hprefix tailTrace_117438
  have hstable : (prefixWord ++ tailWord_117438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117438).length < 2 ^ (prefixWord ++ tailWord_117438).sum := by decide
  have hdescent : baseEnd_117438 < baseStart_117438 := by decide
  rcases family_descends (prefixWord ++ tailWord_117438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117458 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_117458 : Nat := 118140960795 + 117458 * 2 ^ 59
def prefixEnd_117458 : Nat := 4983230072969 + 3 ^ 40 * 117458 * 2
def baseEnd_117458 : Nat := 26805515873736301659923

theorem tailTrace_117458 : CollatzResearch.WordTrace tailWord_117458 prefixEnd_117458 26805515873736301659923 := by
  unfold tailWord_117458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1071011302119300268608257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2856030138984800716288685 1071011302119300268608257)
  ·
    refine ⟨803258476589475201456193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1071011302119300268608257 803258476589475201456193)
    ·
      refine ⟨602443857442106401092145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 803258476589475201456193 602443857442106401092145)
      ·
        refine ⟨451832893081579800819109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602443857442106401092145 451832893081579800819109)
        ·
          refine ⟨84718667452796212653583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451832893081579800819109 84718667452796212653583)
          ·
            refine ⟨127078001179194318980375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84718667452796212653583 127078001179194318980375)
            ·
              refine ⟨190617001768791478470563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127078001179194318980375 190617001768791478470563)
              ·
                refine ⟨285925502653187217705845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190617001768791478470563 285925502653187217705845)
                ·
                  refine ⟨26805515873736301659923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285925502653187217705845 26805515873736301659923)
                  ·
                    rfl

theorem cell21_117458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_117458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117458 prefixEnd_117458 := by exact prefixLift 117458
  have htrace : WordTrace (prefixWord ++ tailWord_117458) baseStart_117458 baseEnd_117458 := by
    simpa [prefixWord, tailWord_117458, baseEnd_117458] using wordTrace_append hprefix tailTrace_117458
  have hstable : (prefixWord ++ tailWord_117458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117458).length < 2 ^ (prefixWord ++ tailWord_117458).sum := by decide
  have hdescent : baseEnd_117458 < baseStart_117458 := by decide
  rcases family_descends (prefixWord ++ tailWord_117458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117497 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_117497 : Nat := 118140960795 + 117497 * 2 ^ 59
def prefixEnd_117497 : Nat := 4983230072969 + 3 ^ 40 * 117497 * 2
def baseEnd_117497 : Nat := 26814416205080900509843

theorem tailTrace_117497 : CollatzResearch.WordTrace tailWord_117497 prefixEnd_117497 26814416205080900509843 := by
  unfold tailWord_117497
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285467655335910735102745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2856978436890607156735163 4285467655335910735102745)
  ·
    refine ⟨3214100741501933051327059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4285467655335910735102745 3214100741501933051327059)
    ·
      refine ⟨4821151112252899576990589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214100741501933051327059 4821151112252899576990589)
      ·
        refine ⟨1807931667094837341371471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4821151112252899576990589 1807931667094837341371471)
        ·
          refine ⟨2711897500642256012057207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807931667094837341371471 2711897500642256012057207)
          ·
            refine ⟨4067846250963384018085811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711897500642256012057207 4067846250963384018085811)
            ·
              refine ⟨6101769376445076027128717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067846250963384018085811 6101769376445076027128717)
              ·
                refine ⟨2288163516166903510173269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6101769376445076027128717 2288163516166903510173269)
                ·
                  refine ⟨26814416205080900509843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2288163516166903510173269 26814416205080900509843)
                  ·
                    rfl

theorem cell21_117497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_117497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117497 prefixEnd_117497 := by exact prefixLift 117497
  have htrace : WordTrace (prefixWord ++ tailWord_117497) baseStart_117497 baseEnd_117497 := by
    simpa [prefixWord, tailWord_117497, baseEnd_117497] using wordTrace_append hprefix tailTrace_117497
  have hstable : (prefixWord ++ tailWord_117497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117497).length < 2 ^ (prefixWord ++ tailWord_117497).sum := by decide
  have hdescent : baseEnd_117497 < baseStart_117497 := by decide
  rcases family_descends (prefixWord ++ tailWord_117497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117565 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 4]
def baseStart_117565 : Nat := 118140960795 + 117565 * 2 ^ 59
def prefixEnd_117565 : Nat := 4983230072969 + 3 ^ 40 * 117565 * 2
def baseEnd_117565 : Nat := 26829934731527893376371

theorem tailTrace_117565 : CollatzResearch.WordTrace tailWord_117565 prefixEnd_117565 26829934731527893376371 := by
  unfold tailWord_117565
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287947819089558348578149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2858631879393038899052099 4287947819089558348578149)
  ·
    refine ⟨803990216079292190358403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4287947819089558348578149 803990216079292190358403)
    ·
      refine ⟨1205985324118938285537605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803990216079292190358403 1205985324118938285537605)
      ·
        refine ⟨226122248272300928538301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1205985324118938285537605 226122248272300928538301)
        ·
          refine ⟨84795843102112848201863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226122248272300928538301 84795843102112848201863)
          ·
            refine ⟨127193764653169272302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84795843102112848201863 127193764653169272302795)
            ·
              refine ⟨190790646979753908454193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127193764653169272302795 190790646979753908454193)
              ·
                refine ⟨143092985234815431340645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190790646979753908454193 143092985234815431340645)
                ·
                  refine ⟨26829934731527893376371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143092985234815431340645 26829934731527893376371)
                  ·
                    rfl

theorem cell21_117565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_117565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117565 prefixEnd_117565 := by exact prefixLift 117565
  have htrace : WordTrace (prefixWord ++ tailWord_117565) baseStart_117565 baseEnd_117565 := by
    simpa [prefixWord, tailWord_117565, baseEnd_117565] using wordTrace_append hprefix tailTrace_117565
  have hstable : (prefixWord ++ tailWord_117565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117565).length < 2 ^ (prefixWord ++ tailWord_117565).sum := by decide
  have hdescent : baseEnd_117565 < baseStart_117565 := by decide
  rcases family_descends (prefixWord ++ tailWord_117565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117576 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 3]
def baseStart_117576 : Nat := 118140960795 + 117576 * 2 ^ 59
def prefixEnd_117576 : Nat := 4983230072969 + 3 ^ 40 * 117576 * 2
def baseEnd_117576 : Nat := 26832445081394318693015

theorem tailTrace_117576 : CollatzResearch.WordTrace tailWord_117576 prefixEnd_117576 26832445081394318693015 := by
  unfold tailWord_117576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2144174511024853613614291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2858899348033138151485721 2144174511024853613614291)
  ·
    refine ⟨3216261766537280420421437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2144174511024853613614291 3216261766537280420421437)
    ·
      refine ⟨1206098162451480157658039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3216261766537280420421437 1206098162451480157658039)
      ·
        refine ⟨1809147243677220236487059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206098162451480157658039 1809147243677220236487059)
        ·
          refine ⟨2713720865515830354730589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809147243677220236487059 2713720865515830354730589)
          ·
            refine ⟨1017645324568436383023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2713720865515830354730589 1017645324568436383023971)
            ·
              refine ⟨1526467986852654574535957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017645324568436383023971 1526467986852654574535957)
              ·
                refine ⟨71553186883718183181373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1526467986852654574535957 71553186883718183181373)
                ·
                  refine ⟨26832445081394318693015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71553186883718183181373 26832445081394318693015)
                  ·
                    rfl

theorem cell21_117576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 3].length) (baseStart_117576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117576 prefixEnd_117576 := by exact prefixLift 117576
  have htrace : WordTrace (prefixWord ++ tailWord_117576) baseStart_117576 baseEnd_117576 := by
    simpa [prefixWord, tailWord_117576, baseEnd_117576] using wordTrace_append hprefix tailTrace_117576
  have hstable : (prefixWord ++ tailWord_117576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117576).length < 2 ^ (prefixWord ++ tailWord_117576).sum := by decide
  have hdescent : baseEnd_117576 < baseStart_117576 := by decide
  rcases family_descends (prefixWord ++ tailWord_117576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117621 : List Nat := [1, 3, 4, 1, 1, 4, 7]
def baseStart_117621 : Nat := 118140960795 + 117621 * 2 ^ 59
def prefixEnd_117621 : Nat := 4983230072969 + 3 ^ 40 * 117621 * 2
def baseEnd_117621 : Nat := 2982523854942693382547

theorem tailTrace_117621 : CollatzResearch.WordTrace tailWord_117621 prefixEnd_117621 2982523854942693382547 := by
  unfold tailWord_117621
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289990306886679912616717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2859993537924453275077811 4289990306886679912616717)
  ·
    refine ⟨1608746365082504967231269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4289990306886679912616717 1608746365082504967231269)
    ·
      refine ⟨301639943452969681355863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1608746365082504967231269 301639943452969681355863)
      ·
        refine ⟨452459915179454522033795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301639943452969681355863 452459915179454522033795)
        ·
          refine ⟨678689872769181783050693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452459915179454522033795 678689872769181783050693)
          ·
            refine ⟨127254351144221584322005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 678689872769181783050693 127254351144221584322005)
            ·
              refine ⟨2982523854942693382547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127254351144221584322005 2982523854942693382547)
              ·
                rfl

theorem cell21_117621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 7].length) (baseStart_117621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117621 prefixEnd_117621 := by exact prefixLift 117621
  have htrace : WordTrace (prefixWord ++ tailWord_117621) baseStart_117621 baseEnd_117621 := by
    simpa [prefixWord, tailWord_117621, baseEnd_117621] using wordTrace_append hprefix tailTrace_117621
  have hstable : (prefixWord ++ tailWord_117621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117621).length < 2 ^ (prefixWord ++ tailWord_117621).sum := by decide
  have hdescent : baseEnd_117621 < baseStart_117621 := by decide
  rcases family_descends (prefixWord ++ tailWord_117621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117711 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_117711 : Nat := 118140960795 + 117711 * 2 ^ 59
def prefixEnd_117711 : Nat := 4983230072969 + 3 ^ 40 * 117711 * 2
def baseEnd_117711 : Nat := 26863253920664083942739

theorem tailTrace_117711 : CollatzResearch.WordTrace tailWord_117711 prefixEnd_117711 26863253920664083942739 := by
  unfold tailWord_117711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293272876560625283392987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2862181917707083522261991 4293272876560625283392987)
  ·
    refine ⟨6439909314840937925089481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4293272876560625283392987 6439909314840937925089481)
    ·
      refine ⟨4829931986130703443817111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6439909314840937925089481 4829931986130703443817111)
      ·
        refine ⟨7244897979196055165725667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829931986130703443817111 7244897979196055165725667)
        ·
          refine ⟨10867346968794082748588501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244897979196055165725667 10867346968794082748588501)
          ·
            refine ⟨254703444581111314420043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10867346968794082748588501 254703444581111314420043)
            ·
              refine ⟨382055166871666971630065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254703444581111314420043 382055166871666971630065)
              ·
                refine ⟨286541375153750228722549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 382055166871666971630065 286541375153750228722549)
                ·
                  refine ⟨26863253920664083942739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286541375153750228722549 26863253920664083942739)
                  ·
                    rfl

theorem cell21_117711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_117711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117711 prefixEnd_117711 := by exact prefixLift 117711
  have htrace : WordTrace (prefixWord ++ tailWord_117711) baseStart_117711 baseEnd_117711 := by
    simpa [prefixWord, tailWord_117711, baseEnd_117711] using wordTrace_append hprefix tailTrace_117711
  have hstable : (prefixWord ++ tailWord_117711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117711).length < 2 ^ (prefixWord ++ tailWord_117711).sum := by decide
  have hdescent : baseEnd_117711 < baseStart_117711 := by decide
  rcases family_descends (prefixWord ++ tailWord_117711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117714 : List Nat := [3, 2, 2, 3, 1, 2, 3, 5]
def baseStart_117714 : Nat := 118140960795 + 117714 * 2 ^ 59
def prefixEnd_117714 : Nat := 4983230072969 + 3 ^ 40 * 117714 * 2
def baseEnd_117714 : Nat := 8954646187178915130911

theorem tailTrace_117714 : CollatzResearch.WordTrace tailWord_117714 prefixEnd_117714 8954646187178915130911 := by
  unfold tailWord_117714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073345573887439198938049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2862254863699837863834797 1073345573887439198938049)
  ·
    refine ⟨805009180415579399203537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1073345573887439198938049 805009180415579399203537)
    ·
      refine ⟨603756885311684549402653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 805009180415579399203537 603756885311684549402653)
      ·
        refine ⟨226408831991881706025995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603756885311684549402653 226408831991881706025995)
        ·
          refine ⟨339613247987822559038993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226408831991881706025995 339613247987822559038993)
          ·
            refine ⟨254709935990866919279245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339613247987822559038993 254709935990866919279245)
            ·
              refine ⟨95516225996575094729717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254709935990866919279245 95516225996575094729717)
              ·
                refine ⟨8954646187178915130911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95516225996575094729717 8954646187178915130911)
                ·
                  rfl

theorem cell21_117714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_117714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117714 prefixEnd_117714 := by exact prefixLift 117714
  have htrace : WordTrace (prefixWord ++ tailWord_117714) baseStart_117714 baseEnd_117714 := by
    simpa [prefixWord, tailWord_117714, baseEnd_117714] using wordTrace_append hprefix tailTrace_117714
  have hstable : (prefixWord ++ tailWord_117714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117714).length < 2 ^ (prefixWord ++ tailWord_117714).sum := by decide
  have hdescent : baseEnd_117714 < baseStart_117714 := by decide
  rcases family_descends (prefixWord ++ tailWord_117714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117911 : List Nat := [1, 1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_117911 : Nat := 118140960795 + 117911 * 2 ^ 59
def prefixEnd_117911 : Nat := 4983230072969 + 3 ^ 40 * 117911 * 2
def baseEnd_117911 : Nat := 26908896645508180608997

theorem tailTrace_117911 : CollatzResearch.WordTrace tailWord_117911 prefixEnd_117911 26908896645508180608997 := by
  unfold tailWord_117911
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300567475836059440673587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2867044983890706293782391 4300567475836059440673587)
  ·
    refine ⟨6450851213754089161010381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300567475836059440673587 6450851213754089161010381)
    ·
      refine ⟨2419069205157783435378893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6450851213754089161010381 2419069205157783435378893)
      ·
        refine ⟨907150951934168788267085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2419069205157783435378893 907150951934168788267085)
        ·
          refine ⟨340181606975313295600157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 907150951934168788267085 340181606975313295600157)
          ·
            refine ⟨127568102615742485850059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340181606975313295600157 127568102615742485850059)
            ·
              refine ⟨191352153923613728775089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127568102615742485850059 191352153923613728775089)
              ·
                refine ⟨143514115442710296581317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191352153923613728775089 143514115442710296581317)
                ·
                  refine ⟨26908896645508180608997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143514115442710296581317 26908896645508180608997)
                  ·
                    rfl

theorem cell21_117911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_117911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117911 prefixEnd_117911 := by exact prefixLift 117911
  have htrace : WordTrace (prefixWord ++ tailWord_117911) baseStart_117911 baseEnd_117911 := by
    simpa [prefixWord, tailWord_117911, baseEnd_117911] using wordTrace_append hprefix tailTrace_117911
  have hstable : (prefixWord ++ tailWord_117911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117911).length < 2 ^ (prefixWord ++ tailWord_117911).sum := by decide
  have hdescent : baseEnd_117911 < baseStart_117911 := by decide
  rcases family_descends (prefixWord ++ tailWord_117911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117970 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_117970 : Nat := 118140960795 + 117970 * 2 ^ 59
def prefixEnd_117970 : Nat := 4983230072969 + 3 ^ 40 * 117970 * 2
def baseEnd_117970 : Nat := 26922361249337189125543

theorem tailTrace_117970 : CollatzResearch.WordTrace tailWord_117970 prefixEnd_117970 26922361249337189125543 := by
  unfold tailWord_117970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1075679845655578129267841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2868479588414875011380909 1075679845655578129267841)
  ·
    refine ⟨806759884241683596950881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1075679845655578129267841 806759884241683596950881)
    ·
      refine ⟨605069913181262697713161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 806759884241683596950881 605069913181262697713161)
      ·
        refine ⟨453802434885947023284871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 605069913181262697713161 453802434885947023284871)
        ·
          refine ⟨680703652328920534927307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 453802434885947023284871 680703652328920534927307)
          ·
            refine ⟨1021055478493380802390961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680703652328920534927307 1021055478493380802390961)
            ·
              refine ⟨765791608870035601793221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1021055478493380802390961 765791608870035601793221)
              ·
                refine ⟨143585926663131675336229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765791608870035601793221 143585926663131675336229)
                ·
                  refine ⟨26922361249337189125543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143585926663131675336229 26922361249337189125543)
                  ·
                    rfl

theorem cell21_117970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_117970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117970 prefixEnd_117970 := by exact prefixLift 117970
  have htrace : WordTrace (prefixWord ++ tailWord_117970) baseStart_117970 baseEnd_117970 := by
    simpa [prefixWord, tailWord_117970, baseEnd_117970] using wordTrace_append hprefix tailTrace_117970
  have hstable : (prefixWord ++ tailWord_117970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117970).length < 2 ^ (prefixWord ++ tailWord_117970).sum := by decide
  have hdescent : baseEnd_117970 < baseStart_117970 := by decide
  rcases family_descends (prefixWord ++ tailWord_117970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117984 : List Nat := [2, 1, 1, 3, 1, 5, 2, 6]
def baseStart_117984 : Nat := 118140960795 + 117984 * 2 ^ 59
def prefixEnd_117984 : Nat := 4983230072969 + 3 ^ 40 * 117984 * 2
def baseEnd_117984 : Nat := 8975185413358758630727

theorem tailTrace_117984 : CollatzResearch.WordTrace tailWord_117984 prefixEnd_117984 8975185413358758630727 := by
  unfold tailWord_117984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2151615002285796454040503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2868820003047728605387337 2151615002285796454040503)
  ·
    refine ⟨3227422503428694681060755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2151615002285796454040503 3227422503428694681060755)
    ·
      refine ⟨4841133755143042021591133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3227422503428694681060755 4841133755143042021591133)
      ·
        refine ⟨1815425158178640758096675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4841133755143042021591133 1815425158178640758096675)
        ·
          refine ⟨2723137737267961137145013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1815425158178640758096675 2723137737267961137145013)
          ·
            refine ⟨255294162868871356607345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2723137737267961137145013 255294162868871356607345)
            ·
              refine ⟨191470622151653517455509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255294162868871356607345 191470622151653517455509)
              ·
                refine ⟨8975185413358758630727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191470622151653517455509 8975185413358758630727)
                ·
                  rfl

theorem cell21_117984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_117984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_117984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_117984 prefixEnd_117984 := by exact prefixLift 117984
  have htrace : WordTrace (prefixWord ++ tailWord_117984) baseStart_117984 baseEnd_117984 := by
    simpa [prefixWord, tailWord_117984, baseEnd_117984] using wordTrace_append hprefix tailTrace_117984
  have hstable : (prefixWord ++ tailWord_117984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117984).length < 2 ^ (prefixWord ++ tailWord_117984).sum := by decide
  have hdescent : baseEnd_117984 < baseStart_117984 := by decide
  rcases family_descends (prefixWord ++ tailWord_117984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118074 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_118074 : Nat := 118140960795 + 118074 * 2 ^ 59
def prefixEnd_118074 : Nat := 4983230072969 + 3 ^ 40 * 118074 * 2
def baseEnd_118074 : Nat := 26946095466256119391997

theorem tailTrace_118074 : CollatzResearch.WordTrace tailWord_118074 prefixEnd_118074 26946095466256119391997 := by
  unfold tailWord_118074
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076628143561384569714319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2871008382830358852571517 1076628143561384569714319)
  ·
    refine ⟨1614942215342076854571479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1076628143561384569714319 1614942215342076854571479)
    ·
      refine ⟨2422413323013115281857219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1614942215342076854571479 2422413323013115281857219)
      ·
        refine ⟨3633619984519672922785829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2422413323013115281857219 3633619984519672922785829)
        ·
          refine ⟨681303747097438673022343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3633619984519672922785829 681303747097438673022343)
          ·
            refine ⟨1021955620646158009533515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 681303747097438673022343 1021955620646158009533515)
            ·
              refine ⟨1532933430969237014300273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1021955620646158009533515 1532933430969237014300273)
              ·
                refine ⟨1149700073226927760725205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1532933430969237014300273 1149700073226927760725205)
                ·
                  refine ⟨26946095466256119391997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1149700073226927760725205 26946095466256119391997)
                  ·
                    rfl

theorem cell21_118074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_118074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118074 prefixEnd_118074 := by exact prefixLift 118074
  have htrace : WordTrace (prefixWord ++ tailWord_118074) baseStart_118074 baseEnd_118074 := by
    simpa [prefixWord, tailWord_118074, baseEnd_118074] using wordTrace_append hprefix tailTrace_118074
  have hstable : (prefixWord ++ tailWord_118074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118074).length < 2 ^ (prefixWord ++ tailWord_118074).sum := by decide
  have hdescent : baseEnd_118074 < baseStart_118074 := by decide
  rcases family_descends (prefixWord ++ tailWord_118074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118077 : List Nat := [1, 4, 1, 5, 1, 1, 8]
def baseStart_118077 : Nat := 118140960795 + 118077 * 2 ^ 59
def prefixEnd_118077 : Nat := 4983230072969 + 3 ^ 40 * 118077 * 2
def baseEnd_118077 : Nat := 2994086678569864537999

theorem tailTrace_118077 : CollatzResearch.WordTrace tailWord_118077 prefixEnd_118077 2994086678569864537999 := by
  unfold tailWord_118077
  simp only [CollatzResearch.WordTrace]
  refine ⟨4306621993234669791216485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2871081328823113194144323 4306621993234669791216485)
  ·
    refine ⟨807491623731500585853091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4306621993234669791216485 807491623731500585853091)
    ·
      refine ⟨1211237435597250878779637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807491623731500585853091 1211237435597250878779637)
      ·
        refine ⟨113553509587242269885591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1211237435597250878779637 113553509587242269885591)
        ·
          refine ⟨170330264380863404828387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113553509587242269885591 170330264380863404828387)
          ·
            refine ⟨255495396571295107242581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170330264380863404828387 255495396571295107242581)
            ·
              refine ⟨2994086678569864537999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 255495396571295107242581 2994086678569864537999)
              ·
                rfl

theorem cell21_118077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 8].length) (baseStart_118077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118077 prefixEnd_118077 := by exact prefixLift 118077
  have htrace : WordTrace (prefixWord ++ tailWord_118077) baseStart_118077 baseEnd_118077 := by
    simpa [prefixWord, tailWord_118077, baseEnd_118077] using wordTrace_append hprefix tailTrace_118077
  have hstable : (prefixWord ++ tailWord_118077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118077).length < 2 ^ (prefixWord ++ tailWord_118077).sum := by decide
  have hdescent : baseEnd_118077 < baseStart_118077 := by decide
  rcases family_descends (prefixWord ++ tailWord_118077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118105 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_118105 : Nat := 118140960795 + 118105 * 2 ^ 59
def prefixEnd_118105 : Nat := 4983230072969 + 3 ^ 40 * 118105 * 2
def baseEnd_118105 : Nat := 26953170088606954375267

theorem tailTrace_118105 : CollatzResearch.WordTrace tailWord_118105 prefixEnd_118105 26953170088606954375267 := by
  unfold tailWord_118105
  simp only [CollatzResearch.WordTrace]
  refine ⟨4307643237133230573235769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2871762158088820382157179 4307643237133230573235769)
  ·
    refine ⟨3230732427849922929926827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4307643237133230573235769 3230732427849922929926827)
    ·
      refine ⟨4846098641774884394890241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3230732427849922929926827 4846098641774884394890241)
      ·
        refine ⟨3634573981331163296167681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4846098641774884394890241 3634573981331163296167681)
        ·
          refine ⟨2725930485998372472125761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3634573981331163296167681 2725930485998372472125761)
          ·
            refine ⟨2044447864498779354094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2725930485998372472125761 2044447864498779354094321)
            ·
              refine ⟨1533335898374084515570741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2044447864498779354094321 1533335898374084515570741)
              ·
                refine ⟨143750240472570423334757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1533335898374084515570741 143750240472570423334757)
                ·
                  refine ⟨26953170088606954375267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143750240472570423334757 26953170088606954375267)
                  ·
                    rfl

theorem cell21_118105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_118105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118105 prefixEnd_118105 := by exact prefixLift 118105
  have htrace : WordTrace (prefixWord ++ tailWord_118105) baseStart_118105 baseEnd_118105 := by
    simpa [prefixWord, tailWord_118105, baseEnd_118105] using wordTrace_append hprefix tailTrace_118105
  have hstable : (prefixWord ++ tailWord_118105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118105).length < 2 ^ (prefixWord ++ tailWord_118105).sum := by decide
  have hdescent : baseEnd_118105 < baseStart_118105 := by decide
  rcases family_descends (prefixWord ++ tailWord_118105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118125 : List Nat := [1, 5, 1, 1, 1, 5, 1, 3, 3]
def baseStart_118125 : Nat := 118140960795 + 118125 * 2 ^ 59
def prefixEnd_118125 : Nat := 4983230072969 + 3 ^ 40 * 118125 * 2
def baseEnd_118125 : Nat := 26957734361091364041893

theorem tailTrace_118125 : CollatzResearch.WordTrace tailWord_118125 prefixEnd_118125 26957734361091364041893 := by
  unfold tailWord_118125
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308372697060773988963829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2872248464707182659309219 4308372697060773988963829)
  ·
    refine ⟨403909940349447561465359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4308372697060773988963829 403909940349447561465359)
    ·
      refine ⟨605864910524171342198039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403909940349447561465359 605864910524171342198039)
      ·
        refine ⟨908797365786257013297059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 605864910524171342198039 908797365786257013297059)
        ·
          refine ⟨1363196048679385519945589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908797365786257013297059 1363196048679385519945589)
          ·
            refine ⟨127799629563692392494899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1363196048679385519945589 127799629563692392494899)
            ·
              refine ⟨191699444345538588742349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127799629563692392494899 191699444345538588742349)
              ·
                refine ⟨71887291629576970778381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191699444345538588742349 71887291629576970778381)
                ·
                  refine ⟨26957734361091364041893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71887291629576970778381 26957734361091364041893)
                  ·
                    rfl

theorem cell21_118125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_118125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118125 prefixEnd_118125 := by exact prefixLift 118125
  have htrace : WordTrace (prefixWord ++ tailWord_118125) baseStart_118125 baseEnd_118125 := by
    simpa [prefixWord, tailWord_118125, baseEnd_118125] using wordTrace_append hprefix tailTrace_118125
  have hstable : (prefixWord ++ tailWord_118125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118125).length < 2 ^ (prefixWord ++ tailWord_118125).sum := by decide
  have hdescent : baseEnd_118125 < baseStart_118125 := by decide
  rcases family_descends (prefixWord ++ tailWord_118125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118142 : List Nat := [4, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_118142 : Nat := 118140960795 + 118142 * 2 ^ 59
def prefixEnd_118142 : Nat := 4983230072969 + 3 ^ 40 * 118142 * 2
def baseEnd_118142 : Nat := 26961613992703112258525

theorem tailTrace_118142 : CollatzResearch.WordTrace tailWord_118142 prefixEnd_118142 26961613992703112258525 := by
  unfold tailWord_118142
  simp only [CollatzResearch.WordTrace]
  refine ⟨538624092249898236541585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2872661825332790594888453 538624092249898236541585)
  ·
    refine ⟨403968069187423677406189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 538624092249898236541585 403968069187423677406189)
    ·
      refine ⟨151488025945283879027321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 403968069187423677406189 151488025945283879027321)
      ·
        refine ⟨113616019458962909270491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151488025945283879027321 113616019458962909270491)
        ·
          refine ⟨170424029188444363905737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113616019458962909270491 170424029188444363905737)
          ·
            refine ⟨127818021891333272929303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170424029188444363905737 127818021891333272929303)
            ·
              refine ⟨191727032836999909393955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127818021891333272929303 191727032836999909393955)
              ·
                refine ⟨287590549255499864090933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191727032836999909393955 287590549255499864090933)
                ·
                  refine ⟨26961613992703112258525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 287590549255499864090933 26961613992703112258525)
                  ·
                    rfl

theorem cell21_118142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_118142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118142 prefixEnd_118142 := by exact prefixLift 118142
  have htrace : WordTrace (prefixWord ++ tailWord_118142) baseStart_118142 baseEnd_118142 := by
    simpa [prefixWord, tailWord_118142, baseEnd_118142] using wordTrace_append hprefix tailTrace_118142
  have hstable : (prefixWord ++ tailWord_118142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118142).length < 2 ^ (prefixWord ++ tailWord_118142).sum := by decide
  have hdescent : baseEnd_118142 < baseStart_118142 := by decide
  rcases family_descends (prefixWord ++ tailWord_118142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118257 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_118257 : Nat := 118140960795 + 118257 * 2 ^ 59
def prefixEnd_118257 : Nat := 4983230072969 + 3 ^ 40 * 118257 * 2
def baseEnd_118257 : Nat := 26987858559488467841623

theorem tailTrace_118257 : CollatzResearch.WordTrace tailWord_118257 prefixEnd_118257 26987858559488467841623 := by
  unfold tailWord_118257
  simp only [CollatzResearch.WordTrace]
  refine ⟨4313187132582560532769025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2875458088388373688512683 4313187132582560532769025)
  ·
    refine ⟨3234890349436920399576769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4313187132582560532769025 3234890349436920399576769)
    ·
      refine ⟨2426167762077690299682577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3234890349436920399576769 2426167762077690299682577)
      ·
        refine ⟨1819625821558267724761933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2426167762077690299682577 1819625821558267724761933)
        ·
          refine ⟨682359683084350396785725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1819625821558267724761933 682359683084350396785725)
          ·
            refine ⟨255884881156631398794647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 682359683084350396785725 255884881156631398794647)
            ·
              refine ⟨383827321734947098191971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255884881156631398794647 383827321734947098191971)
              ·
                refine ⟨575740982602420647287957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383827321734947098191971 575740982602420647287957)
                ·
                  refine ⟨26987858559488467841623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 575740982602420647287957 26987858559488467841623)
                  ·
                    rfl

theorem cell21_118257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_118257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118257 prefixEnd_118257 := by exact prefixLift 118257
  have htrace : WordTrace (prefixWord ++ tailWord_118257) baseStart_118257 baseEnd_118257 := by
    simpa [prefixWord, tailWord_118257, baseEnd_118257] using wordTrace_append hprefix tailTrace_118257
  have hstable : (prefixWord ++ tailWord_118257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118257).length < 2 ^ (prefixWord ++ tailWord_118257).sum := by decide
  have hdescent : baseEnd_118257 < baseStart_118257 := by decide
  rcases family_descends (prefixWord ++ tailWord_118257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118381 : List Nat := [1, 5, 1, 1, 4, 2, 1, 6]
def baseStart_118381 : Nat := 118140960795 + 118381 * 2 ^ 59
def prefixEnd_118381 : Nat := 4983230072969 + 3 ^ 40 * 118381 * 2
def baseEnd_118381 : Nat := 9005385682963935924901

theorem tailTrace_118381 : CollatzResearch.WordTrace tailWord_118381 prefixEnd_118381 9005385682963935924901 := by
  unfold tailWord_118381
  simp only [CollatzResearch.WordTrace]
  refine ⟨4317709784133329710282997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878473189422219806855331 4317709784133329710282997)
  ·
    refine ⟨404785292262499660339031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4317709784133329710282997 404785292262499660339031)
    ·
      refine ⟨607177938393749490508547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404785292262499660339031 607177938393749490508547)
      ·
        refine ⟨910766907590624235762821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 607177938393749490508547 910766907590624235762821)
        ·
          refine ⟨170768795173242044205529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 910766907590624235762821 170768795173242044205529)
          ·
            refine ⟨128076596379931533154147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170768795173242044205529 128076596379931533154147)
            ·
              refine ⟨192114894569897299731221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128076596379931533154147 192114894569897299731221)
              ·
                refine ⟨9005385682963935924901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192114894569897299731221 9005385682963935924901)
                ·
                  rfl

theorem cell21_118381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_118381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118381 prefixEnd_118381 := by exact prefixLift 118381
  have htrace : WordTrace (prefixWord ++ tailWord_118381) baseStart_118381 baseEnd_118381 := by
    simpa [prefixWord, tailWord_118381, baseEnd_118381] using wordTrace_append hprefix tailTrace_118381
  have hstable : (prefixWord ++ tailWord_118381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118381).length < 2 ^ (prefixWord ++ tailWord_118381).sum := by decide
  have hdescent : baseEnd_118381 < baseStart_118381 := by decide
  rcases family_descends (prefixWord ++ tailWord_118381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118423 : List Nat := [1, 1, 3, 3, 2, 3, 8]
def baseStart_118423 : Nat := 118140960795 + 118423 * 2 ^ 59
def prefixEnd_118423 : Nat := 4983230072969 + 3 ^ 40 * 118423 * 2
def baseEnd_118423 : Nat := 3002860224567674230513

theorem tailTrace_118423 : CollatzResearch.WordTrace tailWord_118423 prefixEnd_118423 3002860224567674230513 := by
  unfold tailWord_118423
  simp only [CollatzResearch.WordTrace]
  refine ⟨4319241649981170883311923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2879494433320780588874615 4319241649981170883311923)
  ·
    refine ⟨6478862474971756324967885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4319241649981170883311923 6478862474971756324967885)
    ·
      refine ⟨2429573428114408621862957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6478862474971756324967885 2429573428114408621862957)
      ·
        refine ⟨911090035542903233198609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2429573428114408621862957 911090035542903233198609)
        ·
          refine ⟨683317526657177424898957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 911090035542903233198609 683317526657177424898957)
          ·
            refine ⟨256244072496441534337109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683317526657177424898957 256244072496441534337109)
            ·
              refine ⟨3002860224567674230513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 256244072496441534337109 3002860224567674230513)
              ·
                rfl

theorem cell21_118423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_118423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118423 prefixEnd_118423 := by exact prefixLift 118423
  have htrace : WordTrace (prefixWord ++ tailWord_118423) baseStart_118423 baseEnd_118423 := by
    simpa [prefixWord, tailWord_118423, baseEnd_118423] using wordTrace_append hprefix tailTrace_118423
  have hstable : (prefixWord ++ tailWord_118423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118423).length < 2 ^ (prefixWord ++ tailWord_118423).sum := by decide
  have hdescent : baseEnd_118423 < baseStart_118423 := by decide
  rcases family_descends (prefixWord ++ tailWord_118423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118488 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_118488 : Nat := 118140960795 + 118488 * 2 ^ 59
def prefixEnd_118488 : Nat := 4983230072969 + 3 ^ 40 * 118488 * 2
def baseEnd_118488 : Nat := 27040575906683399491151

theorem tailTrace_118488 : CollatzResearch.WordTrace tailWord_118488 prefixEnd_118488 27040575906683399491151 := by
  unfold tailWord_118488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160806197372843492214059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2881074929830457989618745 2160806197372843492214059)
  ·
    refine ⟨3241209296059265238321089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2160806197372843492214059 3241209296059265238321089)
    ·
      refine ⟨2430906972044448928740817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3241209296059265238321089 2430906972044448928740817)
      ·
        refine ⟨1823180229033336696555613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2430906972044448928740817 1823180229033336696555613)
        ·
          refine ⟨683692585887501261208355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1823180229033336696555613 683692585887501261208355)
          ·
            refine ⟨1025538878831251891812533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 683692585887501261208355 1025538878831251891812533)
            ·
              refine ⟨96144269890429864857425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1025538878831251891812533 96144269890429864857425)
              ·
                refine ⟨72108202417822398643069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96144269890429864857425 72108202417822398643069)
                ·
                  refine ⟨27040575906683399491151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72108202417822398643069 27040575906683399491151)
                  ·
                    rfl

theorem cell21_118488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_118488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118488 prefixEnd_118488 := by exact prefixLift 118488
  have htrace : WordTrace (prefixWord ++ tailWord_118488) baseStart_118488 baseEnd_118488 := by
    simpa [prefixWord, tailWord_118488, baseEnd_118488] using wordTrace_append hprefix tailTrace_118488
  have hstable : (prefixWord ++ tailWord_118488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118488).length < 2 ^ (prefixWord ++ tailWord_118488).sum := by decide
  have hdescent : baseEnd_118488 < baseStart_118488 := by decide
  rcases family_descends (prefixWord ++ tailWord_118488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118561 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_118561 : Nat := 118140960795 + 118561 * 2 ^ 59
def prefixEnd_118561 : Nat := 4983230072969 + 3 ^ 40 * 118561 * 2
def baseEnd_118561 : Nat := 27057235501251494774335

theorem tailTrace_118561 : CollatzResearch.WordTrace tailWord_118561 prefixEnd_118561 27057235501251494774335 := by
  unfold tailWord_118561
  simp only [CollatzResearch.WordTrace]
  refine ⟨4324274923481220451835537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2882849948987480301223691 4324274923481220451835537)
  ·
    refine ⟨3243206192610915338876653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4324274923481220451835537 3243206192610915338876653)
    ·
      refine ⟨1216202322229093252078745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3243206192610915338876653 1216202322229093252078745)
      ·
        refine ⟨912151741671819939059059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1216202322229093252078745 912151741671819939059059)
        ·
          refine ⟨1368227612507729908588589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 912151741671819939059059 1368227612507729908588589)
          ·
            refine ⟨513085354690398715720721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1368227612507729908588589 513085354690398715720721)
            ·
              refine ⟨384814016017799036790541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513085354690398715720721 384814016017799036790541)
              ·
                refine ⟨144305256006674638796453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 384814016017799036790541 144305256006674638796453)
                ·
                  refine ⟨27057235501251494774335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144305256006674638796453 27057235501251494774335)
                  ·
                    rfl

theorem cell21_118561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_118561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118561 prefixEnd_118561 := by exact prefixLift 118561
  have htrace : WordTrace (prefixWord ++ tailWord_118561) baseStart_118561 baseEnd_118561 := by
    simpa [prefixWord, tailWord_118561, baseEnd_118561] using wordTrace_append hprefix tailTrace_118561
  have hstable : (prefixWord ++ tailWord_118561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118561).length < 2 ^ (prefixWord ++ tailWord_118561).sum := by decide
  have hdescent : baseEnd_118561 < baseStart_118561 := by decide
  rcases family_descends (prefixWord ++ tailWord_118561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118654 : List Nat := [4, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_118654 : Nat := 118140960795 + 118654 * 2 ^ 59
def prefixEnd_118654 : Nat := 4983230072969 + 3 ^ 40 * 118654 * 2
def baseEnd_118654 : Nat := 27078459368303999724145

theorem tailTrace_118654 : CollatzResearch.WordTrace tailWord_118654 prefixEnd_118654 27078459368303999724145 := by
  unfold tailWord_118654
  simp only [CollatzResearch.WordTrace]
  refine ⟨540958364018037166871377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2885111274762864889980677 540958364018037166871377)
  ·
    refine ⟨405718773013527875153533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 540958364018037166871377 405718773013527875153533)
    ·
      refine ⟨152144539880072953182575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405718773013527875153533 152144539880072953182575)
      ·
        refine ⟨228216809820109429773863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152144539880072953182575 228216809820109429773863)
        ·
          refine ⟨342325214730164144660795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228216809820109429773863 342325214730164144660795)
          ·
            refine ⟨513487822095246216991193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342325214730164144660795 513487822095246216991193)
            ·
              refine ⟨385115866571434662743395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 513487822095246216991193 385115866571434662743395)
              ·
                refine ⟨577673799857151994115093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385115866571434662743395 577673799857151994115093)
                ·
                  refine ⟨27078459368303999724145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 577673799857151994115093 27078459368303999724145)
                  ·
                    rfl

theorem cell21_118654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_118654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118654 prefixEnd_118654 := by exact prefixLift 118654
  have htrace : WordTrace (prefixWord ++ tailWord_118654) baseStart_118654 baseEnd_118654 := by
    simpa [prefixWord, tailWord_118654, baseEnd_118654] using wordTrace_append hprefix tailTrace_118654
  have hstable : (prefixWord ++ tailWord_118654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118654).length < 2 ^ (prefixWord ++ tailWord_118654).sum := by decide
  have hdescent : baseEnd_118654 < baseStart_118654 := by decide
  rcases family_descends (prefixWord ++ tailWord_118654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118657 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 5]
def baseStart_118657 : Nat := 118140960795 + 118657 * 2 ^ 59
def prefixEnd_118657 : Nat := 4983230072969 + 3 ^ 40 * 118657 * 2
def baseEnd_118657 : Nat := 27079144009176661174139

theorem tailTrace_118657 : CollatzResearch.WordTrace tailWord_118657 prefixEnd_118657 27079144009176661174139 := by
  unfold tailWord_118657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4327776331133428847330225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2885184220755619231553483 4327776331133428847330225)
  ·
    refine ⟨3245832248350071635497669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4327776331133428847330225 3245832248350071635497669)
    ·
      refine ⟨608593546565638431655813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3245832248350071635497669 608593546565638431655813)
      ·
        refine ⟨114111289981057205935465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 608593546565638431655813 114111289981057205935465)
        ·
          refine ⟨85583467485792904451599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114111289981057205935465 85583467485792904451599)
          ·
            refine ⟨128375201228689356677399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85583467485792904451599 128375201228689356677399)
            ·
              refine ⟨192562801843034035016099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128375201228689356677399 192562801843034035016099)
              ·
                refine ⟨288844202764551052524149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192562801843034035016099 288844202764551052524149)
                ·
                  refine ⟨27079144009176661174139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 288844202764551052524149 27079144009176661174139)
                  ·
                    rfl

theorem cell21_118657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 5].length) (baseStart_118657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118657 prefixEnd_118657 := by exact prefixLift 118657
  have htrace : WordTrace (prefixWord ++ tailWord_118657) baseStart_118657 baseEnd_118657 := by
    simpa [prefixWord, tailWord_118657, baseEnd_118657] using wordTrace_append hprefix tailTrace_118657
  have hstable : (prefixWord ++ tailWord_118657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118657).length < 2 ^ (prefixWord ++ tailWord_118657).sum := by decide
  have hdescent : baseEnd_118657 < baseStart_118657 := by decide
  rcases family_descends (prefixWord ++ tailWord_118657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118702 : List Nat := [4, 1, 5, 1, 2, 8]
def baseStart_118702 : Nat := 118140960795 + 118702 * 2 ^ 59
def prefixEnd_118702 : Nat := 4983230072969 + 3 ^ 40 * 118702 * 2
def baseEnd_118702 : Nat := 1003311615639503071261

theorem tailTrace_118702 : CollatzResearch.WordTrace tailWord_118702 prefixEnd_118702 1003311615639503071261 := by
  unfold tailWord_118702
  simp only [CollatzResearch.WordTrace]
  refine ⟨541177201996300191589795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2886278410646934355145573 541177201996300191589795)
  ·
    refine ⟨811765802994450287384693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 541177201996300191589795 811765802994450287384693)
    ·
      refine ⟨76103044030729714442315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 811765802994450287384693 76103044030729714442315)
      ·
        refine ⟨114154566046094571663473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76103044030729714442315 114154566046094571663473)
        ·
          refine ⟨85615924534570928747605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114154566046094571663473 85615924534570928747605)
          ·
            refine ⟨1003311615639503071261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 85615924534570928747605 1003311615639503071261)
            ·
              rfl

theorem cell21_118702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 8].length) (baseStart_118702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118702 prefixEnd_118702 := by exact prefixLift 118702
  have htrace : WordTrace (prefixWord ++ tailWord_118702) baseStart_118702 baseEnd_118702 := by
    simpa [prefixWord, tailWord_118702, baseEnd_118702] using wordTrace_append hprefix tailTrace_118702
  have hstable : (prefixWord ++ tailWord_118702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118702).length < 2 ^ (prefixWord ++ tailWord_118702).sum := by decide
  have hdescent : baseEnd_118702 < baseStart_118702 := by decide
  rcases family_descends (prefixWord ++ tailWord_118702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118713 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_118713 : Nat := 118140960795 + 118713 * 2 ^ 59
def prefixEnd_118713 : Nat := 4983230072969 + 3 ^ 40 * 118713 * 2
def baseEnd_118713 : Nat := 27091923972133008240691

theorem tailTrace_118713 : CollatzResearch.WordTrace tailWord_118713 prefixEnd_118713 27091923972133008240691 := by
  unfold tailWord_118713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329818818930550411368793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2886545879287033607579195 4329818818930550411368793)
  ·
    refine ⟨3247364114197912808526595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4329818818930550411368793 3247364114197912808526595)
    ·
      refine ⟨4871046171296869212789893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3247364114197912808526595 4871046171296869212789893)
      ·
        refine ⟨913321157118162977398105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4871046171296869212789893 913321157118162977398105)
        ·
          refine ⟨684990867838622233048579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913321157118162977398105 684990867838622233048579)
          ·
            refine ⟨1027486301757933349572869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 684990867838622233048579 1027486301757933349572869)
            ·
              refine ⟨192653681579612503044913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1027486301757933349572869 192653681579612503044913)
              ·
                refine ⟨144490261184709377283685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192653681579612503044913 144490261184709377283685)
                ·
                  refine ⟨27091923972133008240691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144490261184709377283685 27091923972133008240691)
                  ·
                    rfl

theorem cell21_118713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_118713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118713 prefixEnd_118713 := by exact prefixLift 118713
  have htrace : WordTrace (prefixWord ++ tailWord_118713) baseStart_118713 baseEnd_118713 := by
    simpa [prefixWord, tailWord_118713, baseEnd_118713] using wordTrace_append hprefix tailTrace_118713
  have hstable : (prefixWord ++ tailWord_118713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118713).length < 2 ^ (prefixWord ++ tailWord_118713).sum := by decide
  have hdescent : baseEnd_118713 < baseStart_118713 := by decide
  rcases family_descends (prefixWord ++ tailWord_118713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118803 : List Nat := [1, 1, 1, 2, 1, 4, 6, 5]
def baseStart_118803 : Nat := 118140960795 + 118803 * 2 ^ 59
def prefixEnd_118803 : Nat := 4983230072969 + 3 ^ 40 * 118803 * 2
def baseEnd_118803 : Nat := 9037487732770950580169

theorem tailTrace_118803 : CollatzResearch.WordTrace tailWord_118803 prefixEnd_118803 9037487732770950580169 := by
  unfold tailWord_118803
  simp only [CollatzResearch.WordTrace]
  refine ⟨4333101388604495782145063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2888734259069663854763375 4333101388604495782145063)
  ·
    refine ⟨6499652082906743673217595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4333101388604495782145063 6499652082906743673217595)
    ·
      refine ⟨9749478124360115509826393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6499652082906743673217595 9749478124360115509826393)
      ·
        refine ⟨7312108593270086632369795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9749478124360115509826393 7312108593270086632369795)
        ·
          refine ⟨10968162889905129948554693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7312108593270086632369795 10968162889905129948554693)
          ·
            refine ⟨2056530541857211865354005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10968162889905129948554693 2056530541857211865354005)
            ·
              refine ⟨96399869149556806188469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2056530541857211865354005 96399869149556806188469)
              ·
                refine ⟨9037487732770950580169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96399869149556806188469 9037487732770950580169)
                ·
                  rfl

theorem cell21_118803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 6, 5].length) (baseStart_118803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118803 prefixEnd_118803 := by exact prefixLift 118803
  have htrace : WordTrace (prefixWord ++ tailWord_118803) baseStart_118803 baseEnd_118803 := by
    simpa [prefixWord, tailWord_118803, baseEnd_118803] using wordTrace_append hprefix tailTrace_118803
  have hstable : (prefixWord ++ tailWord_118803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118803).length < 2 ^ (prefixWord ++ tailWord_118803).sum := by decide
  have hdescent : baseEnd_118803 < baseStart_118803 := by decide
  rcases family_descends (prefixWord ++ tailWord_118803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118820 : List Nat := [2, 3, 1, 4, 2, 2, 7]
def baseStart_118820 : Nat := 118140960795 + 118820 * 2 ^ 59
def prefixEnd_118820 : Nat := 4983230072969 + 3 ^ 40 * 118820 * 2
def baseEnd_118820 : Nat := 3012926981102733328571

theorem tailTrace_118820 : CollatzResearch.WordTrace tailWord_118820 prefixEnd_118820 3012926981102733328571 := by
  unfold tailWord_118820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2166860714771453842756957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2889147619695271790342609 2166860714771453842756957)
  ·
    refine ⟨812572768039295191033859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2166860714771453842756957 812572768039295191033859)
    ·
      refine ⟨1218859152058942786550789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812572768039295191033859 1218859152058942786550789)
      ·
        refine ⟨228536091011051772478273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1218859152058942786550789 228536091011051772478273)
        ·
          refine ⟨171402068258288829358705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228536091011051772478273 171402068258288829358705)
          ·
            refine ⟨128551551193716622019029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171402068258288829358705 128551551193716622019029)
            ·
              refine ⟨3012926981102733328571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128551551193716622019029 3012926981102733328571)
              ·
                rfl

theorem cell21_118820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 7].length) (baseStart_118820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118820 prefixEnd_118820 := by exact prefixLift 118820
  have htrace : WordTrace (prefixWord ++ tailWord_118820) baseStart_118820 baseEnd_118820 := by
    simpa [prefixWord, tailWord_118820, baseEnd_118820] using wordTrace_append hprefix tailTrace_118820
  have hstable : (prefixWord ++ tailWord_118820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118820).length < 2 ^ (prefixWord ++ tailWord_118820).sum := by decide
  have hdescent : baseEnd_118820 < baseStart_118820 := by decide
  rcases family_descends (prefixWord ++ tailWord_118820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118834 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_118834 : Nat := 118140960795 + 118834 * 2 ^ 59
def prefixEnd_118834 : Nat := 4983230072969 + 3 ^ 40 * 118834 * 2
def baseEnd_118834 : Nat := 27119537820663686723777

theorem tailTrace_118834 : CollatzResearch.WordTrace tailWord_118834 prefixEnd_118834 27119537820663686723777 := by
  unfold tailWord_118834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1083558012873047019130889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2889488034328125384349037 1083558012873047019130889)
  ·
    refine ⟨812668509654785264348167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1083558012873047019130889 812668509654785264348167)
    ·
      refine ⟨1219002764482177896522251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 812668509654785264348167 1219002764482177896522251)
      ·
        refine ⟨1828504146723266844783377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1219002764482177896522251 1828504146723266844783377)
        ·
          refine ⟨1371378110042450133587533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1828504146723266844783377 1371378110042450133587533)
          ·
            refine ⟨514266791265918800095325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1371378110042450133587533 514266791265918800095325)
            ·
              refine ⟨192850046724719550035747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514266791265918800095325 192850046724719550035747)
              ·
                refine ⟨289275070087079325053621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192850046724719550035747 289275070087079325053621)
                ·
                  refine ⟨27119537820663686723777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289275070087079325053621 27119537820663686723777)
                  ·
                    rfl

theorem cell21_118834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_118834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118834 prefixEnd_118834 := by exact prefixLift 118834
  have htrace : WordTrace (prefixWord ++ tailWord_118834) baseStart_118834 baseEnd_118834 := by
    simpa [prefixWord, tailWord_118834, baseEnd_118834] using wordTrace_append hprefix tailTrace_118834
  have hstable : (prefixWord ++ tailWord_118834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118834).length < 2 ^ (prefixWord ++ tailWord_118834).sum := by decide
  have hdescent : baseEnd_118834 < baseStart_118834 := by decide
  rcases family_descends (prefixWord ++ tailWord_118834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118907 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_118907 : Nat := 118140960795 + 118907 * 2 ^ 59
def prefixEnd_118907 : Nat := 4983230072969 + 3 ^ 40 * 118907 * 2
def baseEnd_118907 : Nat := 27136197415231782006961

theorem tailTrace_118907 : CollatzResearch.WordTrace tailWord_118907 prefixEnd_118907 27136197415231782006961 := by
  unfold tailWord_118907
  simp only [CollatzResearch.WordTrace]
  refine ⟨4336894580227721543930975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2891263053485147695953983 4336894580227721543930975)
  ·
    refine ⟨6505341870341582315896463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4336894580227721543930975 6505341870341582315896463)
    ·
      refine ⟨9758012805512373473844695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6505341870341582315896463 9758012805512373473844695)
      ·
        refine ⟨14637019208268560210767043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9758012805512373473844695 14637019208268560210767043)
        ·
          refine ⟨21955528812402840316150565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14637019208268560210767043 21955528812402840316150565)
          ·
            refine ⟨4116661652325532559278231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21955528812402840316150565 4116661652325532559278231)
            ·
              refine ⟨6174992478488298838917347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4116661652325532559278231 6174992478488298838917347)
              ·
                refine ⟨9262488717732448258376021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6174992478488298838917347 9262488717732448258376021)
                ·
                  refine ⟨27136197415231782006961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9262488717732448258376021 27136197415231782006961)
                  ·
                    rfl

theorem cell21_118907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_118907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118907 prefixEnd_118907 := by exact prefixLift 118907
  have htrace : WordTrace (prefixWord ++ tailWord_118907) baseStart_118907 baseEnd_118907 := by
    simpa [prefixWord, tailWord_118907, baseEnd_118907] using wordTrace_append hprefix tailTrace_118907
  have hstable : (prefixWord ++ tailWord_118907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118907).length < 2 ^ (prefixWord ++ tailWord_118907).sum := by decide
  have hdescent : baseEnd_118907 < baseStart_118907 := by decide
  rcases family_descends (prefixWord ++ tailWord_118907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118941 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_118941 : Nat := 118140960795 + 118941 * 2 ^ 59
def prefixEnd_118941 : Nat := 4983230072969 + 3 ^ 40 * 118941 * 2
def baseEnd_118941 : Nat := 27143956678455278440225

theorem tailTrace_118941 : CollatzResearch.WordTrace tailWord_118941 prefixEnd_118941 27143956678455278440225 := by
  unfold tailWord_118941
  simp only [CollatzResearch.WordTrace]
  refine ⟨4338134662104545350668677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2892089774736363567112451 4338134662104545350668677)
  ·
    refine ⟨813400249144602253250377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4338134662104545350668677 813400249144602253250377)
    ·
      refine ⟨610050186858451689937783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813400249144602253250377 610050186858451689937783)
      ·
        refine ⟨915075280287677534906675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 610050186858451689937783 915075280287677534906675)
        ·
          refine ⟨1372612920431516302360013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915075280287677534906675 1372612920431516302360013)
          ·
            refine ⟨514729845161818613385005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1372612920431516302360013 514729845161818613385005)
            ·
              refine ⟨193023691935681980019377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514729845161818613385005 193023691935681980019377)
              ·
                refine ⟨144767768951761485014533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193023691935681980019377 144767768951761485014533)
                ·
                  refine ⟨27143956678455278440225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144767768951761485014533 27143956678455278440225)
                  ·
                    rfl

theorem cell21_118941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_118941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118941 prefixEnd_118941 := by exact prefixLift 118941
  have htrace : WordTrace (prefixWord ++ tailWord_118941) baseStart_118941 baseEnd_118941 := by
    simpa [prefixWord, tailWord_118941, baseEnd_118941] using wordTrace_append hprefix tailTrace_118941
  have hstable : (prefixWord ++ tailWord_118941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118941).length < 2 ^ (prefixWord ++ tailWord_118941).sum := by decide
  have hdescent : baseEnd_118941 < baseStart_118941 := by decide
  rcases family_descends (prefixWord ++ tailWord_118941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118964 : List Nat := [2, 5, 3, 1, 2, 1, 2, 5]
def baseStart_118964 : Nat := 118140960795 + 118964 * 2 ^ 59
def prefixEnd_118964 : Nat := 4983230072969 + 3 ^ 40 * 118964 * 2
def baseEnd_118964 : Nat := 9049735197270783185615

theorem tailTrace_118964 : CollatzResearch.WordTrace tailWord_118964 prefixEnd_118964 9049735197270783185615 := by
  unfold tailWord_118964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2169486770510610139377973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2892649027347480185837297 2169486770510610139377973)
  ·
    refine ⟨203389384735369700566685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2169486770510610139377973 203389384735369700566685)
    ·
      refine ⟨76271019275763637712507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203389384735369700566685 76271019275763637712507)
      ·
        refine ⟨114406528913645456568761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76271019275763637712507 114406528913645456568761)
        ·
          refine ⟨85804896685234092426571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114406528913645456568761 85804896685234092426571)
          ·
            refine ⟨128707345027851138639857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85804896685234092426571 128707345027851138639857)
            ·
              refine ⟨96530508770888353979893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128707345027851138639857 96530508770888353979893)
              ·
                refine ⟨9049735197270783185615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96530508770888353979893 9049735197270783185615)
                ·
                  rfl

theorem cell21_118964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 5].length) (baseStart_118964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118964 prefixEnd_118964 := by exact prefixLift 118964
  have htrace : WordTrace (prefixWord ++ tailWord_118964) baseStart_118964 baseEnd_118964 := by
    simpa [prefixWord, tailWord_118964, baseEnd_118964] using wordTrace_append hprefix tailTrace_118964
  have hstable : (prefixWord ++ tailWord_118964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118964).length < 2 ^ (prefixWord ++ tailWord_118964).sum := by decide
  have hdescent : baseEnd_118964 < baseStart_118964 := by decide
  rcases family_descends (prefixWord ++ tailWord_118964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118969 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_118969 : Nat := 118140960795 + 118969 * 2 ^ 59
def prefixEnd_118969 : Nat := 4983230072969 + 3 ^ 40 * 118969 * 2
def baseEnd_118969 : Nat := 27150346659933451973501

theorem tailTrace_118969 : CollatzResearch.WordTrace tailWord_118969 prefixEnd_118969 27150346659933451973501 := by
  unfold tailWord_118969
  simp only [CollatzResearch.WordTrace]
  refine ⟨4339155906003106132687961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2892770604002070755125307 4339155906003106132687961)
  ·
    refine ⟨3254366929502329599515971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4339155906003106132687961 3254366929502329599515971)
    ·
      refine ⟨4881550394253494399273957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3254366929502329599515971 4881550394253494399273957)
      ·
        refine ⟨915290698922530199863867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4881550394253494399273957 915290698922530199863867)
        ·
          refine ⟨1372936048383795299795801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 915290698922530199863867 1372936048383795299795801)
          ·
            refine ⟨1029702036287846474846851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1372936048383795299795801 1029702036287846474846851)
            ·
              refine ⟨1544553054431769712270277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1029702036287846474846851 1544553054431769712270277)
              ·
                refine ⟨289603697705956821050677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1544553054431769712270277 289603697705956821050677)
                ·
                  refine ⟨27150346659933451973501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289603697705956821050677 27150346659933451973501)
                  ·
                    rfl

theorem cell21_118969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_118969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118969 prefixEnd_118969 := by exact prefixLift 118969
  have htrace : WordTrace (prefixWord ++ tailWord_118969) baseStart_118969 baseEnd_118969 := by
    simpa [prefixWord, tailWord_118969, baseEnd_118969] using wordTrace_append hprefix tailTrace_118969
  have hstable : (prefixWord ++ tailWord_118969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118969).length < 2 ^ (prefixWord ++ tailWord_118969).sum := by decide
  have hdescent : baseEnd_118969 < baseStart_118969 := by decide
  rcases family_descends (prefixWord ++ tailWord_118969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118978 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_118978 : Nat := 118140960795 + 118978 * 2 ^ 59
def prefixEnd_118978 : Nat := 4983230072969 + 3 ^ 40 * 118978 * 2
def baseEnd_118978 : Nat := 27152400582551436323483

theorem tailTrace_118978 : CollatzResearch.WordTrace tailWord_118978 prefixEnd_118978 27152400582551436323483 := by
  unfold tailWord_118978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1084871040742625167441397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2892989441980333779843725 1084871040742625167441397)
  ·
    refine ⟨101706660069621109447631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1084871040742625167441397 101706660069621109447631)
    ·
      refine ⟨152559990104431664171447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101706660069621109447631 152559990104431664171447)
      ·
        refine ⟨228839985156647496257171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152559990104431664171447 228839985156647496257171)
        ·
          refine ⟨343259977734971244385757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228839985156647496257171 343259977734971244385757)
          ·
            refine ⟨128722491650614216644659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 343259977734971244385757 128722491650614216644659)
            ·
              refine ⟨193083737475921324966989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128722491650614216644659 193083737475921324966989)
              ·
                refine ⟨72406401553470496862621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 193083737475921324966989 72406401553470496862621)
                ·
                  refine ⟨27152400582551436323483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72406401553470496862621 27152400582551436323483)
                  ·
                    rfl

theorem cell21_118978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_118978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_118978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_118978 prefixEnd_118978 := by exact prefixLift 118978
  have htrace : WordTrace (prefixWord ++ tailWord_118978) baseStart_118978 baseEnd_118978 := by
    simpa [prefixWord, tailWord_118978, baseEnd_118978] using wordTrace_append hprefix tailTrace_118978
  have hstable : (prefixWord ++ tailWord_118978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118978).length < 2 ^ (prefixWord ++ tailWord_118978).sum := by decide
  have hdescent : baseEnd_118978 < baseStart_118978 := by decide
  rcases family_descends (prefixWord ++ tailWord_118978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119000 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_119000 : Nat := 118140960795 + 119000 * 2 ^ 59
def prefixEnd_119000 : Nat := 4983230072969 + 3 ^ 40 * 119000 * 2
def baseEnd_119000 : Nat := 27157421282284286956771

theorem tailTrace_119000 : CollatzResearch.WordTrace tailWord_119000 prefixEnd_119000 27157421282284286956771 := by
  unfold tailWord_119000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2170143284445399213533227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2893524379260532284710969 2170143284445399213533227)
  ·
    refine ⟨3255214926668098820299841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2170143284445399213533227 3255214926668098820299841)
    ·
      refine ⟨2441411195001074115224881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3255214926668098820299841 2441411195001074115224881)
      ·
        refine ⟨1831058396250805586418661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2441411195001074115224881 1831058396250805586418661)
        ·
          refine ⟨343323449297026047453499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1831058396250805586418661 343323449297026047453499)
          ·
            refine ⟨514985173945539071180249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343323449297026047453499 514985173945539071180249)
            ·
              refine ⟨386238880459154303385187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514985173945539071180249 386238880459154303385187)
              ·
                refine ⟨579358320688731455077781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 386238880459154303385187 579358320688731455077781)
                ·
                  refine ⟨27157421282284286956771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 579358320688731455077781 27157421282284286956771)
                  ·
                    rfl

theorem cell21_119000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_119000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119000 prefixEnd_119000 := by exact prefixLift 119000
  have htrace : WordTrace (prefixWord ++ tailWord_119000) baseStart_119000 baseEnd_119000 := by
    simpa [prefixWord, tailWord_119000, baseEnd_119000] using wordTrace_append hprefix tailTrace_119000
  have hstable : (prefixWord ++ tailWord_119000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119000).length < 2 ^ (prefixWord ++ tailWord_119000).sum := by decide
  have hdescent : baseEnd_119000 < baseStart_119000 := by decide
  rcases family_descends (prefixWord ++ tailWord_119000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119059 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_119059 : Nat := 118140960795 + 119059 * 2 ^ 59
def prefixEnd_119059 : Nat := 4983230072969 + 3 ^ 40 * 119059 * 2
def baseEnd_119059 : Nat := 27170885886113295473317

theorem tailTrace_119059 : CollatzResearch.WordTrace tailWord_119059 prefixEnd_119059 27170885886113295473317 := by
  unfold tailWord_119059
  simp only [CollatzResearch.WordTrace]
  refine ⟨4342438475677051503464231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2894958983784701002309487 4342438475677051503464231)
  ·
    refine ⟨6513657713515577255196347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4342438475677051503464231 6513657713515577255196347)
    ·
      refine ⟨9770486570273365882794521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6513657713515577255196347 9770486570273365882794521)
      ·
        refine ⟨7327864927705024412095891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9770486570273365882794521 7327864927705024412095891)
        ·
          refine ⟨10991797391557536618143837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7327864927705024412095891 10991797391557536618143837)
          ·
            refine ⟨4121924021834076231803939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10991797391557536618143837 4121924021834076231803939)
            ·
              refine ⟨6182886032751114347705909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4121924021834076231803939 6182886032751114347705909)
              ·
                refine ⟨579645565570416970097429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6182886032751114347705909 579645565570416970097429)
                ·
                  refine ⟨27170885886113295473317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 579645565570416970097429 27170885886113295473317)
                  ·
                    rfl

theorem cell21_119059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_119059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119059 prefixEnd_119059 := by exact prefixLift 119059
  have htrace : WordTrace (prefixWord ++ tailWord_119059) baseStart_119059 baseEnd_119059 := by
    simpa [prefixWord, tailWord_119059, baseEnd_119059] using wordTrace_append hprefix tailTrace_119059
  have hstable : (prefixWord ++ tailWord_119059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119059).length < 2 ^ (prefixWord ++ tailWord_119059).sum := by decide
  have hdescent : baseEnd_119059 < baseStart_119059 := by decide
  rcases family_descends (prefixWord ++ tailWord_119059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119121 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_119121 : Nat := 118140960795 + 119121 * 2 ^ 59
def prefixEnd_119121 : Nat := 4983230072969 + 3 ^ 40 * 119121 * 2
def baseEnd_119121 : Nat := 27185035130814965439857

theorem tailTrace_119121 : CollatzResearch.WordTrace tailWord_119121 prefixEnd_119121 27185035130814965439857 := by
  unfold tailWord_119121
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344699801452436092221217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2896466534301624061480811 4344699801452436092221217)
  ·
    refine ⟨3258524851089327069165913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4344699801452436092221217 3258524851089327069165913)
    ·
      refine ⟨2443893638316995301874435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3258524851089327069165913 2443893638316995301874435)
      ·
        refine ⟨3665840457475492952811653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2443893638316995301874435 3665840457475492952811653)
        ·
          refine ⟨687345085776654928652185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3665840457475492952811653 687345085776654928652185)
          ·
            refine ⟨515508814332491196489139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687345085776654928652185 515508814332491196489139)
            ·
              refine ⟨773263221498736794733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515508814332491196489139 773263221498736794733709)
              ·
                refine ⟨289973708062026298025141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 773263221498736794733709 289973708062026298025141)
                ·
                  refine ⟨27185035130814965439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289973708062026298025141 27185035130814965439857)
                  ·
                    rfl

theorem cell21_119121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_119121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119121 prefixEnd_119121 := by exact prefixLift 119121
  have htrace : WordTrace (prefixWord ++ tailWord_119121) baseStart_119121 baseEnd_119121 := by
    simpa [prefixWord, tailWord_119121, baseEnd_119121] using wordTrace_append hprefix tailTrace_119121
  have hstable : (prefixWord ++ tailWord_119121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119121).length < 2 ^ (prefixWord ++ tailWord_119121).sum := by decide
  have hdescent : baseEnd_119121 < baseStart_119121 := by decide
  rcases family_descends (prefixWord ++ tailWord_119121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119138 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_119138 : Nat := 118140960795 + 119138 * 2 ^ 59
def prefixEnd_119138 : Nat := 4983230072969 + 3 ^ 40 * 119138 * 2
def baseEnd_119138 : Nat := 27188914762426713656489

theorem tailTrace_119138 : CollatzResearch.WordTrace tailWord_119138 prefixEnd_119138 27188914762426713656489 := by
  unfold tailWord_119138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1086329960597711998897517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2896879894927231997060045 1086329960597711998897517)
  ·
    refine ⟨407373735224141999586569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1086329960597711998897517 407373735224141999586569)
    ·
      refine ⟨305530301418106499689927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 407373735224141999586569 305530301418106499689927)
      ·
        refine ⟨458295452127159749534891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 305530301418106499689927 458295452127159749534891)
        ·
          refine ⟨687443178190739624302337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 458295452127159749534891 687443178190739624302337)
          ·
            refine ⟨515582383643054718226753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 687443178190739624302337 515582383643054718226753)
            ·
              refine ⟨386686787732291038670065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 515582383643054718226753 386686787732291038670065)
              ·
                refine ⟨290015090799218279002549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 386686787732291038670065 290015090799218279002549)
                ·
                  refine ⟨27188914762426713656489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290015090799218279002549 27188914762426713656489)
                  ·
                    rfl

theorem cell21_119138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_119138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119138 prefixEnd_119138 := by exact prefixLift 119138
  have htrace : WordTrace (prefixWord ++ tailWord_119138) baseStart_119138 baseEnd_119138 := by
    simpa [prefixWord, tailWord_119138, baseEnd_119138] using wordTrace_append hprefix tailTrace_119138
  have hstable : (prefixWord ++ tailWord_119138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119138).length < 2 ^ (prefixWord ++ tailWord_119138).sum := by decide
  have hdescent : baseEnd_119138 < baseStart_119138 := by decide
  rcases family_descends (prefixWord ++ tailWord_119138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119341 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 5]
def baseStart_119341 : Nat := 118140960795 + 119341 * 2 ^ 59
def prefixEnd_119341 : Nat := 4983230072969 + 3 ^ 40 * 119341 * 2
def baseEnd_119341 : Nat := 27235242128143471772741

theorem tailTrace_119341 : CollatzResearch.WordTrace tailWord_119341 prefixEnd_119341 27235242128143471772741 := by
  unfold tailWord_119341
  simp only [CollatzResearch.WordTrace]
  refine ⟨4352723860655413665229877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2901815907103609110153251 4352723860655413665229877)
  ·
    refine ⟨408067861936445031115301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4352723860655413665229877 408067861936445031115301)
    ·
      refine ⟨76512724113083443334119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 408067861936445031115301 76512724113083443334119)
      ·
        refine ⟨114769086169625165001179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76512724113083443334119 114769086169625165001179)
        ·
          refine ⟨172153629254437747501769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114769086169625165001179 172153629254437747501769)
          ·
            refine ⟨129115221940828310626327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172153629254437747501769 129115221940828310626327)
            ·
              refine ⟨193672832911242465939491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129115221940828310626327 193672832911242465939491)
              ·
                refine ⟨290509249366863698909237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 193672832911242465939491 290509249366863698909237)
                ·
                  refine ⟨27235242128143471772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290509249366863698909237 27235242128143471772741)
                  ·
                    rfl

theorem cell21_119341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_119341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119341 prefixEnd_119341 := by exact prefixLift 119341
  have htrace : WordTrace (prefixWord ++ tailWord_119341) baseStart_119341 baseEnd_119341 := by
    simpa [prefixWord, tailWord_119341, baseEnd_119341] using wordTrace_append hprefix tailTrace_119341
  have hstable : (prefixWord ++ tailWord_119341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119341).length < 2 ^ (prefixWord ++ tailWord_119341).sum := by decide
  have hdescent : baseEnd_119341 < baseStart_119341 := by decide
  rcases family_descends (prefixWord ++ tailWord_119341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119397 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_119397 : Nat := 118140960795 + 119397 * 2 ^ 59
def prefixEnd_119397 : Nat := 4983230072969 + 3 ^ 40 * 119397 * 2
def baseEnd_119397 : Nat := 27248022091099818839293

theorem tailTrace_119397 : CollatzResearch.WordTrace tailWord_119397 prefixEnd_119397 27248022091099818839293 := by
  unfold tailWord_119397
  simp only [CollatzResearch.WordTrace]
  refine ⟨4354766348452535229268445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2903177565635023486178963 4354766348452535229268445)
  ·
    refine ⟨1633037380669700710975667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4354766348452535229268445 1633037380669700710975667)
    ·
      refine ⟨2449556071004551066463501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1633037380669700710975667 2449556071004551066463501)
      ·
        refine ⟨918583526626706649923813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2449556071004551066463501 918583526626706649923813)
        ·
          refine ⟨172234411242507496860715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 918583526626706649923813 172234411242507496860715)
          ·
            refine ⟨258351616863761245291073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172234411242507496860715 258351616863761245291073)
            ·
              refine ⟨193763712647820933968305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 258351616863761245291073 193763712647820933968305)
              ·
                refine ⟨145322784485865700476229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 193763712647820933968305 145322784485865700476229)
                ·
                  refine ⟨27248022091099818839293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145322784485865700476229 27248022091099818839293)
                  ·
                    rfl

theorem cell21_119397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_119397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119397 prefixEnd_119397 := by exact prefixLift 119397
  have htrace : WordTrace (prefixWord ++ tailWord_119397) baseStart_119397 baseEnd_119397 := by
    simpa [prefixWord, tailWord_119397, baseEnd_119397] using wordTrace_append hprefix tailTrace_119397
  have hstable : (prefixWord ++ tailWord_119397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119397).length < 2 ^ (prefixWord ++ tailWord_119397).sum := by decide
  have hdescent : baseEnd_119397 < baseStart_119397 := by decide
  rcases family_descends (prefixWord ++ tailWord_119397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119425 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_119425 : Nat := 118140960795 + 119425 * 2 ^ 59
def prefixEnd_119425 : Nat := 4983230072969 + 3 ^ 40 * 119425 * 2
def baseEnd_119425 : Nat := 27254412072577992372569

theorem tailTrace_119425 : CollatzResearch.WordTrace tailWord_119425 prefixEnd_119425 27254412072577992372569 := by
  unfold tailWord_119425
  simp only [CollatzResearch.WordTrace]
  refine ⟨4355787592351096011287729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2903858394900730674191819 4355787592351096011287729)
  ·
    refine ⟨3266840694263322008465797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4355787592351096011287729 3266840694263322008465797)
    ·
      refine ⟨612532630174372876587337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3266840694263322008465797 612532630174372876587337)
      ·
        refine ⟨459399472630779657440503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 612532630174372876587337 459399472630779657440503)
        ·
          refine ⟨689099208946169486160755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 459399472630779657440503 689099208946169486160755)
          ·
            refine ⟨1033648813419254229241133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 689099208946169486160755 1033648813419254229241133)
            ·
              refine ⟨387618305032220335965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1033648813419254229241133 387618305032220335965425)
              ·
                refine ⟨290713728774165251974069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 387618305032220335965425 290713728774165251974069)
                ·
                  refine ⟨27254412072577992372569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 290713728774165251974069 27254412072577992372569)
                  ·
                    rfl

theorem cell21_119425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_119425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119425 prefixEnd_119425 := by exact prefixLift 119425
  have htrace : WordTrace (prefixWord ++ tailWord_119425) baseStart_119425 baseEnd_119425 := by
    simpa [prefixWord, tailWord_119425, baseEnd_119425] using wordTrace_append hprefix tailTrace_119425
  have hstable : (prefixWord ++ tailWord_119425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119425).length < 2 ^ (prefixWord ++ tailWord_119425).sum := by decide
  have hdescent : baseEnd_119425 < baseStart_119425 := by decide
  rcases family_descends (prefixWord ++ tailWord_119425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119456 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_119456 : Nat := 118140960795 + 119456 * 2 ^ 59
def prefixEnd_119456 : Nat := 4983230072969 + 3 ^ 40 * 119456 * 2
def baseEnd_119456 : Nat := 27261486694928827355839

theorem tailTrace_119456 : CollatzResearch.WordTrace tailWord_119456 prefixEnd_119456 27261486694928827355839 := by
  unfold tailWord_119456
  simp only [CollatzResearch.WordTrace]
  refine ⟨2178459127619394152833111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2904612170159192203777481 2178459127619394152833111)
  ·
    refine ⟨3267688691429091229249667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2178459127619394152833111 3267688691429091229249667)
    ·
      refine ⟨4901533037143636843874501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3267688691429091229249667 4901533037143636843874501)
      ·
        refine ⟨919037444464431908226469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4901533037143636843874501 919037444464431908226469)
        ·
          refine ⟨172319520837080982792463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 919037444464431908226469 172319520837080982792463)
          ·
            refine ⟨258479281255621474188695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172319520837080982792463 258479281255621474188695)
            ·
              refine ⟨387718921883432211283043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258479281255621474188695 387718921883432211283043)
              ·
                refine ⟨581578382825148316924565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 387718921883432211283043 581578382825148316924565)
                ·
                  refine ⟨27261486694928827355839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 581578382825148316924565 27261486694928827355839)
                  ·
                    rfl

theorem cell21_119456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_119456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119456 prefixEnd_119456 := by exact prefixLift 119456
  have htrace : WordTrace (prefixWord ++ tailWord_119456) baseStart_119456 baseEnd_119456 := by
    simpa [prefixWord, tailWord_119456, baseEnd_119456] using wordTrace_append hprefix tailTrace_119456
  have hstable : (prefixWord ++ tailWord_119456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119456).length < 2 ^ (prefixWord ++ tailWord_119456).sum := by decide
  have hdescent : baseEnd_119456 < baseStart_119456 := by decide
  rcases family_descends (prefixWord ++ tailWord_119456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119487 : List Nat := [1, 1, 2, 2, 2, 6, 2, 5]
def baseStart_119487 : Nat := 118140960795 + 119487 * 2 ^ 59
def prefixEnd_119487 : Nat := 4983230072969 + 3 ^ 40 * 119487 * 2
def baseEnd_119487 : Nat := 9089520439093220779703

theorem tailTrace_119487 : CollatzResearch.WordTrace tailWord_119487 prefixEnd_119487 9089520439093220779703 := by
  unfold tailWord_119487
  simp only [CollatzResearch.WordTrace]
  refine ⟨4358048918126480600044715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2905365945417653733363143 4358048918126480600044715)
  ·
    refine ⟨6537073377189720900067073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4358048918126480600044715 6537073377189720900067073)
    ·
      refine ⟨4902805032892290675050305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6537073377189720900067073 4902805032892290675050305)
      ·
        refine ⟨3677103774669218006287729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902805032892290675050305 3677103774669218006287729)
        ·
          refine ⟨2757827831001913504715797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3677103774669218006287729 2757827831001913504715797)
          ·
            refine ⟨129273179578214695533553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2757827831001913504715797 129273179578214695533553)
            ·
              refine ⟨96954884683661021650165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129273179578214695533553 96954884683661021650165)
              ·
                refine ⟨9089520439093220779703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96954884683661021650165 9089520439093220779703)
                ·
                  rfl

theorem cell21_119487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 5].length) (baseStart_119487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119487 prefixEnd_119487 := by exact prefixLift 119487
  have htrace : WordTrace (prefixWord ++ tailWord_119487) baseStart_119487 baseEnd_119487 := by
    simpa [prefixWord, tailWord_119487, baseEnd_119487] using wordTrace_append hprefix tailTrace_119487
  have hstable : (prefixWord ++ tailWord_119487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119487).length < 2 ^ (prefixWord ++ tailWord_119487).sum := by decide
  have hdescent : baseEnd_119487 < baseStart_119487 := by decide
  rcases family_descends (prefixWord ++ tailWord_119487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119529 : List Nat := [1, 2, 1, 1, 1, 2, 5, 8]
def baseStart_119529 : Nat := 118140960795 + 119529 * 2 ^ 59
def prefixEnd_119529 : Nat := 4983230072969 + 3 ^ 40 * 119529 * 2
def baseEnd_119529 : Nat := 9092715429832307546341

theorem tailTrace_119529 : CollatzResearch.WordTrace tailWord_119529 prefixEnd_119529 9092715429832307546341 := by
  unfold tailWord_119529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4359580783974321773073641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2906387189316214515382427 4359580783974321773073641)
  ·
    refine ⟨3269685587980741329805231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4359580783974321773073641 3269685587980741329805231)
    ·
      refine ⟨4904528381971111994707847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3269685587980741329805231 4904528381971111994707847)
      ·
        refine ⟨7356792572956667992061771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4904528381971111994707847 7356792572956667992061771)
        ·
          refine ⟨11035188859435001988092657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7356792572956667992061771 11035188859435001988092657)
          ·
            refine ⟨8276391644576251491069493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11035188859435001988092657 8276391644576251491069493)
            ·
              refine ⟨775911716679023577287765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8276391644576251491069493 775911716679023577287765)
              ·
                refine ⟨9092715429832307546341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 775911716679023577287765 9092715429832307546341)
                ·
                  rfl

theorem cell21_119529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_119529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119529 prefixEnd_119529 := by exact prefixLift 119529
  have htrace : WordTrace (prefixWord ++ tailWord_119529) baseStart_119529 baseEnd_119529 := by
    simpa [prefixWord, tailWord_119529, baseEnd_119529] using wordTrace_append hprefix tailTrace_119529
  have hstable : (prefixWord ++ tailWord_119529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119529).length < 2 ^ (prefixWord ++ tailWord_119529).sum := by decide
  have hdescent : baseEnd_119529 < baseStart_119529 := by decide
  rcases family_descends (prefixWord ++ tailWord_119529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119597 : List Nat := [1, 5, 3, 2, 1, 1, 3, 5]
def baseStart_119597 : Nat := 118140960795 + 119597 * 2 ^ 59
def prefixEnd_119597 : Nat := 4983230072969 + 3 ^ 40 * 119597 * 2
def baseEnd_119597 : Nat := 9097888271981305168517

theorem tailTrace_119597 : CollatzResearch.WordTrace tailWord_119597 prefixEnd_119597 9097888271981305168517 := by
  unfold tailWord_119597
  simp only [CollatzResearch.WordTrace]
  refine ⟨4362060947727969386549045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2908040631818646257699363 4362060947727969386549045)
  ·
    refine ⟨408943213849497129988973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4362060947727969386549045 408943213849497129988973)
    ·
      refine ⟨153353705193561423745865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 408943213849497129988973 153353705193561423745865)
      ·
        refine ⟨115015278895171067809399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153353705193561423745865 115015278895171067809399)
        ·
          refine ⟨172522918342756601714099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115015278895171067809399 172522918342756601714099)
          ·
            refine ⟨258784377514134902571149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172522918342756601714099 258784377514134902571149)
            ·
              refine ⟨97044141567800588464181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258784377514134902571149 97044141567800588464181)
              ·
                refine ⟨9097888271981305168517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97044141567800588464181 9097888271981305168517)
                ·
                  rfl

theorem cell21_119597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 5].length) (baseStart_119597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119597 prefixEnd_119597 := by exact prefixLift 119597
  have htrace : WordTrace (prefixWord ++ tailWord_119597) baseStart_119597 baseEnd_119597 := by
    simpa [prefixWord, tailWord_119597, baseEnd_119597] using wordTrace_append hprefix tailTrace_119597
  have hstable : (prefixWord ++ tailWord_119597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119597).length < 2 ^ (prefixWord ++ tailWord_119597).sum := by decide
  have hdescent : baseEnd_119597 < baseStart_119597 := by decide
  rcases family_descends (prefixWord ++ tailWord_119597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119687 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 3]
def baseStart_119687 : Nat := 118140960795 + 119687 * 2 ^ 59
def prefixEnd_119687 : Nat := 4983230072969 + 3 ^ 40 * 119687 * 2
def baseEnd_119687 : Nat := 27314204042123759005367

theorem tailTrace_119687 : CollatzResearch.WordTrace tailWord_119687 prefixEnd_119687 27314204042123759005367 := by
  unfold tailWord_119687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365343517401914757325315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2910229011601276504883543 4365343517401914757325315)
  ·
    refine ⟨6548015276102872135987973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4365343517401914757325315 6548015276102872135987973)
    ·
      refine ⟨1227752864269288525497745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6548015276102872135987973 1227752864269288525497745)
      ·
        refine ⟨920814648201966394123309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1227752864269288525497745 920814648201966394123309)
        ·
          refine ⟨345305493075737397796241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 920814648201966394123309 345305493075737397796241)
          ·
            refine ⟨258979119806803048347181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345305493075737397796241 258979119806803048347181)
            ·
              refine ⟨97117169927551143130193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 258979119806803048347181 97117169927551143130193)
              ·
                refine ⟨72837877445663357347645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97117169927551143130193 72837877445663357347645)
                ·
                  refine ⟨27314204042123759005367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72837877445663357347645 27314204042123759005367)
                  ·
                    rfl

theorem cell21_119687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 3].length) (baseStart_119687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119687 prefixEnd_119687 := by exact prefixLift 119687
  have htrace : WordTrace (prefixWord ++ tailWord_119687) baseStart_119687 baseEnd_119687 := by
    simpa [prefixWord, tailWord_119687, baseEnd_119687] using wordTrace_append hprefix tailTrace_119687
  have hstable : (prefixWord ++ tailWord_119687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119687).length < 2 ^ (prefixWord ++ tailWord_119687).sum := by decide
  have hdescent : baseEnd_119687 < baseStart_119687 := by decide
  rcases family_descends (prefixWord ++ tailWord_119687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119701 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 4]
def baseStart_119701 : Nat := 118140960795 + 119701 * 2 ^ 59
def prefixEnd_119701 : Nat := 4983230072969 + 3 ^ 40 * 119701 * 2
def baseEnd_119701 : Nat := 27317399032862845772005

theorem tailTrace_119701 : CollatzResearch.WordTrace tailWord_119701 prefixEnd_119701 27317399032862845772005 := by
  unfold tailWord_119701
  simp only [CollatzResearch.WordTrace]
  refine ⟨4365854139351195148334957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2910569426234130098889971 4365854139351195148334957)
  ·
    refine ⟨1637195302256698180625609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4365854139351195148334957 1637195302256698180625609)
    ·
      refine ⟨1227896476692523635469207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1637195302256698180625609 1227896476692523635469207)
      ·
        refine ⟨1841844715038785453203811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1227896476692523635469207 1841844715038785453203811)
        ·
          refine ⟨2762767072558178179805717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1841844715038785453203811 2762767072558178179805717)
          ·
            refine ⟨129504706526164602178393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2762767072558178179805717 129504706526164602178393)
            ·
              refine ⟨97128529894623451633795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129504706526164602178393 97128529894623451633795)
              ·
                refine ⟨145692794841935177450693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97128529894623451633795 145692794841935177450693)
                ·
                  refine ⟨27317399032862845772005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145692794841935177450693 27317399032862845772005)
                  ·
                    rfl

theorem cell21_119701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_119701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119701 prefixEnd_119701 := by exact prefixLift 119701
  have htrace : WordTrace (prefixWord ++ tailWord_119701) baseStart_119701 baseEnd_119701 := by
    simpa [prefixWord, tailWord_119701, baseEnd_119701] using wordTrace_append hprefix tailTrace_119701
  have hstable : (prefixWord ++ tailWord_119701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119701).length < 2 ^ (prefixWord ++ tailWord_119701).sum := by decide
  have hdescent : baseEnd_119701 < baseStart_119701 := by decide
  rcases family_descends (prefixWord ++ tailWord_119701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119712 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_119712 : Nat := 118140960795 + 119712 * 2 ^ 59
def prefixEnd_119712 : Nat := 4983230072969 + 3 ^ 40 * 119712 * 2
def baseEnd_119712 : Nat := 27319909382729271088649

theorem tailTrace_119712 : CollatzResearch.WordTrace tailWord_119712 prefixEnd_119712 27319909382729271088649 := by
  unfold tailWord_119712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183127671155672013492695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2910836894874229351323593 2183127671155672013492695)
  ·
    refine ⟨3274691506733508020239043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183127671155672013492695 3274691506733508020239043)
    ·
      refine ⟨4912037260100262030358565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3274691506733508020239043 4912037260100262030358565)
      ·
        refine ⟨921006986268799130692231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4912037260100262030358565 921006986268799130692231)
        ·
          refine ⟨1381510479403198696038347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 921006986268799130692231 1381510479403198696038347)
          ·
            refine ⟨2072265719104798044057521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1381510479403198696038347 2072265719104798044057521)
            ·
              refine ⟨1554199289328598533043141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2072265719104798044057521 1554199289328598533043141)
              ·
                refine ⟨291412366749112224945589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1554199289328598533043141 291412366749112224945589)
                ·
                  refine ⟨27319909382729271088649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291412366749112224945589 27319909382729271088649)
                  ·
                    rfl

theorem cell21_119712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_119712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119712 prefixEnd_119712 := by exact prefixLift 119712
  have htrace : WordTrace (prefixWord ++ tailWord_119712) baseStart_119712 baseEnd_119712 := by
    simpa [prefixWord, tailWord_119712, baseEnd_119712] using wordTrace_append hprefix tailTrace_119712
  have hstable : (prefixWord ++ tailWord_119712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119712).length < 2 ^ (prefixWord ++ tailWord_119712).sum := by decide
  have hdescent : baseEnd_119712 < baseStart_119712 := by decide
  rcases family_descends (prefixWord ++ tailWord_119712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119794 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_119794 : Nat := 118140960795 + 119794 * 2 ^ 59
def prefixEnd_119794 : Nat := 4983230072969 + 3 ^ 40 * 119794 * 2
def baseEnd_119794 : Nat := 27338622899915350721815

theorem tailTrace_119794 : CollatzResearch.WordTrace tailWord_119794 prefixEnd_119794 27338622899915350721815 := by
  unfold tailWord_119794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092311532003568007867609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2912830752009514687646957 1092311532003568007867609)
  ·
    refine ⟨819233649002676005900707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092311532003568007867609 819233649002676005900707)
    ·
      refine ⟨1228850473504014008851061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 819233649002676005900707 1228850473504014008851061)
      ·
        refine ⟨115204731891001313329787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1228850473504014008851061 115204731891001313329787)
        ·
          refine ⟨172807097836501969994681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115204731891001313329787 172807097836501969994681)
          ·
            refine ⟨129605323377376477496011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172807097836501969994681 129605323377376477496011)
            ·
              refine ⟨194407985066064716244017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129605323377376477496011 194407985066064716244017)
              ·
                refine ⟨145805988799548537183013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194407985066064716244017 145805988799548537183013)
                ·
                  refine ⟨27338622899915350721815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145805988799548537183013 27338622899915350721815)
                  ·
                    rfl

theorem cell21_119794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_119794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_119794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_119794 prefixEnd_119794 := by exact prefixLift 119794
  have htrace : WordTrace (prefixWord ++ tailWord_119794) baseStart_119794 baseEnd_119794 := by
    simpa [prefixWord, tailWord_119794, baseEnd_119794] using wordTrace_append hprefix tailTrace_119794
  have hstable : (prefixWord ++ tailWord_119794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119794).length < 2 ^ (prefixWord ++ tailWord_119794).sum := by decide
  have hdescent : baseEnd_119794 < baseStart_119794 := by decide
  rcases family_descends (prefixWord ++ tailWord_119794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
