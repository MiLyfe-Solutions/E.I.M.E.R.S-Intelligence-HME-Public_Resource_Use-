import V185TrunkScan22Chunk381

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3407031 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 4, 3]
def baseStart_3407031 : Nat := 118140960795 + 3407031 * 2 ^ 59
def prefixEnd_3407031 : Nat := 4983230072969 + 3 ^ 40 * 3407031 * 2
def baseEnd_3407031 : Nat := 1166296338512376472829237

theorem tailTrace_3407031 : CollatzResearch.WordTrace tailWord_3407031 prefixEnd_3407031 1166296338512376472829237 := by
  unfold tailWord_3407031
  simp only [CollatzResearch.WordTrace]
  refine ⟨124264629319916036414508947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82843086213277357609672631 124264629319916036414508947)
  ·
    refine ⟨186396943979874054621763421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124264629319916036414508947 186396943979874054621763421)
    ·
      refine ⟨69898853992452770483161283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186396943979874054621763421 69898853992452770483161283)
      ·
        refine ⟨104848280988679155724741925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69898853992452770483161283 104848280988679155724741925)
        ·
          refine ⟨19659052685377341698389111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104848280988679155724741925 19659052685377341698389111)
          ·
            refine ⟨29488579028066012547583667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19659052685377341698389111 29488579028066012547583667)
            ·
              refine ⟨44232868542099018821375501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29488579028066012547583667 44232868542099018821375501)
              ·
                refine ⟨16587325703287132058015813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44232868542099018821375501 16587325703287132058015813)
                ·
                  refine ⟨3110123569366337260877965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16587325703287132058015813 3110123569366337260877965)
                  ·
                    refine ⟨1166296338512376472829237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110123569366337260877965 1166296338512376472829237)
                    ·
                      rfl

theorem cell22_3407031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_3407031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407031 prefixEnd_3407031 := by exact prefixLift 3407031
  have htrace : WordTrace (prefixWord ++ tailWord_3407031) baseStart_3407031 baseEnd_3407031 := by
    simpa [prefixWord, tailWord_3407031, baseEnd_3407031] using wordTrace_append hprefix tailTrace_3407031
  have hstable : (prefixWord ++ tailWord_3407031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407031).length < 2 ^ (prefixWord ++ tailWord_3407031).sum := by decide
  have hdescent : baseEnd_3407031 < baseStart_3407031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407061 : List Nat := [1, 3, 2, 4, 1, 1, 2, 8]
def baseStart_3407061 : Nat := 118140960795 + 3407061 * 2 ^ 59
def prefixEnd_3407061 : Nat := 4983230072969 + 3 ^ 40 * 3407061 * 2
def baseEnd_3407061 : Nat := 129589623125051821619905

theorem tailTrace_3407061 : CollatzResearch.WordTrace tailWord_3407061 prefixEnd_3407061 129589623125051821619905 := by
  unfold tailWord_3407061
  simp only [CollatzResearch.WordTrace]
  refine ⟨124265723509807351538101037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82843815673204901025400691 124265723509807351538101037)
  ·
    refine ⟨46599646316177756826787889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124265723509807351538101037 46599646316177756826787889)
    ·
      refine ⟨34949734737133317620090917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46599646316177756826787889 34949734737133317620090917)
      ·
        refine ⟨6553075263212497053767047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34949734737133317620090917 6553075263212497053767047)
        ·
          refine ⟨9829612894818745580650571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553075263212497053767047 9829612894818745580650571)
          ·
            refine ⟨14744419342228118370975857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9829612894818745580650571 14744419342228118370975857)
            ·
              refine ⟨11058314506671088778231893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14744419342228118370975857 11058314506671088778231893)
              ·
                refine ⟨129589623125051821619905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11058314506671088778231893 129589623125051821619905)
                ·
                  rfl

theorem cell22_3407061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 8].length) (baseStart_3407061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407061 prefixEnd_3407061 := by exact prefixLift 3407061
  have htrace : WordTrace (prefixWord ++ tailWord_3407061) baseStart_3407061 baseEnd_3407061 := by
    simpa [prefixWord, tailWord_3407061, baseEnd_3407061] using wordTrace_append hprefix tailTrace_3407061
  have hstable : (prefixWord ++ tailWord_3407061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407061).length < 2 ^ (prefixWord ++ tailWord_3407061).sum := by decide
  have hdescent : baseEnd_3407061 < baseStart_3407061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407202 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3407202 : Nat := 118140960795 + 3407202 * 2 ^ 59
def prefixEnd_3407202 : Nat := 4983230072969 + 3 ^ 40 * 3407202 * 2
def baseEnd_3407202 : Nat := 388784958435663008934571

theorem tailTrace_3407202 : CollatzResearch.WordTrace tailWord_3407202 prefixEnd_3407202 388784958435663008934571 := by
  unfold tailWord_3407202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31067716550574133154745965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82847244134864355079322573 31067716550574133154745965)
  ·
    refine ⟨11650393706465299933029737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31067716550574133154745965 11650393706465299933029737)
    ·
      refine ⟨8737795279848974949772303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11650393706465299933029737 8737795279848974949772303)
      ·
        refine ⟨13106692919773462424658455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8737795279848974949772303 13106692919773462424658455)
        ·
          refine ⟨19660039379660193636987683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13106692919773462424658455 19660039379660193636987683)
          ·
            refine ⟨29490059069490290455481525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19660039379660193636987683 29490059069490290455481525)
            ·
              refine ⟨2764693037764714730201393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29490059069490290455481525 2764693037764714730201393)
              ·
                refine ⟨2073519778323536047651045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2764693037764714730201393 2073519778323536047651045)
                ·
                  refine ⟨388784958435663008934571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073519778323536047651045 388784958435663008934571)
                  ·
                    rfl

theorem cell22_3407202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3407202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407202 prefixEnd_3407202 := by exact prefixLift 3407202
  have htrace : WordTrace (prefixWord ++ tailWord_3407202) baseStart_3407202 baseEnd_3407202 := by
    simpa [prefixWord, tailWord_3407202, baseEnd_3407202] using wordTrace_append hprefix tailTrace_3407202
  have hstable : (prefixWord ++ tailWord_3407202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407202).length < 2 ^ (prefixWord ++ tailWord_3407202).sum := by decide
  have hdescent : baseEnd_3407202 < baseStart_3407202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407213 : List Nat := [1, 5, 1, 1, 1, 4, 2, 7]
def baseStart_3407213 : Nat := 118140960795 + 3407213 * 2 ^ 59
def prefixEnd_3407213 : Nat := 4983230072969 + 3 ^ 40 * 3407213 * 2
def baseEnd_3407213 : Nat := 129595404536865407197631

theorem tailTrace_3407213 : CollatzResearch.WordTrace tailWord_3407213 prefixEnd_3407213 129595404536865407197631 := by
  unfold tailWord_3407213
  simp only [CollatzResearch.WordTrace]
  refine ⟨124271267405256681497634293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82847511603504454331756195 124271267405256681497634293)
  ·
    refine ⟨11650431319242813890403215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124271267405256681497634293 11650431319242813890403215)
    ·
      refine ⟨17475646978864220835604823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11650431319242813890403215 17475646978864220835604823)
      ·
        refine ⟨26213470468296331253407235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17475646978864220835604823 26213470468296331253407235)
        ·
          refine ⟨39320205702444496880110853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26213470468296331253407235 39320205702444496880110853)
          ·
            refine ⟨7372538569208343165020785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39320205702444496880110853 7372538569208343165020785)
            ·
              refine ⟨5529403926906257373765589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7372538569208343165020785 5529403926906257373765589)
              ·
                refine ⟨129595404536865407197631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5529403926906257373765589 129595404536865407197631)
                ·
                  rfl

theorem cell22_3407213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 7].length) (baseStart_3407213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407213 prefixEnd_3407213 := by exact prefixLift 3407213
  have htrace : WordTrace (prefixWord ++ tailWord_3407213) baseStart_3407213 baseEnd_3407213 := by
    simpa [prefixWord, tailWord_3407213, baseEnd_3407213] using wordTrace_append hprefix tailTrace_3407213
  have hstable : (prefixWord ++ tailWord_3407213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407213).length < 2 ^ (prefixWord ++ tailWord_3407213).sum := by decide
  have hdescent : baseEnd_3407213 < baseStart_3407213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407226 : List Nat := [3, 1, 1, 1, 1, 1, 2, 4, 2, 6]
def baseStart_3407226 : Nat := 118140960795 + 3407226 * 2 ^ 59
def prefixEnd_3407226 : Nat := 4983230072969 + 3 ^ 40 * 3407226 * 2
def baseEnd_3407226 : Nat := 1166363090997460964203639

theorem tailTrace_3407226 : CollatzResearch.WordTrace tailWord_3407226 prefixEnd_3407226 1166363090997460964203639 := by
  unfold tailWord_3407226
  simp only [CollatzResearch.WordTrace]
  refine ⟨31067935388552396179464383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82847827702806389811905021 31067935388552396179464383)
  ·
    refine ⟨46601903082828594269196575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31067935388552396179464383 46601903082828594269196575)
    ·
      refine ⟨69902854624242891403794863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46601903082828594269196575 69902854624242891403794863)
      ·
        refine ⟨104854281936364337105692295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69902854624242891403794863 104854281936364337105692295)
        ·
          refine ⟨157281422904546505658538443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104854281936364337105692295 157281422904546505658538443)
          ·
            refine ⟨235922134356819758487807665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157281422904546505658538443 235922134356819758487807665)
            ·
              refine ⟨176941600767614818865855749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235922134356819758487807665 176941600767614818865855749)
              ·
                refine ⟨33176550143927778537347953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176941600767614818865855749 33176550143927778537347953)
                ·
                  refine ⟨24882412607945833903010965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33176550143927778537347953 24882412607945833903010965)
                  ·
                    refine ⟨1166363090997460964203639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24882412607945833903010965 1166363090997460964203639)
                    ·
                      rfl

theorem cell22_3407226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_3407226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407226 prefixEnd_3407226 := by exact prefixLift 3407226
  have htrace : WordTrace (prefixWord ++ tailWord_3407226) baseStart_3407226 baseEnd_3407226 := by
    simpa [prefixWord, tailWord_3407226, baseEnd_3407226] using wordTrace_append hprefix tailTrace_3407226
  have hstable : (prefixWord ++ tailWord_3407226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407226).length < 2 ^ (prefixWord ++ tailWord_3407226).sum := by decide
  have hdescent : baseEnd_3407226 < baseStart_3407226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407228 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_3407228 : Nat := 118140960795 + 3407228 * 2 ^ 59
def prefixEnd_3407228 : Nat := 4983230072969 + 3 ^ 40 * 3407228 * 2
def baseEnd_3407228 : Nat := 1166363775638333625653633

theorem tailTrace_3407228 : CollatzResearch.WordTrace tailWord_3407228 prefixEnd_3407228 1166363775638333625653633 := by
  unfold tailWord_3407228
  simp only [CollatzResearch.WordTrace]
  refine ⟨62135907250101169529715169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82847876333468226039620225 62135907250101169529715169)
  ·
    refine ⟨46601930437575877147286377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62135907250101169529715169 46601930437575877147286377)
    ·
      refine ⟨34951447828181907860464783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46601930437575877147286377 34951447828181907860464783)
      ·
        refine ⟨52427171742272861790697175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34951447828181907860464783 52427171742272861790697175)
        ·
          refine ⟨78640757613409292686045763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52427171742272861790697175 78640757613409292686045763)
          ·
            refine ⟨117961136420113939029068645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78640757613409292686045763 117961136420113939029068645)
            ·
              refine ⟨22117713078771363567950371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117961136420113939029068645 22117713078771363567950371)
              ·
                refine ⟨33176569618157045351925557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22117713078771363567950371 33176569618157045351925557)
                ·
                  refine ⟨3110303401702223001743021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33176569618157045351925557 3110303401702223001743021)
                  ·
                    refine ⟨1166363775638333625653633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110303401702223001743021 1166363775638333625653633)
                    ·
                      rfl

theorem cell22_3407228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_3407228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407228 prefixEnd_3407228 := by exact prefixLift 3407228
  have htrace : WordTrace (prefixWord ++ tailWord_3407228) baseStart_3407228 baseEnd_3407228 := by
    simpa [prefixWord, tailWord_3407228, baseEnd_3407228] using wordTrace_append hprefix tailTrace_3407228
  have hstable : (prefixWord ++ tailWord_3407228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407228).length < 2 ^ (prefixWord ++ tailWord_3407228).sum := by decide
  have hdescent : baseEnd_3407228 < baseStart_3407228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407288 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_3407288 : Nat := 118140960795 + 3407288 * 2 ^ 59
def prefixEnd_3407288 : Nat := 4983230072969 + 3 ^ 40 * 3407288 * 2
def baseEnd_3407288 : Nat := 1166384314864513469153449

theorem tailTrace_3407288 : CollatzResearch.WordTrace tailWord_3407288 prefixEnd_3407288 1166384314864513469153449 := by
  unfold tailWord_3407288
  simp only [CollatzResearch.WordTrace]
  refine ⟨62137001439992484653307259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82849335253323312871076345 62137001439992484653307259)
  ·
    refine ⟨93205502159988726979960889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62137001439992484653307259 93205502159988726979960889)
    ·
      refine ⟨69904126619991545234970667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93205502159988726979960889 69904126619991545234970667)
      ·
        refine ⟨104856189929987317852456001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69904126619991545234970667 104856189929987317852456001)
        ·
          refine ⟨78642142447490488389342001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104856189929987317852456001 78642142447490488389342001)
          ·
            refine ⟨58981606835617866292006501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78642142447490488389342001 58981606835617866292006501)
            ·
              refine ⟨11059051281678349929751219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58981606835617866292006501 11059051281678349929751219)
              ·
                refine ⟨16588576922517524894626829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059051281678349929751219 16588576922517524894626829)
                ·
                  refine ⟨6220716345944071835485061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16588576922517524894626829 6220716345944071835485061)
                  ·
                    refine ⟨1166384314864513469153449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220716345944071835485061 1166384314864513469153449)
                    ·
                      rfl

theorem cell22_3407288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_3407288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407288 prefixEnd_3407288 := by exact prefixLift 3407288
  have htrace : WordTrace (prefixWord ++ tailWord_3407288) baseStart_3407288 baseEnd_3407288 := by
    simpa [prefixWord, tailWord_3407288, baseEnd_3407288] using wordTrace_append hprefix tailTrace_3407288
  have hstable : (prefixWord ++ tailWord_3407288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407288).length < 2 ^ (prefixWord ++ tailWord_3407288).sum := by decide
  have hdescent : baseEnd_3407288 < baseStart_3407288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407320 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_3407320 : Nat := 118140960795 + 3407320 * 2 ^ 59
def prefixEnd_3407320 : Nat := 4983230072969 + 3 ^ 40 * 3407320 * 2
def baseEnd_3407320 : Nat := 388798423039492017451117

theorem tailTrace_3407320 : CollatzResearch.WordTrace tailWord_3407320 prefixEnd_3407320 388798423039492017451117 := by
  unfold tailWord_3407320
  simp only [CollatzResearch.WordTrace]
  refine ⟨62137585007934519385889707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82850113343912692514519609 62137585007934519385889707)
  ·
    refine ⟨93206377511901779078834561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62137585007934519385889707 93206377511901779078834561)
    ·
      refine ⟨69904783133926334309125921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93206377511901779078834561 69904783133926334309125921)
      ·
        refine ⟨52428587350444750731844441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69904783133926334309125921 52428587350444750731844441)
        ·
          refine ⟨39321440512833563048883331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52428587350444750731844441 39321440512833563048883331)
          ·
            refine ⟨58982160769250344573324997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39321440512833563048883331 58982160769250344573324997)
            ·
              refine ⟨11059155144234439607498437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58982160769250344573324997 11059155144234439607498437)
              ·
                refine ⟨2073591589543957426405957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11059155144234439607498437 2073591589543957426405957)
                ·
                  refine ⟨388798423039492017451117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073591589543957426405957 388798423039492017451117)
                  ·
                    rfl

theorem cell22_3407320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_3407320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407320 prefixEnd_3407320 := by exact prefixLift 3407320
  have htrace : WordTrace (prefixWord ++ tailWord_3407320) baseStart_3407320 baseEnd_3407320 := by
    simpa [prefixWord, tailWord_3407320, baseEnd_3407320] using wordTrace_append hprefix tailTrace_3407320
  have hstable : (prefixWord ++ tailWord_3407320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407320).length < 2 ^ (prefixWord ++ tailWord_3407320).sum := by decide
  have hdescent : baseEnd_3407320 < baseStart_3407320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407335 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3407335 : Nat := 118140960795 + 3407335 * 2 ^ 59
def prefixEnd_3407335 : Nat := 4983230072969 + 3 ^ 40 * 3407335 * 2
def baseEnd_3407335 : Nat := 1166400403925021013228305

theorem tailTrace_3407335 : CollatzResearch.WordTrace tailWord_3407335 prefixEnd_3407335 1166400403925021013228305 := by
  unfold tailWord_3407335
  simp only [CollatzResearch.WordTrace]
  refine ⟨124275717110814696333575459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82850478073876464222383639 124275717110814696333575459)
  ·
    refine ⟨186413575666222044500363189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124275717110814696333575459 186413575666222044500363189)
    ·
      refine ⟨17476272718708316671909049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186413575666222044500363189 17476272718708316671909049)
      ·
        refine ⟨13107204539031237503931787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17476272718708316671909049 13107204539031237503931787)
        ·
          refine ⟨19660806808546856255897681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13107204539031237503931787 19660806808546856255897681)
          ·
            refine ⟨14745605106410142191923261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19660806808546856255897681 14745605106410142191923261)
            ·
              refine ⟨5529601914903803321971223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14745605106410142191923261 5529601914903803321971223)
              ·
                refine ⟨8294402872355704982956835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5529601914903803321971223 8294402872355704982956835)
                ·
                  refine ⟨12441604308533557474435253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8294402872355704982956835 12441604308533557474435253)
                  ·
                    refine ⟨1166400403925021013228305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12441604308533557474435253 1166400403925021013228305)
                    ·
                      rfl

theorem cell22_3407335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3407335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407335 prefixEnd_3407335 := by exact prefixLift 3407335
  have htrace : WordTrace (prefixWord ++ tailWord_3407335) baseStart_3407335 baseEnd_3407335 := by
    simpa [prefixWord, tailWord_3407335, baseEnd_3407335] using wordTrace_append hprefix tailTrace_3407335
  have hstable : (prefixWord ++ tailWord_3407335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407335).length < 2 ^ (prefixWord ++ tailWord_3407335).sum := by decide
  have hdescent : baseEnd_3407335 < baseStart_3407335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407350 : List Nat := [5, 1, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3407350 : Nat := 118140960795 + 3407350 * 2 ^ 59
def prefixEnd_3407350 : Nat := 4983230072969 + 3 ^ 40 * 3407350 * 2
def baseEnd_3407350 : Nat := 1166405538731565974103259

theorem tailTrace_3407350 : CollatzResearch.WordTrace tailWord_3407350 prefixEnd_3407350 1166405538731565974103259 := by
  unfold tailWord_3407350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7767266512860022118460719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82850842803840235930247669 7767266512860022118460719)
  ·
    refine ⟨11650899769290033177691079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7767266512860022118460719 11650899769290033177691079)
    ·
      refine ⟨17476349653935049766536619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11650899769290033177691079 17476349653935049766536619)
      ·
        refine ⟨26214524480902574649804929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17476349653935049766536619 26214524480902574649804929)
        ·
          refine ⟨19660893360676930987353697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26214524480902574649804929 19660893360676930987353697)
          ·
            refine ⟨14745670020507698240515273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19660893360676930987353697 14745670020507698240515273)
            ·
              refine ⟨11059252515380773680386455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14745670020507698240515273 11059252515380773680386455)
              ·
                refine ⟨16588878773071160520579683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059252515380773680386455 16588878773071160520579683)
                ·
                  refine ⟨24883318159606740780869525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16588878773071160520579683 24883318159606740780869525)
                  ·
                    refine ⟨1166405538731565974103259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24883318159606740780869525 1166405538731565974103259)
                    ·
                      rfl

theorem cell22_3407350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3407350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407350 prefixEnd_3407350 := by exact prefixLift 3407350
  have htrace : WordTrace (prefixWord ++ tailWord_3407350) baseStart_3407350 baseEnd_3407350 := by
    simpa [prefixWord, tailWord_3407350, baseEnd_3407350] using wordTrace_append hprefix tailTrace_3407350
  have hstable : (prefixWord ++ tailWord_3407350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407350).length < 2 ^ (prefixWord ++ tailWord_3407350).sum := by decide
  have hdescent : baseEnd_3407350 < baseStart_3407350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407390 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3407390 : Nat := 118140960795 + 3407390 * 2 ^ 59
def prefixEnd_3407390 : Nat := 4983230072969 + 3 ^ 40 * 3407390 * 2
def baseEnd_3407390 : Nat := 1166419231549019203103137

theorem tailTrace_3407390 : CollatzResearch.WordTrace tailWord_3407390 prefixEnd_3407390 1166419231549019203103137 := by
  unfold tailWord_3407390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15534715390701930090853453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82851815417076960484551749 15534715390701930090853453)
  ·
    refine ⟨5825518271513223784070045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15534715390701930090853453 5825518271513223784070045)
    ·
      refine ⟨2184569351817458919026267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5825518271513223784070045 2184569351817458919026267)
      ·
        refine ⟨3276854027726188378539401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2184569351817458919026267 3276854027726188378539401)
        ·
          refine ⟨2457640520794641283904551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3276854027726188378539401 2457640520794641283904551)
          ·
            refine ⟨3686460781191961925856827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457640520794641283904551 3686460781191961925856827)
            ·
              refine ⟨5529691171787942888785241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686460781191961925856827 5529691171787942888785241)
              ·
                refine ⟨4147268378840957166588931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5529691171787942888785241 4147268378840957166588931)
                ·
                  refine ⟨6220902568261435749883397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147268378840957166588931 6220902568261435749883397)
                  ·
                    refine ⟨1166419231549019203103137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6220902568261435749883397 1166419231549019203103137)
                    ·
                      rfl

theorem cell22_3407390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3407390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407390 prefixEnd_3407390 := by exact prefixLift 3407390
  have htrace : WordTrace (prefixWord ++ tailWord_3407390) baseStart_3407390 baseEnd_3407390 := by
    simpa [prefixWord, tailWord_3407390, baseEnd_3407390] using wordTrace_append hprefix tailTrace_3407390
  have hstable : (prefixWord ++ tailWord_3407390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407390).length < 2 ^ (prefixWord ++ tailWord_3407390).sum := by decide
  have hdescent : baseEnd_3407390 < baseStart_3407390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407408 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_3407408 : Nat := 118140960795 + 3407408 * 2 ^ 59
def prefixEnd_3407408 : Nat := 4983230072969 + 3 ^ 40 * 3407408 * 2
def baseEnd_3407408 : Nat := 1166425393316873156153081

theorem tailTrace_3407408 : CollatzResearch.WordTrace tailWord_3407408 prefixEnd_3407408 1166425393316873156153081 := by
  unfold tailWord_3407408
  simp only [CollatzResearch.WordTrace]
  refine ⟨62139189819775114900491439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82852253093033486533988585 62139189819775114900491439)
  ·
    refine ⟨93208784729662672350737159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62139189819775114900491439 93208784729662672350737159)
    ·
      refine ⟨139813177094494008526105739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93208784729662672350737159 139813177094494008526105739)
      ·
        refine ⟨209719765641741012789158609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139813177094494008526105739 209719765641741012789158609)
        ·
          refine ⟨157289824231305759591868957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209719765641741012789158609 157289824231305759591868957)
          ·
            refine ⟨58983684086739659846950859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157289824231305759591868957 58983684086739659846950859)
            ·
              refine ⟨88475526130109489770426289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58983684086739659846950859 88475526130109489770426289)
              ·
                refine ⟨66356644597582117327819717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88475526130109489770426289 66356644597582117327819717)
                ·
                  refine ⟨12441870862046646998966197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66356644597582117327819717 12441870862046646998966197)
                  ·
                    refine ⟨1166425393316873156153081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12441870862046646998966197 1166425393316873156153081)
                    ·
                      rfl

theorem cell22_3407408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_3407408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407408 prefixEnd_3407408 := by exact prefixLift 3407408
  have htrace : WordTrace (prefixWord ++ tailWord_3407408) baseStart_3407408 baseEnd_3407408 := by
    simpa [prefixWord, tailWord_3407408, baseEnd_3407408] using wordTrace_append hprefix tailTrace_3407408
  have hstable : (prefixWord ++ tailWord_3407408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407408).length < 2 ^ (prefixWord ++ tailWord_3407408).sum := by decide
  have hdescent : baseEnd_3407408 < baseStart_3407408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407425 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3407425 : Nat := 118140960795 + 3407425 * 2 ^ 59
def prefixEnd_3407425 : Nat := 4983230072969 + 3 ^ 40 * 3407425 * 2
def baseEnd_3407425 : Nat := 1166431212764290778478029

theorem tailTrace_3407425 : CollatzResearch.WordTrace tailWord_3407425 prefixEnd_3407425 1166431212764290778478029 := by
  unfold tailWord_3407425
  simp only [CollatzResearch.WordTrace]
  refine ⟨124278999680488641704351729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82852666453659094469567819 124278999680488641704351729)
  ·
    refine ⟨93209249760366481278263797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124278999680488641704351729 93209249760366481278263797)
    ·
      refine ⟨8738367165034357619837231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93209249760366481278263797 8738367165034357619837231)
      ·
        refine ⟨13107550747551536429755847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8738367165034357619837231 13107550747551536429755847)
        ·
          refine ⟨19661326121327304644633771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13107550747551536429755847 19661326121327304644633771)
          ·
            refine ⟨29491989181990956966950657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19661326121327304644633771 29491989181990956966950657)
            ·
              refine ⟨22118991886493217725212993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29491989181990956966950657 22118991886493217725212993)
              ·
                refine ⟨16589243914869913293909745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22118991886493217725212993 16589243914869913293909745)
                ·
                  refine ⟨12441932936152434970432309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16589243914869913293909745 12441932936152434970432309)
                  ·
                    refine ⟨1166431212764290778478029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12441932936152434970432309 1166431212764290778478029)
                    ·
                      rfl

theorem cell22_3407425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3407425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407425 prefixEnd_3407425 := by exact prefixLift 3407425
  have htrace : WordTrace (prefixWord ++ tailWord_3407425) baseStart_3407425 baseEnd_3407425 := by
    simpa [prefixWord, tailWord_3407425, baseEnd_3407425] using wordTrace_append hprefix tailTrace_3407425
  have hstable : (prefixWord ++ tailWord_3407425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407425).length < 2 ^ (prefixWord ++ tailWord_3407425).sum := by decide
  have hdescent : baseEnd_3407425 < baseStart_3407425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407472 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_3407472 : Nat := 118140960795 + 3407472 * 2 ^ 59
def prefixEnd_3407472 : Nat := 4983230072969 + 3 ^ 40 * 3407472 * 2
def baseEnd_3407472 : Nat := 388815767274932774184295

theorem tailTrace_3407472 : CollatzResearch.WordTrace tailWord_3407472 prefixEnd_3407472 388815767274932774184295 := by
  unfold tailWord_3407472
  simp only [CollatzResearch.WordTrace]
  refine ⟨62140356955659184365656335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82853809274212245820875113 62140356955659184365656335)
  ·
    refine ⟨93210535433488776548484503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62140356955659184365656335 93210535433488776548484503)
    ·
      refine ⟨139815803150233164822726755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93210535433488776548484503 139815803150233164822726755)
      ·
        refine ⟨209723704725349747234090133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139815803150233164822726755 209723704725349747234090133)
        ·
          refine ⟨9830798659000769401597975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 209723704725349747234090133 9830798659000769401597975)
          ·
            refine ⟨14746197988501154102396963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830798659000769401597975 14746197988501154102396963)
            ·
              refine ⟨22119296982751731153595445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14746197988501154102396963 22119296982751731153595445)
              ·
                refine ⟨2073684092132974795649573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22119296982751731153595445 2073684092132974795649573)
                ·
                  refine ⟨388815767274932774184295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073684092132974795649573 388815767274932774184295)
                  ·
                    rfl

theorem cell22_3407472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_3407472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407472 prefixEnd_3407472 := by exact prefixLift 3407472
  have htrace : WordTrace (prefixWord ++ tailWord_3407472) baseStart_3407472 baseEnd_3407472 := by
    simpa [prefixWord, tailWord_3407472, baseEnd_3407472] using wordTrace_append hprefix tailTrace_3407472
  have hstable : (prefixWord ++ tailWord_3407472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407472).length < 2 ^ (prefixWord ++ tailWord_3407472).sum := by decide
  have hdescent : baseEnd_3407472 < baseStart_3407472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407474 : List Nat := [3, 2, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_3407474 : Nat := 118140960795 + 3407474 * 2 ^ 59
def prefixEnd_3407474 : Nat := 4983230072969 + 3 ^ 40 * 3407474 * 2
def baseEnd_3407474 : Nat := 1166447986465670984002879

theorem tailTrace_3407474 : CollatzResearch.WordTrace tailWord_3407474 prefixEnd_3407474 1166447986465670984002879 := by
  unfold tailWord_3407474
  simp only [CollatzResearch.WordTrace]
  refine ⟨31070196714327780768221369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82853857904874082048590317 31070196714327780768221369)
  ·
    refine ⟨23302647535745835576166027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31070196714327780768221369 23302647535745835576166027)
    ·
      refine ⟨34953971303618753364249041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23302647535745835576166027 34953971303618753364249041)
      ·
        refine ⟨26215478477714065023186781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34953971303618753364249041 26215478477714065023186781)
        ·
          refine ⟨9830804429142774383695043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26215478477714065023186781 9830804429142774383695043)
          ·
            refine ⟨14746206643714161575542565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830804429142774383695043 14746206643714161575542565)
            ·
              refine ⟨2764913745696405295414231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14746206643714161575542565 2764913745696405295414231)
              ·
                refine ⟨4147370618544607943121347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2764913745696405295414231 4147370618544607943121347)
                ·
                  refine ⟨6221055927816911914682021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4147370618544607943121347 6221055927816911914682021)
                  ·
                    refine ⟨1166447986465670984002879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6221055927816911914682021 1166447986465670984002879)
                    ·
                      rfl

theorem cell22_3407474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_3407474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407474 prefixEnd_3407474 := by exact prefixLift 3407474
  have htrace : WordTrace (prefixWord ++ tailWord_3407474) baseStart_3407474 baseEnd_3407474 := by
    simpa [prefixWord, tailWord_3407474, baseEnd_3407474] using wordTrace_append hprefix tailTrace_3407474
  have hstable : (prefixWord ++ tailWord_3407474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407474).length < 2 ^ (prefixWord ++ tailWord_3407474).sum := by decide
  have hdescent : baseEnd_3407474 < baseStart_3407474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407483 : List Nat := [1, 1, 1, 1, 1, 4, 13]
def baseStart_3407483 : Nat := 118140960795 + 3407483 * 2 ^ 59
def prefixEnd_3407483 : Nat := 4983230072969 + 3 ^ 40 * 3407483 * 2
def baseEnd_3407483 : Nat := 43201891383318442982513

theorem tailTrace_3407483 : CollatzResearch.WordTrace tailWord_3407483 prefixEnd_3407483 43201891383318442982513 := by
  unfold tailWord_3407483
  simp only [CollatzResearch.WordTrace]
  refine ⟨124281115114278517609963103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82854076742852345073308735 124281115114278517609963103)
  ·
    refine ⟨186421672671417776414944655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124281115114278517609963103 186421672671417776414944655)
    ·
      refine ⟨279632509007126664622416983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186421672671417776414944655 279632509007126664622416983)
      ·
        refine ⟨419448763510689996933625475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279632509007126664622416983 419448763510689996933625475)
        ·
          refine ⟨629173145266034995400438213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419448763510689996933625475 629173145266034995400438213)
          ·
            refine ⟨117969964737381561637582165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 629173145266034995400438213 117969964737381561637582165)
            ·
              refine ⟨43201891383318442982513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 117969964737381561637582165 43201891383318442982513)
              ·
                rfl

theorem cell22_3407483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 13].length) (baseStart_3407483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407483 prefixEnd_3407483 := by exact prefixLift 3407483
  have htrace : WordTrace (prefixWord ++ tailWord_3407483) baseStart_3407483 baseEnd_3407483 := by
    simpa [prefixWord, tailWord_3407483, baseEnd_3407483] using wordTrace_append hprefix tailTrace_3407483
  have hstable : (prefixWord ++ tailWord_3407483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407483).length < 2 ^ (prefixWord ++ tailWord_3407483).sum := by decide
  have hdescent : baseEnd_3407483 < baseStart_3407483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407534 : List Nat := [4, 1, 4, 1, 2, 2, 8]
def baseStart_3407534 : Nat := 118140960795 + 3407534 * 2 ^ 59
def prefixEnd_3407534 : Nat := 4983230072969 + 3 ^ 40 * 3407534 * 2
def baseEnd_3407534 : Nat := 43202537988587067685285

theorem tailTrace_3407534 : CollatzResearch.WordTrace tailWord_3407534 prefixEnd_3407534 43202537988587067685285 := by
  unfold tailWord_3407534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535371904636719165008707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82855316824729168880046437 15535371904636719165008707)
  ·
    refine ⟨23303057856955078747513061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535371904636719165008707 23303057856955078747513061)
    ·
      refine ⟨4369323348179077265158699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23303057856955078747513061 4369323348179077265158699)
      ·
        refine ⟨6553985022268615897738049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369323348179077265158699 6553985022268615897738049)
        ·
          refine ⟨4915488766701461923303537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6553985022268615897738049 4915488766701461923303537)
          ·
            refine ⟨3686616575026096442477653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4915488766701461923303537 3686616575026096442477653)
            ·
              refine ⟨43202537988587067685285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3686616575026096442477653 43202537988587067685285)
              ·
                rfl

theorem cell22_3407534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 8].length) (baseStart_3407534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407534 prefixEnd_3407534 := by exact prefixLift 3407534
  have htrace : WordTrace (prefixWord ++ tailWord_3407534) baseStart_3407534 baseEnd_3407534 := by
    simpa [prefixWord, tailWord_3407534, baseEnd_3407534] using wordTrace_append hprefix tailTrace_3407534
  have hstable : (prefixWord ++ tailWord_3407534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407534).length < 2 ^ (prefixWord ++ tailWord_3407534).sum := by decide
  have hdescent : baseEnd_3407534 < baseStart_3407534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407545 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 7]
def baseStart_3407545 : Nat := 118140960795 + 3407545 * 2 ^ 59
def prefixEnd_3407545 : Nat := 4983230072969 + 3 ^ 40 * 3407545 * 2
def baseEnd_3407545 : Nat := 388824097072216821825887

theorem tailTrace_3407545 : CollatzResearch.WordTrace tailWord_3407545 prefixEnd_3407545 388824097072216821825887 := by
  unfold tailWord_3407545
  simp only [CollatzResearch.WordTrace]
  refine ⟨124283376440053902198720089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82855584293369268132480059 124283376440053902198720089)
  ·
    refine ⟨93212532330040426649040067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124283376440053902198720089 93212532330040426649040067)
    ·
      refine ⟨139818798495060639973560101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93212532330040426649040067 139818798495060639973560101)
      ·
        refine ⟨26216024717823869995042519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139818798495060639973560101 26216024717823869995042519)
        ·
          refine ⟨39324037076735804992563779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26216024717823869995042519 39324037076735804992563779)
          ·
            refine ⟨58986055615103707488845669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39324037076735804992563779 58986055615103707488845669)
            ·
              refine ⟨11059885427831945154158563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58986055615103707488845669 11059885427831945154158563)
              ·
                refine ⟨16589828141747917731237845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11059885427831945154158563 16589828141747917731237845)
                ·
                  refine ⟨388824097072216821825887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16589828141747917731237845 388824097072216821825887)
                  ·
                    rfl

theorem cell22_3407545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_3407545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407545 prefixEnd_3407545 := by exact prefixLift 3407545
  have htrace : WordTrace (prefixWord ++ tailWord_3407545) baseStart_3407545 baseEnd_3407545 := by
    simpa [prefixWord, tailWord_3407545, baseEnd_3407545] using wordTrace_append hprefix tailTrace_3407545
  have hstable : (prefixWord ++ tailWord_3407545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407545).length < 2 ^ (prefixWord ++ tailWord_3407545).sum := by decide
  have hdescent : baseEnd_3407545 < baseStart_3407545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407560 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_3407560 : Nat := 118140960795 + 3407560 * 2 ^ 59
def prefixEnd_3407560 : Nat := 4983230072969 + 3 ^ 40 * 3407560 * 2
def baseEnd_3407560 : Nat := 1166477426023195426352615

theorem tailTrace_3407560 : CollatzResearch.WordTrace tailWord_3407560 prefixEnd_3407560 1166477426023195426352615 := by
  unfold tailWord_3407560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62141961767499779880258067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82855949023333039840344089 62141961767499779880258067)
  ·
    refine ⟨93212942651249669820387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62141961767499779880258067 93212942651249669820387101)
    ·
      refine ⟨34954853494218626182645163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93212942651249669820387101 34954853494218626182645163)
      ·
        refine ⟨52432280241327939273967745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34954853494218626182645163 52432280241327939273967745)
        ·
          refine ⟨39324210180995954455475809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52432280241327939273967745 39324210180995954455475809)
          ·
            refine ⟨29493157635746965841606857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39324210180995954455475809 29493157635746965841606857)
            ·
              refine ⟨22119868226810224381205143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29493157635746965841606857 22119868226810224381205143)
              ·
                refine ⟨33179802340215336571807715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22119868226810224381205143 33179802340215336571807715)
                ·
                  refine ⟨49769703510323004857711573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33179802340215336571807715 49769703510323004857711573)
                  ·
                    refine ⟨1166477426023195426352615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49769703510323004857711573 1166477426023195426352615)
                    ·
                      rfl

theorem cell22_3407560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_3407560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407560 prefixEnd_3407560 := by exact prefixLift 3407560
  have htrace : WordTrace (prefixWord ++ tailWord_3407560) baseStart_3407560 baseEnd_3407560 := by
    simpa [prefixWord, tailWord_3407560, baseEnd_3407560] using wordTrace_append hprefix tailTrace_3407560
  have hstable : (prefixWord ++ tailWord_3407560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407560).length < 2 ^ (prefixWord ++ tailWord_3407560).sum := by decide
  have hdescent : baseEnd_3407560 < baseStart_3407560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407637 : List Nat := [1, 3, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3407637 : Nat := 118140960795 + 3407637 * 2 ^ 59
def prefixEnd_3407637 : Nat := 4983230072969 + 3 ^ 40 * 3407637 * 2
def baseEnd_3407637 : Nat := 1166503784696792892177379

theorem tailTrace_3407637 : CollatzResearch.WordTrace tailWord_3407637 prefixEnd_3407637 1166503784696792892177379 := by
  unfold tailWord_3407637
  simp only [CollatzResearch.WordTrace]
  refine ⟨124286731955720601911069165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82857821303813734607379443 124286731955720601911069165)
  ·
    refine ⟨46607524483395225716650937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124286731955720601911069165 46607524483395225716650937)
    ·
      refine ⟨34955643362546419287488203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46607524483395225716650937 34955643362546419287488203)
      ·
        refine ⟨52433465043819628931232305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34955643362546419287488203 52433465043819628931232305)
        ·
          refine ⟨39325098782864721698424229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52433465043819628931232305 39325098782864721698424229)
          ·
            refine ⟨7373456021787135318454543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39325098782864721698424229 7373456021787135318454543)
            ·
              refine ⟨11060184032680702977681815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7373456021787135318454543 11060184032680702977681815)
              ·
                refine ⟨16590276049021054466522723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060184032680702977681815 16590276049021054466522723)
                ·
                  refine ⟨24885414073531581699784085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16590276049021054466522723 24885414073531581699784085)
                  ·
                    refine ⟨1166503784696792892177379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24885414073531581699784085 1166503784696792892177379)
                    ·
                      rfl

theorem cell22_3407637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3407637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407637 prefixEnd_3407637 := by exact prefixLift 3407637
  have htrace : WordTrace (prefixWord ++ tailWord_3407637) baseStart_3407637 baseEnd_3407637 := by
    simpa [prefixWord, tailWord_3407637, baseEnd_3407637] using wordTrace_append hprefix tailTrace_3407637
  have hstable : (prefixWord ++ tailWord_3407637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407637).length < 2 ^ (prefixWord ++ tailWord_3407637).sum := by decide
  have hdescent : baseEnd_3407637 < baseStart_3407637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407652 : List Nat := [2, 3, 1, 3, 2, 2, 9]
def baseStart_3407652 : Nat := 118140960795 + 3407652 * 2 ^ 59
def prefixEnd_3407652 : Nat := 4983230072969 + 3 ^ 40 * 3407652 * 2
def baseEnd_3407652 : Nat := 43204034055679179742679

theorem tailTrace_3407652 : CollatzResearch.WordTrace tailWord_3407652 prefixEnd_3407652 43204034055679179742679 := by
  unfold tailWord_3407652
  simp only [CollatzResearch.WordTrace]
  refine ⟨62143639525333129736432605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82858186033777506315243473 62143639525333129736432605)
  ·
    refine ⟨23303864821999923651162227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62143639525333129736432605 23303864821999923651162227)
    ·
      refine ⟨34955797232999885476743341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23303864821999923651162227 34955797232999885476743341)
      ·
        refine ⟨13108423962374957053778753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34955797232999885476743341 13108423962374957053778753)
        ·
          refine ⟨9831317971781217790334065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108423962374957053778753 9831317971781217790334065)
          ·
            refine ⟨7373488478835913342750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9831317971781217790334065 7373488478835913342750549)
            ·
              refine ⟨43204034055679179742679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7373488478835913342750549 43204034055679179742679)
              ·
                rfl

theorem cell22_3407652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 9].length) (baseStart_3407652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407652 prefixEnd_3407652 := by exact prefixLift 3407652
  have htrace : WordTrace (prefixWord ++ tailWord_3407652) baseStart_3407652 baseEnd_3407652 := by
    simpa [prefixWord, tailWord_3407652, baseEnd_3407652] using wordTrace_append hprefix tailTrace_3407652
  have hstable : (prefixWord ++ tailWord_3407652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407652).length < 2 ^ (prefixWord ++ tailWord_3407652).sum := by decide
  have hdescent : baseEnd_3407652 < baseStart_3407652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407656 : List Nat := [2, 1, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_3407656 : Nat := 118140960795 + 3407656 * 2 ^ 59
def prefixEnd_3407656 : Nat := 4983230072969 + 3 ^ 40 * 3407656 * 2
def baseEnd_3407656 : Nat := 1166510288785083175952321

theorem tailTrace_3407656 : CollatzResearch.WordTrace tailWord_3407656 prefixEnd_3407656 1166510288785083175952321 := by
  unfold tailWord_3407656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62143712471325884078005411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82858283295101178770673881 62143712471325884078005411)
  ·
    refine ⟨93215568706988826117008117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62143712471325884078005411 93215568706988826117008117)
    ·
      refine ⟨8738959566280202448469511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93215568706988826117008117 8738959566280202448469511)
      ·
        refine ⟨13108439349420303672704267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8738959566280202448469511 13108439349420303672704267)
        ·
          refine ⟨19662659024130455509056401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13108439349420303672704267 19662659024130455509056401)
          ·
            refine ⟨14746994268097841631792301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19662659024130455509056401 14746994268097841631792301)
            ·
              refine ⟨5530122850536690611922113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14746994268097841631792301 5530122850536690611922113)
              ·
                refine ⟨4147592137902517958941585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5530122850536690611922113 4147592137902517958941585)
                ·
                  refine ⟨3110694103426888469206189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147592137902517958941585 3110694103426888469206189)
                  ·
                    refine ⟨1166510288785083175952321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110694103426888469206189 1166510288785083175952321)
                    ·
                      rfl

theorem cell22_3407656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_3407656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407656 prefixEnd_3407656 := by exact prefixLift 3407656
  have htrace : WordTrace (prefixWord ++ tailWord_3407656) baseStart_3407656 baseEnd_3407656 := by
    simpa [prefixWord, tailWord_3407656, baseEnd_3407656] using wordTrace_append hprefix tailTrace_3407656
  have hstable : (prefixWord ++ tailWord_3407656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407656).length < 2 ^ (prefixWord ++ tailWord_3407656).sum := by decide
  have hdescent : baseEnd_3407656 < baseStart_3407656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407673 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_3407673 : Nat := 118140960795 + 3407673 * 2 ^ 59
def prefixEnd_3407673 : Nat := 4983230072969 + 3 ^ 40 * 3407673 * 2
def baseEnd_3407673 : Nat := 1166516108232500798277269

theorem tailTrace_3407673 : CollatzResearch.WordTrace tailWord_3407673 prefixEnd_3407673 1166516108232500798277269 := by
  unfold tailWord_3407673
  simp only [CollatzResearch.WordTrace]
  refine ⟨124288044983590180059379673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82858696655726786706253115 124288044983590180059379673)
  ·
    refine ⟨93216033737692635044534755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124288044983590180059379673 93216033737692635044534755)
    ·
      refine ⟨139824050606538952566802133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93216033737692635044534755 139824050606538952566802133)
      ·
        refine ⟨3277126186090756700784425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139824050606538952566802133 3277126186090756700784425)
        ·
          refine ⟨2457844639568067525588319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277126186090756700784425 2457844639568067525588319)
          ·
            refine ⟨3686766959352101288382479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457844639568067525588319 3686766959352101288382479)
            ·
              refine ⟨5530150439028151932573719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686766959352101288382479 5530150439028151932573719)
              ·
                refine ⟨8295225658542227898860579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530150439028151932573719 8295225658542227898860579)
                ·
                  refine ⟨12442838487813341848290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8295225658542227898860579 12442838487813341848290869)
                  ·
                    refine ⟨1166516108232500798277269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12442838487813341848290869 1166516108232500798277269)
                    ·
                      rfl

theorem cell22_3407673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_3407673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407673 prefixEnd_3407673 := by exact prefixLift 3407673
  have htrace : WordTrace (prefixWord ++ tailWord_3407673) baseStart_3407673 baseEnd_3407673 := by
    simpa [prefixWord, tailWord_3407673, baseEnd_3407673] using wordTrace_append hprefix tailTrace_3407673
  have hstable : (prefixWord ++ tailWord_3407673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407673).length < 2 ^ (prefixWord ++ tailWord_3407673).sum := by decide
  have hdescent : baseEnd_3407673 < baseStart_3407673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407686 : List Nat := [6, 1, 1, 2, 1, 2, 1, 8]
def baseStart_3407686 : Nat := 118140960795 + 3407686 * 2 ^ 59
def prefixEnd_3407686 : Nat := 4983230072969 + 3 ^ 40 * 3407686 * 2
def baseEnd_3407686 : Nat := 129613395377574788633581

theorem tailTrace_3407686 : CollatzResearch.WordTrace tailWord_3407686 prefixEnd_3407686 129613395377574788633581 := by
  unfold tailWord_3407686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884016222891971352487591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82859012755028722186401941 3884016222891971352487591)
  ·
    refine ⟨5826024334337957028731387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3884016222891971352487591 5826024334337957028731387)
    ·
      refine ⟨8739036501506935543097081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5826024334337957028731387 8739036501506935543097081)
      ·
        refine ⟨6554277376130201657322811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8739036501506935543097081 6554277376130201657322811)
        ·
          refine ⟨9831416064195302485984217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6554277376130201657322811 9831416064195302485984217)
          ·
            refine ⟨7373562048146476864488163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9831416064195302485984217 7373562048146476864488163)
            ·
              refine ⟨11060343072219715296732245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7373562048146476864488163 11060343072219715296732245)
              ·
                refine ⟨129613395377574788633581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11060343072219715296732245 129613395377574788633581)
                ·
                  rfl

theorem cell22_3407686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_3407686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407686 prefixEnd_3407686 := by exact prefixLift 3407686
  have htrace : WordTrace (prefixWord ++ tailWord_3407686) baseStart_3407686 baseEnd_3407686 := by
    simpa [prefixWord, tailWord_3407686, baseEnd_3407686] using wordTrace_append hprefix tailTrace_3407686
  have hstable : (prefixWord ++ tailWord_3407686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407686).length < 2 ^ (prefixWord ++ tailWord_3407686).sum := by decide
  have hdescent : baseEnd_3407686 < baseStart_3407686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407697 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 7]
def baseStart_3407697 : Nat := 118140960795 + 3407697 * 2 ^ 59
def prefixEnd_3407697 : Nat := 4983230072969 + 3 ^ 40 * 3407697 * 2
def baseEnd_3407697 : Nat := 388841441307657578559065

theorem tailTrace_3407697 : CollatzResearch.WordTrace tailWord_3407697 prefixEnd_3407697 388841441307657578559065 := by
  unfold tailWord_3407697
  simp only [CollatzResearch.WordTrace]
  refine ⟨124288920335503232158253345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82859280223668821438835563 124288920335503232158253345)
  ·
    refine ⟨93216690251627424118690009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124288920335503232158253345 93216690251627424118690009)
    ·
      refine ⟨69912517688720568089017507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93216690251627424118690009 69912517688720568089017507)
      ·
        refine ⟨104868776533080852133526261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69912517688720568089017507 104868776533080852133526261)
        ·
          refine ⟨9831447799976329887518087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104868776533080852133526261 9831447799976329887518087)
          ·
            refine ⟨14747171699964494831277131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831447799976329887518087 14747171699964494831277131)
            ·
              refine ⟨22120757549946742246915697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14747171699964494831277131 22120757549946742246915697)
              ·
                refine ⟨16590568162460056685186773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22120757549946742246915697 16590568162460056685186773)
                ·
                  refine ⟨388841441307657578559065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16590568162460056685186773 388841441307657578559065)
                  ·
                    rfl

theorem cell22_3407697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_3407697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407697 prefixEnd_3407697 := by exact prefixLift 3407697
  have htrace : WordTrace (prefixWord ++ tailWord_3407697) baseStart_3407697 baseEnd_3407697 := by
    simpa [prefixWord, tailWord_3407697, baseEnd_3407697] using wordTrace_append hprefix tailTrace_3407697
  have hstable : (prefixWord ++ tailWord_3407697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407697).length < 2 ^ (prefixWord ++ tailWord_3407697).sum := by decide
  have hdescent : baseEnd_3407697 < baseStart_3407697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407714 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3407714 : Nat := 118140960795 + 3407714 * 2 ^ 59
def prefixEnd_3407714 : Nat := 4983230072969 + 3 ^ 40 * 3407714 * 2
def baseEnd_3407714 : Nat := 388843381123463452667381

theorem tailTrace_3407714 : CollatzResearch.WordTrace tailWord_3407714 prefixEnd_3407714 388843381123463452667381 := by
  unfold tailWord_3407714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31072385094110411015405549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82859693584294429374414797 31072385094110411015405549)
  ·
    refine ⟨11652144410291404130777081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31072385094110411015405549 11652144410291404130777081)
    ·
      refine ⟨8739108307718553098082811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11652144410291404130777081 8739108307718553098082811)
      ·
        refine ⟨13108662461577829647124217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8739108307718553098082811 13108662461577829647124217)
        ·
          refine ⟨9831496846183372235343163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13108662461577829647124217 9831496846183372235343163)
          ·
            refine ⟨14747245269275058353014745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9831496846183372235343163 14747245269275058353014745)
            ·
              refine ⟨11060433951956293764761059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14747245269275058353014745 11060433951956293764761059)
              ·
                refine ⟨16590650927934440647141589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11060433951956293764761059 16590650927934440647141589)
                ·
                  refine ⟨388843381123463452667381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16590650927934440647141589 388843381123463452667381)
                  ·
                    rfl

theorem cell22_3407714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3407714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407714 prefixEnd_3407714 := by exact prefixLift 3407714
  have htrace : WordTrace (prefixWord ++ tailWord_3407714) baseStart_3407714 baseEnd_3407714 := by
    simpa [prefixWord, tailWord_3407714, baseEnd_3407714] using wordTrace_append hprefix tailTrace_3407714
  have hstable : (prefixWord ++ tailWord_3407714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407714).length < 2 ^ (prefixWord ++ tailWord_3407714).sum := by decide
  have hdescent : baseEnd_3407714 < baseStart_3407714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407802 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_3407802 : Nat := 118140960795 + 3407802 * 2 ^ 59
def prefixEnd_3407802 : Nat := 4983230072969 + 3 ^ 40 * 3407802 * 2
def baseEnd_3407802 : Nat := 1166560267568787461801873

theorem tailTrace_3407802 : CollatzResearch.WordTrace tailWord_3407802 prefixEnd_3407802 1166560267568787461801873 := by
  unfold tailWord_3407802
  simp only [CollatzResearch.WordTrace]
  refine ⟨31073187500030708772706415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82861833333415223393883773 31073187500030708772706415)
  ·
    refine ⟨46609781250046063159059623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31073187500030708772706415 46609781250046063159059623)
    ·
      refine ⟨69914671875069094738589435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46609781250046063159059623 69914671875069094738589435)
      ·
        refine ⟨104872007812603642107884153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69914671875069094738589435 104872007812603642107884153)
        ·
          refine ⟨78654005859452731580913115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104872007812603642107884153 78654005859452731580913115)
          ·
            refine ⟨117981008789179097371369673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78654005859452731580913115 117981008789179097371369673)
            ·
              refine ⟨88485756591884323028527255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117981008789179097371369673 88485756591884323028527255)
              ·
                refine ⟨132728634887826484542790883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88485756591884323028527255 132728634887826484542790883)
                ·
                  refine ⟨199092952331739726814186325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 132728634887826484542790883 199092952331739726814186325)
                  ·
                    refine ⟨1166560267568787461801873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199092952331739726814186325 1166560267568787461801873)
                    ·
                      rfl

theorem cell22_3407802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_3407802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407802 prefixEnd_3407802 := by exact prefixLift 3407802
  have htrace : WordTrace (prefixWord ++ tailWord_3407802) baseStart_3407802 baseEnd_3407802 := by
    simpa [prefixWord, tailWord_3407802, baseEnd_3407802] using wordTrace_append hprefix tailTrace_3407802
  have hstable : (prefixWord ++ tailWord_3407802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407802).length < 2 ^ (prefixWord ++ tailWord_3407802).sum := by decide
  have hdescent : baseEnd_3407802 < baseStart_3407802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407806 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3407806 : Nat := 118140960795 + 3407806 * 2 ^ 59
def prefixEnd_3407806 : Nat := 4983230072969 + 3 ^ 40 * 3407806 * 2
def baseEnd_3407806 : Nat := 1166561636850532784701861

theorem tailTrace_3407806 : CollatzResearch.WordTrace tailWord_3407806 prefixEnd_3407806 1166561636850532784701861 := by
  unfold tailWord_3407806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15536611986513542971746409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82861930594738895849314181 15536611986513542971746409)
  ·
    refine ⟨11652458989885157228809807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15536611986513542971746409 11652458989885157228809807)
    ·
      refine ⟨17478688484827735843214711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11652458989885157228809807 17478688484827735843214711)
      ·
        refine ⟨26218032727241603764822067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17478688484827735843214711 26218032727241603764822067)
        ·
          refine ⟨39327049090862405647233101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26218032727241603764822067 39327049090862405647233101)
          ·
            refine ⟨14747643409073402117712413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39327049090862405647233101 14747643409073402117712413)
            ·
              refine ⟨5530366278402525794142155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14747643409073402117712413 5530366278402525794142155)
              ·
                refine ⟨8295549417603788691213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530366278402525794142155 8295549417603788691213233)
                ·
                  refine ⟨6221662063202841518409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8295549417603788691213233 6221662063202841518409925)
                  ·
                    refine ⟨1166561636850532784701861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6221662063202841518409925 1166561636850532784701861)
                    ·
                      rfl

theorem cell22_3407806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3407806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407806 prefixEnd_3407806 := by exact prefixLift 3407806
  have htrace : WordTrace (prefixWord ++ tailWord_3407806) baseStart_3407806 baseEnd_3407806 := by
    simpa [prefixWord, tailWord_3407806, baseEnd_3407806] using wordTrace_append hprefix tailTrace_3407806
  have hstable : (prefixWord ++ tailWord_3407806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407806).length < 2 ^ (prefixWord ++ tailWord_3407806).sum := by decide
  have hdescent : baseEnd_3407806 < baseStart_3407806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407817 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_3407817 : Nat := 118140960795 + 3407817 * 2 ^ 59
def prefixEnd_3407817 : Nat := 4983230072969 + 3 ^ 40 * 3407817 * 2
def baseEnd_3407817 : Nat := 1166565402375332422676827

theorem tailTrace_3407817 : CollatzResearch.WordTrace tailWord_3407817 prefixEnd_3407817 1166565402375332422676827 := by
  unfold tailWord_3407817
  simp only [CollatzResearch.WordTrace]
  refine ⟨124293297095068492652621705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82862198063378995101747803 124293297095068492652621705)
  ·
    refine ⟨93219972821301369489466279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124293297095068492652621705 93219972821301369489466279)
    ·
      refine ⟨139829959231952054234199419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93219972821301369489466279 139829959231952054234199419)
      ·
        refine ⟨209744938847928081351299129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139829959231952054234199419 209744938847928081351299129)
        ·
          refine ⟨157308704135946061013474347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209744938847928081351299129 157308704135946061013474347)
          ·
            refine ⟨235963056203919091520211521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157308704135946061013474347 235963056203919091520211521)
            ·
              refine ⟨176972292152939318640158641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235963056203919091520211521 176972292152939318640158641)
              ·
                refine ⟨132729219114704488980118981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 176972292152939318640158641 132729219114704488980118981)
                ·
                  refine ⟨24886728584007091683772309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132729219114704488980118981 24886728584007091683772309)
                  ·
                    refine ⟨1166565402375332422676827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24886728584007091683772309 1166565402375332422676827)
                    ·
                      rfl

theorem cell22_3407817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_3407817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407817 prefixEnd_3407817 := by exact prefixLift 3407817
  have htrace : WordTrace (prefixWord ++ tailWord_3407817) baseStart_3407817 baseEnd_3407817 := by
    simpa [prefixWord, tailWord_3407817, baseEnd_3407817] using wordTrace_append hprefix tailTrace_3407817
  have hstable : (prefixWord ++ tailWord_3407817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407817).length < 2 ^ (prefixWord ++ tailWord_3407817).sum := by decide
  have hdescent : baseEnd_3407817 < baseStart_3407817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407819 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 5, 3]
def baseStart_3407819 : Nat := 118140960795 + 3407819 * 2 ^ 59
def prefixEnd_3407819 : Nat := 4983230072969 + 3 ^ 40 * 3407819 * 2
def baseEnd_3407819 : Nat := 1166566087016205084126821

theorem tailTrace_3407819 : CollatzResearch.WordTrace tailWord_3407819 prefixEnd_3407819 1166566087016205084126821 := by
  unfold tailWord_3407819
  simp only [CollatzResearch.WordTrace]
  refine ⟨124293370041061246994194511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82862246694040831329463007 124293370041061246994194511)
  ·
    refine ⟨186440055061591870491291767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124293370041061246994194511 186440055061591870491291767)
    ·
      refine ⟨279660082592387805736937651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186440055061591870491291767 279660082592387805736937651)
      ·
        refine ⟨419490123888581708605406477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279660082592387805736937651 419490123888581708605406477)
        ·
          refine ⟨157308796458218140727027429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419490123888581708605406477 157308796458218140727027429)
          ·
            refine ⟨29495399335915901386317643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157308796458218140727027429 29495399335915901386317643)
            ·
              refine ⟨44243099003873852079476465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29495399335915901386317643 44243099003873852079476465)
              ·
                refine ⟨33182324252905389059607349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44243099003873852079476465 33182324252905389059607349)
                ·
                  refine ⟨3110842898709880224338189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33182324252905389059607349 3110842898709880224338189)
                  ·
                    refine ⟨1166566087016205084126821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110842898709880224338189 1166566087016205084126821)
                    ·
                      rfl

theorem cell22_3407819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 3].length) (baseStart_3407819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407819 prefixEnd_3407819 := by exact prefixLift 3407819
  have htrace : WordTrace (prefixWord ++ tailWord_3407819) baseStart_3407819 baseEnd_3407819 := by
    simpa [prefixWord, tailWord_3407819, baseEnd_3407819] using wordTrace_append hprefix tailTrace_3407819
  have hstable : (prefixWord ++ tailWord_3407819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407819).length < 2 ^ (prefixWord ++ tailWord_3407819).sum := by decide
  have hdescent : baseEnd_3407819 < baseStart_3407819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407842 : List Nat := [3, 3, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_3407842 : Nat := 118140960795 + 3407842 * 2 ^ 59
def prefixEnd_3407842 : Nat := 4983230072969 + 3 ^ 40 * 3407842 * 2
def baseEnd_3407842 : Nat := 1166573960386240690801751

theorem tailTrace_3407842 : CollatzResearch.WordTrace tailWord_3407842 prefixEnd_3407842 1166573960386240690801751 := by
  unfold tailWord_3407842
  simp only [CollatzResearch.WordTrace]
  refine ⟨31073552229994480480570445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82862805946651947948187853 31073552229994480480570445)
  ·
    refine ⟨11652582086247930180213917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31073552229994480480570445 11652582086247930180213917)
    ·
      refine ⟨4369718282342973817580219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11652582086247930180213917 4369718282342973817580219)
      ·
        refine ⟨6554577423514460726370329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369718282342973817580219 6554577423514460726370329)
        ·
          refine ⟨4915933067635845544777747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554577423514460726370329 4915933067635845544777747)
          ·
            refine ⟨7373899601453768317166621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4915933067635845544777747 7373899601453768317166621)
            ·
              refine ⟨2765212350545163118937483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7373899601453768317166621 2765212350545163118937483)
              ·
                refine ⟨4147818525817744678406225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765212350545163118937483 4147818525817744678406225)
                ·
                  refine ⟨3110863894363308508804669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147818525817744678406225 3110863894363308508804669)
                  ·
                    refine ⟨1166573960386240690801751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110863894363308508804669 1166573960386240690801751)
                    ·
                      rfl

theorem cell22_3407842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_3407842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407842 prefixEnd_3407842 := by exact prefixLift 3407842
  have htrace : WordTrace (prefixWord ++ tailWord_3407842) baseStart_3407842 baseEnd_3407842 := by
    simpa [prefixWord, tailWord_3407842, baseEnd_3407842] using wordTrace_append hprefix tailTrace_3407842
  have hstable : (prefixWord ++ tailWord_3407842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407842).length < 2 ^ (prefixWord ++ tailWord_3407842).sum := by decide
  have hdescent : baseEnd_3407842 < baseStart_3407842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407943 : List Nat := [1, 1, 4, 1, 3, 1, 4, 2, 2, 3]
def baseStart_3407943 : Nat := 118140960795 + 3407943 * 2 ^ 59
def prefixEnd_3407943 : Nat := 4983230072969 + 3 ^ 40 * 3407943 * 2
def baseEnd_3407943 : Nat := 1166608534750310094026441

theorem tailTrace_3407943 : CollatzResearch.WordTrace tailWord_3407943 prefixEnd_3407943 1166608534750310094026441 := by
  unfold tailWord_3407943
  simp only [CollatzResearch.WordTrace]
  refine ⟨124297892692612016171708483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82865261795074677447805655 124297892692612016171708483)
  ·
    refine ⟨186446839038918024257562725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124297892692612016171708483 186446839038918024257562725)
    ·
      refine ⟨34958782319797129548293011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186446839038918024257562725 34958782319797129548293011)
      ·
        refine ⟨52438173479695694322439517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34958782319797129548293011 52438173479695694322439517)
        ·
          refine ⟨19664315054885885370914819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52438173479695694322439517 19664315054885885370914819)
          ·
            refine ⟨29496472582328828056372229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19664315054885885370914819 29496472582328828056372229)
            ·
              refine ⟨5530588609186655260569793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29496472582328828056372229 5530588609186655260569793)
              ·
                refine ⟨4147941456889991445427345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5530588609186655260569793 4147941456889991445427345)
                ·
                  refine ⟨3110956092667493584070509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4147941456889991445427345 3110956092667493584070509)
                  ·
                    refine ⟨1166608534750310094026441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110956092667493584070509 1166608534750310094026441)
                    ·
                      rfl

theorem cell22_3407943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_3407943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407943 prefixEnd_3407943 := by exact prefixLift 3407943
  have htrace : WordTrace (prefixWord ++ tailWord_3407943) baseStart_3407943 baseEnd_3407943 := by
    simpa [prefixWord, tailWord_3407943, baseEnd_3407943] using wordTrace_append hprefix tailTrace_3407943
  have hstable : (prefixWord ++ tailWord_3407943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407943).length < 2 ^ (prefixWord ++ tailWord_3407943).sum := by decide
  have hdescent : baseEnd_3407943 < baseStart_3407943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407969 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3407969 : Nat := 118140960795 + 3407969 * 2 ^ 59
def prefixEnd_3407969 : Nat := 4983230072969 + 3 ^ 40 * 3407969 * 2
def baseEnd_3407969 : Nat := 1166617435081654692876361

theorem tailTrace_3407969 : CollatzResearch.WordTrace tailWord_3407969 prefixEnd_3407969 1166617435081654692876361 := by
  unfold tailWord_3407969
  simp only [CollatzResearch.WordTrace]
  refine ⟨124298840990517822612154961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82865893993678548408103307 124298840990517822612154961)
  ·
    refine ⟨93224130742888366959116221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124298840990517822612154961 93224130742888366959116221)
    ·
      refine ⟨34959049028583137609668583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93224130742888366959116221 34959049028583137609668583)
      ·
        refine ⟨52438573542874706414502875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34959049028583137609668583 52438573542874706414502875)
        ·
          refine ⟨78657860314312059621754313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52438573542874706414502875 78657860314312059621754313)
          ·
            refine ⟨58993395235734044716315735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78657860314312059621754313 58993395235734044716315735)
            ·
              refine ⟨88490092853601067074473603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58993395235734044716315735 88490092853601067074473603)
              ·
                refine ⟨132735139280401600611710405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88490092853601067074473603 132735139280401600611710405)
                ·
                  refine ⟨24887838615075300114695701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132735139280401600611710405 24887838615075300114695701)
                  ·
                    refine ⟨1166617435081654692876361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24887838615075300114695701 1166617435081654692876361)
                    ·
                      rfl

theorem cell22_3407969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3407969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407969 prefixEnd_3407969 := by exact prefixLift 3407969
  have htrace : WordTrace (prefixWord ++ tailWord_3407969) baseStart_3407969 baseEnd_3407969 := by
    simpa [prefixWord, tailWord_3407969, baseEnd_3407969] using wordTrace_append hprefix tailTrace_3407969
  have hstable : (prefixWord ++ tailWord_3407969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407969).length < 2 ^ (prefixWord ++ tailWord_3407969).sum := by decide
  have hdescent : baseEnd_3407969 < baseStart_3407969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3407971 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 5, 3]
def baseStart_3407971 : Nat := 118140960795 + 3407971 * 2 ^ 59
def prefixEnd_3407971 : Nat := 4983230072969 + 3 ^ 40 * 3407971 * 2
def baseEnd_3407971 : Nat := 1166618119722527354326355

theorem tailTrace_3407971 : CollatzResearch.WordTrace tailWord_3407971 prefixEnd_3407971 1166618119722527354326355 := by
  unfold tailWord_3407971
  simp only [CollatzResearch.WordTrace]
  refine ⟨124298913936510576953727767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82865942624340384635818511 124298913936510576953727767)
  ·
    refine ⟨186448370904765865430591651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124298913936510576953727767 186448370904765865430591651)
    ·
      refine ⟨279672556357148798145887477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186448370904765865430591651 279672556357148798145887477)
      ·
        refine ⟨26219302158482699826176951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 279672556357148798145887477 26219302158482699826176951)
        ·
          refine ⟨39328953237724049739265427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26219302158482699826176951 39328953237724049739265427)
          ·
            refine ⟨58993429856586074608898141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39328953237724049739265427 58993429856586074608898141)
            ·
              refine ⟨22122536196219777978336803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58993429856586074608898141 22122536196219777978336803)
              ·
                refine ⟨33183804294329666967505205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22122536196219777978336803 33183804294329666967505205)
                ·
                  refine ⟨3110981652593406278203613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33183804294329666967505205 3110981652593406278203613)
                  ·
                    refine ⟨1166618119722527354326355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3110981652593406278203613 1166618119722527354326355)
                    ·
                      rfl

theorem cell22_3407971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 3].length) (baseStart_3407971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3407971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3407971 prefixEnd_3407971 := by exact prefixLift 3407971
  have htrace : WordTrace (prefixWord ++ tailWord_3407971) baseStart_3407971 baseEnd_3407971 := by
    simpa [prefixWord, tailWord_3407971, baseEnd_3407971] using wordTrace_append hprefix tailTrace_3407971
  have hstable : (prefixWord ++ tailWord_3407971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3407971).length < 2 ^ (prefixWord ++ tailWord_3407971).sum := by decide
  have hdescent : baseEnd_3407971 < baseStart_3407971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3407971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408005 : List Nat := [1, 3, 1, 1, 5, 1, 2, 4, 1, 3]
def baseStart_3408005 : Nat := 118140960795 + 3408005 * 2 ^ 59
def prefixEnd_3408005 : Nat := 4983230072969 + 3 ^ 40 * 3408005 * 2
def baseEnd_3408005 : Nat := 1166629758617362598976251

theorem tailTrace_3408005 : CollatzResearch.WordTrace tailWord_3408005 prefixEnd_3408005 1166629758617362598976251 := by
  unfold tailWord_3408005
  simp only [CollatzResearch.WordTrace]
  refine ⟨124300154018387400760465469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82866769345591600506976979 124300154018387400760465469)
  ·
    refine ⟨46612557756895275285174551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124300154018387400760465469 46612557756895275285174551)
    ·
      refine ⟨69918836635342912927761827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46612557756895275285174551 69918836635342912927761827)
      ·
        refine ⟨104878254953014369391642741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69918836635342912927761827 104878254953014369391642741)
        ·
          refine ⟨9832336401845097130466507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104878254953014369391642741 9832336401845097130466507)
          ·
            refine ⟨14748504602767645695699761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832336401845097130466507 14748504602767645695699761)
            ·
              refine ⟨11061378452075734271774821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14748504602767645695699761 11061378452075734271774821)
              ·
                refine ⟨2074008459764200175957779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11061378452075734271774821 2074008459764200175957779)
                ·
                  refine ⟨3111012689646300263936669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074008459764200175957779 3111012689646300263936669)
                  ·
                    refine ⟨1166629758617362598976251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111012689646300263936669 1166629758617362598976251)
                    ·
                      rfl

theorem cell22_3408005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_3408005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408005 prefixEnd_3408005 := by exact prefixLift 3408005
  have htrace : WordTrace (prefixWord ++ tailWord_3408005) baseStart_3408005 baseEnd_3408005 := by
    simpa [prefixWord, tailWord_3408005, baseEnd_3408005] using wordTrace_append hprefix tailTrace_3408005
  have hstable : (prefixWord ++ tailWord_3408005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408005).length < 2 ^ (prefixWord ++ tailWord_3408005).sum := by decide
  have hdescent : baseEnd_3408005 < baseStart_3408005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408039 : List Nat := [1, 1, 6, 2, 2, 2, 1, 3, 1, 3]
def baseStart_3408039 : Nat := 118140960795 + 3408039 * 2 ^ 59
def prefixEnd_3408039 : Nat := 4983230072969 + 3 ^ 40 * 3408039 * 2
def baseEnd_3408039 : Nat := 1166641397512197843626147

theorem tailTrace_3408039 : CollatzResearch.WordTrace tailWord_3408039 prefixEnd_3408039 1166641397512197843626147 := by
  unfold tailWord_3408039
  simp only [CollatzResearch.WordTrace]
  refine ⟨124301394100264224567203171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82867596066842816378135447 124301394100264224567203171)
  ·
    refine ⟨186452091150396336850804757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124301394100264224567203171 186452091150396336850804757)
    ·
      refine ⟨8739941772674828289881473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186452091150396336850804757 8739941772674828289881473)
      ·
        refine ⟨6554956329506121217411105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8739941772674828289881473 6554956329506121217411105)
        ·
          refine ⟨4916217247129590913058329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554956329506121217411105 4916217247129590913058329)
          ·
            refine ⟨3687162935347193184793747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916217247129590913058329 3687162935347193184793747)
            ·
              refine ⟨5530744403020789777190621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687162935347193184793747 5530744403020789777190621)
              ·
                refine ⟨2074029151132796166446483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5530744403020789777190621 2074029151132796166446483)
                ·
                  refine ⟨3111043726699194249669725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074029151132796166446483 3111043726699194249669725)
                  ·
                    refine ⟨1166641397512197843626147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111043726699194249669725 1166641397512197843626147)
                    ·
                      rfl

theorem cell22_3408039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_3408039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408039 prefixEnd_3408039 := by exact prefixLift 3408039
  have htrace : WordTrace (prefixWord ++ tailWord_3408039) baseStart_3408039 baseEnd_3408039 := by
    simpa [prefixWord, tailWord_3408039, baseEnd_3408039] using wordTrace_append hprefix tailTrace_3408039
  have hstable : (prefixWord ++ tailWord_3408039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408039).length < 2 ^ (prefixWord ++ tailWord_3408039).sum := by decide
  have hdescent : baseEnd_3408039 < baseStart_3408039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408170 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_3408170 : Nat := 118140960795 + 3408170 * 2 ^ 59
def prefixEnd_3408170 : Nat := 4983230072969 + 3 ^ 40 * 3408170 * 2
def baseEnd_3408170 : Nat := 388895413829785722866915

theorem tailTrace_3408170 : CollatzResearch.WordTrace tailWord_3408170 prefixEnd_3408170 388895413829785722866915 := by
  unfold tailWord_3408170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076543015697408485055491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82870781375193089293481309 31076543015697408485055491)
  ·
    refine ⟨46614814523546112727583237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31076543015697408485055491 46614814523546112727583237)
    ·
      refine ⟨8740277723164896136421857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46614814523546112727583237 8740277723164896136421857)
      ·
        refine ⟨6555208292373672102316393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8740277723164896136421857 6555208292373672102316393)
        ·
          refine ⟨4916406219280254076737295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6555208292373672102316393 4916406219280254076737295)
          ·
            refine ⟨7374609328920381115105943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916406219280254076737295 7374609328920381115105943)
            ·
              refine ⟨11061913993380571672658915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7374609328920381115105943 11061913993380571672658915)
              ·
                refine ⟨16592870990070857508988373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11061913993380571672658915 16592870990070857508988373)
                ·
                  refine ⟨388895413829785722866915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16592870990070857508988373 388895413829785722866915)
                  ·
                    rfl

theorem cell22_3408170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_3408170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408170 prefixEnd_3408170 := by exact prefixLift 3408170
  have htrace : WordTrace (prefixWord ++ tailWord_3408170) baseStart_3408170 baseEnd_3408170 := by
    simpa [prefixWord, tailWord_3408170, baseEnd_3408170] using wordTrace_append hprefix tailTrace_3408170
  have hstable : (prefixWord ++ tailWord_3408170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408170).length < 2 ^ (prefixWord ++ tailWord_3408170).sum := by decide
  have hdescent : baseEnd_3408170 < baseStart_3408170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408174 : List Nat := [4, 1, 3, 3, 1, 1, 2, 1, 3, 3]
def baseStart_3408174 : Nat := 118140960795 + 3408174 * 2 ^ 59
def prefixEnd_3408174 : Nat := 4983230072969 + 3 ^ 40 * 3408174 * 2
def baseEnd_3408174 : Nat := 1166687610771102491500733

theorem tailTrace_3408174 : CollatzResearch.WordTrace tailWord_3408174 prefixEnd_3408174 1166687610771102491500733 := by
  unfold tailWord_3408174
  simp only [CollatzResearch.WordTrace]
  refine ⟨15538289744346892827920947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82870878636516761748911717 15538289744346892827920947)
  ·
    refine ⟨23307434616520339241881421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15538289744346892827920947 23307434616520339241881421)
    ·
      refine ⟨8740287981195127215705533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23307434616520339241881421 8740287981195127215705533)
      ·
        refine ⟨3277607992948172705889575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8740287981195127215705533 3277607992948172705889575)
        ·
          refine ⟨4916411989422259058834363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277607992948172705889575 4916411989422259058834363)
          ·
            refine ⟨7374617984133388588251545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916411989422259058834363 7374617984133388588251545)
            ·
              refine ⟨5530963488100041441188659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7374617984133388588251545 5530963488100041441188659)
              ·
                refine ⟨8296445232150062161782989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5530963488100041441188659 8296445232150062161782989)
                ·
                  refine ⟨3111166962056273310668621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8296445232150062161782989 3111166962056273310668621)
                  ·
                    refine ⟨1166687610771102491500733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111166962056273310668621 1166687610771102491500733)
                    ·
                      rfl

theorem cell22_3408174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_3408174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408174 prefixEnd_3408174 := by exact prefixLift 3408174
  have htrace : WordTrace (prefixWord ++ tailWord_3408174) baseStart_3408174 baseEnd_3408174 := by
    simpa [prefixWord, tailWord_3408174, baseEnd_3408174] using wordTrace_append hprefix tailTrace_3408174
  have hstable : (prefixWord ++ tailWord_3408174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408174).length < 2 ^ (prefixWord ++ tailWord_3408174).sum := by decide
  have hdescent : baseEnd_3408174 < baseStart_3408174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408305 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 5]
def baseStart_3408305 : Nat := 118140960795 + 3408305 * 2 ^ 59
def prefixEnd_3408305 : Nat := 4983230072969 + 3 ^ 40 * 3408305 * 2
def baseEnd_3408305 : Nat := 388910818249420605491777

theorem tailTrace_3408305 : CollatzResearch.WordTrace tailWord_3408305 prefixEnd_3408305 388910818249420605491777 := by
  unfold tailWord_3408305
  simp only [CollatzResearch.WordTrace]
  refine ⟨124311095917300551996386369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82874063944867034664257579 124311095917300551996386369)
  ·
    refine ⟨93233321937975413997289777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124311095917300551996386369 93233321937975413997289777)
    ·
      refine ⟨69924991453481560497967333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93233321937975413997289777 69924991453481560497967333)
      ·
        refine ⟨13110935897527792593368875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69924991453481560497967333 13110935897527792593368875)
        ·
          refine ⟨19666403846291688890053313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13110935897527792593368875 19666403846291688890053313)
          ·
            refine ⟨14749802884718766667539985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19666403846291688890053313 14749802884718766667539985)
            ·
              refine ⟨11062352163539075000654989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14749802884718766667539985 11062352163539075000654989)
              ·
                refine ⟨4148382061327153125245621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11062352163539075000654989 4148382061327153125245621)
                ·
                  refine ⟨388910818249420605491777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4148382061327153125245621 388910818249420605491777)
                  ·
                    rfl

theorem cell22_3408305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 5].length) (baseStart_3408305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408305 prefixEnd_3408305 := by exact prefixLift 3408305
  have htrace : WordTrace (prefixWord ++ tailWord_3408305) baseStart_3408305 baseEnd_3408305 := by
    simpa [prefixWord, tailWord_3408305, baseEnd_3408305] using wordTrace_append hprefix tailTrace_3408305
  have hstable : (prefixWord ++ tailWord_3408305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408305).length < 2 ^ (prefixWord ++ tailWord_3408305).sum := by decide
  have hdescent : baseEnd_3408305 < baseStart_3408305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408363 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 3, 6]
def baseStart_3408363 : Nat := 118140960795 + 3408363 * 2 ^ 59
def prefixEnd_3408363 : Nat := 4983230072969 + 3 ^ 40 * 3408363 * 2
def baseEnd_3408363 : Nat := 1166752309333568998525153

theorem tailTrace_3408363 : CollatzResearch.WordTrace tailWord_3408363 prefixEnd_3408363 1166752309333568998525153 := by
  unfold tailWord_3408363
  simp only [CollatzResearch.WordTrace]
  refine ⟨124313211351090427901997743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82875474234060285267998495 124313211351090427901997743)
  ·
    refine ⟨186469817026635641852996615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124313211351090427901997743 186469817026635641852996615)
    ·
      refine ⟨279704725539953462779494923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186469817026635641852996615 279704725539953462779494923)
      ·
        refine ⟨419557088309930194169242385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279704725539953462779494923 419557088309930194169242385)
        ·
          refine ⟨314667816232447645626931789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419557088309930194169242385 314667816232447645626931789)
          ·
            refine ⟨118000431087167867110099421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 314667816232447645626931789 118000431087167867110099421)
            ·
              refine ⟨44250161657687950166287283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118000431087167867110099421 44250161657687950166287283)
              ·
                refine ⟨66375242486531925249430925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44250161657687950166287283 66375242486531925249430925)
                ·
                  refine ⟨24890715932449471968536597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66375242486531925249430925 24890715932449471968536597)
                  ·
                    refine ⟨1166752309333568998525153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24890715932449471968536597 1166752309333568998525153)
                    ·
                      rfl

theorem cell22_3408363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_3408363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408363 prefixEnd_3408363 := by exact prefixLift 3408363
  have htrace : WordTrace (prefixWord ++ tailWord_3408363) baseStart_3408363 baseEnd_3408363 := by
    simpa [prefixWord, tailWord_3408363, baseEnd_3408363] using wordTrace_append hprefix tailTrace_3408363
  have hstable : (prefixWord ++ tailWord_3408363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408363).length < 2 ^ (prefixWord ++ tailWord_3408363).sum := by decide
  have hdescent : baseEnd_3408363 < baseStart_3408363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408380 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_3408380 : Nat := 118140960795 + 3408380 * 2 ^ 59
def prefixEnd_3408380 : Nat := 4983230072969 + 3 ^ 40 * 3408380 * 2
def baseEnd_3408380 : Nat := 1166758128780986620850101

theorem tailTrace_3408380 : CollatzResearch.WordTrace tailWord_3408380 prefixEnd_3408380 1166758128780986620850101 := by
  unfold tailWord_3408380
  simp only [CollatzResearch.WordTrace]
  refine ⟨62156915696014419902683297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82875887594685893203577729 62156915696014419902683297)
  ·
    refine ⟨46617686772010814927012473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62156915696014419902683297 46617686772010814927012473)
    ·
      refine ⟨34963265079008111195259355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46617686772010814927012473 34963265079008111195259355)
      ·
        refine ⟨52444897618512166792889033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34963265079008111195259355 52444897618512166792889033)
        ·
          refine ⟨39333673213884125094666775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52444897618512166792889033 39333673213884125094666775)
          ·
            refine ⟨59000509820826187642000163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39333673213884125094666775 59000509820826187642000163)
            ·
              refine ⟨88500764731239281463000245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59000509820826187642000163 88500764731239281463000245)
              ·
                refine ⟨8296946693553682637156273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88500764731239281463000245 8296946693553682637156273)
                ·
                  refine ⟨6222710020165261977867205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8296946693553682637156273 6222710020165261977867205)
                  ·
                    refine ⟨1166758128780986620850101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222710020165261977867205 1166758128780986620850101)
                    ·
                      rfl

theorem cell22_3408380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_3408380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408380 prefixEnd_3408380 := by exact prefixLift 3408380
  have htrace : WordTrace (prefixWord ++ tailWord_3408380) baseStart_3408380 baseEnd_3408380 := by
    simpa [prefixWord, tailWord_3408380, baseEnd_3408380] using wordTrace_append hprefix tailTrace_3408380
  have hstable : (prefixWord ++ tailWord_3408380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408380).length < 2 ^ (prefixWord ++ tailWord_3408380).sum := by decide
  have hdescent : baseEnd_3408380 < baseStart_3408380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408395 : List Nat := [1, 1, 1, 1, 7, 3, 8]
def baseStart_3408395 : Nat := 118140960795 + 3408395 * 2 ^ 59
def prefixEnd_3408395 : Nat := 4983230072969 + 3 ^ 40 * 3408395 * 2
def baseEnd_3408395 : Nat := 43213454206945614137965

theorem tailTrace_3408395 : CollatzResearch.WordTrace tailWord_3408395 prefixEnd_3408395 43213454206945614137965 := by
  unfold tailWord_3408395
  simp only [CollatzResearch.WordTrace]
  refine ⟨124314378486974497367162639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82876252324649664911441759 124314378486974497367162639)
  ·
    refine ⟨186471567730461746050743959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124314378486974497367162639 186471567730461746050743959)
    ·
      refine ⟨279707351595692619076115939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186471567730461746050743959 279707351595692619076115939)
      ·
        refine ⟨419561027393538928614173909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279707351595692619076115939 419561027393538928614173909)
        ·
          refine ⟨9833461579536068639394701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 419561027393538928614173909 9833461579536068639394701)
          ·
            refine ⟨3687548092326025739773013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9833461579536068639394701 3687548092326025739773013)
            ·
              refine ⟨43213454206945614137965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3687548092326025739773013 43213454206945614137965)
              ·
                rfl

theorem cell22_3408395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 8].length) (baseStart_3408395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408395 prefixEnd_3408395 := by exact prefixLift 3408395
  have htrace : WordTrace (prefixWord ++ tailWord_3408395) baseStart_3408395 baseEnd_3408395 := by
    simpa [prefixWord, tailWord_3408395, baseEnd_3408395] using wordTrace_append hprefix tailTrace_3408395
  have hstable : (prefixWord ++ tailWord_3408395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408395).length < 2 ^ (prefixWord ++ tailWord_3408395).sum := by decide
  have hdescent : baseEnd_3408395 < baseStart_3408395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408452 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_3408452 : Nat := 118140960795 + 3408452 * 2 ^ 59
def prefixEnd_3408452 : Nat := 4983230072969 + 3 ^ 40 * 3408452 * 2
def baseEnd_3408452 : Nat := 388927591950800811016627

theorem tailTrace_3408452 : CollatzResearch.WordTrace tailWord_3408452 prefixEnd_3408452 388927591950800811016627 := by
  unfold tailWord_3408452
  simp only [CollatzResearch.WordTrace]
  refine ⟨62158228723883998050993805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82877638298511997401325073 62158228723883998050993805)
  ·
    refine ⟨23309335771456499269122677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62158228723883998050993805 23309335771456499269122677)
    ·
      refine ⟨2185250228574046806480251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23309335771456499269122677 2185250228574046806480251)
      ·
        refine ⟨3277875342861070209720377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185250228574046806480251 3277875342861070209720377)
        ·
          refine ⟨2458406507145802657290283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277875342861070209720377 2458406507145802657290283)
          ·
            refine ⟨3687609760718703985935425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458406507145802657290283 3687609760718703985935425)
            ·
              refine ⟨2765707320539027989451569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687609760718703985935425 2765707320539027989451569)
              ·
                refine ⟨2074280490404270992088677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2765707320539027989451569 2074280490404270992088677)
                ·
                  refine ⟨388927591950800811016627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074280490404270992088677 388927591950800811016627)
                  ·
                    rfl

theorem cell22_3408452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_3408452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408452 prefixEnd_3408452 := by exact prefixLift 3408452
  have htrace : WordTrace (prefixWord ++ tailWord_3408452) baseStart_3408452 baseEnd_3408452 := by
    simpa [prefixWord, tailWord_3408452, baseEnd_3408452] using wordTrace_append hprefix tailTrace_3408452
  have hstable : (prefixWord ++ tailWord_3408452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408452).length < 2 ^ (prefixWord ++ tailWord_3408452).sum := by decide
  have hdescent : baseEnd_3408452 < baseStart_3408452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408487 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3408487 : Nat := 118140960795 + 3408487 * 2 ^ 59
def prefixEnd_3408487 : Nat := 4983230072969 + 3 ^ 40 * 3408487 * 2
def baseEnd_3408487 : Nat := 1166794757067674008424773

theorem tailTrace_3408487 : CollatzResearch.WordTrace tailWord_3408487 prefixEnd_3408487 1166794757067674008424773 := by
  unfold tailWord_3408487
  simp only [CollatzResearch.WordTrace]
  refine ⟨124317734002641197079511715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82878489335094131386341143 124317734002641197079511715)
  ·
    refine ⟨186476601003961795619267573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124317734002641197079511715 186476601003961795619267573)
    ·
      refine ⟨17482181344121418339306335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186476601003961795619267573 17482181344121418339306335)
      ·
        refine ⟨26223272016182127508959503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17482181344121418339306335 26223272016182127508959503)
        ·
          refine ⟨39334908024273191263439255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26223272016182127508959503 39334908024273191263439255)
          ·
            refine ⟨59002362036409786895158883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39334908024273191263439255 59002362036409786895158883)
            ·
              refine ⟨88503543054614680342738325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59002362036409786895158883 88503543054614680342738325)
              ·
                refine ⟨4148603580685063141065859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88503543054614680342738325 4148603580685063141065859)
                ·
                  refine ⟨6222905371027594711598789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4148603580685063141065859 6222905371027594711598789)
                  ·
                    refine ⟨1166794757067674008424773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6222905371027594711598789 1166794757067674008424773)
                    ·
                      rfl

theorem cell22_3408487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3408487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408487 prefixEnd_3408487 := by exact prefixLift 3408487
  have htrace : WordTrace (prefixWord ++ tailWord_3408487) baseStart_3408487 baseEnd_3408487 := by
    simpa [prefixWord, tailWord_3408487, baseEnd_3408487] using wordTrace_append hprefix tailTrace_3408487
  have hstable : (prefixWord ++ tailWord_3408487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408487).length < 2 ^ (prefixWord ++ tailWord_3408487).sum := by decide
  have hdescent : baseEnd_3408487 < baseStart_3408487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408560 : List Nat := [2, 1, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_3408560 : Nat := 118140960795 + 3408560 * 2 ^ 59
def prefixEnd_3408560 : Nat := 4983230072969 + 3 ^ 40 * 3408560 * 2
def baseEnd_3408560 : Nat := 1166819746459526151349549

theorem tailTrace_3408560 : CollatzResearch.WordTrace tailWord_3408560 prefixEnd_3408560 1166819746459526151349549 := by
  unfold tailWord_3408560
  simp only [CollatzResearch.WordTrace]
  refine ⟨62160198265688365273459567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82880264354251153697946089 62160198265688365273459567)
  ·
    refine ⟨93240297398532547910189351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62160198265688365273459567 93240297398532547910189351)
    ·
      refine ⟨139860446097798821865284027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93240297398532547910189351 139860446097798821865284027)
      ·
        refine ⟨209790669146698232797926041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139860446097798821865284027 209790669146698232797926041)
        ·
          refine ⟨157343001860023674598444531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209790669146698232797926041 157343001860023674598444531)
          ·
            refine ⟨236014502790035511897666797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157343001860023674598444531 236014502790035511897666797)
            ·
              refine ⟨88505438546263316961625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236014502790035511897666797 88505438546263316961625049)
              ·
                refine ⟨66379078909697487721218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88505438546263316961625049 66379078909697487721218787)
                ·
                  refine ⟨99568618364546231581828181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66379078909697487721218787 99568618364546231581828181)
                  ·
                    refine ⟨1166819746459526151349549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99568618364546231581828181 1166819746459526151349549)
                    ·
                      rfl

theorem cell22_3408560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_3408560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408560 prefixEnd_3408560 := by exact prefixLift 3408560
  have htrace : WordTrace (prefixWord ++ tailWord_3408560) baseStart_3408560 baseEnd_3408560 := by
    simpa [prefixWord, tailWord_3408560, baseEnd_3408560] using wordTrace_append hprefix tailTrace_3408560
  have hstable : (prefixWord ++ tailWord_3408560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408560).length < 2 ^ (prefixWord ++ tailWord_3408560).sum := by decide
  have hdescent : baseEnd_3408560 < baseStart_3408560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408637 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 6]
def baseStart_3408637 : Nat := 118140960795 + 3408637 * 2 ^ 59
def prefixEnd_3408637 : Nat := 4983230072969 + 3 ^ 40 * 3408637 * 2
def baseEnd_3408637 : Nat := 388948701711041205724771

theorem tailTrace_3408637 : CollatzResearch.WordTrace tailWord_3408637 prefixEnd_3408637 388948701711041205724771 := by
  unfold tailWord_3408637
  simp only [CollatzResearch.WordTrace]
  refine ⟨124323204952097772697472165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82882136634731848464981443 124323204952097772697472165)
  ·
    refine ⟨23310600928518332380776031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124323204952097772697472165 23310600928518332380776031)
    ·
      refine ⟨34965901392777498571164047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23310600928518332380776031 34965901392777498571164047)
      ·
        refine ⟨52448852089166247856746071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34965901392777498571164047 52448852089166247856746071)
        ·
          refine ⟨78673278133749371785119107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52448852089166247856746071 78673278133749371785119107)
          ·
            refine ⟨118009917200624057677678661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78673278133749371785119107 118009917200624057677678661)
            ·
              refine ⟨22126859475117010814564749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118009917200624057677678661 22126859475117010814564749)
              ·
                refine ⟨8297572303168879055461781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22126859475117010814564749 8297572303168879055461781)
                ·
                  refine ⟨388948701711041205724771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8297572303168879055461781 388948701711041205724771)
                  ·
                    rfl

theorem cell22_3408637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_3408637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408637 prefixEnd_3408637 := by exact prefixLift 3408637
  have htrace : WordTrace (prefixWord ++ tailWord_3408637) baseStart_3408637 baseEnd_3408637 := by
    simpa [prefixWord, tailWord_3408637, baseEnd_3408637] using wordTrace_append hprefix tailTrace_3408637
  have hstable : (prefixWord ++ tailWord_3408637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408637).length < 2 ^ (prefixWord ++ tailWord_3408637).sum := by decide
  have hdescent : baseEnd_3408637 < baseStart_3408637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408671 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 4]
def baseStart_3408671 : Nat := 118140960795 + 3408671 * 2 ^ 59
def prefixEnd_3408671 : Nat := 4983230072969 + 3 ^ 40 * 3408671 * 2
def baseEnd_3408671 : Nat := 388952581342652953941403

theorem tailTrace_3408671 : CollatzResearch.WordTrace tailWord_3408671 prefixEnd_3408671 388952581342652953941403 := by
  unfold tailWord_3408671
  simp only [CollatzResearch.WordTrace]
  refine ⟨124324445033974596504209867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82882963355983064336139911 124324445033974596504209867)
  ·
    refine ⟨186486667550961894756314801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124324445033974596504209867 186486667550961894756314801)
    ·
      refine ⟨139865000663221421067236101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186486667550961894756314801 139865000663221421067236101)
      ·
        refine ⟨26224687624354016450106769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139865000663221421067236101 26224687624354016450106769)
        ·
          refine ⟨19668515718265512337580077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26224687624354016450106769 19668515718265512337580077)
          ·
            refine ⟨7375693394349567126592529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19668515718265512337580077 7375693394349567126592529)
            ·
              refine ⟨5531770045762175344944397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7375693394349567126592529 5531770045762175344944397)
              ·
                refine ⟨2074413767160815754354149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5531770045762175344944397 2074413767160815754354149)
                ·
                  refine ⟨388952581342652953941403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074413767160815754354149 388952581342652953941403)
                  ·
                    rfl

theorem cell22_3408671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 4].length) (baseStart_3408671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408671 prefixEnd_3408671 := by exact prefixLift 3408671
  have htrace : WordTrace (prefixWord ++ tailWord_3408671) baseStart_3408671 baseEnd_3408671 := by
    simpa [prefixWord, tailWord_3408671, baseEnd_3408671] using wordTrace_append hprefix tailTrace_3408671
  have hstable : (prefixWord ++ tailWord_3408671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408671).length < 2 ^ (prefixWord ++ tailWord_3408671).sum := by decide
  have hdescent : baseEnd_3408671 < baseStart_3408671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408703 : List Nat := [1, 1, 2, 2, 5, 2, 3, 1, 2, 3]
def baseStart_3408703 : Nat := 118140960795 + 3408703 * 2 ^ 59
def prefixEnd_3408703 : Nat := 4983230072969 + 3 ^ 40 * 3408703 * 2
def baseEnd_3408703 : Nat := 1166868698281921445024111

theorem tailTrace_3408703 : CollatzResearch.WordTrace tailWord_3408703 prefixEnd_3408703 1166868698281921445024111 := by
  unfold tailWord_3408703
  simp only [CollatzResearch.WordTrace]
  refine ⟨124325612169858665969374763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82883741446572443979583175 124325612169858665969374763)
  ·
    refine ⟨186488418254787998954062145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124325612169858665969374763 186488418254787998954062145)
    ·
      refine ⟨139866313691090999215546609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186488418254787998954062145 139866313691090999215546609)
      ·
        refine ⟨104899735268318249411659957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139866313691090999215546609 104899735268318249411659957)
        ·
          refine ⟨9834350181404835882343121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104899735268318249411659957 9834350181404835882343121)
          ·
            refine ⟨7375762636053626911757341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9834350181404835882343121 7375762636053626911757341)
            ·
              refine ⟨2765910988520110091909003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7375762636053626911757341 2765910988520110091909003)
              ·
                refine ⟨4148866482780165137863505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765910988520110091909003 4148866482780165137863505)
                ·
                  refine ⟨3111649862085123853397629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4148866482780165137863505 3111649862085123853397629)
                  ·
                    refine ⟨1166868698281921445024111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111649862085123853397629 1166868698281921445024111)
                    ·
                      rfl

theorem cell22_3408703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 2, 3].length) (baseStart_3408703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408703 prefixEnd_3408703 := by exact prefixLift 3408703
  have htrace : WordTrace (prefixWord ++ tailWord_3408703) baseStart_3408703 baseEnd_3408703 := by
    simpa [prefixWord, tailWord_3408703, baseEnd_3408703] using wordTrace_append hprefix tailTrace_3408703
  have hstable : (prefixWord ++ tailWord_3408703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408703).length < 2 ^ (prefixWord ++ tailWord_3408703).sum := by decide
  have hdescent : baseEnd_3408703 < baseStart_3408703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408714 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_3408714 : Nat := 118140960795 + 3408714 * 2 ^ 59
def prefixEnd_3408714 : Nat := 4983230072969 + 3 ^ 40 * 3408714 * 2
def baseEnd_3408714 : Nat := 1166872463806721082999077

theorem tailTrace_3408714 : CollatzResearch.WordTrace tailWord_3408714 prefixEnd_3408714 1166872463806721082999077 := by
  unfold tailWord_3408714
  simp only [CollatzResearch.WordTrace]
  refine ⟨31081503343204703712006299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82884008915212543232016797 31081503343204703712006299)
  ·
    refine ⟨46622255014807055568009449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31081503343204703712006299 46622255014807055568009449)
    ·
      refine ⟨34966691261105291676007087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46622255014807055568009449 34966691261105291676007087)
      ·
        refine ⟨52450036891657937514010631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34966691261105291676007087 52450036891657937514010631)
        ·
          refine ⟨78675055337486906271015947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52450036891657937514010631 78675055337486906271015947)
          ·
            refine ⟨118012583006230359406523921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78675055337486906271015947 118012583006230359406523921)
            ·
              refine ⟨88509437254672769554892941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118012583006230359406523921 88509437254672769554892941)
              ·
                refine ⟨33191038970502288583084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88509437254672769554892941 33191038970502288583084853)
                ·
                  refine ⟨3111659903484589554664205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33191038970502288583084853 3111659903484589554664205)
                  ·
                    refine ⟨1166872463806721082999077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111659903484589554664205 1166872463806721082999077)
                    ·
                      rfl

theorem cell22_3408714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_3408714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408714 prefixEnd_3408714 := by exact prefixLift 3408714
  have htrace : WordTrace (prefixWord ++ tailWord_3408714) baseStart_3408714 baseEnd_3408714 := by
    simpa [prefixWord, tailWord_3408714, baseEnd_3408714] using wordTrace_append hprefix tailTrace_3408714
  have hstable : (prefixWord ++ tailWord_3408714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408714).length < 2 ^ (prefixWord ++ tailWord_3408714).sum := by decide
  have hdescent : baseEnd_3408714 < baseStart_3408714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408716 : List Nat := [2, 2, 1, 3, 3, 3, 2, 6]
def baseStart_3408716 : Nat := 118140960795 + 3408716 * 2 ^ 59
def prefixEnd_3408716 : Nat := 4983230072969 + 3 ^ 40 * 3408716 * 2
def baseEnd_3408716 : Nat := 129652572049732638272119

theorem tailTrace_3408716 : CollatzResearch.WordTrace tailWord_3408716 prefixEnd_3408716 129652572049732638272119 := by
  unfold tailWord_3408716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163043159405784594799001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82884057545874379459732001 62163043159405784594799001)
  ·
    refine ⟨46622282369554338446099251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62163043159405784594799001 46622282369554338446099251)
    ·
      refine ⟨69933423554331507669148877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46622282369554338446099251 69933423554331507669148877)
      ·
        refine ⟨26225033832874315375930829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69933423554331507669148877 26225033832874315375930829)
        ·
          refine ⟨9834387687327868265974061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26225033832874315375930829 9834387687327868265974061)
          ·
            refine ⟨3687895382747950599740273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9834387687327868265974061 3687895382747950599740273)
            ·
              refine ⟨2765921537060962949805205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687895382747950599740273 2765921537060962949805205)
              ·
                refine ⟨129652572049732638272119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2765921537060962949805205 129652572049732638272119)
                ·
                  rfl

theorem cell22_3408716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_3408716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408716 prefixEnd_3408716 := by exact prefixLift 3408716
  have htrace : WordTrace (prefixWord ++ tailWord_3408716) baseStart_3408716 baseEnd_3408716 := by
    simpa [prefixWord, tailWord_3408716, baseEnd_3408716] using wordTrace_append hprefix tailTrace_3408716
  have hstable : (prefixWord ++ tailWord_3408716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408716).length < 2 ^ (prefixWord ++ tailWord_3408716).sum := by decide
  have hdescent : baseEnd_3408716 < baseStart_3408716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408744 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_3408744 : Nat := 118140960795 + 3408744 * 2 ^ 59
def prefixEnd_3408744 : Nat := 4983230072969 + 3 ^ 40 * 3408744 * 2
def baseEnd_3408744 : Nat := 388960911139937001582995

theorem tailTrace_3408744 : CollatzResearch.WordTrace tailWord_3408744 prefixEnd_3408744 388960911139937001582995 := by
  unfold tailWord_3408744
  simp only [CollatzResearch.WordTrace]
  refine ⟨62163553781355064985808643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82884738375140086647744857 62163553781355064985808643)
  ·
    refine ⟨93245330672032597478712965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62163553781355064985808643 93245330672032597478712965)
    ·
      refine ⟨17483499501006112027258681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93245330672032597478712965 17483499501006112027258681)
      ·
        refine ⟨13112624625754584020444011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17483499501006112027258681 13112624625754584020444011)
        ·
          refine ⟨19668936938631876030666017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13112624625754584020444011 19668936938631876030666017)
          ·
            refine ⟨14751702703973907022999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19668936938631876030666017 14751702703973907022999513)
            ·
              refine ⟨11063777027980430267249635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14751702703973907022999513 11063777027980430267249635)
              ·
                refine ⟨16595665541970645400874453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11063777027980430267249635 16595665541970645400874453)
                ·
                  refine ⟨388960911139937001582995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16595665541970645400874453 388960911139937001582995)
                  ·
                    rfl

theorem cell22_3408744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_3408744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408744 prefixEnd_3408744 := by exact prefixLift 3408744
  have htrace : WordTrace (prefixWord ++ tailWord_3408744) baseStart_3408744 baseEnd_3408744 := by
    simpa [prefixWord, tailWord_3408744, baseEnd_3408744] using wordTrace_append hprefix tailTrace_3408744
  have hstable : (prefixWord ++ tailWord_3408744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408744).length < 2 ^ (prefixWord ++ tailWord_3408744).sum := by decide
  have hdescent : baseEnd_3408744 < baseStart_3408744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408761 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 5]
def baseStart_3408761 : Nat := 118140960795 + 3408761 * 2 ^ 59
def prefixEnd_3408761 : Nat := 4983230072969 + 3 ^ 40 * 3408761 * 2
def baseEnd_3408761 : Nat := 388962850955742875691311

theorem tailTrace_3408761 : CollatzResearch.WordTrace tailWord_3408761 prefixEnd_3408761 388962850955742875691311 := by
  unfold tailWord_3408761
  simp only [CollatzResearch.WordTrace]
  refine ⟨124327727603648541874986137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82885151735765694583324091 124327727603648541874986137)
  ·
    refine ⟨93245795702736406406239603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124327727603648541874986137 93245795702736406406239603)
    ·
      refine ⟨139868693554104609609359405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93245795702736406406239603 139868693554104609609359405)
      ·
        refine ⟨52450760082789228603509777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139868693554104609609359405 52450760082789228603509777)
        ·
          refine ⟨39338070062091921452632333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52450760082789228603509777 39338070062091921452632333)
          ·
            refine ⟨14751776273284470544737125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39338070062091921452632333 14751776273284470544737125)
            ·
              refine ⟨2765958051240838227138211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14751776273284470544737125 2765958051240838227138211)
              ·
                refine ⟨4148937076861257340707317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2765958051240838227138211 4148937076861257340707317)
                ·
                  refine ⟨388962850955742875691311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4148937076861257340707317 388962850955742875691311)
                  ·
                    rfl

theorem cell22_3408761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 5].length) (baseStart_3408761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408761 prefixEnd_3408761 := by exact prefixLift 3408761
  have htrace : WordTrace (prefixWord ++ tailWord_3408761) baseStart_3408761 baseEnd_3408761 := by
    simpa [prefixWord, tailWord_3408761, baseEnd_3408761] using wordTrace_append hprefix tailTrace_3408761
  have hstable : (prefixWord ++ tailWord_3408761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408761).length < 2 ^ (prefixWord ++ tailWord_3408761).sum := by decide
  have hdescent : baseEnd_3408761 < baseStart_3408761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408804 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_3408804 : Nat := 118140960795 + 3408804 * 2 ^ 59
def prefixEnd_3408804 : Nat := 4983230072969 + 3 ^ 40 * 3408804 * 2
def baseEnd_3408804 : Nat := 1166903272645990848248801

theorem tailTrace_3408804 : CollatzResearch.WordTrace tailWord_3408804 prefixEnd_3408804 1166903272645990848248801 := by
  unfold tailWord_3408804
  simp only [CollatzResearch.WordTrace]
  refine ⟨62164647971246380109400733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82886197294995173479200977 62164647971246380109400733)
  ·
    refine ⟨23311742989217392541025275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62164647971246380109400733 23311742989217392541025275)
    ·
      refine ⟨34967614483826088811537913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23311742989217392541025275 34967614483826088811537913)
      ·
        refine ⟨26225710862869566608653435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34967614483826088811537913 26225710862869566608653435)
        ·
          refine ⟨39338566294304349912980153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26225710862869566608653435 39338566294304349912980153)
          ·
            refine ⟨29503924720728262434735115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39338566294304349912980153 29503924720728262434735115)
            ·
              refine ⟨44255887081092393652102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29503924720728262434735115 44255887081092393652102673)
              ·
                refine ⟨33191915310819295239077005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44255887081092393652102673 33191915310819295239077005)
                ·
                  refine ⟨12446968241557235714653877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33191915310819295239077005 12446968241557235714653877)
                  ·
                    refine ⟨1166903272645990848248801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12446968241557235714653877 1166903272645990848248801)
                    ·
                      rfl

theorem cell22_3408804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_3408804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408804 prefixEnd_3408804 := by exact prefixLift 3408804
  have htrace : WordTrace (prefixWord ++ tailWord_3408804) baseStart_3408804 baseEnd_3408804 := by
    simpa [prefixWord, tailWord_3408804, baseEnd_3408804] using wordTrace_append hprefix tailTrace_3408804
  have hstable : (prefixWord ++ tailWord_3408804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408804).length < 2 ^ (prefixWord ++ tailWord_3408804).sum := by decide
  have hdescent : baseEnd_3408804 < baseStart_3408804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408821 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3408821 : Nat := 118140960795 + 3408821 * 2 ^ 59
def prefixEnd_3408821 : Nat := 4983230072969 + 3 ^ 40 * 3408821 * 2
def baseEnd_3408821 : Nat := 1166909092093408470573749

theorem tailTrace_3408821 : CollatzResearch.WordTrace tailWord_3408821 prefixEnd_3408821 1166909092093408470573749 := by
  unfold tailWord_3408821
  simp only [CollatzResearch.WordTrace]
  refine ⟨124329915983431172122170317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82886610655620781414780211 124329915983431172122170317)
  ·
    refine ⟨46623718493786689545813869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124329915983431172122170317 46623718493786689545813869)
    ·
      refine ⟨17483894435170008579680201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46623718493786689545813869 17483894435170008579680201)
      ·
        refine ⟨13112920826377506434760151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17483894435170008579680201 13112920826377506434760151)
        ·
          refine ⟨19669381239566259652140227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13112920826377506434760151 19669381239566259652140227)
          ·
            refine ⟨29504071859349389478210341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19669381239566259652140227 29504071859349389478210341)
            ·
              refine ⟨5532013473628010527164439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29504071859349389478210341 5532013473628010527164439)
              ·
                refine ⟨8298020210442015790746659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532013473628010527164439 8298020210442015790746659)
                ·
                  refine ⟨12447030315663023686119989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298020210442015790746659 12447030315663023686119989)
                  ·
                    refine ⟨1166909092093408470573749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12447030315663023686119989 1166909092093408470573749)
                    ·
                      rfl

theorem cell22_3408821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3408821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408821 prefixEnd_3408821 := by exact prefixLift 3408821
  have htrace : WordTrace (prefixWord ++ tailWord_3408821) baseStart_3408821 baseEnd_3408821 := by
    simpa [prefixWord, tailWord_3408821, baseEnd_3408821] using wordTrace_append hprefix tailTrace_3408821
  have hstable : (prefixWord ++ tailWord_3408821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408821).length < 2 ^ (prefixWord ++ tailWord_3408821).sum := by decide
  have hdescent : baseEnd_3408821 < baseStart_3408821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408917 : List Nat := [1, 3, 2, 1, 4, 2, 3, 2, 1, 3]
def baseStart_3408917 : Nat := 118140960795 + 3408917 * 2 ^ 59
def prefixEnd_3408917 : Nat := 4983230072969 + 3 ^ 40 * 3408917 * 2
def baseEnd_3408917 : Nat := 1166941954855296220173455

theorem tailTrace_3408917 : CollatzResearch.WordTrace tailWord_3408917 prefixEnd_3408917 1166941954855296220173455 := by
  unfold tailWord_3408917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124333417391083380517665005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82888944927388920345110003 124333417391083380517665005)
  ·
    refine ⟨46625031521656267694124377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124333417391083380517665005 46625031521656267694124377)
    ·
      refine ⟨34968773641242200770593283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46625031521656267694124377 34968773641242200770593283)
      ·
        refine ⟨52453160461863301155889925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34968773641242200770593283 52453160461863301155889925)
        ·
          refine ⟨9834967586599368966729361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52453160461863301155889925 9834967586599368966729361)
          ·
            refine ⟨7376225689949526725047021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9834967586599368966729361 7376225689949526725047021)
            ·
              refine ⟨2766084633731072521892633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7376225689949526725047021 2766084633731072521892633)
              ·
                refine ⟨2074563475298304391419475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766084633731072521892633 2074563475298304391419475)
                ·
                  refine ⟨3111845212947456587129213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074563475298304391419475 3111845212947456587129213)
                  ·
                    refine ⟨1166941954855296220173455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3111845212947456587129213 1166941954855296220173455)
                    ·
                      rfl

theorem cell22_3408917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_3408917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408917 prefixEnd_3408917 := by exact prefixLift 3408917
  have htrace : WordTrace (prefixWord ++ tailWord_3408917) baseStart_3408917 baseEnd_3408917 := by
    simpa [prefixWord, tailWord_3408917, baseEnd_3408917] using wordTrace_append hprefix tailTrace_3408917
  have hstable : (prefixWord ++ tailWord_3408917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408917).length < 2 ^ (prefixWord ++ tailWord_3408917).sum := by decide
  have hdescent : baseEnd_3408917 < baseStart_3408917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408930 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3408930 : Nat := 118140960795 + 3408930 * 2 ^ 59
def prefixEnd_3408930 : Nat := 4983230072969 + 3 ^ 40 * 3408930 * 2
def baseEnd_3408930 : Nat := 388982135006989506532805

theorem tailTrace_3408930 : CollatzResearch.WordTrace tailWord_3408930 prefixEnd_3408930 388982135006989506532805 := by
  unfold tailWord_3408930
  simp only [CollatzResearch.WordTrace]
  refine ⟨31083472885009070934472061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82889261026690855825258829 31083472885009070934472061)
  ·
    refine ⟨11656302331878401600427023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31083472885009070934472061 11656302331878401600427023)
    ·
      refine ⟨17484453497817602400640535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656302331878401600427023 17484453497817602400640535)
      ·
        refine ⟨26226680246726403600960803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17484453497817602400640535 26226680246726403600960803)
        ·
          refine ⟨39340020370089605401441205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26226680246726403600960803 39340020370089605401441205)
          ·
            refine ⟨3688126909695900506385113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39340020370089605401441205 3688126909695900506385113)
            ·
              refine ⟨2766095182271925379788835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3688126909695900506385113 2766095182271925379788835)
              ·
                refine ⟨4149142773407888069683253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766095182271925379788835 4149142773407888069683253)
                ·
                  refine ⟨388982135006989506532805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149142773407888069683253 388982135006989506532805)
                  ·
                    rfl

theorem cell22_3408930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3408930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408930 prefixEnd_3408930 := by exact prefixLift 3408930
  have htrace : WordTrace (prefixWord ++ tailWord_3408930) baseStart_3408930 baseEnd_3408930 := by
    simpa [prefixWord, tailWord_3408930, baseEnd_3408930] using wordTrace_append hprefix tailTrace_3408930
  have hstable : (prefixWord ++ tailWord_3408930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408930).length < 2 ^ (prefixWord ++ tailWord_3408930).sum := by decide
  have hdescent : baseEnd_3408930 < baseStart_3408930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3408956 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_3408956 : Nat := 118140960795 + 3408956 * 2 ^ 59
def prefixEnd_3408956 : Nat := 4983230072969 + 3 ^ 40 * 3408956 * 2
def baseEnd_3408956 : Nat := 1166955305352313118448335

theorem tailTrace_3408956 : CollatzResearch.WordTrace tailWord_3408956 prefixEnd_3408956 1166955305352313118448335 := by
  unfold tailWord_3408956
  simp only [CollatzResearch.WordTrace]
  refine ⟨62167419918971045089167361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82889893225294726785556481 62167419918971045089167361)
  ·
    refine ⟨46625564939228283816875521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62167419918971045089167361 46625564939228283816875521)
    ·
      refine ⟨34969173704421212862656641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46625564939228283816875521 34969173704421212862656641)
      ·
        refine ⟨26226880278315909646992481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34969173704421212862656641 26226880278315909646992481)
        ·
          refine ⟨19670160208736932235244361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26226880278315909646992481 19670160208736932235244361)
          ·
            refine ⟨14752620156552699176433271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19670160208736932235244361 14752620156552699176433271)
            ·
              refine ⟨22128930234829048764649907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14752620156552699176433271 22128930234829048764649907)
              ·
                refine ⟨33193395352243573146974861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22128930234829048764649907 33193395352243573146974861)
                ·
                  refine ⟨12447523257091339930115573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33193395352243573146974861 12447523257091339930115573)
                  ·
                    refine ⟨1166955305352313118448335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12447523257091339930115573 1166955305352313118448335)
                    ·
                      rfl

theorem cell22_3408956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_3408956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3408956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3408956 prefixEnd_3408956 := by exact prefixLift 3408956
  have htrace : WordTrace (prefixWord ++ tailWord_3408956) baseStart_3408956 baseEnd_3408956 := by
    simpa [prefixWord, tailWord_3408956, baseEnd_3408956] using wordTrace_append hprefix tailTrace_3408956
  have hstable : (prefixWord ++ tailWord_3408956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3408956).length < 2 ^ (prefixWord ++ tailWord_3408956).sum := by decide
  have hdescent : baseEnd_3408956 < baseStart_3408956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3408956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409005 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3409005 : Nat := 118140960795 + 3409005 * 2 ^ 59
def prefixEnd_3409005 : Nat := 4983230072969 + 3 ^ 40 * 3409005 * 2
def baseEnd_3409005 : Nat := 1166972079053693323973185

theorem tailTrace_3409005 : CollatzResearch.WordTrace tailWord_3409005 prefixEnd_3409005 1166972079053693323973185 := by
  unfold tailWord_3409005
  simp only [CollatzResearch.WordTrace]
  refine ⟨124336627014764571546868469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82891084676509714364578979 124336627014764571546868469)
  ·
    refine ⟨11656558782634178582518919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124336627014764571546868469 11656558782634178582518919)
    ·
      refine ⟨17484838173951267873778379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11656558782634178582518919 17484838173951267873778379)
      ·
        refine ⟨26227257260926901810667569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17484838173951267873778379 26227257260926901810667569)
        ·
          refine ⟨19670442945695176358000677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26227257260926901810667569 19670442945695176358000677)
          ·
            refine ⟨3688208052317845567125127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19670442945695176358000677 3688208052317845567125127)
            ·
              refine ⟨5532312078476768350687691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688208052317845567125127 5532312078476768350687691)
              ·
                refine ⟨8298468117715152526031537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5532312078476768350687691 8298468117715152526031537)
                ·
                  refine ⟨6223851088286364394523653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8298468117715152526031537 6223851088286364394523653)
                  ·
                    refine ⟨1166972079053693323973185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6223851088286364394523653 1166972079053693323973185)
                    ·
                      rfl

theorem cell22_3409005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3409005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409005 prefixEnd_3409005 := by exact prefixLift 3409005
  have htrace : WordTrace (prefixWord ++ tailWord_3409005) baseStart_3409005 baseEnd_3409005 := by
    simpa [prefixWord, tailWord_3409005, baseEnd_3409005] using wordTrace_append hprefix tailTrace_3409005
  have hstable : (prefixWord ++ tailWord_3409005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409005).length < 2 ^ (prefixWord ++ tailWord_3409005).sum := by decide
  have hdescent : baseEnd_3409005 < baseStart_3409005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409091 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 5, 5]
def baseStart_3409091 : Nat := 118140960795 + 3409091 * 2 ^ 59
def prefixEnd_3409091 : Nat := 4983230072969 + 3 ^ 40 * 3409091 * 2
def baseEnd_3409091 : Nat := 1167001518611217766322921

theorem tailTrace_3409091 : CollatzResearch.WordTrace tailWord_3409091 prefixEnd_3409091 1167001518611217766322921 := by
  unfold tailWord_3409091
  simp only [CollatzResearch.WordTrace]
  refine ⟨124339763692453008234499127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82893175794968672156332751 124339763692453008234499127)
  ·
    refine ⟨186509645538679512351748691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124339763692453008234499127 186509645538679512351748691)
    ·
      refine ⟨279764468308019268527623037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186509645538679512351748691 279764468308019268527623037)
      ·
        refine ⟨104911675615507225697858639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 279764468308019268527623037 104911675615507225697858639)
        ·
          refine ⟨157367513423260838546787959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104911675615507225697858639 157367513423260838546787959)
          ·
            refine ⟨236051270134891257820181939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157367513423260838546787959 236051270134891257820181939)
            ·
              refine ⟨354076905202336886730272909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236051270134891257820181939 354076905202336886730272909)
              ·
                refine ⟨132778839450876332523852341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354076905202336886730272909 132778839450876332523852341)
                ·
                  refine ⟨12448016198519656174111157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132778839450876332523852341 12448016198519656174111157)
                  ·
                    refine ⟨1167001518611217766322921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12448016198519656174111157 1167001518611217766322921)
                    ·
                      rfl

theorem cell22_3409091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_3409091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409091 prefixEnd_3409091 := by exact prefixLift 3409091
  have htrace : WordTrace (prefixWord ++ tailWord_3409091) baseStart_3409091 baseEnd_3409091 := by
    simpa [prefixWord, tailWord_3409091, baseEnd_3409091] using wordTrace_append hprefix tailTrace_3409091
  have hstable : (prefixWord ++ tailWord_3409091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409091).length < 2 ^ (prefixWord ++ tailWord_3409091).sum := by decide
  have hdescent : baseEnd_3409091 < baseStart_3409091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409112 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_3409112 : Nat := 118140960795 + 3409112 * 2 ^ 59
def prefixEnd_3409112 : Nat := 4983230072969 + 3 ^ 40 * 3409112 * 2
def baseEnd_3409112 : Nat := 1167008707340380711547857

theorem tailTrace_3409112 : CollatzResearch.WordTrace tailWord_3409112 prefixEnd_3409112 1167008707340380711547857 := by
  unfold tailWord_3409112
  simp only [CollatzResearch.WordTrace]
  refine ⟨62170264812688464410506795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82893686416917952547342393 62170264812688464410506795)
  ·
    refine ⟨93255397219032696615760193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62170264812688464410506795 93255397219032696615760193)
    ·
      refine ⟨69941547914274522461820145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93255397219032696615760193 69941547914274522461820145)
      ·
        refine ⟨52456160935705891846365109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69941547914274522461820145 52456160935705891846365109)
        ·
          refine ⟨4917765087722427360596729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52456160935705891846365109 4917765087722427360596729)
          ·
            refine ⟨3688323815791820520447547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4917765087722427360596729 3688323815791820520447547)
            ·
              refine ⟨5532485723687730780671321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688323815791820520447547 5532485723687730780671321)
              ·
                refine ⟨4149364292765798085503491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532485723687730780671321 4149364292765798085503491)
                ·
                  refine ⟨6224046439148697128255237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149364292765798085503491 6224046439148697128255237)
                  ·
                    refine ⟨1167008707340380711547857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224046439148697128255237 1167008707340380711547857)
                    ·
                      rfl

theorem cell22_3409112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_3409112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409112 prefixEnd_3409112 := by exact prefixLift 3409112
  have htrace : WordTrace (prefixWord ++ tailWord_3409112) baseStart_3409112 baseEnd_3409112 := by
    simpa [prefixWord, tailWord_3409112, baseEnd_3409112] using wordTrace_append hprefix tailTrace_3409112
  have hstable : (prefixWord ++ tailWord_3409112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409112).length < 2 ^ (prefixWord ++ tailWord_3409112).sum := by decide
  have hdescent : baseEnd_3409112 < baseStart_3409112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409125 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3409125 : Nat := 118140960795 + 3409125 * 2 ^ 59
def prefixEnd_3409125 : Nat := 4983230072969 + 3 ^ 40 * 3409125 * 2
def baseEnd_3409125 : Nat := 1167013157506053010972817

theorem tailTrace_3409125 : CollatzResearch.WordTrace tailWord_3409125 prefixEnd_3409125 1167013157506053010972817 := by
  unfold tailWord_3409125
  simp only [CollatzResearch.WordTrace]
  refine ⟨124341003774329832041236829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82894002516219888027491219 124341003774329832041236829)
  ·
    refine ⟨46627876415373687015463811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124341003774329832041236829 46627876415373687015463811)
    ·
      refine ⟨69941814623060530523195717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46627876415373687015463811 69941814623060530523195717)
      ·
        refine ⟨13114090241823849473099197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69941814623060530523195717 13114090241823849473099197)
        ·
          refine ⟨4917783840683943552412199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13114090241823849473099197 4917783840683943552412199)
          ·
            refine ⟨7376675761025915328618299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4917783840683943552412199 7376675761025915328618299)
            ·
              refine ⟨11065013641538872992927449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7376675761025915328618299 11065013641538872992927449)
              ·
                refine ⟨8298760231154154744695587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11065013641538872992927449 8298760231154154744695587)
                ·
                  refine ⟨12448140346731232117043381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8298760231154154744695587 12448140346731232117043381)
                  ·
                    refine ⟨1167013157506053010972817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12448140346731232117043381 1167013157506053010972817)
                    ·
                      rfl

theorem cell22_3409125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3409125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409125 prefixEnd_3409125 := by exact prefixLift 3409125
  have htrace : WordTrace (prefixWord ++ tailWord_3409125) baseStart_3409125 baseEnd_3409125 := by
    simpa [prefixWord, tailWord_3409125, baseEnd_3409125] using wordTrace_append hprefix tailTrace_3409125
  have hstable : (prefixWord ++ tailWord_3409125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409125).length < 2 ^ (prefixWord ++ tailWord_3409125).sum := by decide
  have hdescent : baseEnd_3409125 < baseStart_3409125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409138 : List Nat := [3, 2, 1, 3, 3, 10]
def baseStart_3409138 : Nat := 118140960795 + 3409138 * 2 ^ 59
def prefixEnd_3409138 : Nat := 4983230072969 + 3 ^ 40 * 3409138 * 2
def baseEnd_3409138 : Nat := 14407624786070682844417

theorem tailTrace_3409138 : CollatzResearch.WordTrace tailWord_3409138 prefixEnd_3409138 14407624786070682844417 := by
  unfold tailWord_3409138
  simp only [CollatzResearch.WordTrace]
  refine ⟨31085369480820683815365017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82894318615521823507640045 31085369480820683815365017)
  ·
    refine ⟨23314027110615512861523763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31085369480820683815365017 23314027110615512861523763)
    ·
      refine ⟨34971040665923269292285645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23314027110615512861523763 34971040665923269292285645)
      ·
        refine ⟨13114140249721225984607117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34971040665923269292285645 13114140249721225984607117)
        ·
          refine ⟨4917802593645459744227669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13114140249721225984607117 4917802593645459744227669)
          ·
            refine ⟨14407624786070682844417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4917802593645459744227669 14407624786070682844417)
            ·
              rfl

theorem cell22_3409138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 10].length) (baseStart_3409138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409138 prefixEnd_3409138 := by exact prefixLift 3409138
  have htrace : WordTrace (prefixWord ++ tailWord_3409138) baseStart_3409138 baseEnd_3409138 := by
    simpa [prefixWord, tailWord_3409138, baseEnd_3409138] using wordTrace_append hprefix tailTrace_3409138
  have hstable : (prefixWord ++ tailWord_3409138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409138).length < 2 ^ (prefixWord ++ tailWord_3409138).sum := by decide
  have hdescent : baseEnd_3409138 < baseStart_3409138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409187 : List Nat := [1, 1, 1, 4, 2, 3, 1, 5, 1, 3]
def baseStart_3409187 : Nat := 118140960795 + 3409187 * 2 ^ 59
def prefixEnd_3409187 : Nat := 4983230072969 + 3 ^ 40 * 3409187 * 2
def baseEnd_3409187 : Nat := 1167034381373105515922627

theorem tailTrace_3409187 : CollatzResearch.WordTrace tailWord_3409187 prefixEnd_3409187 1167034381373105515922627 := by
  unfold tailWord_3409187
  simp only [CollatzResearch.WordTrace]
  refine ⟨124343265100105216629993815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82895510066736811086662543 124343265100105216629993815)
  ·
    refine ⟨186514897650157824944990723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124343265100105216629993815 186514897650157824944990723)
    ·
      refine ⟨279772346475236737417486085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186514897650157824944990723 279772346475236737417486085)
      ·
        refine ⟨52457314964106888265778641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279772346475236737417486085 52457314964106888265778641)
        ·
          refine ⟨39342986223080166199333981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52457314964106888265778641 39342986223080166199333981)
          ·
            refine ⟨14753619833655062324750243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39342986223080166199333981 14753619833655062324750243)
            ·
              refine ⟨22130429750482593487125365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14753619833655062324750243 22130429750482593487125365)
              ·
                refine ⟨2074727789107743139418003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22130429750482593487125365 2074727789107743139418003)
                ·
                  refine ⟨3112091683661614709127005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074727789107743139418003 3112091683661614709127005)
                  ·
                    refine ⟨1167034381373105515922627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112091683661614709127005 1167034381373105515922627)
                    ·
                      rfl

theorem cell22_3409187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 5, 1, 3].length) (baseStart_3409187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409187 prefixEnd_3409187 := by exact prefixLift 3409187
  have htrace : WordTrace (prefixWord ++ tailWord_3409187) baseStart_3409187 baseEnd_3409187 := by
    simpa [prefixWord, tailWord_3409187, baseEnd_3409187] using wordTrace_append hprefix tailTrace_3409187
  have hstable : (prefixWord ++ tailWord_3409187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409187).length < 2 ^ (prefixWord ++ tailWord_3409187).sum := by decide
  have hdescent : baseEnd_3409187 < baseStart_3409187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409204 : List Nat := [2, 5, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_3409204 : Nat := 118140960795 + 3409204 * 2 ^ 59
def prefixEnd_3409204 : Nat := 4983230072969 + 3 ^ 40 * 3409204 * 2
def baseEnd_3409204 : Nat := 1167040200820523138247575

theorem tailTrace_3409204 : CollatzResearch.WordTrace tailWord_3409204 prefixEnd_3409204 1167040200820523138247575 := by
  unfold tailWord_3409204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62171942570521814266681333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82895923427362419022241777 62171942570521814266681333)
  ·
    refine ⟨5828619615986420087501375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62171942570521814266681333 5828619615986420087501375)
    ·
      refine ⟨8742929423979630131252063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828619615986420087501375 8742929423979630131252063)
      ·
        refine ⟨13114394135969445196878095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742929423979630131252063 13114394135969445196878095)
        ·
          refine ⟨19671591203954167795317143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13114394135969445196878095 19671591203954167795317143)
          ·
            refine ⟨29507386805931251692975715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19671591203954167795317143 29507386805931251692975715)
            ·
              refine ⟨44261080208896877539463573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29507386805931251692975715 44261080208896877539463573)
              ·
                refine ⟨2074738134792041134662355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44261080208896877539463573 2074738134792041134662355)
                ·
                  refine ⟨3112107202188061701993533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074738134792041134662355 3112107202188061701993533)
                  ·
                    refine ⟨1167040200820523138247575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112107202188061701993533 1167040200820523138247575)
                    ·
                      rfl

theorem cell22_3409204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_3409204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409204 prefixEnd_3409204 := by exact prefixLift 3409204
  have htrace : WordTrace (prefixWord ++ tailWord_3409204) baseStart_3409204 baseEnd_3409204 := by
    simpa [prefixWord, tailWord_3409204, baseEnd_3409204] using wordTrace_append hprefix tailTrace_3409204
  have hstable : (prefixWord ++ tailWord_3409204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409204).length < 2 ^ (prefixWord ++ tailWord_3409204).sum := by decide
  have hdescent : baseEnd_3409204 < baseStart_3409204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409273 : List Nat := [1, 2, 1, 3, 2, 1, 3, 9]
def baseStart_3409273 : Nat := 118140960795 + 3409273 * 2 ^ 59
def prefixEnd_3409273 : Nat := 4983230072969 + 3 ^ 40 * 3409273 * 2
def baseEnd_3409273 : Nat := 129673757881181106474707

theorem tailTrace_3409273 : CollatzResearch.WordTrace tailWord_3409273 prefixEnd_3409273 129673757881181106474707 := by
  unfold tailWord_3409273
  simp only [CollatzResearch.WordTrace]
  refine ⟨124346401777793653317624473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82897601185195768878416315 124346401777793653317624473)
  ·
    refine ⟨93259801333345239988218355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124346401777793653317624473 93259801333345239988218355)
    ·
      refine ⟨139889702000017859982327533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93259801333345239988218355 139889702000017859982327533)
      ·
        refine ⟨52458638250006697493372825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139889702000017859982327533 52458638250006697493372825)
        ·
          refine ⟨39343978687505023120029619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52458638250006697493372825 39343978687505023120029619)
          ·
            refine ⟨59015968031257534680044429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39343978687505023120029619 59015968031257534680044429)
            ·
              refine ⟨22130988011721575505016661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59015968031257534680044429 22130988011721575505016661)
              ·
                refine ⟨129673757881181106474707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22130988011721575505016661 129673757881181106474707)
                ·
                  rfl

theorem cell22_3409273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 9].length) (baseStart_3409273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409273 prefixEnd_3409273 := by exact prefixLift 3409273
  have htrace : WordTrace (prefixWord ++ tailWord_3409273) baseStart_3409273 baseEnd_3409273 := by
    simpa [prefixWord, tailWord_3409273, baseEnd_3409273] using wordTrace_append hprefix tailTrace_3409273
  have hstable : (prefixWord ++ tailWord_3409273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409273).length < 2 ^ (prefixWord ++ tailWord_3409273).sum := by decide
  have hdescent : baseEnd_3409273 < baseStart_3409273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409277 : List Nat := [1, 4, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_3409277 : Nat := 118140960795 + 3409277 * 2 ^ 59
def prefixEnd_3409277 : Nat := 4983230072969 + 3 ^ 40 * 3409277 * 2
def baseEnd_3409277 : Nat := 1167065190212375281172351

theorem tailTrace_3409277 : CollatzResearch.WordTrace tailWord_3409277 prefixEnd_3409277 1167065190212375281172351 := by
  unfold tailWord_3409277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124346547669779162000770085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82897698446519441333846723 124346547669779162000770085)
  ·
    refine ⟨23314977688083592875144391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124346547669779162000770085 23314977688083592875144391)
    ·
      refine ⟨34972466532125389312716587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23314977688083592875144391 34972466532125389312716587)
      ·
        refine ⟨52458699798188083969074881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34972466532125389312716587 52458699798188083969074881)
        ·
          refine ⟨39344024848641062976806161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52458699798188083969074881 39344024848641062976806161)
          ·
            refine ⟨29508018636480797232604621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39344024848641062976806161 29508018636480797232604621)
            ·
              refine ⟨11065506988680298962226733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29508018636480797232604621 11065506988680298962226733)
              ·
                refine ⟨4149565120755112110835025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11065506988680298962226733 4149565120755112110835025)
                ·
                  refine ⟨3112173840566334083126269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4149565120755112110835025 3112173840566334083126269)
                  ·
                    refine ⟨1167065190212375281172351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112173840566334083126269 1167065190212375281172351)
                    ·
                      rfl

theorem cell22_3409277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_3409277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409277 prefixEnd_3409277 := by exact prefixLift 3409277
  have htrace : WordTrace (prefixWord ++ tailWord_3409277) baseStart_3409277 baseEnd_3409277 := by
    simpa [prefixWord, tailWord_3409277, baseEnd_3409277] using wordTrace_append hprefix tailTrace_3409277
  have hstable : (prefixWord ++ tailWord_3409277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409277).length < 2 ^ (prefixWord ++ tailWord_3409277).sum := by decide
  have hdescent : baseEnd_3409277 < baseStart_3409277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409281 : List Nat := [1, 2, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3409281 : Nat := 118140960795 + 3409281 * 2 ^ 59
def prefixEnd_3409281 : Nat := 4983230072969 + 3 ^ 40 * 3409281 * 2
def baseEnd_3409281 : Nat := 1167066559494120604072339

theorem tailTrace_3409281 : CollatzResearch.WordTrace tailWord_3409281 prefixEnd_3409281 1167066559494120604072339 := by
  unfold tailWord_3409281
  simp only [CollatzResearch.WordTrace]
  refine ⟨124346693561764670683915697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82897795707843113789277131 124346693561764670683915697)
  ·
    refine ⟨93260020171323503012936773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124346693561764670683915697 93260020171323503012936773)
    ·
      refine ⟨17486253782123156814925645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93260020171323503012936773 17486253782123156814925645)
      ·
        refine ⟨6557345168296183805597117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17486253782123156814925645 6557345168296183805597117)
        ·
          refine ⟨2459004438111068927098919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6557345168296183805597117 2459004438111068927098919)
          ·
            refine ⟨3688506657166603390648379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459004438111068927098919 3688506657166603390648379)
            ·
              refine ⟨5532759985749905085972569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688506657166603390648379 5532759985749905085972569)
              ·
                refine ⟨4149569989312428814479427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5532759985749905085972569 4149569989312428814479427)
                ·
                  refine ⟨6224354983968643221719141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4149569989312428814479427 6224354983968643221719141)
                  ·
                    refine ⟨1167066559494120604072339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224354983968643221719141 1167066559494120604072339)
                    ·
                      rfl

theorem cell22_3409281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3409281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409281 prefixEnd_3409281 := by exact prefixLift 3409281
  have htrace : WordTrace (prefixWord ++ tailWord_3409281) baseStart_3409281 baseEnd_3409281 := by
    simpa [prefixWord, tailWord_3409281, baseEnd_3409281] using wordTrace_append hprefix tailTrace_3409281
  have hstable : (prefixWord ++ tailWord_3409281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409281).length < 2 ^ (prefixWord ++ tailWord_3409281).sum := by decide
  have hdescent : baseEnd_3409281 < baseStart_3409281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409335 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 5]
def baseStart_3409335 : Nat := 118140960795 + 3409335 * 2 ^ 59
def prefixEnd_3409335 : Nat := 4983230072969 + 3 ^ 40 * 3409335 * 2
def baseEnd_3409335 : Nat := 389028348265894154407391

theorem tailTrace_3409335 : CollatzResearch.WordTrace tailWord_3409335 prefixEnd_3409335 389028348265894154407391 := by
  unfold tailWord_3409335
  simp only [CollatzResearch.WordTrace]
  refine ⟨124348663103569037906381459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82899108735712691937587639 124348663103569037906381459)
  ·
    refine ⟨186522994655353556859572189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124348663103569037906381459 186522994655353556859572189)
    ·
      refine ⟨69946122995757583822339571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186522994655353556859572189 69946122995757583822339571)
      ·
        refine ⟨104919184493636375733509357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69946122995757583822339571 104919184493636375733509357)
        ·
          refine ⟨39344694185113640900066009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104919184493636375733509357 39344694185113640900066009)
          ·
            refine ⟨29508520638835230675049507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39344694185113640900066009 29508520638835230675049507)
            ·
              refine ⟨44262780958252846012574261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29508520638835230675049507 44262780958252846012574261)
              ·
                refine ⟨4149635714836204313678837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44262780958252846012574261 4149635714836204313678837)
                ·
                  refine ⟨389028348265894154407391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4149635714836204313678837 389028348265894154407391)
                  ·
                    rfl

theorem cell22_3409335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 5].length) (baseStart_3409335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409335 prefixEnd_3409335 := by exact prefixLift 3409335
  have htrace : WordTrace (prefixWord ++ tailWord_3409335) baseStart_3409335 baseEnd_3409335 := by
    simpa [prefixWord, tailWord_3409335, baseEnd_3409335] using wordTrace_append hprefix tailTrace_3409335
  have hstable : (prefixWord ++ tailWord_3409335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409335).length < 2 ^ (prefixWord ++ tailWord_3409335).sum := by decide
  have hdescent : baseEnd_3409335 < baseStart_3409335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409356 : List Nat := [2, 2, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_3409356 : Nat := 118140960795 + 3409356 * 2 ^ 59
def prefixEnd_3409356 : Nat := 4983230072969 + 3 ^ 40 * 3409356 * 2
def baseEnd_3409356 : Nat := 1167092233526845408447109

theorem tailTrace_3409356 : CollatzResearch.WordTrace tailWord_3409356 prefixEnd_3409356 1167092233526845408447109 := by
  unfold tailWord_3409356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62174714518246479246447961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82899619357661972328597281 62174714518246479246447961)
  ·
    refine ⟨46631035888684859434835971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62174714518246479246447961 46631035888684859434835971)
    ·
      refine ⟨69946553833027289152253957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46631035888684859434835971 69946553833027289152253957)
      ·
        refine ⟨13114978843692616716047617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69946553833027289152253957 13114978843692616716047617)
        ·
          refine ⟨9836234132769462537035713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13114978843692616716047617 9836234132769462537035713)
          ·
            refine ⟨7377175599577096902776785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9836234132769462537035713 7377175599577096902776785)
            ·
              refine ⟨5532881699682822677082589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377175599577096902776785 5532881699682822677082589)
              ·
                refine ⟨2074830637381058503905971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5532881699682822677082589 2074830637381058503905971)
                ·
                  refine ⟨3112245956071587755858957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2074830637381058503905971 3112245956071587755858957)
                  ·
                    refine ⟨1167092233526845408447109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112245956071587755858957 1167092233526845408447109)
                    ·
                      rfl

theorem cell22_3409356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_3409356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409356 prefixEnd_3409356 := by exact prefixLift 3409356
  have htrace : WordTrace (prefixWord ++ tailWord_3409356) baseStart_3409356 baseEnd_3409356 := by
    simpa [prefixWord, tailWord_3409356, baseEnd_3409356] using wordTrace_append hprefix tailTrace_3409356
  have hstable : (prefixWord ++ tailWord_3409356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409356).length < 2 ^ (prefixWord ++ tailWord_3409356).sum := by decide
  have hdescent : baseEnd_3409356 < baseStart_3409356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409395 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 1, 5]
def baseStart_3409395 : Nat := 118140960795 + 3409395 * 2 ^ 59
def prefixEnd_3409395 : Nat := 4983230072969 + 3 ^ 40 * 3409395 * 2
def baseEnd_3409395 : Nat := 1167105584023862306721989

theorem tailTrace_3409395 : CollatzResearch.WordTrace tailWord_3409395 prefixEnd_3409395 1167105584023862306721989 := by
  unfold tailWord_3409395
  simp only [CollatzResearch.WordTrace]
  refine ⟨124350851483351668153565639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82900567655567778769043759 124350851483351668153565639)
  ·
    refine ⟨186526277225027502230348459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124350851483351668153565639 186526277225027502230348459)
    ·
      refine ⟨279789415837541253345522689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186526277225027502230348459 279789415837541253345522689)
      ·
        refine ⟨209842061878155940009142017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279789415837541253345522689 209842061878155940009142017)
        ·
          refine ⟨157381546408616955006856513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209842061878155940009142017 157381546408616955006856513)
          ·
            refine ⟨118036159806462716255142385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157381546408616955006856513 118036159806462716255142385)
            ·
              refine ⟨88527119854847037191356789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118036159806462716255142385 88527119854847037191356789)
              ·
                refine ⟨8299417486391909736689699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88527119854847037191356789 8299417486391909736689699)
                ·
                  refine ⟨12449126229587864605034549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8299417486391909736689699 12449126229587864605034549)
                  ·
                    refine ⟨1167105584023862306721989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12449126229587864605034549 1167105584023862306721989)
                    ·
                      rfl

theorem cell22_3409395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 5].length) (baseStart_3409395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409395 prefixEnd_3409395 := by exact prefixLift 3409395
  have htrace : WordTrace (prefixWord ++ tailWord_3409395) baseStart_3409395 baseEnd_3409395 := by
    simpa [prefixWord, tailWord_3409395, baseEnd_3409395] using wordTrace_append hprefix tailTrace_3409395
  have hstable : (prefixWord ++ tailWord_3409395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409395).length < 2 ^ (prefixWord ++ tailWord_3409395).sum := by decide
  have hdescent : baseEnd_3409395 < baseStart_3409395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409427 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 2, 4]
def baseStart_3409427 : Nat := 118140960795 + 3409427 * 2 ^ 59
def prefixEnd_3409427 : Nat := 4983230072969 + 3 ^ 40 * 3409427 * 2
def baseEnd_3409427 : Nat := 1167116538277824889921891

theorem tailTrace_3409427 : CollatzResearch.WordTrace tailWord_3409427 prefixEnd_3409427 1167116538277824889921891 := by
  unfold tailWord_3409427
  simp only [CollatzResearch.WordTrace]
  refine ⟨124352018619235737618730535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82901345746157158412487023 124352018619235737618730535)
  ·
    refine ⟨186528027928853606428095803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124352018619235737618730535 186528027928853606428095803)
    ·
      refine ⟨279792041893280409642143705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186528027928853606428095803 279792041893280409642143705)
      ·
        refine ⟨209844031419960307231607779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279792041893280409642143705 209844031419960307231607779)
        ·
          refine ⟨314766047129940460847411669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209844031419960307231607779 314766047129940460847411669)
          ·
            refine ⟨7377329229607979551111211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 314766047129940460847411669 7377329229607979551111211)
            ·
              refine ⟨11065993844411969326666817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377329229607979551111211 11065993844411969326666817)
              ·
                refine ⟨8299495383308976995000113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11065993844411969326666817 8299495383308976995000113)
                ·
                  refine ⟨6224621537481732746250085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8299495383308976995000113 6224621537481732746250085)
                  ·
                    refine ⟨1167116538277824889921891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6224621537481732746250085 1167116538277824889921891)
                    ·
                      rfl

theorem cell22_3409427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 4].length) (baseStart_3409427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409427 prefixEnd_3409427 := by exact prefixLift 3409427
  have htrace : WordTrace (prefixWord ++ tailWord_3409427) baseStart_3409427 baseEnd_3409427 := by
    simpa [prefixWord, tailWord_3409427, baseEnd_3409427] using wordTrace_append hprefix tailTrace_3409427
  have hstable : (prefixWord ++ tailWord_3409427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409427).length < 2 ^ (prefixWord ++ tailWord_3409427).sum := by decide
  have hdescent : baseEnd_3409427 < baseStart_3409427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409457 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 5, 3]
def baseStart_3409457 : Nat := 118140960795 + 3409457 * 2 ^ 59
def prefixEnd_3409457 : Nat := 4983230072969 + 3 ^ 40 * 3409457 * 2
def baseEnd_3409457 : Nat := 1167126807890914811671799

theorem tailTrace_3409457 : CollatzResearch.WordTrace tailWord_3409457 prefixEnd_3409457 1167126807890914811671799 := by
  unfold tailWord_3409457
  simp only [CollatzResearch.WordTrace]
  refine ⟨124353112809127052742322625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82902075206084701828215083 124353112809127052742322625)
  ·
    refine ⟨93264834606845289556741969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124353112809127052742322625 93264834606845289556741969)
    ·
      refine ⟨69948625955133967167556477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93264834606845289556741969 69948625955133967167556477)
      ·
        refine ⟨26230734733175237687833679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69948625955133967167556477 26230734733175237687833679)
        ·
          refine ⟨39346102099762856531750519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26230734733175237687833679 39346102099762856531750519)
          ·
            refine ⟨59019153149644284797625779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39346102099762856531750519 59019153149644284797625779)
            ·
              refine ⟨88528729724466427196438669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59019153149644284797625779 88528729724466427196438669)
              ·
                refine ⟨33198273646674910198664501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88528729724466427196438669 33198273646674910198664501)
                ·
                  refine ⟨3112338154375772831124797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33198273646674910198664501 3112338154375772831124797)
                  ·
                    refine ⟨1167126807890914811671799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112338154375772831124797 1167126807890914811671799)
                    ·
                      rfl

theorem cell22_3409457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_3409457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409457 prefixEnd_3409457 := by exact prefixLift 3409457
  have htrace : WordTrace (prefixWord ++ tailWord_3409457) baseStart_3409457 baseEnd_3409457 := by
    simpa [prefixWord, tailWord_3409457, baseEnd_3409457] using wordTrace_append hprefix tailTrace_3409457
  have hstable : (prefixWord ++ tailWord_3409457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409457).length < 2 ^ (prefixWord ++ tailWord_3409457).sum := by decide
  have hdescent : baseEnd_3409457 < baseStart_3409457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409607 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3409607 : Nat := 118140960795 + 3409607 * 2 ^ 59
def prefixEnd_3409607 : Nat := 4983230072969 + 3 ^ 40 * 3409607 * 2
def baseEnd_3409607 : Nat := 1167178155956364420421339

theorem tailTrace_3409607 : CollatzResearch.WordTrace tailWord_3409607 prefixEnd_3409607 1167178155956364420421339 := by
  unfold tailWord_3409607
  simp only [CollatzResearch.WordTrace]
  refine ⟨124358583758583628360283075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82905722505722418906855383 124358583758583628360283075)
  ·
    refine ⟨186537875637875442540424613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124358583758583628360283075 186537875637875442540424613)
    ·
      refine ⟨34975851682101645476329615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186537875637875442540424613 34975851682101645476329615)
      ·
        refine ⟨52463777523152468214494423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34975851682101645476329615 52463777523152468214494423)
        ·
          refine ⟨78695666284728702321741635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52463777523152468214494423 78695666284728702321741635)
          ·
            refine ⟨118043499427093053482612453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78695666284728702321741635 118043499427093053482612453)
            ·
              refine ⟨22133156142579947527989835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118043499427093053482612453 22133156142579947527989835)
              ·
                refine ⟨33199734213869921291984753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22133156142579947527989835 33199734213869921291984753)
                ·
                  refine ⟨24899800660402440968988565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33199734213869921291984753 24899800660402440968988565)
                  ·
                    refine ⟨1167178155956364420421339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24899800660402440968988565 1167178155956364420421339)
                    ·
                      rfl

theorem cell22_3409607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3409607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409607 prefixEnd_3409607 := by exact prefixLift 3409607
  have htrace : WordTrace (prefixWord ++ tailWord_3409607) baseStart_3409607 baseEnd_3409607 := by
    simpa [prefixWord, tailWord_3409607, baseEnd_3409607] using wordTrace_append hprefix tailTrace_3409607
  have hstable : (prefixWord ++ tailWord_3409607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409607).length < 2 ^ (prefixWord ++ tailWord_3409607).sum := by decide
  have hdescent : baseEnd_3409607 < baseStart_3409607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409671 : List Nat := [1, 1, 4, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3409671 : Nat := 118140960795 + 3409671 * 2 ^ 59
def prefixEnd_3409671 : Nat := 4983230072969 + 3 ^ 40 * 3409671 * 2
def baseEnd_3409671 : Nat := 1167200064464289586821143

theorem tailTrace_3409671 : CollatzResearch.WordTrace tailWord_3409671 prefixEnd_3409671 1167200064464289586821143 := by
  unfold tailWord_3409671
  simp only [CollatzResearch.WordTrace]
  refine ⟨124360918030351767290612867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82907278686901178193741911 124360918030351767290612867)
  ·
    refine ⟨186541377045527650935919301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124360918030351767290612867 186541377045527650935919301)
    ·
      refine ⟨34976508196036434550484869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186541377045527650935919301 34976508196036434550484869)
      ·
        refine ⟨6558095286756831478215913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34976508196036434550484869 6558095286756831478215913)
        ·
          refine ⟨4918571465067623608661935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6558095286756831478215913 4918571465067623608661935)
          ·
            refine ⟨7377857197601435412992903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918571465067623608661935 7377857197601435412992903)
            ·
              refine ⟨11066785796402153119489355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377857197601435412992903 11066785796402153119489355)
              ·
                refine ⟨16600178694603229679234033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11066785796402153119489355 16600178694603229679234033)
                ·
                  refine ⟨12450134020952422259425525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16600178694603229679234033 12450134020952422259425525)
                  ·
                    refine ⟨1167200064464289586821143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12450134020952422259425525 1167200064464289586821143)
                    ·
                      rfl

theorem cell22_3409671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3409671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409671 prefixEnd_3409671 := by exact prefixLift 3409671
  have htrace : WordTrace (prefixWord ++ tailWord_3409671) baseStart_3409671 baseEnd_3409671 := by
    simpa [prefixWord, tailWord_3409671, baseEnd_3409671] using wordTrace_append hprefix tailTrace_3409671
  have hstable : (prefixWord ++ tailWord_3409671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409671).length < 2 ^ (prefixWord ++ tailWord_3409671).sum := by decide
  have hdescent : baseEnd_3409671 < baseStart_3409671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409694 : List Nat := [4, 3, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3409694 : Nat := 118140960795 + 3409694 * 2 ^ 59
def prefixEnd_3409694 : Nat := 4983230072969 + 3 ^ 40 * 3409694 * 2
def baseEnd_3409694 : Nat := 1167207937834325193496073

theorem tailTrace_3409694 : CollatzResearch.WordTrace tailWord_3409694 prefixEnd_3409694 1167207937834325193496073 := by
  unfold tailWord_3409694
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545219613658555277337517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82907837939512294812466757 15545219613658555277337517)
  ·
    refine ⟨5829457355121958229001569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15545219613658555277337517 5829457355121958229001569)
    ·
      refine ⟨4372093016341468671751177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5829457355121958229001569 4372093016341468671751177)
      ·
        refine ⟨3279069762256101503813383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4372093016341468671751177 3279069762256101503813383)
        ·
          refine ⟨4918604643384152255720075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279069762256101503813383 4918604643384152255720075)
          ·
            refine ⟨7377906965076228383580113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918604643384152255720075 7377906965076228383580113)
            ·
              refine ⟨5533430223807171287685085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377906965076228383580113 5533430223807171287685085)
              ·
                refine ⟨2075036333927689232881907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5533430223807171287685085 2075036333927689232881907)
                ·
                  refine ⟨3112554500891533849322861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075036333927689232881907 3112554500891533849322861)
                  ·
                    refine ⟨1167207937834325193496073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112554500891533849322861 1167207937834325193496073)
                    ·
                      rfl

theorem cell22_3409694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3409694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409694 prefixEnd_3409694 := by exact prefixLift 3409694
  have htrace : WordTrace (prefixWord ++ tailWord_3409694) baseStart_3409694 baseEnd_3409694 := by
    simpa [prefixWord, tailWord_3409694, baseEnd_3409694] using wordTrace_append hprefix tailTrace_3409694
  have hstable : (prefixWord ++ tailWord_3409694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409694).length < 2 ^ (prefixWord ++ tailWord_3409694).sum := by decide
  have hdescent : baseEnd_3409694 < baseStart_3409694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409699 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 1, 5]
def baseStart_3409699 : Nat := 118140960795 + 3409699 * 2 ^ 59
def prefixEnd_3409699 : Nat := 4983230072969 + 3 ^ 40 * 3409699 * 2
def baseEnd_3409699 : Nat := 1167209649436506847121057

theorem tailTrace_3409699 : CollatzResearch.WordTrace tailWord_3409699 prefixEnd_3409699 1167209649436506847121057 := by
  unfold tailWord_3409699
  simp only [CollatzResearch.WordTrace]
  refine ⟨124361939274250328072632151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82907959516166885381754767 124361939274250328072632151)
  ·
    refine ⟨186542908911375492108948227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124361939274250328072632151 186542908911375492108948227)
    ·
      refine ⟨279814363367063238163422341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186542908911375492108948227 279814363367063238163422341)
      ·
        refine ⟨52465193131324357155641689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279814363367063238163422341 52465193131324357155641689)
        ·
          refine ⟨39348894848493267866731267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52465193131324357155641689 39348894848493267866731267)
          ·
            refine ⟨59023342272739901800096901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39348894848493267866731267 59023342272739901800096901)
            ·
              refine ⟨11066876676138731587518169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59023342272739901800096901 11066876676138731587518169)
              ·
                refine ⟨8300157507104048690638627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11066876676138731587518169 8300157507104048690638627)
                ·
                  refine ⟨12450236260656073035957941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8300157507104048690638627 12450236260656073035957941)
                  ·
                    refine ⟨1167209649436506847121057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12450236260656073035957941 1167209649436506847121057)
                    ·
                      rfl

theorem cell22_3409699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 5].length) (baseStart_3409699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409699 prefixEnd_3409699 := by exact prefixLift 3409699
  have htrace : WordTrace (prefixWord ++ tailWord_3409699) baseStart_3409699 baseEnd_3409699 := by
    simpa [prefixWord, tailWord_3409699, baseEnd_3409699] using wordTrace_append hprefix tailTrace_3409699
  have hstable : (prefixWord ++ tailWord_3409699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409699).length < 2 ^ (prefixWord ++ tailWord_3409699).sum := by decide
  have hdescent : baseEnd_3409699 < baseStart_3409699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409701 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 4]
def baseStart_3409701 : Nat := 118140960795 + 3409701 * 2 ^ 59
def prefixEnd_3409701 : Nat := 4983230072969 + 3 ^ 40 * 3409701 * 2
def baseEnd_3409701 : Nat := 389070111359126502857017

theorem tailTrace_3409701 : CollatzResearch.WordTrace tailWord_3409701 prefixEnd_3409701 389070111359126502857017 := by
  unfold tailWord_3409701
  simp only [CollatzResearch.WordTrace]
  refine ⟨124362012220243082414204957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82908008146828721609469971 124362012220243082414204957)
  ·
    refine ⟨46635754582591155905326859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124362012220243082414204957 46635754582591155905326859)
    ·
      refine ⟨69953631873886733857990289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46635754582591155905326859 69953631873886733857990289)
      ·
        refine ⟨52465223905415050393492717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69953631873886733857990289 52465223905415050393492717)
        ·
          refine ⟨19674458964530643897559769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52465223905415050393492717 19674458964530643897559769)
          ·
            refine ⟨14755844223397982923169827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19674458964530643897559769 14755844223397982923169827)
            ·
              refine ⟨22133766335096974384754741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14755844223397982923169827 22133766335096974384754741)
              ·
                refine ⟨2075040593915341348570757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22133766335096974384754741 2075040593915341348570757)
                ·
                  refine ⟨389070111359126502857017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075040593915341348570757 389070111359126502857017)
                  ·
                    rfl

theorem cell22_3409701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_3409701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409701 prefixEnd_3409701 := by exact prefixLift 3409701
  have htrace : WordTrace (prefixWord ++ tailWord_3409701) baseStart_3409701 baseEnd_3409701 := by
    simpa [prefixWord, tailWord_3409701, baseEnd_3409701] using wordTrace_append hprefix tailTrace_3409701
  have hstable : (prefixWord ++ tailWord_3409701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409701).length < 2 ^ (prefixWord ++ tailWord_3409701).sum := by decide
  have hdescent : baseEnd_3409701 < baseStart_3409701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409718 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 6]
def baseStart_3409718 : Nat := 118140960795 + 3409718 * 2 ^ 59
def prefixEnd_3409718 : Nat := 4983230072969 + 3 ^ 40 * 3409718 * 2
def baseEnd_3409718 : Nat := 389072051174932376965333

theorem tailTrace_3409718 : CollatzResearch.WordTrace tailWord_3409718 prefixEnd_3409718 389072051174932376965333 := by
  unfold tailWord_3409718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772664516323843394848363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82908421507454329545049205 7772664516323843394848363)
  ·
    refine ⟨11658996774485765092272545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7772664516323843394848363 11658996774485765092272545)
    ·
      refine ⟨8744247580864323819204409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11658996774485765092272545 8744247580864323819204409)
      ·
        refine ⟨6558185685648242864403307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8744247580864323819204409 6558185685648242864403307)
        ·
          refine ⟨9837278528472364296604961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558185685648242864403307 9837278528472364296604961)
          ·
            refine ⟨7377958896354273222453721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9837278528472364296604961 7377958896354273222453721)
            ·
              refine ⟨5533469172265704916840291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7377958896354273222453721 5533469172265704916840291)
              ·
                refine ⟨8300203758398557375260437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5533469172265704916840291 8300203758398557375260437)
                ·
                  refine ⟨389072051174932376965333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8300203758398557375260437 389072051174932376965333)
                  ·
                    rfl

theorem cell22_3409718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_3409718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409718 prefixEnd_3409718 := by exact prefixLift 3409718
  have htrace : WordTrace (prefixWord ++ tailWord_3409718) baseStart_3409718 baseEnd_3409718 := by
    simpa [prefixWord, tailWord_3409718, baseEnd_3409718] using wordTrace_append hprefix tailTrace_3409718
  have hstable : (prefixWord ++ tailWord_3409718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409718).length < 2 ^ (prefixWord ++ tailWord_3409718).sum := by decide
  have hdescent : baseEnd_3409718 < baseStart_3409718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409733 : List Nat := [1, 3, 1, 1, 1, 2, 7, 1, 2, 3]
def baseStart_3409733 : Nat := 118140960795 + 3409733 * 2 ^ 59
def prefixEnd_3409733 : Nat := 4983230072969 + 3 ^ 40 * 3409733 * 2
def baseEnd_3409733 : Nat := 1167221288331342091770953

theorem tailTrace_3409733 : CollatzResearch.WordTrace tailWord_3409733 prefixEnd_3409733 1167221288331342091770953 := by
  unfold tailWord_3409733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124363179356127151879369853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82908786237418101252913235 124363179356127151879369853)
  ·
    refine ⟨46636192258547681954763695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124363179356127151879369853 46636192258547681954763695)
    ·
      refine ⟨69954288387821522932145543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46636192258547681954763695 69954288387821522932145543)
      ·
        refine ⟨104931432581732284398218315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69954288387821522932145543 104931432581732284398218315)
        ·
          refine ⟨157397148872598426597327473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104931432581732284398218315 157397148872598426597327473)
          ·
            refine ⟨118047861654448819947995605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157397148872598426597327473 118047861654448819947995605)
            ·
              refine ⟨2766746757526144217531147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118047861654448819947995605 2766746757526144217531147)
              ·
                refine ⟨4150120136289216326296721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766746757526144217531147 4150120136289216326296721)
                ·
                  refine ⟨3112590102216912244722541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150120136289216326296721 3112590102216912244722541)
                  ·
                    refine ⟨1167221288331342091770953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112590102216912244722541 1167221288331342091770953)
                    ·
                      rfl

theorem cell22_3409733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_3409733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409733 prefixEnd_3409733 := by exact prefixLift 3409733
  have htrace : WordTrace (prefixWord ++ tailWord_3409733) baseStart_3409733 baseEnd_3409733 := by
    simpa [prefixWord, tailWord_3409733, baseEnd_3409733] using wordTrace_append hprefix tailTrace_3409733
  have hstable : (prefixWord ++ tailWord_3409733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409733).length < 2 ^ (prefixWord ++ tailWord_3409733).sum := by decide
  have hdescent : baseEnd_3409733 < baseStart_3409733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409746 : List Nat := [3, 2, 2, 1, 1, 3, 4, 6]
def baseStart_3409746 : Nat := 118140960795 + 3409746 * 2 ^ 59
def prefixEnd_3409746 : Nat := 4983230072969 + 3 ^ 40 * 3409746 * 2
def baseEnd_3409746 : Nat := 129691748721890487910657

theorem tailTrace_3409746 : CollatzResearch.WordTrace tailWord_3409746 prefixEnd_3409746 129691748721890487910657 := by
  unfold tailWord_3409746
  simp only [CollatzResearch.WordTrace]
  refine ⟨31090913376270013774898273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82909102336720036733062061 31090913376270013774898273)
  ·
    refine ⟨23318185032202510331173705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31090913376270013774898273 23318185032202510331173705)
    ·
      refine ⟨17488638774151882748380279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23318185032202510331173705 17488638774151882748380279)
      ·
        refine ⟨26232958161227824122570419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17488638774151882748380279 26232958161227824122570419)
        ·
          refine ⟨39349437241841736183855629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26232958161227824122570419 39349437241841736183855629)
          ·
            refine ⟨14756038965690651068945861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39349437241841736183855629 14756038965690651068945861)
            ·
              refine ⟨2766757306066997075427349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14756038965690651068945861 2766757306066997075427349)
              ·
                refine ⟨129691748721890487910657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766757306066997075427349 129691748721890487910657)
                ·
                  rfl

theorem cell22_3409746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 6].length) (baseStart_3409746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409746 prefixEnd_3409746 := by exact prefixLift 3409746
  have htrace : WordTrace (prefixWord ++ tailWord_3409746) baseStart_3409746 baseEnd_3409746 := by
    simpa [prefixWord, tailWord_3409746, baseEnd_3409746] using wordTrace_append hprefix tailTrace_3409746
  have hstable : (prefixWord ++ tailWord_3409746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409746).length < 2 ^ (prefixWord ++ tailWord_3409746).sum := by decide
  have hdescent : baseEnd_3409746 < baseStart_3409746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409789 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 1, 7]
def baseStart_3409789 : Nat := 118140960795 + 3409789 * 2 ^ 59
def prefixEnd_3409789 : Nat := 4983230072969 + 3 ^ 40 * 3409789 * 2
def baseEnd_3409789 : Nat := 1167240458275776612370781

theorem tailTrace_3409789 : CollatzResearch.WordTrace tailWord_3409789 prefixEnd_3409789 1167240458275776612370781 := by
  unfold tailWord_3409789
  simp only [CollatzResearch.WordTrace]
  refine ⟨124365221843924273443408421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82910147895949515628938947 124365221843924273443408421)
  ·
    refine ⟨23318479095735801270639079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124365221843924273443408421 23318479095735801270639079)
    ·
      refine ⟨34977718643603701905958619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23318479095735801270639079 34977718643603701905958619)
      ·
        refine ⟨52466577965405552858937929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34977718643603701905958619 52466577965405552858937929)
        ·
          refine ⟨39349933474054164644203447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52466577965405552858937929 39349933474054164644203447)
          ·
            refine ⟨59024900211081246966305171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39349933474054164644203447 59024900211081246966305171)
            ·
              refine ⟨88537350316621870449457757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59024900211081246966305171 88537350316621870449457757)
              ·
                refine ⟨33201506368733201418546659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88537350316621870449457757 33201506368733201418546659)
                ·
                  refine ⟨49802259553099802127819989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33201506368733201418546659 49802259553099802127819989)
                  ·
                    refine ⟨1167240458275776612370781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49802259553099802127819989 1167240458275776612370781)
                    ·
                      rfl

theorem cell22_3409789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_3409789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409789 prefixEnd_3409789 := by exact prefixLift 3409789
  have htrace : WordTrace (prefixWord ++ tailWord_3409789) baseStart_3409789 baseEnd_3409789 := by
    simpa [prefixWord, tailWord_3409789, baseEnd_3409789] using wordTrace_append hprefix tailTrace_3409789
  have hstable : (prefixWord ++ tailWord_3409789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409789).length < 2 ^ (prefixWord ++ tailWord_3409789).sum := by decide
  have hdescent : baseEnd_3409789 < baseStart_3409789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409881 : List Nat := [1, 2, 1, 2, 6, 1, 9]
def baseStart_3409881 : Nat := 118140960795 + 3409881 * 2 ^ 59
def prefixEnd_3409881 : Nat := 4983230072969 + 3 ^ 40 * 3409881 * 2
def baseEnd_3409881 : Nat := 43232294509478482928537

theorem tailTrace_3409881 : CollatzResearch.WordTrace tailWord_3409881 prefixEnd_3409881 43232294509478482928537 := by
  unfold tailWord_3409881
  simp only [CollatzResearch.WordTrace]
  refine ⟨124368577359590973155757497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82912384906393982103838331 124368577359590973155757497)
  ·
    refine ⟨93276433019693229866818123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124368577359590973155757497 93276433019693229866818123)
    ·
      refine ⟨139914649529539844800227185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93276433019693229866818123 139914649529539844800227185)
      ·
        refine ⟨104935987147154883600170389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139914649529539844800227185 104935987147154883600170389)
        ·
          refine ⟨4918874397522885168757987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 104935987147154883600170389 4918874397522885168757987)
          ·
            refine ⟨7378311596284327753136981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918874397522885168757987 7378311596284327753136981)
            ·
              refine ⟨43232294509478482928537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7378311596284327753136981 43232294509478482928537)
              ·
                rfl

theorem cell22_3409881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 9].length) (baseStart_3409881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409881 prefixEnd_3409881 := by exact prefixLift 3409881
  have htrace : WordTrace (prefixWord ++ tailWord_3409881) baseStart_3409881 baseEnd_3409881 := by
    simpa [prefixWord, tailWord_3409881, baseEnd_3409881] using wordTrace_append hprefix tailTrace_3409881
  have hstable : (prefixWord ++ tailWord_3409881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409881).length < 2 ^ (prefixWord ++ tailWord_3409881).sum := by decide
  have hdescent : baseEnd_3409881 < baseStart_3409881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409885 : List Nat := [1, 4, 3, 1, 3, 1, 1, 1, 4, 3]
def baseStart_3409885 : Nat := 118140960795 + 3409885 * 2 ^ 59
def prefixEnd_3409885 : Nat := 4983230072969 + 3 ^ 40 * 3409885 * 2
def baseEnd_3409885 : Nat := 1167273321037664361970487

theorem tailTrace_3409885 : CollatzResearch.WordTrace tailWord_3409885 prefixEnd_3409885 1167273321037664361970487 := by
  unfold tailWord_3409885
  simp only [CollatzResearch.WordTrace]
  refine ⟨124368723251576481838903109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82912482167717654559268739 124368723251576481838903109)
  ·
    refine ⟨23319135609670590344794333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124368723251576481838903109 23319135609670590344794333)
    ·
      refine ⟨8744675853626471379297875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23319135609670590344794333 8744675853626471379297875)
      ·
        refine ⟨13117013780439707068946813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8744675853626471379297875 13117013780439707068946813)
        ·
          refine ⟨4918880167664890150855055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13117013780439707068946813 4918880167664890150855055)
          ·
            refine ⟨7378320251497335226282583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918880167664890150855055 7378320251497335226282583)
            ·
              refine ⟨11067480377246002839423875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378320251497335226282583 11067480377246002839423875)
              ·
                refine ⟨16601220565869004259135813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11067480377246002839423875 16601220565869004259135813)
                ·
                  refine ⟨3112728856100438298587965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16601220565869004259135813 3112728856100438298587965)
                  ·
                    refine ⟨1167273321037664361970487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112728856100438298587965 1167273321037664361970487)
                    ·
                      rfl

theorem cell22_3409885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_3409885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409885 prefixEnd_3409885 := by exact prefixLift 3409885
  have htrace : WordTrace (prefixWord ++ tailWord_3409885) baseStart_3409885 baseEnd_3409885 := by
    simpa [prefixWord, tailWord_3409885, baseEnd_3409885] using wordTrace_append hprefix tailTrace_3409885
  have hstable : (prefixWord ++ tailWord_3409885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409885).length < 2 ^ (prefixWord ++ tailWord_3409885).sum := by decide
  have hdescent : baseEnd_3409885 < baseStart_3409885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409902 : List Nat := [4, 1, 2, 1, 3, 2, 3, 1, 2, 3]
def baseStart_3409902 : Nat := 118140960795 + 3409902 * 2 ^ 59
def prefixEnd_3409902 : Nat := 4983230072969 + 3 ^ 40 * 3409902 * 2
def baseEnd_3409902 : Nat := 1167279140485081984295435

theorem tailTrace_3409902 : CollatzResearch.WordTrace tailWord_3409902 prefixEnd_3409902 1167279140485081984295435 := by
  unfold tailWord_3409902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15546167911564361717783995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82912895528343262494847973 15546167911564361717783995)
  ·
    refine ⟨23319251867346542576675993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15546167911564361717783995 23319251867346542576675993)
    ·
      refine ⟨17489438900509906932506995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23319251867346542576675993 17489438900509906932506995)
      ·
        refine ⟨26234158350764860398760493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17489438900509906932506995 26234158350764860398760493)
        ·
          refine ⟨9837809381536822649535185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26234158350764860398760493 9837809381536822649535185)
          ·
            refine ⟨7378357036152616987151389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9837809381536822649535185 7378357036152616987151389)
            ·
              refine ⟨2766883888557231370181771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7378357036152616987151389 2766883888557231370181771)
              ·
                refine ⟨4150325832835847055272657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2766883888557231370181771 4150325832835847055272657)
                ·
                  refine ⟨3112744374626885291454493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150325832835847055272657 3112744374626885291454493)
                  ·
                    refine ⟨1167279140485081984295435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112744374626885291454493 1167279140485081984295435)
                    ·
                      rfl

theorem cell22_3409902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_3409902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409902 prefixEnd_3409902 := by exact prefixLift 3409902
  have htrace : WordTrace (prefixWord ++ tailWord_3409902) baseStart_3409902 baseEnd_3409902 := by
    simpa [prefixWord, tailWord_3409902, baseEnd_3409902] using wordTrace_append hprefix tailTrace_3409902
  have hstable : (prefixWord ++ tailWord_3409902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409902).length < 2 ^ (prefixWord ++ tailWord_3409902).sum := by decide
  have hdescent : baseEnd_3409902 < baseStart_3409902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409913 : List Nat := [1, 2, 1, 3, 1, 4, 2, 2, 3, 3]
def baseStart_3409913 : Nat := 118140960795 + 3409913 * 2 ^ 59
def prefixEnd_3409913 : Nat := 4983230072969 + 3 ^ 40 * 3409913 * 2
def baseEnd_3409913 : Nat := 1167282906009881622270401

theorem tailTrace_3409913 : CollatzResearch.WordTrace tailWord_3409913 prefixEnd_3409913 1167282906009881622270401 := by
  unfold tailWord_3409913
  simp only [CollatzResearch.WordTrace]
  refine ⟨124369744495475042620922393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82913162996983361747281595 124369744495475042620922393)
  ·
    refine ⟨93277308371606281965691795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124369744495475042620922393 93277308371606281965691795)
    ·
      refine ⟨139915962557409422948537693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93277308371606281965691795 139915962557409422948537693)
      ·
        refine ⟨52468485959028533605701635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139915962557409422948537693 52468485959028533605701635)
        ·
          refine ⟨78702728938542800408552453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52468485959028533605701635 78702728938542800408552453)
          ·
            refine ⟨14756761675976775076603585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78702728938542800408552453 14756761675976775076603585)
            ·
              refine ⟨11067571256982581307452689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14756761675976775076603585 11067571256982581307452689)
              ·
                refine ⟨8300678442736935980589517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11067571256982581307452689 8300678442736935980589517)
                ·
                  refine ⟨3112754416026350992721069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8300678442736935980589517 3112754416026350992721069)
                  ·
                    refine ⟨1167282906009881622270401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112754416026350992721069 1167282906009881622270401)
                    ·
                      rfl

theorem cell22_3409913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3, 3].length) (baseStart_3409913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409913 prefixEnd_3409913 := by exact prefixLift 3409913
  have htrace : WordTrace (prefixWord ++ tailWord_3409913) baseStart_3409913 baseEnd_3409913 := by
    simpa [prefixWord, tailWord_3409913, baseEnd_3409913] using wordTrace_append hprefix tailTrace_3409913
  have hstable : (prefixWord ++ tailWord_3409913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409913).length < 2 ^ (prefixWord ++ tailWord_3409913).sum := by decide
  have hdescent : baseEnd_3409913 < baseStart_3409913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3409971 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 6]
def baseStart_3409971 : Nat := 118140960795 + 3409971 * 2 ^ 59
def prefixEnd_3409971 : Nat := 4983230072969 + 3 ^ 40 * 3409971 * 2
def baseEnd_3409971 : Nat := 389100920198396268106741

theorem tailTrace_3409971 : CollatzResearch.WordTrace tailWord_3409971 prefixEnd_3409971 389100920198396268106741 := by
  unfold tailWord_3409971
  simp only [CollatzResearch.WordTrace]
  refine ⟨124371859929264918526533767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82914573286176612351022511 124371859929264918526533767)
  ·
    refine ⟨186557789893897377789800651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124371859929264918526533767 186557789893897377789800651)
    ·
      refine ⟨279836684840846066684700977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186557789893897377789800651 279836684840846066684700977)
      ·
        refine ⟨209877513630634550013525733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279836684840846066684700977 209877513630634550013525733)
        ·
          refine ⟨39352033805743978127536075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 209877513630634550013525733 39352033805743978127536075)
          ·
            refine ⟨59028050708615967191304113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39352033805743978127536075 59028050708615967191304113)
            ·
              refine ⟨44271038031461975393478085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59028050708615967191304113 44271038031461975393478085)
              ·
                refine ⟨8300819630899120386277141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44271038031461975393478085 8300819630899120386277141)
                ·
                  refine ⟨389100920198396268106741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8300819630899120386277141 389100920198396268106741)
                  ·
                    rfl

theorem cell22_3409971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 6].length) (baseStart_3409971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3409971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3409971 prefixEnd_3409971 := by exact prefixLift 3409971
  have htrace : WordTrace (prefixWord ++ tailWord_3409971) baseStart_3409971 baseEnd_3409971 := by
    simpa [prefixWord, tailWord_3409971, baseEnd_3409971] using wordTrace_append hprefix tailTrace_3409971
  have hstable : (prefixWord ++ tailWord_3409971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3409971).length < 2 ^ (prefixWord ++ tailWord_3409971).sum := by decide
  have hdescent : baseEnd_3409971 < baseStart_3409971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3409971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410001 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3410001 : Nat := 118140960795 + 3410001 * 2 ^ 59
def prefixEnd_3410001 : Nat := 4983230072969 + 3 ^ 40 * 3410001 * 2
def baseEnd_3410001 : Nat := 1167313030208278726070131

theorem tailTrace_3410001 : CollatzResearch.WordTrace tailWord_3410001 prefixEnd_3410001 1167313030208278726070131 := by
  unfold tailWord_3410001
  simp only [CollatzResearch.WordTrace]
  refine ⟨124372954119156233650125857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82915302746104155766750571 124372954119156233650125857)
  ·
    refine ⟨93279715589367175237594393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124372954119156233650125857 93279715589367175237594393)
    ·
      refine ⟨69959786692025381428195795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93279715589367175237594393 69959786692025381428195795)
      ·
        refine ⟨104939680038038072142293693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69959786692025381428195795 104939680038038072142293693)
        ·
          refine ⟨39352380014264277053360135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104939680038038072142293693 39352380014264277053360135)
          ·
            refine ⟨59028570021396415580040203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39352380014264277053360135 59028570021396415580040203)
            ·
              refine ⟨88542855032094623370060305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59028570021396415580040203 88542855032094623370060305)
              ·
                refine ⟨66407141274070967527545229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88542855032094623370060305 66407141274070967527545229)
                ·
                  refine ⟨24902677977776612822829461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66407141274070967527545229 24902677977776612822829461)
                  ·
                    refine ⟨1167313030208278726070131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24902677977776612822829461 1167313030208278726070131)
                    ·
                      rfl

theorem cell22_3410001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3410001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410001 prefixEnd_3410001 := by exact prefixLift 3410001
  have htrace : WordTrace (prefixWord ++ tailWord_3410001) baseStart_3410001 baseEnd_3410001 := by
    simpa [prefixWord, tailWord_3410001, baseEnd_3410001] using wordTrace_append hprefix tailTrace_3410001
  have hstable : (prefixWord ++ tailWord_3410001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410001).length < 2 ^ (prefixWord ++ tailWord_3410001).sum := by decide
  have hdescent : baseEnd_3410001 < baseStart_3410001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410005 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 4]
def baseStart_3410005 : Nat := 118140960795 + 3410005 * 2 ^ 59
def prefixEnd_3410005 : Nat := 4983230072969 + 3 ^ 40 * 3410005 * 2
def baseEnd_3410005 : Nat := 389104799830008016323373

theorem tailTrace_3410005 : CollatzResearch.WordTrace tailWord_3410005 prefixEnd_3410005 389104799830008016323373 := by
  unfold tailWord_3410005
  simp only [CollatzResearch.WordTrace]
  refine ⟨124373100011141742333271469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82915400007427828222180979 124373100011141742333271469)
  ·
    refine ⟨46639912504178153374976801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124373100011141742333271469 46639912504178153374976801)
    ·
      refine ⟨34979934378133615031232601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46639912504178153374976801 34979934378133615031232601)
      ·
        refine ⟨26234950783600211273424451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34979934378133615031232601 26234950783600211273424451)
        ·
          refine ⟨39352426175400316910136677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26234950783600211273424451 39352426175400316910136677)
          ·
            refine ⟨7378579907887559420650627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39352426175400316910136677 7378579907887559420650627)
            ·
              refine ⟨11067869861831339130975941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7378579907887559420650627 11067869861831339130975941)
              ·
                refine ⟨2075225599093376087057989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11067869861831339130975941 2075225599093376087057989)
                ·
                  refine ⟨389104799830008016323373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075225599093376087057989 389104799830008016323373)
                  ·
                    rfl

theorem cell22_3410005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_3410005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410005 prefixEnd_3410005 := by exact prefixLift 3410005
  have htrace : WordTrace (prefixWord ++ tailWord_3410005) baseStart_3410005 baseEnd_3410005 := by
    simpa [prefixWord, tailWord_3410005, baseEnd_3410005] using wordTrace_append hprefix tailTrace_3410005
  have hstable : (prefixWord ++ tailWord_3410005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410005).length < 2 ^ (prefixWord ++ tailWord_3410005).sum := by decide
  have hdescent : baseEnd_3410005 < baseStart_3410005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410020 : List Nat := [2, 3, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_3410020 : Nat := 118140960795 + 3410020 * 2 ^ 59
def prefixEnd_3410020 : Nat := 4983230072969 + 3 ^ 40 * 3410020 * 2
def baseEnd_3410020 : Nat := 1167319534296569009845073

theorem tailTrace_3410020 : CollatzResearch.WordTrace tailWord_3410020 prefixEnd_3410020 1167319534296569009845073 := by
  unfold tailWord_3410020
  simp only [CollatzResearch.WordTrace]
  refine ⟨62186823553043699947533757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82915764737391599930045009 62186823553043699947533757)
  ·
    refine ⟨23320058832391387480325159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62186823553043699947533757 23320058832391387480325159)
    ·
      refine ⟨34980088248587081220487739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23320058832391387480325159 34980088248587081220487739)
      ·
        refine ⟨52470132372880621830731609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34980088248587081220487739 52470132372880621830731609)
        ·
          refine ⟨39352599279660466373048707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52470132372880621830731609 39352599279660466373048707)
          ·
            refine ⟨59028898919490699559573061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39352599279660466373048707 59028898919490699559573061)
            ·
              refine ⟨11067918547404506167419949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59028898919490699559573061 11067918547404506167419949)
              ·
                refine ⟨4150469455276689812782481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11067918547404506167419949 4150469455276689812782481)
                ·
                  refine ⟨3112852091457517359586861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150469455276689812782481 3112852091457517359586861)
                  ·
                    refine ⟨1167319534296569009845073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112852091457517359586861 1167319534296569009845073)
                    ·
                      rfl

theorem cell22_3410020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_3410020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410020 prefixEnd_3410020 := by exact prefixLift 3410020
  have htrace : WordTrace (prefixWord ++ tailWord_3410020) baseStart_3410020 baseEnd_3410020 := by
    simpa [prefixWord, tailWord_3410020, baseEnd_3410020] using wordTrace_append hprefix tailTrace_3410020
  have hstable : (prefixWord ++ tailWord_3410020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410020).length < 2 ^ (prefixWord ++ tailWord_3410020).sum := by decide
  have hdescent : baseEnd_3410020 < baseStart_3410020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410033 : List Nat := [1, 2, 2, 2, 1, 1, 7, 6]
def baseStart_3410033 : Nat := 118140960795 + 3410033 * 2 ^ 59
def prefixEnd_3410033 : Nat := 4983230072969 + 3 ^ 40 * 3410033 * 2
def baseEnd_3410033 : Nat := 129702664940249034363337

theorem tailTrace_3410033 : CollatzResearch.WordTrace tailWord_3410033 prefixEnd_3410033 129702664940249034363337 := by
  unfold tailWord_3410033
  simp only [CollatzResearch.WordTrace]
  refine ⟨124374121255040303115290753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82916080836693535410193835 124374121255040303115290753)
  ·
    refine ⟨93280590941280227336468065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124374121255040303115290753 93280590941280227336468065)
    ·
      refine ⟨69960443205960170502351049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93280590941280227336468065 69960443205960170502351049)
      ·
        refine ⟨52470332404470127876763287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69960443205960170502351049 52470332404470127876763287)
        ·
          refine ⟨78705498606705191815144931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52470332404470127876763287 78705498606705191815144931)
          ·
            refine ⟨118058247910057787722717397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78705498606705191815144931 118058247910057787722717397)
            ·
              refine ⟨2766990185391979399751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118058247910057787722717397 2766990185391979399751189)
              ·
                refine ⟨129702664940249034363337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766990185391979399751189 129702664940249034363337)
                ·
                  rfl

theorem cell22_3410033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 6].length) (baseStart_3410033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410033 prefixEnd_3410033 := by exact prefixLift 3410033
  have htrace : WordTrace (prefixWord ++ tailWord_3410033) baseStart_3410033 baseEnd_3410033 := by
    simpa [prefixWord, tailWord_3410033, baseEnd_3410033] using wordTrace_append hprefix tailTrace_3410033
  have hstable : (prefixWord ++ tailWord_3410033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410033).length < 2 ^ (prefixWord ++ tailWord_3410033).sum := by decide
  have hdescent : baseEnd_3410033 < baseStart_3410033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410048 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_3410048 : Nat := 118140960795 + 3410048 * 2 ^ 59
def prefixEnd_3410048 : Nat := 4983230072969 + 3 ^ 40 * 3410048 * 2
def baseEnd_3410048 : Nat := 1167329119268786270144987

theorem tailTrace_3410048 : CollatzResearch.WordTrace tailWord_3410048 prefixEnd_3410048 1167329119268786270144987 := by
  unfold tailWord_3410048
  simp only [CollatzResearch.WordTrace]
  refine ⟨62187334174992980338543399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82916445566657307118057865 62187334174992980338543399)
  ·
    refine ⟨93281001262489470507815099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62187334174992980338543399 93281001262489470507815099)
    ·
      refine ⟨139921501893734205761722649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93281001262489470507815099 139921501893734205761722649)
      ·
        refine ⟨104941126420300654321291987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139921501893734205761722649 104941126420300654321291987)
        ·
          refine ⟨157411689630450981481937981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104941126420300654321291987 157411689630450981481937981)
          ·
            refine ⟨59029383611419118055726743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157411689630450981481937981 59029383611419118055726743)
            ·
              refine ⟨88544075417128677083590115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59029383611419118055726743 88544075417128677083590115)
              ·
                refine ⟨132816113125693015625385173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88544075417128677083590115 132816113125693015625385173)
                ·
                  refine ⟨3112877651383430053719965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132816113125693015625385173 3112877651383430053719965)
                  ·
                    refine ⟨1167329119268786270144987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112877651383430053719965 1167329119268786270144987)
                    ·
                      rfl

theorem cell22_3410048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_3410048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410048 prefixEnd_3410048 := by exact prefixLift 3410048
  have htrace : WordTrace (prefixWord ++ tailWord_3410048) baseStart_3410048 baseEnd_3410048 := by
    simpa [prefixWord, tailWord_3410048, baseEnd_3410048] using wordTrace_append hprefix tailTrace_3410048
  have hstable : (prefixWord ++ tailWord_3410048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410048).length < 2 ^ (prefixWord ++ tailWord_3410048).sum := by decide
  have hdescent : baseEnd_3410048 < baseStart_3410048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410082 : List Nat := [3, 3, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_3410082 : Nat := 118140960795 + 3410082 * 2 ^ 59
def prefixEnd_3410082 : Nat := 4983230072969 + 3 ^ 40 * 3410082 * 2
def baseEnd_3410082 : Nat := 1167340758163621514794883

theorem tailTrace_3410082 : CollatzResearch.WordTrace tailWord_3410082 prefixEnd_3410082 1167340758163621514794883 := by
  unfold tailWord_3410082
  simp only [CollatzResearch.WordTrace]
  refine ⟨31093977107965696120956125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82917272287908522989216333 31093977107965696120956125)
  ·
    refine ⟨11660241415487136045358547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31093977107965696120956125 11660241415487136045358547)
    ·
      refine ⟨17490362123230704068037821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11660241415487136045358547 17490362123230704068037821)
      ·
        refine ⟨6558885796211514025514183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17490362123230704068037821 6558885796211514025514183)
        ·
          refine ⟨9838328694317271038271275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6558885796211514025514183 9838328694317271038271275)
          ·
            refine ⟨14757493041475906557406913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838328694317271038271275 14757493041475906557406913)
            ·
              refine ⟨11068119781106929918055185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14757493041475906557406913 11068119781106929918055185)
              ·
                refine ⟨8301089835830197438541389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11068119781106929918055185 8301089835830197438541389)
                ·
                  refine ⟨3112908688436324039453021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8301089835830197438541389 3112908688436324039453021)
                  ·
                    refine ⟨1167340758163621514794883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112908688436324039453021 1167340758163621514794883)
                    ·
                      rfl

theorem cell22_3410082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_3410082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410082 prefixEnd_3410082 := by exact prefixLift 3410082
  have htrace : WordTrace (prefixWord ++ tailWord_3410082) baseStart_3410082 baseEnd_3410082 := by
    simpa [prefixWord, tailWord_3410082, baseEnd_3410082] using wordTrace_append hprefix tailTrace_3410082
  have hstable : (prefixWord ++ tailWord_3410082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410082).length < 2 ^ (prefixWord ++ tailWord_3410082).sum := by decide
  have hdescent : baseEnd_3410082 < baseStart_3410082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410116 : List Nat := [2, 3, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3410116 : Nat := 118140960795 + 3410116 * 2 ^ 59
def prefixEnd_3410116 : Nat := 4983230072969 + 3 ^ 40 * 3410116 * 2
def baseEnd_3410116 : Nat := 1167352397058456759444779

theorem tailTrace_3410116 : CollatzResearch.WordTrace tailWord_3410116 prefixEnd_3410116 1167352397058456759444779 := by
  unfold tailWord_3410116
  simp only [CollatzResearch.WordTrace]
  refine ⟨62188574256869804145281101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82918099009159738860374801 62188574256869804145281101)
  ·
    refine ⟨23320715346326176554480413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62188574256869804145281101 23320715346326176554480413)
    ·
      refine ⟨8745268254872316207930155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23320715346326176554480413 8745268254872316207930155)
      ·
        refine ⟨13117902382308474311895233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745268254872316207930155 13117902382308474311895233)
        ·
          refine ⟨9838426786731355733921425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13117902382308474311895233 9838426786731355733921425)
          ·
            refine ⟨7378820090048516800441069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9838426786731355733921425 7378820090048516800441069)
            ·
              refine ⟨2767057533768193800165401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7378820090048516800441069 2767057533768193800165401)
              ·
                refine ⟨2075293150326145350124051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767057533768193800165401 2075293150326145350124051)
                ·
                  refine ⟨3112939725489218025186077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075293150326145350124051 3112939725489218025186077)
                  ·
                    refine ⟨1167352397058456759444779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112939725489218025186077 1167352397058456759444779)
                    ·
                      rfl

theorem cell22_3410116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3410116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410116 prefixEnd_3410116 := by exact prefixLift 3410116
  have htrace : WordTrace (prefixWord ++ tailWord_3410116) baseStart_3410116 baseEnd_3410116 := by
    simpa [prefixWord, tailWord_3410116, baseEnd_3410116] using wordTrace_append hprefix tailTrace_3410116
  have hstable : (prefixWord ++ tailWord_3410116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410116).length < 2 ^ (prefixWord ++ tailWord_3410116).sum := by decide
  have hdescent : baseEnd_3410116 < baseStart_3410116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410153 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 6, 4]
def baseStart_3410153 : Nat := 118140960795 + 3410153 * 2 ^ 59
def prefixEnd_3410153 : Nat := 4983230072969 + 3 ^ 40 * 3410153 * 2
def baseEnd_3410153 : Nat := 1167365062914600996269665

theorem tailTrace_3410153 : CollatzResearch.WordTrace tailWord_3410153 prefixEnd_3410153 1167365062914600996269665 := by
  unfold tailWord_3410153
  simp only [CollatzResearch.WordTrace]
  refine ⟨124378498014605563609659113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82918998676403709073106075 124378498014605563609659113)
  ·
    refine ⟨93283873510954172707244335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124378498014605563609659113 93283873510954172707244335)
    ·
      refine ⟨139925810266431259060866503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93283873510954172707244335 139925810266431259060866503)
      ·
        refine ⟨209888715399646888591299755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139925810266431259060866503 209888715399646888591299755)
        ·
          refine ⟨314833073099470332886949633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209888715399646888591299755 314833073099470332886949633)
          ·
            refine ⟨236124804824602749665212225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314833073099470332886949633 236124804824602749665212225)
            ·
              refine ⟨177093603618452062248909169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236124804824602749665212225 177093603618452062248909169)
              ·
                refine ⟨132820202713839046686681877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177093603618452062248909169 132820202713839046686681877)
                ·
                  refine ⟨6225947002211205313438213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132820202713839046686681877 6225947002211205313438213)
                  ·
                    refine ⟨1167365062914600996269665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225947002211205313438213 1167365062914600996269665)
                    ·
                      rfl

theorem cell22_3410153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 6, 4].length) (baseStart_3410153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410153 prefixEnd_3410153 := by exact prefixLift 3410153
  have htrace : WordTrace (prefixWord ++ tailWord_3410153) baseStart_3410153 baseEnd_3410153 := by
    simpa [prefixWord, tailWord_3410153, baseEnd_3410153] using wordTrace_append hprefix tailTrace_3410153
  have hstable : (prefixWord ++ tailWord_3410153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410153).length < 2 ^ (prefixWord ++ tailWord_3410153).sum := by decide
  have hdescent : baseEnd_3410153 < baseStart_3410153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410170 : List Nat := [3, 1, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_3410170 : Nat := 118140960795 + 3410170 * 2 ^ 59
def prefixEnd_3410170 : Nat := 4983230072969 + 3 ^ 40 * 3410170 * 2
def baseEnd_3410170 : Nat := 1167370882362018618594613

theorem tailTrace_3410170 : CollatzResearch.WordTrace tailWord_3410170 prefixEnd_3410170 1167370882362018618594613 := by
  unfold tailWord_3410170
  simp only [CollatzResearch.WordTrace]
  refine ⟨31094779513885993878256991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82919412037029317008685309 31094779513885993878256991)
  ·
    refine ⟨46642169270828990817385487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31094779513885993878256991 46642169270828990817385487)
    ·
      refine ⟨69963253906243486226078231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46642169270828990817385487 69963253906243486226078231)
      ·
        refine ⟨104944880859365229339117347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69963253906243486226078231 104944880859365229339117347)
        ·
          refine ⟨157417321289047844008676021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104944880859365229339117347 157417321289047844008676021)
          ·
            refine ⟨14757873870848235375813377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157417321289047844008676021 14757873870848235375813377)
            ·
              refine ⟨11068405403136176531860033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14757873870848235375813377 11068405403136176531860033)
              ·
                refine ⟨8301304052352132398895025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11068405403136176531860033 8301304052352132398895025)
                ·
                  refine ⟨6225978039264099299171269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8301304052352132398895025 6225978039264099299171269)
                  ·
                    refine ⟨1167370882362018618594613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6225978039264099299171269 1167370882362018618594613)
                    ·
                      rfl

theorem cell22_3410170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_3410170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410170 prefixEnd_3410170 := by exact prefixLift 3410170
  have htrace : WordTrace (prefixWord ++ tailWord_3410170) baseStart_3410170 baseEnd_3410170 := by
    simpa [prefixWord, tailWord_3410170, baseEnd_3410170] using wordTrace_append hprefix tailTrace_3410170
  have hstable : (prefixWord ++ tailWord_3410170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410170).length < 2 ^ (prefixWord ++ tailWord_3410170).sum := by decide
  have hdescent : baseEnd_3410170 < baseStart_3410170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410172 : List Nat := [2, 2, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_3410172 : Nat := 118140960795 + 3410172 * 2 ^ 59
def prefixEnd_3410172 : Nat := 4983230072969 + 3 ^ 40 * 3410172 * 2
def baseEnd_3410172 : Nat := 1167371567002891280044607

theorem tailTrace_3410172 : CollatzResearch.WordTrace tailWord_3410172 prefixEnd_3410172 1167371567002891280044607 := by
  unfold tailWord_3410172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62189595500768364927300385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82919460667691153236400513 62189595500768364927300385)
  ·
    refine ⟨46642196625576273695475289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62189595500768364927300385 46642196625576273695475289)
    ·
      refine ⟨34981647469182205271606467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46642196625576273695475289 34981647469182205271606467)
      ·
        refine ⟨52472471203773307907409701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34981647469182205271606467 52472471203773307907409701)
        ·
          refine ⟨9838588350707495232639319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52472471203773307907409701 9838588350707495232639319)
          ·
            refine ⟨14757882526061242848958979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9838588350707495232639319 14757882526061242848958979)
            ·
              refine ⟨22136823789091864273438469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14757882526061242848958979 22136823789091864273438469)
              ·
                refine ⟨4150654460454724551269713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22136823789091864273438469 4150654460454724551269713)
                ·
                  refine ⟨3112990845341043413452285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4150654460454724551269713 3112990845341043413452285)
                  ·
                    refine ⟨1167371567002891280044607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3112990845341043413452285 1167371567002891280044607)
                    ·
                      rfl

theorem cell22_3410172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_3410172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410172 prefixEnd_3410172 := by exact prefixLift 3410172
  have htrace : WordTrace (prefixWord ++ tailWord_3410172) baseStart_3410172 baseEnd_3410172 := by
    simpa [prefixWord, tailWord_3410172, baseEnd_3410172] using wordTrace_append hprefix tailTrace_3410172
  have hstable : (prefixWord ++ tailWord_3410172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410172).length < 2 ^ (prefixWord ++ tailWord_3410172).sum := by decide
  have hdescent : baseEnd_3410172 < baseStart_3410172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410185 : List Nat := [1, 2, 1, 1, 3, 6, 1, 7]
def baseStart_3410185 : Nat := 118140960795 + 3410185 * 2 ^ 59
def prefixEnd_3410185 : Nat := 4983230072969 + 3 ^ 40 * 3410185 * 2
def baseEnd_3410185 : Nat := 129708446352062619941063

theorem tailTrace_3410185 : CollatzResearch.WordTrace tailWord_3410185 prefixEnd_3410185 129708446352062619941063 := by
  unfold tailWord_3410185
  simp only [CollatzResearch.WordTrace]
  refine ⟨124379665150489633074824009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82919776766993088716549339 124379665150489633074824009)
  ·
    refine ⟨93284748862867224806118007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124379665150489633074824009 93284748862867224806118007)
    ·
      refine ⟨139927123294300837209177011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93284748862867224806118007 139927123294300837209177011)
      ·
        refine ⟨209890684941451255813765517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139927123294300837209177011 209890684941451255813765517)
        ·
          refine ⟨78709006853044220930162069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209890684941451255813765517 78709006853044220930162069)
          ·
            refine ⟨3689484696236447856101347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78709006853044220930162069 3689484696236447856101347)
            ·
              refine ⟨5534227044354671784152021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689484696236447856101347 5534227044354671784152021)
              ·
                refine ⟨129708446352062619941063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5534227044354671784152021 129708446352062619941063)
                ·
                  rfl

theorem cell22_3410185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 7].length) (baseStart_3410185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410185 prefixEnd_3410185 := by exact prefixLift 3410185
  have htrace : WordTrace (prefixWord ++ tailWord_3410185) baseStart_3410185 baseEnd_3410185 := by
    simpa [prefixWord, tailWord_3410185, baseEnd_3410185] using wordTrace_append hprefix tailTrace_3410185
  have hstable : (prefixWord ++ tailWord_3410185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410185).length < 2 ^ (prefixWord ++ tailWord_3410185).sum := by decide
  have hdescent : baseEnd_3410185 < baseStart_3410185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410202 : List Nat := [3, 1, 1, 3, 4, 1, 3, 6]
def baseStart_3410202 : Nat := 118140960795 + 3410202 * 2 ^ 59
def prefixEnd_3410202 : Nat := 4983230072969 + 3 ^ 40 * 3410202 * 2
def baseEnd_3410202 : Nat := 129709092957331244643835

theorem tailTrace_3410202 : CollatzResearch.WordTrace tailWord_3410202 prefixEnd_3410202 129709092957331244643835 := by
  unfold tailWord_3410202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31095071297857011244548215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82920190127618696652128573 31095071297857011244548215)
  ·
    refine ⟨46642606946785516866822323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31095071297857011244548215 46642606946785516866822323)
    ·
      refine ⟨69963910420178275300233485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46642606946785516866822323 69963910420178275300233485)
      ·
        refine ⟨26236466407566853237587557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69963910420178275300233485 26236466407566853237587557)
        ·
          refine ⟨4919337451418784982047667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26236466407566853237587557 4919337451418784982047667)
          ·
            refine ⟨7379006177128177473071501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919337451418784982047667 7379006177128177473071501)
            ·
              refine ⟨2767127316423066552401813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7379006177128177473071501 2767127316423066552401813)
              ·
                refine ⟨129709092957331244643835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2767127316423066552401813 129709092957331244643835)
                ·
                  rfl

theorem cell22_3410202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 6].length) (baseStart_3410202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410202 prefixEnd_3410202 := by exact prefixLift 3410202
  have htrace : WordTrace (prefixWord ++ tailWord_3410202) baseStart_3410202 baseEnd_3410202 := by
    simpa [prefixWord, tailWord_3410202, baseEnd_3410202] using wordTrace_append hprefix tailTrace_3410202
  have hstable : (prefixWord ++ tailWord_3410202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410202).length < 2 ^ (prefixWord ++ tailWord_3410202).sum := by decide
  have hdescent : baseEnd_3410202 < baseStart_3410202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410234 : List Nat := [3, 1, 1, 1, 4, 2, 2, 4, 1, 3]
def baseStart_3410234 : Nat := 118140960795 + 3410234 * 2 ^ 59
def prefixEnd_3410234 : Nat := 4983230072969 + 3 ^ 40 * 3410234 * 2
def baseEnd_3410234 : Nat := 1167392790869943784994417

theorem tailTrace_3410234 : CollatzResearch.WordTrace tailWord_3410234 prefixEnd_3410234 1167392790869943784994417 := by
  unfold tailWord_3410234
  simp only [CollatzResearch.WordTrace]
  refine ⟨31095363081828028610839439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82920968218208076295571837 31095363081828028610839439)
  ·
    refine ⟨46643044622742042916259159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31095363081828028610839439 46643044622742042916259159)
    ·
      refine ⟨69964566934113064374388739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46643044622742042916259159 69964566934113064374388739)
      ·
        refine ⟨104946850401169596561583109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69964566934113064374388739 104946850401169596561583109)
        ·
          refine ⟨19677534450219299355296833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104946850401169596561583109 19677534450219299355296833)
          ·
            refine ⟨14758150837664474516472625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19677534450219299355296833 14758150837664474516472625)
            ·
              refine ⟨11068613128248355887354469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758150837664474516472625 11068613128248355887354469)
              ·
                refine ⟨2075364961546566728878963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11068613128248355887354469 2075364961546566728878963)
                ·
                  refine ⟨3113047442319850093318445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075364961546566728878963 3113047442319850093318445)
                  ·
                    refine ⟨1167392790869943784994417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113047442319850093318445 1167392790869943784994417)
                    ·
                      rfl

theorem cell22_3410234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 4, 1, 3].length) (baseStart_3410234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410234 prefixEnd_3410234 := by exact prefixLift 3410234
  have htrace : WordTrace (prefixWord ++ tailWord_3410234) baseStart_3410234 baseEnd_3410234 := by
    simpa [prefixWord, tailWord_3410234, baseEnd_3410234] using wordTrace_append hprefix tailTrace_3410234
  have hstable : (prefixWord ++ tailWord_3410234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410234).length < 2 ^ (prefixWord ++ tailWord_3410234).sum := by decide
  have hdescent : baseEnd_3410234 < baseStart_3410234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410247 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 5]
def baseStart_3410247 : Nat := 118140960795 + 3410247 * 2 ^ 59
def prefixEnd_3410247 : Nat := 4983230072969 + 3 ^ 40 * 3410247 * 2
def baseEnd_3410247 : Nat := 389132413678538694806459

theorem tailTrace_3410247 : CollatzResearch.WordTrace tailWord_3410247 prefixEnd_3410247 389132413678538694806459 := by
  unfold tailWord_3410247
  simp only [CollatzResearch.WordTrace]
  refine ⟨124381926476265017663580995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82921284317510011775720663 124381926476265017663580995)
  ·
    refine ⟨186572889714397526495371493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124381926476265017663580995 186572889714397526495371493)
    ·
      refine ⟨34982416821449536217882155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186572889714397526495371493 34982416821449536217882155)
      ·
        refine ⟨52473625232174304326823233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34982416821449536217882155 52473625232174304326823233)
        ·
          refine ⟨39355218924130728245117425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52473625232174304326823233 39355218924130728245117425)
          ·
            refine ⟨29516414193098046183838069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39355218924130728245117425 29516414193098046183838069)
            ·
              refine ⟨2767163830602941829734819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29516414193098046183838069 2767163830602941829734819)
              ·
                refine ⟨4150745745904412744602229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2767163830602941829734819 4150745745904412744602229)
                ·
                  refine ⟨389132413678538694806459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150745745904412744602229 389132413678538694806459)
                  ·
                    rfl

theorem cell22_3410247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 5].length) (baseStart_3410247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410247 prefixEnd_3410247 := by exact prefixLift 3410247
  have htrace : WordTrace (prefixWord ++ tailWord_3410247) baseStart_3410247 baseEnd_3410247 := by
    simpa [prefixWord, tailWord_3410247, baseEnd_3410247] using wordTrace_append hprefix tailTrace_3410247
  have hstable : (prefixWord ++ tailWord_3410247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410247).length < 2 ^ (prefixWord ++ tailWord_3410247).sum := by decide
  have hdescent : baseEnd_3410247 < baseStart_3410247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410277 : List Nat := [1, 3, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3410277 : Nat := 118140960795 + 3410277 * 2 ^ 59
def prefixEnd_3410277 : Nat := 4983230072969 + 3 ^ 40 * 3410277 * 2
def baseEnd_3410277 : Nat := 1167407510648706006169285

theorem tailTrace_3410277 : CollatzResearch.WordTrace tailWord_3410277 prefixEnd_3410277 1167407510648706006169285 := by
  unfold tailWord_3410277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124383020666156332787173085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82922013777437555191448723 124383020666156332787173085)
  ·
    refine ⟨46643632749808624795189907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124383020666156332787173085 46643632749808624795189907)
    ·
      refine ⟨69965449124712937192784861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46643632749808624795189907 69965449124712937192784861)
      ·
        refine ⟨26237043421767351447294323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69965449124712937192784861 26237043421767351447294323)
        ·
          refine ⟨39355565132651027170941485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26237043421767351447294323 39355565132651027170941485)
          ·
            refine ⟨14758336924744135189103057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39355565132651027170941485 14758336924744135189103057)
            ·
              refine ⟨11068752693558101391827293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14758336924744135189103057 11068752693558101391827293)
              ·
                refine ⟨4150782260084288021935235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11068752693558101391827293 4150782260084288021935235)
                ·
                  refine ⟨6226173390126432032902853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150782260084288021935235 6226173390126432032902853)
                  ·
                    refine ⟨1167407510648706006169285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226173390126432032902853 1167407510648706006169285)
                    ·
                      rfl

theorem cell22_3410277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3410277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410277 prefixEnd_3410277 := by exact prefixLift 3410277
  have htrace : WordTrace (prefixWord ++ tailWord_3410277) baseStart_3410277 baseEnd_3410277 := by
    simpa [prefixWord, tailWord_3410277, baseEnd_3410277] using wordTrace_append hprefix tailTrace_3410277
  have hstable : (prefixWord ++ tailWord_3410277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410277).length < 2 ^ (prefixWord ++ tailWord_3410277).sum := by decide
  have hdescent : baseEnd_3410277 < baseStart_3410277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410324 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3410324 : Nat := 118140960795 + 3410324 * 2 ^ 59
def prefixEnd_3410324 : Nat := 4983230072969 + 3 ^ 40 * 3410324 * 2
def baseEnd_3410324 : Nat := 1167423599709213550244141

theorem tailTrace_3410324 : CollatzResearch.WordTrace tailWord_3410324 prefixEnd_3410324 1167423599709213550244141 := by
  unfold tailWord_3410324
  simp only [CollatzResearch.WordTrace]
  refine ⟨62192367448493029907067013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82923156597990706542756017 62192367448493029907067013)
  ·
    refine ⟨11661068896592443107575065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62192367448493029907067013 11661068896592443107575065)
    ·
      refine ⟨8745801672444332330681299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11661068896592443107575065 8745801672444332330681299)
      ·
        refine ⟨13118702508666498496021949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745801672444332330681299 13118702508666498496021949)
        ·
          refine ⟨4919513440749936936008231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13118702508666498496021949 4919513440749936936008231)
          ·
            refine ⟨7379270161124905404012347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919513440749936936008231 7379270161124905404012347)
            ·
              refine ⟨11068905241687358106018521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379270161124905404012347 11068905241687358106018521)
              ·
                refine ⟨8301678931265518579513891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11068905241687358106018521 8301678931265518579513891)
                ·
                  refine ⟨12452518396898277869270837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8301678931265518579513891 12452518396898277869270837)
                  ·
                    refine ⟨1167423599709213550244141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12452518396898277869270837 1167423599709213550244141)
                    ·
                      rfl

theorem cell22_3410324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3410324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410324 prefixEnd_3410324 := by exact prefixLift 3410324
  have htrace : WordTrace (prefixWord ++ tailWord_3410324) baseStart_3410324 baseEnd_3410324 := by
    simpa [prefixWord, tailWord_3410324, baseEnd_3410324] using wordTrace_append hprefix tailTrace_3410324
  have hstable : (prefixWord ++ tailWord_3410324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410324).length < 2 ^ (prefixWord ++ tailWord_3410324).sum := by decide
  have hdescent : baseEnd_3410324 < baseStart_3410324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410337 : List Nat := [1, 2, 3, 5, 1, 10]
def baseStart_3410337 : Nat := 118140960795 + 3410337 * 2 ^ 59
def prefixEnd_3410337 : Nat := 4983230072969 + 3 ^ 40 * 3410337 * 2
def baseEnd_3410337 : Nat := 14412691973764022835421

theorem tailTrace_3410337 : CollatzResearch.WordTrace tailWord_3410337 prefixEnd_3410337 14412691973764022835421 := by
  unfold tailWord_3410337
  simp only [CollatzResearch.WordTrace]
  refine ⟨124385209045938963034357265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82923472697292642022904843 124385209045938963034357265)
  ·
    refine ⟨93288906784454222275767949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124385209045938963034357265 93288906784454222275767949)
    ·
      refine ⟨34983340044170333353412981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93288906784454222275767949 34983340044170333353412981)
      ·
        refine ⟨3279688129140968751882467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34983340044170333353412981 3279688129140968751882467)
        ·
          refine ⟨4919532193711453127823701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279688129140968751882467 4919532193711453127823701)
          ·
            refine ⟨14412691973764022835421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4919532193711453127823701 14412691973764022835421)
            ·
              rfl

theorem cell22_3410337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 10].length) (baseStart_3410337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410337 prefixEnd_3410337 := by exact prefixLift 3410337
  have htrace : WordTrace (prefixWord ++ tailWord_3410337) baseStart_3410337 baseEnd_3410337 := by
    simpa [prefixWord, tailWord_3410337, baseEnd_3410337] using wordTrace_append hprefix tailTrace_3410337
  have hstable : (prefixWord ++ tailWord_3410337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410337).length < 2 ^ (prefixWord ++ tailWord_3410337).sum := by decide
  have hdescent : baseEnd_3410337 < baseStart_3410337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410397 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3410397 : Nat := 118140960795 + 3410397 * 2 ^ 59
def prefixEnd_3410397 : Nat := 4983230072969 + 3 ^ 40 * 3410397 * 2
def baseEnd_3410397 : Nat := 1167448589101065693168917

theorem tailTrace_3410397 : CollatzResearch.WordTrace tailWord_3410397 prefixEnd_3410397 1167448589101065693168917 := by
  unfold tailWord_3410397
  simp only [CollatzResearch.WordTrace]
  refine ⟨124387397425721593281541445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82924931617147728854360963 124387397425721593281541445)
  ·
    refine ⟨23322637017322798740289021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124387397425721593281541445 23322637017322798740289021)
    ·
      refine ⟨8745988881496049527608383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23322637017322798740289021 8745988881496049527608383)
      ·
        refine ⟨13118983322244074291412575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8745988881496049527608383 13118983322244074291412575)
        ·
          refine ⟨19678474983366111437118863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13118983322244074291412575 19678474983366111437118863)
          ·
            refine ⟨29517712475049167155678295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678474983366111437118863 29517712475049167155678295)
            ·
              refine ⟨44276568712573750733517443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29517712475049167155678295 44276568712573750733517443)
              ·
                refine ⟨66414853068860626100276165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44276568712573750733517443 66414853068860626100276165)
                ·
                  refine ⟨12452784950411367393801781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66414853068860626100276165 12452784950411367393801781)
                  ·
                    refine ⟨1167448589101065693168917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12452784950411367393801781 1167448589101065693168917)
                    ·
                      rfl

theorem cell22_3410397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3410397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410397 prefixEnd_3410397 := by exact prefixLift 3410397
  have htrace : WordTrace (prefixWord ++ tailWord_3410397) baseStart_3410397 baseEnd_3410397 := by
    simpa [prefixWord, tailWord_3410397, baseEnd_3410397] using wordTrace_append hprefix tailTrace_3410397
  have hstable : (prefixWord ++ tailWord_3410397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410397).length < 2 ^ (prefixWord ++ tailWord_3410397).sum := by decide
  have hdescent : baseEnd_3410397 < baseStart_3410397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410399 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 5]
def baseStart_3410399 : Nat := 118140960795 + 3410399 * 2 ^ 59
def prefixEnd_3410399 : Nat := 4983230072969 + 3 ^ 40 * 3410399 * 2
def baseEnd_3410399 : Nat := 389149757913979451539637

theorem tailTrace_3410399 : CollatzResearch.WordTrace tailWord_3410399 prefixEnd_3410399 389149757913979451539637 := by
  unfold tailWord_3410399
  simp only [CollatzResearch.WordTrace]
  refine ⟨124387470371714347623114251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82924980247809565082076167 124387470371714347623114251)
  ·
    refine ⟨186581205557571521434671377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124387470371714347623114251 186581205557571521434671377)
    ·
      refine ⟨139935904168178641076003533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186581205557571521434671377 139935904168178641076003533)
      ·
        refine ⟨52475964063066990403501325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139935904168178641076003533 52475964063066990403501325)
        ·
          refine ⟨19678486523650121401312997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52475964063066990403501325 19678486523650121401312997)
          ·
            refine ⟨3689716223184397762746187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19678486523650121401312997 3689716223184397762746187)
            ·
              refine ⟨5534574334776596644119281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689716223184397762746187 5534574334776596644119281)
              ·
                refine ⟨4150930751082447483089461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534574334776596644119281 4150930751082447483089461)
                ·
                  refine ⟨389149757913979451539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150930751082447483089461 389149757913979451539637)
                  ·
                    rfl

theorem cell22_3410399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 5].length) (baseStart_3410399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410399 prefixEnd_3410399 := by exact prefixLift 3410399
  have htrace : WordTrace (prefixWord ++ tailWord_3410399) baseStart_3410399 baseEnd_3410399 := by
    simpa [prefixWord, tailWord_3410399, baseEnd_3410399] using wordTrace_append hprefix tailTrace_3410399
  have hstable : (prefixWord ++ tailWord_3410399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410399).length < 2 ^ (prefixWord ++ tailWord_3410399).sum := by decide
  have hdescent : baseEnd_3410399 < baseStart_3410399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410429 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_3410429 : Nat := 118140960795 + 3410429 * 2 ^ 59
def prefixEnd_3410429 : Nat := 4983230072969 + 3 ^ 40 * 3410429 * 2
def baseEnd_3410429 : Nat := 1167459543355028276368819

theorem tailTrace_3410429 : CollatzResearch.WordTrace tailWord_3410429 prefixEnd_3410429 1167459543355028276368819 := by
  unfold tailWord_3410429
  simp only [CollatzResearch.WordTrace]
  refine ⟨124388564561605662746706341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82925709707737108497804227 124388564561605662746706341)
  ·
    refine ⟨23322855855301061765007439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124388564561605662746706341 23322855855301061765007439)
    ·
      refine ⟨34984283782951592647511159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23322855855301061765007439 34984283782951592647511159)
      ·
        refine ⟨52476425674427388971266739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34984283782951592647511159 52476425674427388971266739)
        ·
          refine ⟨78714638511641083456900109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52476425674427388971266739 78714638511641083456900109)
          ·
            refine ⟨29517989441865406296337541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78714638511641083456900109 29517989441865406296337541)
            ·
              refine ⟨5534623020349763680563289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29517989441865406296337541 5534623020349763680563289)
              ·
                refine ⟨4150967265262322760422467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534623020349763680563289 4150967265262322760422467)
                ·
                  refine ⟨6226450897893484140633701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4150967265262322760422467 6226450897893484140633701)
                  ·
                    refine ⟨1167459543355028276368819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226450897893484140633701 1167459543355028276368819)
                    ·
                      rfl

theorem cell22_3410429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_3410429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410429 prefixEnd_3410429 := by exact prefixLift 3410429
  have htrace : WordTrace (prefixWord ++ tailWord_3410429) baseStart_3410429 baseEnd_3410429 := by
    simpa [prefixWord, tailWord_3410429, baseEnd_3410429] using wordTrace_append hprefix tailTrace_3410429
  have hstable : (prefixWord ++ tailWord_3410429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410429).length < 2 ^ (prefixWord ++ tailWord_3410429).sum := by decide
  have hdescent : baseEnd_3410429 < baseStart_3410429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410442 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_3410442 : Nat := 118140960795 + 3410442 * 2 ^ 59
def prefixEnd_3410442 : Nat := 4983230072969 + 3 ^ 40 * 3410442 * 2
def baseEnd_3410442 : Nat := 1167463993520700575793779

theorem tailTrace_3410442 : CollatzResearch.WordTrace tailWord_3410442 prefixEnd_3410442 1167463993520700575793779 := by
  unfold tailWord_3410442
  simp only [CollatzResearch.WordTrace]
  refine ⟨31097259677639641491732395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82926025807039043977953053 31097259677639641491732395)
  ·
    refine ⟨46645889516459462237598593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31097259677639641491732395 46645889516459462237598593)
    ·
      refine ⟨34984417137344596678198945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46645889516459462237598593 34984417137344596678198945)
      ·
        refine ⟨26238312853008447508649209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34984417137344596678198945 26238312853008447508649209)
        ·
          refine ⟨19678734639756335631486907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26238312853008447508649209 19678734639756335631486907)
          ·
            refine ⟨29518101959634503447230361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19678734639756335631486907 29518101959634503447230361)
            ·
              refine ⟨22138576469725877585422771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29518101959634503447230361 22138576469725877585422771)
              ·
                refine ⟨33207864704588816378134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22138576469725877585422771 33207864704588816378134157)
                ·
                  refine ⟨12452949264220806141800309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33207864704588816378134157 12452949264220806141800309)
                  ·
                    refine ⟨1167463993520700575793779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12452949264220806141800309 1167463993520700575793779)
                    ·
                      rfl

theorem cell22_3410442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_3410442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410442 prefixEnd_3410442 := by exact prefixLift 3410442
  have htrace : WordTrace (prefixWord ++ tailWord_3410442) baseStart_3410442 baseEnd_3410442 := by
    simpa [prefixWord, tailWord_3410442, baseEnd_3410442] using wordTrace_append hprefix tailTrace_3410442
  have hstable : (prefixWord ++ tailWord_3410442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410442).length < 2 ^ (prefixWord ++ tailWord_3410442).sum := by decide
  have hdescent : baseEnd_3410442 < baseStart_3410442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410457 : List Nat := [1, 2, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_3410457 : Nat := 118140960795 + 3410457 * 2 ^ 59
def prefixEnd_3410457 : Nat := 4983230072969 + 3 ^ 40 * 3410457 * 2
def baseEnd_3410457 : Nat := 1167469128327245536668733

theorem tailTrace_3410457 : CollatzResearch.WordTrace tailWord_3410457 prefixEnd_3410457 1167469128327245536668733 := by
  unfold tailWord_3410457
  simp only [CollatzResearch.WordTrace]
  refine ⟨124389585805504223528725625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82926390537002815685817083 124389585805504223528725625)
  ·
    refine ⟨93292189354128167646544219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124389585805504223528725625 93292189354128167646544219)
    ·
      refine ⟨139938284031192251469816329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93292189354128167646544219 139938284031192251469816329)
      ·
        refine ⟨104953713023394188602362247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139938284031192251469816329 104953713023394188602362247)
        ·
          refine ⟨157430569535091282903543371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104953713023394188602362247 157430569535091282903543371)
          ·
            refine ⟨236145854302636924355315057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157430569535091282903543371 236145854302636924355315057)
            ·
              refine ⟨177109390726977693266486293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236145854302636924355315057 177109390726977693266486293)
              ·
                refine ⟨8302002690327079371866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 177109390726977693266486293 8302002690327079371866545)
                ·
                  refine ⟨6226502017745309528899909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8302002690327079371866545 6226502017745309528899909)
                  ·
                    refine ⟨1167469128327245536668733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226502017745309528899909 1167469128327245536668733)
                    ·
                      rfl

theorem cell22_3410457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_3410457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410457 prefixEnd_3410457 := by exact prefixLift 3410457
  have htrace : WordTrace (prefixWord ++ tailWord_3410457) baseStart_3410457 baseEnd_3410457 := by
    simpa [prefixWord, tailWord_3410457, baseEnd_3410457] using wordTrace_append hprefix tailTrace_3410457
  have hstable : (prefixWord ++ tailWord_3410457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410457).length < 2 ^ (prefixWord ++ tailWord_3410457).sum := by decide
  have hdescent : baseEnd_3410457 < baseStart_3410457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410517 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3410517 : Nat := 118140960795 + 3410517 * 2 ^ 59
def prefixEnd_3410517 : Nat := 4983230072969 + 3 ^ 40 * 3410517 * 2
def baseEnd_3410517 : Nat := 389163222517808460056183

theorem tailTrace_3410517 : CollatzResearch.WordTrace tailWord_3410517 prefixEnd_3410517 389163222517808460056183 := by
  unfold tailWord_3410517
  simp only [CollatzResearch.WordTrace]
  refine ⟨124391774185286853775909805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82927849456857902517273203 124391774185286853775909805)
  ·
    refine ⟨46646915319482570165966177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124391774185286853775909805 46646915319482570165966177)
    ·
      refine ⟨34985186489611927624474633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46646915319482570165966177 34985186489611927624474633)
      ·
        refine ⟨26238889867208945718355975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34985186489611927624474633 26238889867208945718355975)
        ·
          refine ⟨39358334800813418577533963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26238889867208945718355975 39358334800813418577533963)
          ·
            refine ⟨59037502201220127866300945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39358334800813418577533963 59037502201220127866300945)
            ·
              refine ⟨44278126650915095899725709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59037502201220127866300945 44278126650915095899725709)
              ·
                refine ⟨16604297494093160962397141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44278126650915095899725709 16604297494093160962397141)
                ·
                  refine ⟨389163222517808460056183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16604297494093160962397141 389163222517808460056183)
                  ·
                    rfl

theorem cell22_3410517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3410517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410517 prefixEnd_3410517 := by exact prefixLift 3410517
  have htrace : WordTrace (prefixWord ++ tailWord_3410517) baseStart_3410517 baseEnd_3410517 := by
    simpa [prefixWord, tailWord_3410517, baseEnd_3410517] using wordTrace_append hprefix tailTrace_3410517
  have hstable : (prefixWord ++ tailWord_3410517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410517).length < 2 ^ (prefixWord ++ tailWord_3410517).sum := by decide
  have hdescent : baseEnd_3410517 < baseStart_3410517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410613 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3410613 : Nat := 118140960795 + 3410613 * 2 ^ 59
def prefixEnd_3410613 : Nat := 4983230072969 + 3 ^ 40 * 3410613 * 2
def baseEnd_3410613 : Nat := 389174176771771043256085

theorem tailTrace_3410613 : CollatzResearch.WordTrace tailWord_3410613 prefixEnd_3410613 389174176771771043256085 := by
  unfold tailWord_3410613
  simp only [CollatzResearch.WordTrace]
  refine ⟨124395275592939062171404493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82930183728626041447602995 124395275592939062171404493)
  ·
    refine ⟨46648228347352148314276685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124395275592939062171404493 46648228347352148314276685)
    ·
      refine ⟨17493085630257055617853757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46648228347352148314276685 17493085630257055617853757)
      ·
        refine ⟨6559907111346395856695159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17493085630257055617853757 6559907111346395856695159)
        ·
          refine ⟨9839860667019593785042739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6559907111346395856695159 9839860667019593785042739)
          ·
            refine ⟨14759791000529390677564109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839860667019593785042739 14759791000529390677564109)
            ·
              refine ⟨5534921625198521504086541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14759791000529390677564109 5534921625198521504086541)
              ·
                refine ⟨2075595609449445564032453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5534921625198521504086541 2075595609449445564032453)
                ·
                  refine ⟨389174176771771043256085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075595609449445564032453 389174176771771043256085)
                  ·
                    rfl

theorem cell22_3410613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3410613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410613 prefixEnd_3410613 := by exact prefixLift 3410613
  have htrace : WordTrace (prefixWord ++ tailWord_3410613) baseStart_3410613 baseEnd_3410613 := by
    simpa [prefixWord, tailWord_3410613, baseEnd_3410613] using wordTrace_append hprefix tailTrace_3410613
  have hstable : (prefixWord ++ tailWord_3410613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410613).length < 2 ^ (prefixWord ++ tailWord_3410613).sum := by decide
  have hdescent : baseEnd_3410613 < baseStart_3410613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410624 : List Nat := [2, 1, 1, 2, 4, 4, 8]
def baseStart_3410624 : Nat := 118140960795 + 3410624 * 2 ^ 59
def prefixEnd_3410624 : Nat := 4983230072969 + 3 ^ 40 * 3410624 * 2
def baseEnd_3410624 : Nat := 43241714660744917323823

theorem tailTrace_3410624 : CollatzResearch.WordTrace tailWord_3410624 prefixEnd_3410624 43241714660744917323823 := by
  unfold tailWord_3410624
  simp only [CollatzResearch.WordTrace]
  refine ⟨62197838397949605525027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82930451197266140700036617 62197838397949605525027463)
  ·
    refine ⟨93296757596924408287541195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62197838397949605525027463 93296757596924408287541195)
    ·
      refine ⟨139945136395386612431311793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93296757596924408287541195 139945136395386612431311793)
      ·
        refine ⟨104958852296539959323483845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139945136395386612431311793 104958852296539959323483845)
        ·
          refine ⟨19679784805601242373153221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104958852296539959323483845 19679784805601242373153221)
          ·
            refine ⟨3689959651050232944966229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19679784805601242373153221 3689959651050232944966229)
            ·
              refine ⟨43241714660744917323823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3689959651050232944966229 43241714660744917323823)
              ·
                rfl

theorem cell22_3410624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 8].length) (baseStart_3410624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410624 prefixEnd_3410624 := by exact prefixLift 3410624
  have htrace : WordTrace (prefixWord ++ tailWord_3410624) baseStart_3410624 baseEnd_3410624 := by
    simpa [prefixWord, tailWord_3410624, baseEnd_3410624] using wordTrace_append hprefix tailTrace_3410624
  have hstable : (prefixWord ++ tailWord_3410624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410624).length < 2 ^ (prefixWord ++ tailWord_3410624).sum := by decide
  have hdescent : baseEnd_3410624 < baseStart_3410624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410645 : List Nat := [1, 3, 2, 5, 1, 1, 1, 3, 2, 3]
def baseStart_3410645 : Nat := 118140960795 + 3410645 * 2 ^ 59
def prefixEnd_3410645 : Nat := 4983230072969 + 3 ^ 40 * 3410645 * 2
def baseEnd_3410645 : Nat := 1167533484569275712968157

theorem tailTrace_3410645 : CollatzResearch.WordTrace tailWord_3410645 prefixEnd_3410645 1167533484569275712968157 := by
  unfold tailWord_3410645
  simp only [CollatzResearch.WordTrace]
  refine ⟨124396442728823131636569389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82930961819215421091046259 124396442728823131636569389)
  ·
    refine ⟨46648666023308674363713521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124396442728823131636569389 46648666023308674363713521)
    ·
      refine ⟨34986499517481505772785141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46648666023308674363713521 34986499517481505772785141)
      ·
        refine ⟨3279984329763891166198607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34986499517481505772785141 3279984329763891166198607)
        ·
          refine ⟨4919976494645836749297911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3279984329763891166198607 4919976494645836749297911)
          ·
            refine ⟨7379964741968755123946867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4919976494645836749297911 7379964741968755123946867)
            ·
              refine ⟨11069947112953132685920301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7379964741968755123946867 11069947112953132685920301)
              ·
                refine ⟨4151230167357424757220113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11069947112953132685920301 4151230167357424757220113)
                ·
                  refine ⟨3113422625518068567915085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4151230167357424757220113 3113422625518068567915085)
                  ·
                    refine ⟨1167533484569275712968157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113422625518068567915085 1167533484569275712968157)
                    ·
                      rfl

theorem cell22_3410645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_3410645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410645 prefixEnd_3410645 := by exact prefixLift 3410645
  have htrace : WordTrace (prefixWord ++ tailWord_3410645) baseStart_3410645 baseEnd_3410645 := by
    simpa [prefixWord, tailWord_3410645, baseEnd_3410645] using wordTrace_append hprefix tailTrace_3410645
  have hstable : (prefixWord ++ tailWord_3410645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410645).length < 2 ^ (prefixWord ++ tailWord_3410645).sum := by decide
  have hdescent : baseEnd_3410645 < baseStart_3410645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410673 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_3410673 : Nat := 118140960795 + 3410673 * 2 ^ 59
def prefixEnd_3410673 : Nat := 4983230072969 + 3 ^ 40 * 3410673 * 2
def baseEnd_3410673 : Nat := 1167543069541492973268071

theorem tailTrace_3410673 : CollatzResearch.WordTrace tailWord_3410673 prefixEnd_3410673 1167543069541492973268071 := by
  unfold tailWord_3410673
  simp only [CollatzResearch.WordTrace]
  refine ⟨124397463972721692418588673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82931642648481128279059115 124397463972721692418588673)
  ·
    refine ⟨93298097979541269313941505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124397463972721692418588673 93298097979541269313941505)
    ·
      refine ⟨69973573484655951985456129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93298097979541269313941505 69973573484655951985456129)
      ·
        refine ⟨52480180113491963989092097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69973573484655951985456129 52480180113491963989092097)
        ·
          refine ⟨39360135085118972991819073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52480180113491963989092097 39360135085118972991819073)
          ·
            refine ⟨29520101313839229743864305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39360135085118972991819073 29520101313839229743864305)
            ·
              refine ⟨22140075985379422307898229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29520101313839229743864305 22140075985379422307898229)
              ·
                refine ⟨2075632123629320841365459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22140075985379422307898229 2075632123629320841365459)
                ·
                  refine ⟨3113448185443981262048189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075632123629320841365459 3113448185443981262048189)
                  ·
                    refine ⟨1167543069541492973268071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113448185443981262048189 1167543069541492973268071)
                    ·
                      rfl

theorem cell22_3410673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_3410673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410673 prefixEnd_3410673 := by exact prefixLift 3410673
  have htrace : WordTrace (prefixWord ++ tailWord_3410673) baseStart_3410673 baseEnd_3410673 := by
    simpa [prefixWord, tailWord_3410673, baseEnd_3410673] using wordTrace_append hprefix tailTrace_3410673
  have hstable : (prefixWord ++ tailWord_3410673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410673).length < 2 ^ (prefixWord ++ tailWord_3410673).sum := by decide
  have hdescent : baseEnd_3410673 < baseStart_3410673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410716 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_3410716 : Nat := 118140960795 + 3410716 * 2 ^ 59
def prefixEnd_3410716 : Nat := 4983230072969 + 3 ^ 40 * 3410716 * 2
def baseEnd_3410716 : Nat := 1167557789320255194442939

theorem tailTrace_3410716 : CollatzResearch.WordTrace tailWord_3410716 prefixEnd_3410716 1167557789320255194442939 := by
  unfold tailWord_3410716
  simp only [CollatzResearch.WordTrace]
  refine ⟨62199516155782955381202001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82932688207710607174936001 62199516155782955381202001)
  ·
    refine ⟨46649637116837216535901501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62199516155782955381202001 46649637116837216535901501)
    ·
      refine ⟨17493613918813956200963063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46649637116837216535901501 17493613918813956200963063)
      ·
        refine ⟨26240420878220934301444595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17493613918813956200963063 26240420878220934301444595)
        ·
          refine ⟨39360631317331401452166893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26240420878220934301444595 39360631317331401452166893)
          ·
            refine ⟨14760236743999275544562585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39360631317331401452166893 14760236743999275544562585)
            ·
              refine ⟨11070177557999456658421939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14760236743999275544562585 11070177557999456658421939)
              ·
                refine ⟨16605266336999184987632909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11070177557999456658421939 16605266336999184987632909)
                ·
                  refine ⟨6226974876374694370362341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16605266336999184987632909 6226974876374694370362341)
                  ·
                    refine ⟨1167557789320255194442939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6226974876374694370362341 1167557789320255194442939)
                    ·
                      rfl

theorem cell22_3410716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_3410716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410716 prefixEnd_3410716 := by exact prefixLift 3410716
  have htrace : WordTrace (prefixWord ++ tailWord_3410716) baseStart_3410716 baseEnd_3410716 := by
    simpa [prefixWord, tailWord_3410716, baseEnd_3410716] using wordTrace_append hprefix tailTrace_3410716
  have hstable : (prefixWord ++ tailWord_3410716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410716).length < 2 ^ (prefixWord ++ tailWord_3410716).sum := by decide
  have hdescent : baseEnd_3410716 < baseStart_3410716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 4]
def baseStart_3410731 : Nat := 118140960795 + 3410731 * 2 ^ 59
def prefixEnd_3410731 : Nat := 4983230072969 + 3 ^ 40 * 3410731 * 2
def baseEnd_3410731 : Nat := 389187641375600051772631

theorem tailTrace_3410731 : CollatzResearch.WordTrace tailWord_3410731 prefixEnd_3410731 389187641375600051772631 := by
  unfold tailWord_3410731
  simp only [CollatzResearch.WordTrace]
  refine ⟨124399579406511568324200047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82933052937674378882800031 124399579406511568324200047)
  ·
    refine ⟨186599369109767352486300071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124399579406511568324200047 186599369109767352486300071)
    ·
      refine ⟨279899053664651028729450107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186599369109767352486300071 279899053664651028729450107)
      ·
        refine ⟨419848580496976543094175161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279899053664651028729450107 419848580496976543094175161)
        ·
          refine ⟨314886435372732407320631371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419848580496976543094175161 314886435372732407320631371)
          ·
            refine ⟨472329653059098610980947057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314886435372732407320631371 472329653059098610980947057)
            ·
              refine ⟨354247239794323958235710293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472329653059098610980947057 354247239794323958235710293)
              ·
                refine ⟨2075667420669866942787365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 354247239794323958235710293 2075667420669866942787365)
                ·
                  refine ⟨389187641375600051772631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075667420669866942787365 389187641375600051772631)
                  ·
                    rfl

theorem cell22_3410731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 4].length) (baseStart_3410731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410731 prefixEnd_3410731 := by exact prefixLift 3410731
  have htrace : WordTrace (prefixWord ++ tailWord_3410731) baseStart_3410731 baseEnd_3410731 := by
    simpa [prefixWord, tailWord_3410731, baseEnd_3410731] using wordTrace_append hprefix tailTrace_3410731
  have hstable : (prefixWord ++ tailWord_3410731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410731).length < 2 ^ (prefixWord ++ tailWord_3410731).sum := by decide
  have hdescent : baseEnd_3410731 < baseStart_3410731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410759 : List Nat := [1, 1, 4, 1, 2, 1, 1, 11]
def baseStart_3410759 : Nat := 118140960795 + 3410759 * 2 ^ 59
def prefixEnd_3410759 : Nat := 4983230072969 + 3 ^ 40 * 3410759 * 2
def baseEnd_3410759 : Nat := 129730278788779712846423

theorem tailTrace_3410759 : CollatzResearch.WordTrace tailWord_3410759 prefixEnd_3410759 129730278788779712846423 := by
  unfold tailWord_3410759
  simp only [CollatzResearch.WordTrace]
  refine ⟨124400600650410129106219331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82933733766940086070812887 124400600650410129106219331)
  ·
    refine ⟨186600900975615193659328997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124400600650410129106219331 186600900975615193659328997)
    ·
      refine ⟨34987668932927848811124187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186600900975615193659328997 34987668932927848811124187)
      ·
        refine ⟨52481503399391773216686281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34987668932927848811124187 52481503399391773216686281)
        ·
          refine ⟨39361127549543829912514711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52481503399391773216686281 39361127549543829912514711)
          ·
            refine ⟨59041691324315744868772067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39361127549543829912514711 59041691324315744868772067)
            ·
              refine ⟨88562536986473617303158101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59041691324315744868772067 88562536986473617303158101)
              ·
                refine ⟨129730278788779712846423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 88562536986473617303158101 129730278788779712846423)
                ·
                  rfl

theorem cell22_3410759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 11].length) (baseStart_3410759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410759 prefixEnd_3410759 := by exact prefixLift 3410759
  have htrace : WordTrace (prefixWord ++ tailWord_3410759) baseStart_3410759 baseEnd_3410759 := by
    simpa [prefixWord, tailWord_3410759, baseEnd_3410759] using wordTrace_append hprefix tailTrace_3410759
  have hstable : (prefixWord ++ tailWord_3410759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410759).length < 2 ^ (prefixWord ++ tailWord_3410759).sum := by decide
  have hdescent : baseEnd_3410759 < baseStart_3410759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410855 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 5]
def baseStart_3410855 : Nat := 118140960795 + 3410855 * 2 ^ 59
def prefixEnd_3410855 : Nat := 4983230072969 + 3 ^ 40 * 3410855 * 2
def baseEnd_3410855 : Nat := 389201790620301721739171

theorem tailTrace_3410855 : CollatzResearch.WordTrace tailWord_3410855 prefixEnd_3410855 389201790620301721739171 := by
  unfold tailWord_3410855
  simp only [CollatzResearch.WordTrace]
  refine ⟨124404102058062337501714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82936068038708225001142679 124404102058062337501714019)
  ·
    refine ⟨186606153087093506252571029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124404102058062337501714019 186606153087093506252571029)
    ·
      refine ⟨8747163425957508105589267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186606153087093506252571029 8747163425957508105589267)
      ·
        refine ⟨13120745138936262158383901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747163425957508105589267 13120745138936262158383901)
        ·
          refine ⟨4920279427101098309393963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13120745138936262158383901 4920279427101098309393963)
          ·
            refine ⟨7380419140651647464090945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920279427101098309393963 7380419140651647464090945)
            ·
              refine ⟨5535314355488735598068209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7380419140651647464090945 5535314355488735598068209)
              ·
                refine ⟨4151485766616551698551157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535314355488735598068209 4151485766616551698551157)
                ·
                  refine ⟨389201790620301721739171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4151485766616551698551157 389201790620301721739171)
                  ·
                    rfl

theorem cell22_3410855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 5].length) (baseStart_3410855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410855 prefixEnd_3410855 := by exact prefixLift 3410855
  have htrace : WordTrace (prefixWord ++ tailWord_3410855) baseStart_3410855 baseEnd_3410855 := by
    simpa [prefixWord, tailWord_3410855, baseEnd_3410855] using wordTrace_append hprefix tailTrace_3410855
  have hstable : (prefixWord ++ tailWord_3410855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410855).length < 2 ^ (prefixWord ++ tailWord_3410855).sum := by decide
  have hdescent : baseEnd_3410855 < baseStart_3410855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410893 : List Nat := [1, 6, 3, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3410893 : Nat := 118140960795 + 3410893 * 2 ^ 59
def prefixEnd_3410893 : Nat := 4983230072969 + 3 ^ 40 * 3410893 * 2
def baseEnd_3410893 : Nat := 1167618380037485732767397

theorem tailTrace_3410893 : CollatzResearch.WordTrace tailWord_3410893 prefixEnd_3410893 1167618380037485732767397 := by
  unfold tailWord_3410893
  simp only [CollatzResearch.WordTrace]
  refine ⟨124405488031924669991597333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82936992021283113327731555 124405488031924669991597333)
  ·
    refine ⟨5831507251496468905856125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124405488031924669991597333 5831507251496468905856125)
    ·
      refine ⟨2186815219311175839696047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5831507251496468905856125 2186815219311175839696047)
      ·
        refine ⟨3280222828966763759544071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2186815219311175839696047 3280222828966763759544071)
        ·
          refine ⟨4920334243450145639316107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280222828966763759544071 4920334243450145639316107)
          ·
            refine ⟨7380501365175218458974161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920334243450145639316107 7380501365175218458974161)
            ·
              refine ⟨5535376023881413844230621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7380501365175218458974161 5535376023881413844230621)
              ·
                refine ⟨2075766008955530191586483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5535376023881413844230621 2075766008955530191586483)
                ·
                  refine ⟨3113649013433295287379725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075766008955530191586483 3113649013433295287379725)
                  ·
                    refine ⟨1167618380037485732767397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113649013433295287379725 1167618380037485732767397)
                    ·
                      rfl

theorem cell22_3410893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3410893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410893 prefixEnd_3410893 := by exact prefixLift 3410893
  have htrace : WordTrace (prefixWord ++ tailWord_3410893) baseStart_3410893 baseEnd_3410893 := by
    simpa [prefixWord, tailWord_3410893, baseEnd_3410893] using wordTrace_append hprefix tailTrace_3410893
  have hstable : (prefixWord ++ tailWord_3410893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410893).length < 2 ^ (prefixWord ++ tailWord_3410893).sum := by decide
  have hdescent : baseEnd_3410893 < baseStart_3410893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410900 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 4]
def baseStart_3410900 : Nat := 118140960795 + 3410900 * 2 ^ 59
def prefixEnd_3410900 : Nat := 4983230072969 + 3 ^ 40 * 3410900 * 2
def baseEnd_3410900 : Nat := 389206925426846682614125

theorem tailTrace_3410900 : CollatzResearch.WordTrace tailWord_3410900 prefixEnd_3410900 389206925426846682614125 := by
  unfold tailWord_3410900
  simp only [CollatzResearch.WordTrace]
  refine ⟨62202871671449655093551077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82937162228599540124734769 62202871671449655093551077)
  ·
    refine ⟨11663038438396810330040827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62202871671449655093551077 11663038438396810330040827)
    ·
      refine ⟨17494557657595215495061241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11663038438396810330040827 17494557657595215495061241)
      ·
        refine ⟨13120918243196411621295931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17494557657595215495061241 13120918243196411621295931)
        ·
          refine ⟨19681377364794617431943897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13120918243196411621295931 19681377364794617431943897)
          ·
            refine ⟨14761033023595963073957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19681377364794617431943897 14761033023595963073957923)
            ·
              refine ⟨22141549535393944610936885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14761033023595963073957923 22141549535393944610936885)
              ·
                refine ⟨2075770268943182307275333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22141549535393944610936885 2075770268943182307275333)
                ·
                  refine ⟨389206925426846682614125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075770268943182307275333 389206925426846682614125)
                  ·
                    rfl

theorem cell22_3410900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_3410900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410900 prefixEnd_3410900 := by exact prefixLift 3410900
  have htrace : WordTrace (prefixWord ++ tailWord_3410900) baseStart_3410900 baseEnd_3410900 := by
    simpa [prefixWord, tailWord_3410900, baseEnd_3410900] using wordTrace_append hprefix tailTrace_3410900
  have hstable : (prefixWord ++ tailWord_3410900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410900).length < 2 ^ (prefixWord ++ tailWord_3410900).sum := by decide
  have hdescent : baseEnd_3410900 < baseStart_3410900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410902 : List Nat := [5, 2, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3410902 : Nat := 118140960795 + 3410902 * 2 ^ 59
def prefixEnd_3410902 : Nat := 4983230072969 + 3 ^ 40 * 3410902 * 2
def baseEnd_3410902 : Nat := 1167621460921412709292369

theorem tailTrace_3410902 : CollatzResearch.WordTrace tailWord_3410902 prefixEnd_3410902 1167621460921412709292369 := by
  unfold tailWord_3410902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775363518055754033042185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82937210859261376352449973 7775363518055754033042185)
  ·
    refine ⟨5831522638541815524781639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7775363518055754033042185 5831522638541815524781639)
    ·
      refine ⟨8747283957812723287172459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831522638541815524781639 8747283957812723287172459)
      ·
        refine ⟨13120925936719084930758689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747283957812723287172459 13120925936719084930758689)
        ·
          refine ⟨9840694452539313698069017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13120925936719084930758689 9840694452539313698069017)
          ·
            refine ⟨7380520839404485273551763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9840694452539313698069017 7380520839404485273551763)
            ·
              refine ⟨11070781259106727910327645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380520839404485273551763 11070781259106727910327645)
              ·
                refine ⟨4151542972165022966372867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11070781259106727910327645 4151542972165022966372867)
                ·
                  refine ⟨6227314458247534449559301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151542972165022966372867 6227314458247534449559301)
                  ·
                    refine ⟨1167621460921412709292369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6227314458247534449559301 1167621460921412709292369)
                    ·
                      rfl

theorem cell22_3410902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3410902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410902 prefixEnd_3410902 := by exact prefixLift 3410902
  have htrace : WordTrace (prefixWord ++ tailWord_3410902) baseStart_3410902 baseEnd_3410902 := by
    simpa [prefixWord, tailWord_3410902, baseEnd_3410902] using wordTrace_append hprefix tailTrace_3410902
  have hstable : (prefixWord ++ tailWord_3410902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410902).length < 2 ^ (prefixWord ++ tailWord_3410902).sum := by decide
  have hdescent : baseEnd_3410902 < baseStart_3410902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410945 : List Nat := [1, 2, 4, 1, 2, 4, 2, 6]
def baseStart_3410945 : Nat := 118140960795 + 3410945 * 2 ^ 59
def prefixEnd_3410945 : Nat := 4983230072969 + 3 ^ 40 * 3410945 * 2
def baseEnd_3410945 : Nat := 129737353411130547829693

theorem tailTrace_3410945 : CollatzResearch.WordTrace tailWord_3410945 prefixEnd_3410945 129737353411130547829693 := by
  unfold tailWord_3410945
  simp only [CollatzResearch.WordTrace]
  refine ⟨124407384627736282872490289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82938256418490855248326859 124407384627736282872490289)
  ·
    refine ⟨93305538470802212154367717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124407384627736282872490289 93305538470802212154367717)
    ·
      refine ⟨17494788463275414778943947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93305538470802212154367717 17494788463275414778943947)
      ·
        refine ⟨26242182694913122168415921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17494788463275414778943947 26242182694913122168415921)
        ·
          refine ⟨19681637021184841626311941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26242182694913122168415921 19681637021184841626311941)
          ·
            refine ⟨3690306941472157804933489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19681637021184841626311941 3690306941472157804933489)
            ·
              refine ⟨2767730206104118353700117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690306941472157804933489 2767730206104118353700117)
              ·
                refine ⟨129737353411130547829693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2767730206104118353700117 129737353411130547829693)
                ·
                  rfl

theorem cell22_3410945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 6].length) (baseStart_3410945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410945 prefixEnd_3410945 := by exact prefixLift 3410945
  have htrace : WordTrace (prefixWord ++ tailWord_3410945) baseStart_3410945 baseEnd_3410945 := by
    simpa [prefixWord, tailWord_3410945, baseEnd_3410945] using wordTrace_append hprefix tailTrace_3410945
  have hstable : (prefixWord ++ tailWord_3410945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410945).length < 2 ^ (prefixWord ++ tailWord_3410945).sum := by decide
  have hdescent : baseEnd_3410945 < baseStart_3410945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410977 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 3, 3]
def baseStart_3410977 : Nat := 118140960795 + 3410977 * 2 ^ 59
def prefixEnd_3410977 : Nat := 4983230072969 + 3 ^ 40 * 3410977 * 2
def baseEnd_3410977 : Nat := 1167647134954137513667139

theorem tailTrace_3410977 : CollatzResearch.WordTrace tailWord_3410977 prefixEnd_3410977 1167647134954137513667139 := by
  unfold tailWord_3410977
  simp only [CollatzResearch.WordTrace]
  refine ⟨124408551763620352337655185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82939034509080234891770123 124408551763620352337655185)
  ·
    refine ⟨93306413822715264253241389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124408551763620352337655185 93306413822715264253241389)
    ·
      refine ⟨34989905183518224094965521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93306413822715264253241389 34989905183518224094965521)
      ·
        refine ⟨26242428887638668071224141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34989905183518224094965521 26242428887638668071224141)
        ·
          refine ⟨9840910832864500526709053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26242428887638668071224141 9840910832864500526709053)
          ·
            refine ⟨3690341562324187697515895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9840910832864500526709053 3690341562324187697515895)
            ·
              refine ⟨5535512343486281546273843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690341562324187697515895 5535512343486281546273843)
              ·
                refine ⟨8303268515229422319410765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535512343486281546273843 8303268515229422319410765)
                ·
                  refine ⟨3113725693211033369779037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8303268515229422319410765 3113725693211033369779037)
                  ·
                    refine ⟨1167647134954137513667139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113725693211033369779037 1167647134954137513667139)
                    ·
                      rfl

theorem cell22_3410977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_3410977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410977 prefixEnd_3410977 := by exact prefixLift 3410977
  have htrace : WordTrace (prefixWord ++ tailWord_3410977) baseStart_3410977 baseEnd_3410977 := by
    simpa [prefixWord, tailWord_3410977, baseEnd_3410977] using wordTrace_append hprefix tailTrace_3410977
  have hstable : (prefixWord ++ tailWord_3410977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410977).length < 2 ^ (prefixWord ++ tailWord_3410977).sum := by decide
  have hdescent : baseEnd_3410977 < baseStart_3410977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3410990 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 5]
def baseStart_3410990 : Nat := 118140960795 + 3410990 * 2 ^ 59
def prefixEnd_3410990 : Nat := 4983230072969 + 3 ^ 40 * 3410990 * 2
def baseEnd_3410990 : Nat := 389217195039936604364033

theorem tailTrace_3410990 : CollatzResearch.WordTrace tailWord_3410990 prefixEnd_3410990 389217195039936604364033 := by
  unfold tailWord_3410990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15551128239071656944734803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82939350608382170371918949 15551128239071656944734803)
  ·
    refine ⟨23326692358607485417102205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15551128239071656944734803 23326692358607485417102205)
    ·
      refine ⟨8747509634477807031413327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23326692358607485417102205 8747509634477807031413327)
      ·
        refine ⟨13121264451716710547119991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747509634477807031413327 13121264451716710547119991)
        ·
          refine ⟨19681896677575065820679987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13121264451716710547119991 19681896677575065820679987)
          ·
            refine ⟨29522845016362598731019981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19681896677575065820679987 29522845016362598731019981)
            ·
              refine ⟨11071066881135974524132493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29522845016362598731019981 11071066881135974524132493)
              ·
                refine ⟨4151650080425990446549685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11071066881135974524132493 4151650080425990446549685)
                ·
                  refine ⟨389217195039936604364033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4151650080425990446549685 389217195039936604364033)
                  ·
                    rfl

theorem cell22_3410990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 5].length) (baseStart_3410990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3410990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3410990 prefixEnd_3410990 := by exact prefixLift 3410990
  have htrace : WordTrace (prefixWord ++ tailWord_3410990) baseStart_3410990 baseEnd_3410990 := by
    simpa [prefixWord, tailWord_3410990, baseEnd_3410990] using wordTrace_append hprefix tailTrace_3410990
  have hstable : (prefixWord ++ tailWord_3410990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3410990).length < 2 ^ (prefixWord ++ tailWord_3410990).sum := by decide
  have hdescent : baseEnd_3410990 < baseStart_3410990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3410990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411050 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 5]
def baseStart_3411050 : Nat := 118140960795 + 3411050 * 2 ^ 59
def prefixEnd_3411050 : Nat := 4983230072969 + 3 ^ 40 * 3411050 * 2
def baseEnd_3411050 : Nat := 1167672124345989656591915

theorem tailTrace_3411050 : CollatzResearch.WordTrace tailWord_3411050 prefixEnd_3411050 1167672124345989656591915 := by
  unfold tailWord_3411050
  simp only [CollatzResearch.WordTrace]
  refine ⟨31102803573088971451265651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82940809528237257203375069 31102803573088971451265651)
  ·
    refine ⟨46654205359633457176898477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31102803573088971451265651 46654205359633457176898477)
    ·
      refine ⟨17495327009862546441336929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46654205359633457176898477 17495327009862546441336929)
      ·
        refine ⟨13121495257396909831002697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17495327009862546441336929 13121495257396909831002697)
        ·
          refine ⟨9841121443047682373252023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13121495257396909831002697 9841121443047682373252023)
          ·
            refine ⟨14761682164571523559878035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9841121443047682373252023 14761682164571523559878035)
            ·
              refine ⟨22142523246857285339817053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14761682164571523559878035 22142523246857285339817053)
              ·
                refine ⟨8303446217571482002431395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22142523246857285339817053 8303446217571482002431395)
                ·
                  refine ⟨12455169326357223003647093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303446217571482002431395 12455169326357223003647093)
                  ·
                    refine ⟨1167672124345989656591915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12455169326357223003647093 1167672124345989656591915)
                    ·
                      rfl

theorem cell22_3411050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_3411050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411050 prefixEnd_3411050 := by exact prefixLift 3411050
  have htrace : WordTrace (prefixWord ++ tailWord_3411050) baseStart_3411050 baseEnd_3411050 := by
    simpa [prefixWord, tailWord_3411050, baseEnd_3411050] using wordTrace_append hprefix tailTrace_3411050
  have hstable : (prefixWord ++ tailWord_3411050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411050).length < 2 ^ (prefixWord ++ tailWord_3411050).sum := by decide
  have hdescent : baseEnd_3411050 < baseStart_3411050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411065 : List Nat := [1, 2, 1, 3, 5, 1, 1, 1, 1, 6]
def baseStart_3411065 : Nat := 118140960795 + 3411065 * 2 ^ 59
def prefixEnd_3411065 : Nat := 4983230072969 + 3 ^ 40 * 3411065 * 2
def baseEnd_3411065 : Nat := 1167677259152534617466869

theorem tailTrace_3411065 : CollatzResearch.WordTrace tailWord_3411065 prefixEnd_3411065 1167677259152534617466869 := by
  unfold tailWord_3411065
  simp only [CollatzResearch.WordTrace]
  refine ⟨124411761387301543366858649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82941174258201028911239099 124411761387301543366858649)
  ·
    refine ⟨93308821040476157525143987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124411761387301543366858649 93308821040476157525143987)
    ·
      refine ⟨139963231560714236287715981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93308821040476157525143987 139963231560714236287715981)
      ·
        refine ⟨52486211835267838607893493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139963231560714236287715981 52486211835267838607893493)
        ·
          refine ⟨4920582359556359869490015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52486211835267838607893493 4920582359556359869490015)
          ·
            refine ⟨7380873539334539804235023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920582359556359869490015 7380873539334539804235023)
            ·
              refine ⟨11071310309001809706352535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7380873539334539804235023 11071310309001809706352535)
              ·
                refine ⟨16606965463502714559528803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11071310309001809706352535 16606965463502714559528803)
                ·
                  refine ⟨24910448195254071839293205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16606965463502714559528803 24910448195254071839293205)
                  ·
                    refine ⟨1167677259152534617466869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24910448195254071839293205 1167677259152534617466869)
                    ·
                      rfl

theorem cell22_3411065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 6].length) (baseStart_3411065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411065 prefixEnd_3411065 := by exact prefixLift 3411065
  have htrace : WordTrace (prefixWord ++ tailWord_3411065) baseStart_3411065 baseEnd_3411065 := by
    simpa [prefixWord, tailWord_3411065, baseEnd_3411065] using wordTrace_append hprefix tailTrace_3411065
  have hstable : (prefixWord ++ tailWord_3411065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411065).length < 2 ^ (prefixWord ++ tailWord_3411065).sum := by decide
  have hdescent : baseEnd_3411065 < baseStart_3411065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411080 : List Nat := [2, 1, 3, 4, 2, 1, 9]
def baseStart_3411080 : Nat := 118140960795 + 3411080 * 2 ^ 59
def prefixEnd_3411080 : Nat := 4983230072969 + 3 ^ 40 * 3411080 * 2
def baseEnd_3411080 : Nat := 43247496072558502901549

theorem tailTrace_3411080 : CollatzResearch.WordTrace tailWord_3411080 prefixEnd_3411080 43247496072558502901549 := by
  unfold tailWord_3411080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62206154241123600464327347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82941538988164800619103129 62206154241123600464327347)
  ·
    refine ⟨93309231361685400696491021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62206154241123600464327347 93309231361685400696491021)
    ·
      refine ⟨34990961760632025261184133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93309231361685400696491021 34990961760632025261184133)
      ·
        refine ⟨6560805330118504736472025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34990961760632025261184133 6560805330118504736472025)
        ·
          refine ⟨4920603997588878552354019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560805330118504736472025 4920603997588878552354019)
          ·
            refine ⟨7380905996383317828531029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4920603997588878552354019 7380905996383317828531029)
            ·
              refine ⟨43247496072558502901549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7380905996383317828531029 43247496072558502901549)
              ·
                rfl

theorem cell22_3411080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 9].length) (baseStart_3411080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411080 prefixEnd_3411080 := by exact prefixLift 3411080
  have htrace : WordTrace (prefixWord ++ tailWord_3411080) baseStart_3411080 baseEnd_3411080 := by
    simpa [prefixWord, tailWord_3411080, baseEnd_3411080] using wordTrace_append hprefix tailTrace_3411080
  have hstable : (prefixWord ++ tailWord_3411080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411080).length < 2 ^ (prefixWord ++ tailWord_3411080).sum := by decide
  have hdescent : baseEnd_3411080 < baseStart_3411080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411093 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3411093 : Nat := 118140960795 + 3411093 * 2 ^ 59
def prefixEnd_3411093 : Nat := 4983230072969 + 3 ^ 40 * 3411093 * 2
def baseEnd_3411093 : Nat := 1167686844124751877766783

theorem tailTrace_3411093 : CollatzResearch.WordTrace tailWord_3411093 prefixEnd_3411093 1167686844124751877766783 := by
  unfold tailWord_3411093
  simp only [CollatzResearch.WordTrace]
  refine ⟨124412782631200104148877933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82941855087466736099251955 124412782631200104148877933)
  ·
    refine ⟨46654793486700039055829225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124412782631200104148877933 46654793486700039055829225)
    ·
      refine ⟨34991095115025029291871919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46654793486700039055829225 34991095115025029291871919)
      ·
        refine ⟨52486642672537543937807879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34991095115025029291871919 52486642672537543937807879)
        ·
          refine ⟨78729964008806315906711819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52486642672537543937807879 78729964008806315906711819)
          ·
            refine ⟨118094946013209473860067729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78729964008806315906711819 118094946013209473860067729)
            ·
              refine ⟨88571209509907105395050797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118094946013209473860067729 88571209509907105395050797)
              ·
                refine ⟨33214203566215164523144049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88571209509907105395050797 33214203566215164523144049)
                ·
                  refine ⟨24910652674661373392358037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33214203566215164523144049 24910652674661373392358037)
                  ·
                    refine ⟨1167686844124751877766783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24910652674661373392358037 1167686844124751877766783)
                    ·
                      rfl

theorem cell22_3411093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3411093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411093 prefixEnd_3411093 := by exact prefixLift 3411093
  have htrace : WordTrace (prefixWord ++ tailWord_3411093) baseStart_3411093 baseEnd_3411093 := by
    simpa [prefixWord, tailWord_3411093, baseEnd_3411093] using wordTrace_append hprefix tailTrace_3411093
  have hstable : (prefixWord ++ tailWord_3411093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411093).length < 2 ^ (prefixWord ++ tailWord_3411093).sum := by decide
  have hdescent : baseEnd_3411093 < baseStart_3411093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411114 : List Nat := [3, 1, 5, 1, 1, 3, 2, 6]
def baseStart_3411114 : Nat := 118140960795 + 3411114 * 2 ^ 59
def prefixEnd_3411114 : Nat := 4983230072969 + 3 ^ 40 * 3411114 * 2
def baseEnd_3411114 : Nat := 129743781428212758110191

theorem tailTrace_3411114 : CollatzResearch.WordTrace tailWord_3411114 prefixEnd_3411114 129743781428212758110191 := by
  unfold tailWord_3411114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31103387141031006183848099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82942365709416016490261597 31103387141031006183848099)
  ·
    refine ⟨46655080711546509275772149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31103387141031006183848099 46655080711546509275772149)
    ·
      refine ⟨4373913816707485244603639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46655080711546509275772149 4373913816707485244603639)
      ·
        refine ⟨6560870725061227866905459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373913816707485244603639 6560870725061227866905459)
        ·
          refine ⟨9841306087591841800358189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560870725061227866905459 9841306087591841800358189)
          ·
            refine ⟨3690489782846940675134321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9841306087591841800358189 3690489782846940675134321)
            ·
              refine ⟨2767867337135205506350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3690489782846940675134321 2767867337135205506350741)
              ·
                refine ⟨129743781428212758110191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2767867337135205506350741 129743781428212758110191)
                ·
                  rfl

theorem cell22_3411114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 6].length) (baseStart_3411114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411114 prefixEnd_3411114 := by exact prefixLift 3411114
  have htrace : WordTrace (prefixWord ++ tailWord_3411114) baseStart_3411114 baseEnd_3411114 := by
    simpa [prefixWord, tailWord_3411114, baseEnd_3411114] using wordTrace_append hprefix tailTrace_3411114
  have hstable : (prefixWord ++ tailWord_3411114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411114).length < 2 ^ (prefixWord ++ tailWord_3411114).sum := by decide
  have hdescent : baseEnd_3411114 < baseStart_3411114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411123 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_3411123 : Nat := 118140960795 + 3411123 * 2 ^ 59
def prefixEnd_3411123 : Nat := 4983230072969 + 3 ^ 40 * 3411123 * 2
def baseEnd_3411123 : Nat := 1167697113737841799516691

theorem tailTrace_3411123 : CollatzResearch.WordTrace tailWord_3411123 prefixEnd_3411123 1167697113737841799516691 := by
  unfold tailWord_3411123
  simp only [CollatzResearch.WordTrace]
  refine ⟨124413876821091419272470023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82942584547394279514980015 124413876821091419272470023)
  ·
    refine ⟨186620815231637128908705035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124413876821091419272470023 186620815231637128908705035)
    ·
      refine ⟨279931222847455693363057553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186620815231637128908705035 279931222847455693363057553)
      ·
        refine ⟨209948417135591770022293165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279931222847455693363057553 209948417135591770022293165)
        ·
          refine ⟨78730656425846913758359937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 209948417135591770022293165 78730656425846913758359937)
          ·
            refine ⟨59047992319385185318769953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78730656425846913758359937 59047992319385185318769953)
            ·
              refine ⟨44285994239538888989077465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59047992319385185318769953 44285994239538888989077465)
              ·
                refine ⟨33214495679654166741808099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44285994239538888989077465 33214495679654166741808099)
                ·
                  refine ⟨49821743519481250112712149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33214495679654166741808099 49821743519481250112712149)
                  ·
                    refine ⟨1167697113737841799516691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49821743519481250112712149 1167697113737841799516691)
                    ·
                      rfl

theorem cell22_3411123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_3411123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411123 prefixEnd_3411123 := by exact prefixLift 3411123
  have htrace : WordTrace (prefixWord ++ tailWord_3411123) baseStart_3411123 baseEnd_3411123 := by
    simpa [prefixWord, tailWord_3411123, baseEnd_3411123] using wordTrace_append hprefix tailTrace_3411123
  have hstable : (prefixWord ++ tailWord_3411123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411123).length < 2 ^ (prefixWord ++ tailWord_3411123).sum := by decide
  have hdescent : baseEnd_3411123 < baseStart_3411123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411129 : List Nat := [1, 2, 1, 4, 1, 3, 3, 3, 1, 3]
def baseStart_3411129 : Nat := 118140960795 + 3411129 * 2 ^ 59
def prefixEnd_3411129 : Nat := 4983230072969 + 3 ^ 40 * 3411129 * 2
def baseEnd_3411129 : Nat := 1167699167660459783866673

theorem tailTrace_3411129 : CollatzResearch.WordTrace tailWord_3411129 prefixEnd_3411129 1167699167660459783866673 := by
  unfold tailWord_3411129
  simp only [CollatzResearch.WordTrace]
  refine ⟨124414095659069682297188441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82942730439379788198125627 124414095659069682297188441)
  ·
    refine ⟨93310571744302261722891331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124414095659069682297188441 93310571744302261722891331)
    ·
      refine ⟨139965857616453392584336997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93310571744302261722891331 139965857616453392584336997)
      ·
        refine ⟨26243598303085011109563187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139965857616453392584336997 26243598303085011109563187)
        ·
          refine ⟨39365397454627516664344781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26243598303085011109563187 39365397454627516664344781)
          ·
            refine ⟨14762024045485318749129293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39365397454627516664344781 14762024045485318749129293)
            ·
              refine ⟨5535759017056994530923485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14762024045485318749129293 5535759017056994530923485)
              ·
                refine ⟨2075909631396372949096307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5535759017056994530923485 2075909631396372949096307)
                ·
                  refine ⟨3113864447094559423644461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075909631396372949096307 3113864447094559423644461)
                  ·
                    refine ⟨1167699167660459783866673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113864447094559423644461 1167699167660459783866673)
                    ·
                      rfl

theorem cell22_3411129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 3, 1, 3].length) (baseStart_3411129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411129 prefixEnd_3411129 := by exact prefixLift 3411129
  have htrace : WordTrace (prefixWord ++ tailWord_3411129) baseStart_3411129 baseEnd_3411129 := by
    simpa [prefixWord, tailWord_3411129, baseEnd_3411129] using wordTrace_append hprefix tailTrace_3411129
  have hstable : (prefixWord ++ tailWord_3411129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411129).length < 2 ^ (prefixWord ++ tailWord_3411129).sum := by decide
  have hdescent : baseEnd_3411129 < baseStart_3411129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411146 : List Nat := [3, 1, 2, 1, 3, 3, 3, 2, 1, 3]
def baseStart_3411146 : Nat := 118140960795 + 3411146 * 2 ^ 59
def prefixEnd_3411146 : Nat := 4983230072969 + 3 ^ 40 * 3411146 * 2
def baseEnd_3411146 : Nat := 1167704987107877406191621

theorem tailTrace_3411146 : CollatzResearch.WordTrace tailWord_3411146 prefixEnd_3411146 1167704987107877406191621 := by
  unfold tailWord_3411146
  simp only [CollatzResearch.WordTrace]
  refine ⟨31103678925002023550139323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82943143800005396133704861 31103678925002023550139323)
  ·
    refine ⟨46655518387503035325208985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31103678925002023550139323 46655518387503035325208985)
    ·
      refine ⟨34991638790627276493906739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46655518387503035325208985 34991638790627276493906739)
      ·
        refine ⟨52487458185940914740860109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34991638790627276493906739 52487458185940914740860109)
        ·
          refine ⟨19682796819727843027822541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52487458185940914740860109 19682796819727843027822541)
          ·
            refine ⟨7381048807397941135433453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19682796819727843027822541 7381048807397941135433453)
            ·
              refine ⟨2767893302774227925787545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7381048807397941135433453 2767893302774227925787545)
              ·
                refine ⟨2075919977080670944340659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767893302774227925787545 2075919977080670944340659)
                ·
                  refine ⟨3113879965621006416510989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075919977080670944340659 3113879965621006416510989)
                  ·
                    refine ⟨1167704987107877406191621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113879965621006416510989 1167704987107877406191621)
                    ·
                      rfl

theorem cell22_3411146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_3411146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411146 prefixEnd_3411146 := by exact prefixLift 3411146
  have htrace : WordTrace (prefixWord ++ tailWord_3411146) baseStart_3411146 baseEnd_3411146 := by
    simpa [prefixWord, tailWord_3411146, baseEnd_3411146] using wordTrace_append hprefix tailTrace_3411146
  have hstable : (prefixWord ++ tailWord_3411146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411146).length < 2 ^ (prefixWord ++ tailWord_3411146).sum := by decide
  have hdescent : baseEnd_3411146 < baseStart_3411146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411172 : List Nat := [2, 3, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_3411172 : Nat := 118140960795 + 3411172 * 2 ^ 59
def prefixEnd_3411172 : Nat := 4983230072969 + 3 ^ 40 * 3411172 * 2
def baseEnd_3411172 : Nat := 1167713887439222005041541

theorem tailTrace_3411172 : CollatzResearch.WordTrace tailWord_3411172 prefixEnd_3411172 1167713887439222005041541 := by
  unfold tailWord_3411172
  simp only [CollatzResearch.WordTrace]
  refine ⟨62207831998956950320501885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82943775998609267094002513 62207831998956950320501885)
  ·
    refine ⟨23327936999608856370188207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62207831998956950320501885 23327936999608856370188207)
    ·
      refine ⟨34991905499413284555282311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23327936999608856370188207 34991905499413284555282311)
      ·
        refine ⟨52487858249119926832923467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34991905499413284555282311 52487858249119926832923467)
        ·
          refine ⟨78731787373679890249385201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52487858249119926832923467 78731787373679890249385201)
          ·
            refine ⟨59048840530259917687038901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78731787373679890249385201 59048840530259917687038901)
            ·
              refine ⟨5535828799711867283159897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59048840530259917687038901 5535828799711867283159897)
              ·
                refine ⟨4151871599783900462369923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5535828799711867283159897 4151871599783900462369923)
                ·
                  refine ⟨6227807399675850693554885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4151871599783900462369923 6227807399675850693554885)
                  ·
                    refine ⟨1167713887439222005041541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6227807399675850693554885 1167713887439222005041541)
                    ·
                      rfl

theorem cell22_3411172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_3411172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411172 prefixEnd_3411172 := by exact prefixLift 3411172
  have htrace : WordTrace (prefixWord ++ tailWord_3411172) baseStart_3411172 baseEnd_3411172 := by
    simpa [prefixWord, tailWord_3411172, baseEnd_3411172] using wordTrace_append hprefix tailTrace_3411172
  have hstable : (prefixWord ++ tailWord_3411172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411172).length < 2 ^ (prefixWord ++ tailWord_3411172).sum := by decide
  have hdescent : baseEnd_3411172 < baseStart_3411172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411204 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3411204 : Nat := 118140960795 + 3411204 * 2 ^ 59
def prefixEnd_3411204 : Nat := 4983230072969 + 3 ^ 40 * 3411204 * 2
def baseEnd_3411204 : Nat := 389241613897728196080481

theorem tailTrace_3411204 : CollatzResearch.WordTrace tailWord_3411204 prefixEnd_3411204 389241613897728196080481 := by
  unfold tailWord_3411204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62208415566898985053084333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82944554089198646737445777 62208415566898985053084333)
  ·
    refine ⟨23328155837587119394906625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62208415566898985053084333 23328155837587119394906625)
    ·
      refine ⟨17496116878190339546179969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23328155837587119394906625 17496116878190339546179969)
      ·
        refine ⟨13122087658642754659634977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17496116878190339546179969 13122087658642754659634977)
        ·
          refine ⟨9841565743982065994726233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13122087658642754659634977 9841565743982065994726233)
          ·
            refine ⟨7381174307986549496044675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9841565743982065994726233 7381174307986549496044675)
            ·
              refine ⟨11071761461979824244067013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381174307986549496044675 11071761461979824244067013)
              ·
                refine ⟨2075955274121217045762565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11071761461979824244067013 2075955274121217045762565)
                ·
                  refine ⟨389241613897728196080481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075955274121217045762565 389241613897728196080481)
                  ·
                    rfl

theorem cell22_3411204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3411204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411204 prefixEnd_3411204 := by exact prefixLift 3411204
  have htrace : WordTrace (prefixWord ++ tailWord_3411204) baseStart_3411204 baseEnd_3411204 := by
    simpa [prefixWord, tailWord_3411204, baseEnd_3411204] using wordTrace_append hprefix tailTrace_3411204
  have hstable : (prefixWord ++ tailWord_3411204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411204).length < 2 ^ (prefixWord ++ tailWord_3411204).sum := by decide
  have hdescent : baseEnd_3411204 < baseStart_3411204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411264 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 1, 3]
def baseStart_3411264 : Nat := 118140960795 + 3411264 * 2 ^ 59
def prefixEnd_3411264 : Nat := 4983230072969 + 3 ^ 40 * 3411264 * 2
def baseEnd_3411264 : Nat := 1167745380919364431741259

theorem tailTrace_3411264 : CollatzResearch.WordTrace tailWord_3411264 prefixEnd_3411264 1167745380919364431741259 := by
  unfold tailWord_3411264
  simp only [CollatzResearch.WordTrace]
  refine ⟨62209509756790300176676423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82946013009053733568901897 62209509756790300176676423)
  ·
    refine ⟨93314264635185450265014635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62209509756790300176676423 93314264635185450265014635)
    ·
      refine ⟨139971396952778175397521953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93314264635185450265014635 139971396952778175397521953)
      ·
        refine ⟨104978547714583631548141465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139971396952778175397521953 104978547714583631548141465)
        ·
          refine ⟨78733910785937723661106099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104978547714583631548141465 78733910785937723661106099)
          ·
            refine ⟨118100866178906585491659149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78733910785937723661106099 118100866178906585491659149)
            ·
              refine ⟨44287824817089969559372181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118100866178906585491659149 44287824817089969559372181)
              ·
                refine ⟨2075991788301092323095571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44287824817089969559372181 2075991788301092323095571)
                ·
                  refine ⟨3113987682451638484643357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2075991788301092323095571 3113987682451638484643357)
                  ·
                    refine ⟨1167745380919364431741259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3113987682451638484643357 1167745380919364431741259)
                    ·
                      rfl

theorem cell22_3411264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 3].length) (baseStart_3411264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411264 prefixEnd_3411264 := by exact prefixLift 3411264
  have htrace : WordTrace (prefixWord ++ tailWord_3411264) baseStart_3411264 baseEnd_3411264 := by
    simpa [prefixWord, tailWord_3411264, baseEnd_3411264] using wordTrace_append hprefix tailTrace_3411264
  have hstable : (prefixWord ++ tailWord_3411264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411264).length < 2 ^ (prefixWord ++ tailWord_3411264).sum := by decide
  have hdescent : baseEnd_3411264 < baseStart_3411264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411270 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_3411270 : Nat := 118140960795 + 3411270 * 2 ^ 59
def prefixEnd_3411270 : Nat := 4983230072969 + 3 ^ 40 * 3411270 * 2
def baseEnd_3411270 : Nat := 1167747434841982416091241

theorem tailTrace_3411270 : CollatzResearch.WordTrace tailWord_3411270 prefixEnd_3411270 1167747434841982416091241 := by
  unfold tailWord_3411270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888101198486214480564727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82946158901039242252047509 3888101198486214480564727)
  ·
    refine ⟨5832151797729321720847091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888101198486214480564727 5832151797729321720847091)
    ·
      refine ⟨8748227696593982581270637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5832151797729321720847091 8748227696593982581270637)
      ·
        refine ⟨3280585386222743467976489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8748227696593982581270637 3280585386222743467976489)
        ·
          refine ⟨2460439039667057600982367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3280585386222743467976489 2460439039667057600982367)
          ·
            refine ⟨3690658559500586401473551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460439039667057600982367 3690658559500586401473551)
            ·
              refine ⟨5535987839250879602210327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690658559500586401473551 5535987839250879602210327)
              ·
                refine ⟨8303981758876319403315491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5535987839250879602210327 8303981758876319403315491)
                ·
                  refine ⟨12455972638314479104973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8303981758876319403315491 12455972638314479104973237)
                  ·
                    refine ⟨1167747434841982416091241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12455972638314479104973237 1167747434841982416091241)
                    ·
                      rfl

theorem cell22_3411270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_3411270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411270 prefixEnd_3411270 := by exact prefixLift 3411270
  have htrace : WordTrace (prefixWord ++ tailWord_3411270) baseStart_3411270 baseEnd_3411270 := by
    simpa [prefixWord, tailWord_3411270, baseEnd_3411270] using wordTrace_append hprefix tailTrace_3411270
  have hstable : (prefixWord ++ tailWord_3411270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411270).length < 2 ^ (prefixWord ++ tailWord_3411270).sum := by decide
  have hdescent : baseEnd_3411270 < baseStart_3411270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411373 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 4]
def baseStart_3411373 : Nat := 118140960795 + 3411373 * 2 ^ 59
def prefixEnd_3411373 : Nat := 4983230072969 + 3 ^ 40 * 3411373 * 2
def baseEnd_3411373 : Nat := 389260897948974826921975

theorem tailTrace_3411373 : CollatzResearch.WordTrace tailWord_3411373 prefixEnd_3411373 389260897948974826921975 := by
  unfold tailWord_3411373
  simp only [CollatzResearch.WordTrace]
  refine ⟨124422995070185711969070773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82948663380123807979380515 124422995070185711969070773)
  ·
    refine ⟨11664655787829910497100385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124422995070185711969070773 11664655787829910497100385)
    ·
      refine ⟨8748491840872432872825289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11664655787829910497100385 8748491840872432872825289)
      ·
        refine ⟨6561368880654324654618967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8748491840872432872825289 6561368880654324654618967)
        ·
          refine ⟨9842053320981486981928451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561368880654324654618967 9842053320981486981928451)
          ·
            refine ⟨14763079981472230472892677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842053320981486981928451 14763079981472230472892677)
            ·
              refine ⟨2768077496526043213667377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14763079981472230472892677 2768077496526043213667377)
              ·
                refine ⟨2076058122394532410250533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768077496526043213667377 2076058122394532410250533)
                ·
                  refine ⟨389260897948974826921975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076058122394532410250533 389260897948974826921975)
                  ·
                    rfl

theorem cell22_3411373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_3411373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411373 prefixEnd_3411373 := by exact prefixLift 3411373
  have htrace : WordTrace (prefixWord ++ tailWord_3411373) baseStart_3411373 baseEnd_3411373 := by
    simpa [prefixWord, tailWord_3411373, baseEnd_3411373] using wordTrace_append hprefix tailTrace_3411373
  have hstable : (prefixWord ++ tailWord_3411373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411373).length < 2 ^ (prefixWord ++ tailWord_3411373).sum := by decide
  have hdescent : baseEnd_3411373 < baseStart_3411373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411399 : List Nat := [1, 1, 4, 1, 1, 3, 3, 2, 3, 3]
def baseStart_3411399 : Nat := 118140960795 + 3411399 * 2 ^ 59
def prefixEnd_3411399 : Nat := 4983230072969 + 3 ^ 40 * 3411399 * 2
def baseEnd_3411399 : Nat := 1167791594178269079615845

theorem tailTrace_3411399 : CollatzResearch.WordTrace tailWord_3411399 prefixEnd_3411399 1167791594178269079615845 := by
  unfold tailWord_3411399
  simp only [CollatzResearch.WordTrace]
  refine ⟨124423943368091518409517251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82949295578727678939678167 124423943368091518409517251)
  ·
    refine ⟨186635915052137277614275877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124423943368091518409517251 186635915052137277614275877)
    ·
      refine ⟨34994234072275739552676727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186635915052137277614275877 34994234072275739552676727)
      ·
        refine ⟨52491351108413609329015091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34994234072275739552676727 52491351108413609329015091)
        ·
          refine ⟨78737026662620413993522637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52491351108413609329015091 78737026662620413993522637)
          ·
            refine ⟨29526384998482655247570989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78737026662620413993522637 29526384998482655247570989)
            ·
              refine ⟨11072394374430995717839121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29526384998482655247570989 11072394374430995717839121)
              ·
                refine ⟨8304295780823246788379341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11072394374430995717839121 8304295780823246788379341)
                ·
                  refine ⟨3114110917808717545642253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8304295780823246788379341 3114110917808717545642253)
                  ·
                    refine ⟨1167791594178269079615845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114110917808717545642253 1167791594178269079615845)
                    ·
                      rfl

theorem cell22_3411399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_3411399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411399 prefixEnd_3411399 := by exact prefixLift 3411399
  have htrace : WordTrace (prefixWord ++ tailWord_3411399) baseStart_3411399 baseEnd_3411399 := by
    simpa [prefixWord, tailWord_3411399, baseEnd_3411399] using wordTrace_append hprefix tailTrace_3411399
  have hstable : (prefixWord ++ tailWord_3411399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411399).length < 2 ^ (prefixWord ++ tailWord_3411399).sum := by decide
  have hdescent : baseEnd_3411399 < baseStart_3411399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411416 : List Nat := [2, 1, 2, 2, 2, 1, 3, 5, 1, 3]
def baseStart_3411416 : Nat := 118140960795 + 3411416 * 2 ^ 59
def prefixEnd_3411416 : Nat := 4983230072969 + 3 ^ 40 * 3411416 * 2
def baseEnd_3411416 : Nat := 1167797413625686701940793

theorem tailTrace_3411416 : CollatzResearch.WordTrace tailWord_3411416 prefixEnd_3411416 1167797413625686701940793 := by
  unfold tailWord_3411416
  simp only [CollatzResearch.WordTrace]
  refine ⟨62212281704514965156443051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82949708939353286875257401 62212281704514965156443051)
  ·
    refine ⟨93318422556772447734664577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62212281704514965156443051 93318422556772447734664577)
    ·
      refine ⟨69988816917579335800998433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93318422556772447734664577 69988816917579335800998433)
      ·
        refine ⟨52491612688184501850748825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69988816917579335800998433 52491612688184501850748825)
        ·
          refine ⟨39368709516138376388061619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52491612688184501850748825 39368709516138376388061619)
          ·
            refine ⟨59053064274207564582092429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39368709516138376388061619 59053064274207564582092429)
            ·
              refine ⟨22144899102827836718284661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59053064274207564582092429 22144899102827836718284661)
              ·
                refine ⟨2076084290890109692339187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22144899102827836718284661 2076084290890109692339187)
                ·
                  refine ⟨3114126436335164538508781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076084290890109692339187 3114126436335164538508781)
                  ·
                    refine ⟨1167797413625686701940793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114126436335164538508781 1167797413625686701940793)
                    ·
                      rfl

theorem cell22_3411416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_3411416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411416 prefixEnd_3411416 := by exact prefixLift 3411416
  have htrace : WordTrace (prefixWord ++ tailWord_3411416) baseStart_3411416 baseEnd_3411416 := by
    simpa [prefixWord, tailWord_3411416, baseEnd_3411416] using wordTrace_append hprefix tailTrace_3411416
  have hstable : (prefixWord ++ tailWord_3411416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411416).length < 2 ^ (prefixWord ++ tailWord_3411416).sum := by decide
  have hdescent : baseEnd_3411416 < baseStart_3411416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411429 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3411429 : Nat := 118140960795 + 3411429 * 2 ^ 59
def prefixEnd_3411429 : Nat := 4983230072969 + 3 ^ 40 * 3411429 * 2
def baseEnd_3411429 : Nat := 389267287930453000455251

theorem tailTrace_3411429 : CollatzResearch.WordTrace tailWord_3411429 prefixEnd_3411429 389267287930453000455251 := by
  unfold tailWord_3411429
  simp only [CollatzResearch.WordTrace]
  refine ⟨124425037557982833533109341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82950025038655222355406227 124425037557982833533109341)
  ·
    refine ⟨46659389084243562574916003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124425037557982833533109341 46659389084243562574916003)
    ·
      refine ⟨69989083626365343862374005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46659389084243562574916003 69989083626365343862374005)
      ·
        refine ⟨6561476589971750987097563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69989083626365343862374005 6561476589971750987097563)
        ·
          refine ⟨9842214884957626480646345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6561476589971750987097563 9842214884957626480646345)
          ·
            refine ⟨7381661163718219860484759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9842214884957626480646345 7381661163718219860484759)
            ·
              refine ⟨11072491745577329790727139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381661163718219860484759 11072491745577329790727139)
              ·
                refine ⟨16608737618365994686090709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11072491745577329790727139 16608737618365994686090709)
                ·
                  refine ⟨389267287930453000455251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16608737618365994686090709 389267287930453000455251)
                  ·
                    rfl

theorem cell22_3411429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3411429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411429 prefixEnd_3411429 := by exact prefixLift 3411429
  have htrace : WordTrace (prefixWord ++ tailWord_3411429) baseStart_3411429 baseEnd_3411429 := by
    simpa [prefixWord, tailWord_3411429, baseEnd_3411429] using wordTrace_append hprefix tailTrace_3411429
  have hstable : (prefixWord ++ tailWord_3411429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411429).length < 2 ^ (prefixWord ++ tailWord_3411429).sum := by decide
  have hdescent : baseEnd_3411429 < baseStart_3411429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411491 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 6]
def baseStart_3411491 : Nat := 118140960795 + 3411491 * 2 ^ 59
def prefixEnd_3411491 : Nat := 4983230072969 + 3 ^ 40 * 3411491 * 2
def baseEnd_3411491 : Nat := 389274362552803835438521

theorem tailTrace_3411491 : CollatzResearch.WordTrace tailWord_3411491 prefixEnd_3411491 389274362552803835438521 := by
  unfold tailWord_3411491
  simp only [CollatzResearch.WordTrace]
  refine ⟨124427298883758218121866327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82951532589172145414577551 124427298883758218121866327)
  ·
    refine ⟨186640948325637327182799491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124427298883758218121866327 186640948325637327182799491)
    ·
      refine ⟨279961422488455990774199237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186640948325637327182799491 279961422488455990774199237)
      ·
        refine ⟨52492766716585498270162357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 279961422488455990774199237 52492766716585498270162357)
        ·
          refine ⟨4921196879679890462827721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52492766716585498270162357 4921196879679890462827721)
          ·
            refine ⟨3690897659759917847120791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4921196879679890462827721 3690897659759917847120791)
            ·
              refine ⟨5536346489639876770681187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690897659759917847120791 5536346489639876770681187)
              ·
                refine ⟨8304519734459815156021781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536346489639876770681187 8304519734459815156021781)
                ·
                  refine ⟨389274362552803835438521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8304519734459815156021781 389274362552803835438521)
                  ·
                    rfl

theorem cell22_3411491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 6].length) (baseStart_3411491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411491 prefixEnd_3411491 := by exact prefixLift 3411491
  have htrace : WordTrace (prefixWord ++ tailWord_3411491) baseStart_3411491 baseEnd_3411491 := by
    simpa [prefixWord, tailWord_3411491, baseEnd_3411491] using wordTrace_append hprefix tailTrace_3411491
  have hstable : (prefixWord ++ tailWord_3411491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411491).length < 2 ^ (prefixWord ++ tailWord_3411491).sum := by decide
  have hdescent : baseEnd_3411491 < baseStart_3411491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411510 : List Nat := [5, 1, 2, 1, 3, 2, 1, 2, 1, 4]
def baseStart_3411510 : Nat := 118140960795 + 3411510 * 2 ^ 59
def prefixEnd_3411510 : Nat := 4983230072969 + 3 ^ 40 * 3411510 * 2
def baseEnd_3411510 : Nat := 1167829591746701790090505

theorem tailTrace_3411510 : CollatzResearch.WordTrace tailWord_3411510 prefixEnd_3411510 1167829591746701790090505 := by
  unfold tailWord_3411510
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776749491918086522925499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82951994580459589577871989 7776749491918086522925499)
  ·
    refine ⟨11665124237877129784388249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7776749491918086522925499 11665124237877129784388249)
    ·
      refine ⟨8748843178407847338291187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11665124237877129784388249 8748843178407847338291187)
      ·
        refine ⟨13123264767611771007436781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748843178407847338291187 13123264767611771007436781)
        ·
          refine ⟨4921224287854414127788793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13123264767611771007436781 4921224287854414127788793)
          ·
            refine ⟨3690918215890810595841595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4921224287854414127788793 3690918215890810595841595)
            ·
              refine ⟨5536377323836215893762393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690918215890810595841595 5536377323836215893762393)
              ·
                refine ⟨4152282992877161920321795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5536377323836215893762393 4152282992877161920321795)
                ·
                  refine ⟨6228424489315742880482693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4152282992877161920321795 6228424489315742880482693)
                  ·
                    refine ⟨1167829591746701790090505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228424489315742880482693 1167829591746701790090505)
                    ·
                      rfl

theorem cell22_3411510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_3411510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411510 prefixEnd_3411510 := by exact prefixLift 3411510
  have htrace : WordTrace (prefixWord ++ tailWord_3411510) baseStart_3411510 baseEnd_3411510 := by
    simpa [prefixWord, tailWord_3411510, baseEnd_3411510] using wordTrace_append hprefix tailTrace_3411510
  have hstable : (prefixWord ++ tailWord_3411510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411510).length < 2 ^ (prefixWord ++ tailWord_3411510).sum := by decide
  have hdescent : baseEnd_3411510 < baseStart_3411510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411521 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 2, 4]
def baseStart_3411521 : Nat := 118140960795 + 3411521 * 2 ^ 59
def prefixEnd_3411521 : Nat := 4983230072969 + 3 ^ 40 * 3411521 * 2
def baseEnd_3411521 : Nat := 1167833357271501428065471

theorem tailTrace_3411521 : CollatzResearch.WordTrace tailWord_3411521 prefixEnd_3411521 1167833357271501428065471 := by
  unfold tailWord_3411521
  simp only [CollatzResearch.WordTrace]
  refine ⟨124428393073649533245458417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82952262049099688830305611 124428393073649533245458417)
  ·
    refine ⟨93321294805237149934093813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124428393073649533245458417 93321294805237149934093813)
    ·
      refine ⟨8748871387990982806321295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93321294805237149934093813 8748871387990982806321295)
      ·
        refine ⟨13123307081986474209481943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8748871387990982806321295 13123307081986474209481943)
        ·
          refine ⟨19684960622979711314222915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123307081986474209481943 19684960622979711314222915)
          ·
            refine ⟨29527440934469566971334373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19684960622979711314222915 29527440934469566971334373)
            ·
              refine ⟨5536395175213043807125195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29527440934469566971334373 5536395175213043807125195)
              ·
                refine ⟨8304592762819565710687793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536395175213043807125195 8304592762819565710687793)
                ·
                  refine ⟨6228444572114674283015845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304592762819565710687793 6228444572114674283015845)
                  ·
                    refine ⟨1167833357271501428065471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228444572114674283015845 1167833357271501428065471)
                    ·
                      rfl

theorem cell22_3411521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_3411521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411521 prefixEnd_3411521 := by exact prefixLift 3411521
  have htrace : WordTrace (prefixWord ++ tailWord_3411521) baseStart_3411521 baseEnd_3411521 := by
    simpa [prefixWord, tailWord_3411521, baseEnd_3411521] using wordTrace_append hprefix tailTrace_3411521
  have hstable : (prefixWord ++ tailWord_3411521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411521).length < 2 ^ (prefixWord ++ tailWord_3411521).sum := by decide
  have hdescent : baseEnd_3411521 < baseStart_3411521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411542 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 4]
def baseStart_3411542 : Nat := 118140960795 + 3411542 * 2 ^ 59
def prefixEnd_3411542 : Nat := 4983230072969 + 3 ^ 40 * 3411542 * 2
def baseEnd_3411542 : Nat := 389280182000221457763469

theorem tailTrace_3411542 : CollatzResearch.WordTrace tailWord_3411542 prefixEnd_3411542 389280182000221457763469 := by
  unfold tailWord_3411542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7776822437910840864498305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82952772671048969221315253 7776822437910840864498305)
  ·
    refine ⟨5832616828433130648373729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7776822437910840864498305 5832616828433130648373729)
    ·
      refine ⟨4374462621324847986280297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832616828433130648373729 4374462621324847986280297)
      ·
        refine ⟨3280846965993635989710223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4374462621324847986280297 3280846965993635989710223)
        ·
          refine ⟨4921270448990453984565335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280846965993635989710223 4921270448990453984565335)
          ·
            refine ⟨7381905673485680976848003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921270448990453984565335 7381905673485680976848003)
            ·
              refine ⟨11072858510228521465272005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7381905673485680976848003 11072858510228521465272005)
              ·
                refine ⟨2076160970667847774738501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11072858510228521465272005 2076160970667847774738501)
                ·
                  refine ⟨389280182000221457763469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076160970667847774738501 389280182000221457763469)
                  ·
                    rfl

theorem cell22_3411542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_3411542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411542 prefixEnd_3411542 := by exact prefixLift 3411542
  have htrace : WordTrace (prefixWord ++ tailWord_3411542) baseStart_3411542 baseEnd_3411542 := by
    simpa [prefixWord, tailWord_3411542, baseEnd_3411542] using wordTrace_append hprefix tailTrace_3411542
  have hstable : (prefixWord ++ tailWord_3411542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411542).length < 2 ^ (prefixWord ++ tailWord_3411542).sum := by decide
  have hdescent : baseEnd_3411542 < baseStart_3411542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411585 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 1, 3]
def baseStart_3411585 : Nat := 118140960795 + 3411585 * 2 ^ 59
def prefixEnd_3411585 : Nat := 4983230072969 + 3 ^ 40 * 3411585 * 2
def baseEnd_3411585 : Nat := 1167855265779426594465275

theorem tailTrace_3411585 : CollatzResearch.WordTrace tailWord_3411585 prefixEnd_3411585 1167855265779426594465275 := by
  unfold tailWord_3411585
  simp only [CollatzResearch.WordTrace]
  refine ⟨124430727345417672175788209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82953818230278448117192139 124430727345417672175788209)
  ·
    refine ⟨93323045509063254131841157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124430727345417672175788209 93323045509063254131841157)
    ·
      refine ⟨17498071032949360149720217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93323045509063254131841157 17498071032949360149720217)
      ·
        refine ⟨13123553274712020112290163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17498071032949360149720217 13123553274712020112290163)
        ·
          refine ⟨19685329912068030168435245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123553274712020112290163 19685329912068030168435245)
          ·
            refine ⟨7381998717025511313163217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19685329912068030168435245 7381998717025511313163217)
            ·
              refine ⟨5536499037769133484872413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7381998717025511313163217 5536499037769133484872413)
              ·
                refine ⟨2076187139163425056827155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536499037769133484872413 2076187139163425056827155)
                ·
                  refine ⟨3114280708745137585240733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076187139163425056827155 3114280708745137585240733)
                  ·
                    refine ⟨1167855265779426594465275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114280708745137585240733 1167855265779426594465275)
                    ·
                      rfl

theorem cell22_3411585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_3411585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411585 prefixEnd_3411585 := by exact prefixLift 3411585
  have htrace : WordTrace (prefixWord ++ tailWord_3411585) baseStart_3411585 baseEnd_3411585 := by
    simpa [prefixWord, tailWord_3411585, baseEnd_3411585] using wordTrace_append hprefix tailTrace_3411585
  have hstable : (prefixWord ++ tailWord_3411585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411585).length < 2 ^ (prefixWord ++ tailWord_3411585).sum := by decide
  have hdescent : baseEnd_3411585 < baseStart_3411585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411598 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3411598 : Nat := 118140960795 + 3411598 * 2 ^ 59
def prefixEnd_3411598 : Nat := 4983230072969 + 3 ^ 40 * 3411598 * 2
def baseEnd_3411598 : Nat := 389286571981699631296745

theorem tailTrace_3411598 : CollatzResearch.WordTrace tailWord_3411598 prefixEnd_3411598 389286571981699631296745 := by
  unfold tailWord_3411598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553900186796321924501431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82954134329580383597340965 15553900186796321924501431)
  ·
    refine ⟨23330850280194482886752147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15553900186796321924501431 23330850280194482886752147)
    ·
      refine ⟨34996275420291724330128221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23330850280194482886752147 34996275420291724330128221)
      ·
        refine ⟨13123603282609396623798083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34996275420291724330128221 13123603282609396623798083)
        ·
          refine ⟨19685404923914094935697125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13123603282609396623798083 19685404923914094935697125)
          ·
            refine ⟨3691013423233892800443211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19685404923914094935697125 3691013423233892800443211)
            ·
              refine ⟨5536520134850839200664817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691013423233892800443211 5536520134850839200664817)
              ·
                refine ⟨4152390101138129400498613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5536520134850839200664817 4152390101138129400498613)
                ·
                  refine ⟨389286571981699631296745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4152390101138129400498613 389286571981699631296745)
                  ·
                    rfl

theorem cell22_3411598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3411598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411598 prefixEnd_3411598 := by exact prefixLift 3411598
  have htrace : WordTrace (prefixWord ++ tailWord_3411598) baseStart_3411598 baseEnd_3411598 := by
    simpa [prefixWord, tailWord_3411598, baseEnd_3411598] using wordTrace_append hprefix tailTrace_3411598
  have hstable : (prefixWord ++ tailWord_3411598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411598).length < 2 ^ (prefixWord ++ tailWord_3411598).sum := by decide
  have hdescent : baseEnd_3411598 < baseStart_3411598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411615 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 5]
def baseStart_3411615 : Nat := 118140960795 + 3411615 * 2 ^ 59
def prefixEnd_3411615 : Nat := 4983230072969 + 3 ^ 40 * 3411615 * 2
def baseEnd_3411615 : Nat := 389288511797505505405061

theorem tailTrace_3411615 : CollatzResearch.WordTrace tailWord_3411615 prefixEnd_3411615 389288511797505505405061 := by
  unfold tailWord_3411615
  simp only [CollatzResearch.WordTrace]
  refine ⟨124431821535308987299380299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82954547690205991532920199 124431821535308987299380299)
  ·
    refine ⟨186647732302963480949070449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124431821535308987299380299 186647732302963480949070449)
    ·
      refine ⟨139985799227222610711802837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186647732302963480949070449 139985799227222610711802837)
      ·
        refine ⟨3280917169388029938557879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139985799227222610711802837 3280917169388029938557879)
        ·
          refine ⟨4921375754082044907836819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280917169388029938557879 4921375754082044907836819)
          ·
            refine ⟨7382063631123067361755229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921375754082044907836819 7382063631123067361755229)
            ·
              refine ⟨2768273861671150260658211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7382063631123067361755229 2768273861671150260658211)
              ·
                refine ⟨4152410792506725390987317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768273861671150260658211 4152410792506725390987317)
                ·
                  refine ⟨389288511797505505405061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4152410792506725390987317 389288511797505505405061)
                  ·
                    rfl

theorem cell22_3411615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 5].length) (baseStart_3411615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411615 prefixEnd_3411615 := by exact prefixLift 3411615
  have htrace : WordTrace (prefixWord ++ tailWord_3411615) baseStart_3411615 baseEnd_3411615 := by
    simpa [prefixWord, tailWord_3411615, baseEnd_3411615] using wordTrace_append hprefix tailTrace_3411615
  have hstable : (prefixWord ++ tailWord_3411615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411615).length < 2 ^ (prefixWord ++ tailWord_3411615).sum := by decide
  have hdescent : baseEnd_3411615 < baseStart_3411615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411641 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 4, 3]
def baseStart_3411641 : Nat := 118140960795 + 3411641 * 2 ^ 59
def prefixEnd_3411641 : Nat := 4983230072969 + 3 ^ 40 * 3411641 * 2
def baseEnd_3411641 : Nat := 1167874435723861115065103

theorem tailTrace_3411641 : CollatzResearch.WordTrace tailWord_3411641 prefixEnd_3411641 1167874435723861115065103 := by
  unfold tailWord_3411641
  simp only [CollatzResearch.WordTrace]
  refine ⟨124432769833214793739826777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82955179888809862493217851 124432769833214793739826777)
  ·
    refine ⟨93324577374911095304870083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124432769833214793739826777 93324577374911095304870083)
    ·
      refine ⟨139986866062366642957305125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93324577374911095304870083 139986866062366642957305125)
      ·
        refine ⟨26247537386693745554494711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139986866062366642957305125 26247537386693745554494711)
        ·
          refine ⟨39371306080040618331742067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26247537386693745554494711 39371306080040618331742067)
          ·
            refine ⟨59056959120060927497613101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39371306080040618331742067 59056959120060927497613101)
            ·
              refine ⟨22146359670022847811604913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59056959120060927497613101 22146359670022847811604913)
              ·
                refine ⟨16609769752517135858703685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22146359670022847811604913 16609769752517135858703685)
                ·
                  refine ⟨3114331828596962973506941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16609769752517135858703685 3114331828596962973506941)
                  ·
                    refine ⟨1167874435723861115065103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114331828596962973506941 1167874435723861115065103)
                    ·
                      rfl

theorem cell22_3411641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 3].length) (baseStart_3411641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411641 prefixEnd_3411641 := by exact prefixLift 3411641
  have htrace : WordTrace (prefixWord ++ tailWord_3411641) baseStart_3411641 baseEnd_3411641 := by
    simpa [prefixWord, tailWord_3411641, baseEnd_3411641] using wordTrace_append hprefix tailTrace_3411641
  have hstable : (prefixWord ++ tailWord_3411641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411641).length < 2 ^ (prefixWord ++ tailWord_3411641).sum := by decide
  have hdescent : baseEnd_3411641 < baseStart_3411641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411656 : List Nat := [2, 1, 3, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3411656 : Nat := 118140960795 + 3411656 * 2 ^ 59
def prefixEnd_3411656 : Nat := 4983230072969 + 3 ^ 40 * 3411656 * 2
def baseEnd_3411656 : Nat := 1167879570530406075940057

theorem tailTrace_3411656 : CollatzResearch.WordTrace tailWord_3411656 prefixEnd_3411656 1167879570530406075940057 := by
  unfold tailWord_3411656
  simp only [CollatzResearch.WordTrace]
  refine ⟨62216658464080225650811411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82955544618773634201081881 62216658464080225650811411)
  ·
    refine ⟨93324987696120338476217117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62216658464080225650811411 93324987696120338476217117)
    ·
      refine ⟨34996870386045126928581419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93324987696120338476217117 34996870386045126928581419)
      ·
        refine ⟨52495305579067690392872129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34996870386045126928581419 52495305579067690392872129)
        ·
          refine ⟨39371479184300767794654097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52495305579067690392872129 39371479184300767794654097)
          ·
            refine ⟨29528609388225575845990573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39371479184300767794654097 29528609388225575845990573)
            ·
              refine ⟨11073228520584590942246465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29528609388225575845990573 11073228520584590942246465)
              ·
                refine ⟨8304921390438443206684849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11073228520584590942246465 8304921390438443206684849)
                ·
                  refine ⟨6228691042828832405013637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8304921390438443206684849 6228691042828832405013637)
                  ·
                    refine ⟨1167879570530406075940057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6228691042828832405013637 1167879570530406075940057)
                    ·
                      rfl

theorem cell22_3411656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3411656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411656 prefixEnd_3411656 := by exact prefixLift 3411656
  have htrace : WordTrace (prefixWord ++ tailWord_3411656) baseStart_3411656 baseEnd_3411656 := by
    simpa [prefixWord, tailWord_3411656, baseEnd_3411656] using wordTrace_append hprefix tailTrace_3411656
  have hstable : (prefixWord ++ tailWord_3411656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411656).length < 2 ^ (prefixWord ++ tailWord_3411656).sum := by decide
  have hdescent : baseEnd_3411656 < baseStart_3411656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411660 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 6]
def baseStart_3411660 : Nat := 118140960795 + 3411660 * 2 ^ 59
def prefixEnd_3411660 : Nat := 4983230072969 + 3 ^ 40 * 3411660 * 2
def baseEnd_3411660 : Nat := 389293646604050466280015

theorem tailTrace_3411660 : CollatzResearch.WordTrace tailWord_3411660 prefixEnd_3411660 389293646604050466280015 := by
  unfold tailWord_3411660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62216731410072979992384217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82955641880097306656512289 62216731410072979992384217)
  ·
    refine ⟨46662548557554734994288163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62216731410072979992384217 46662548557554734994288163)
    ·
      refine ⟨69993822836332102491432245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46662548557554734994288163 69993822836332102491432245)
      ·
        refine ⟨6561920890906134608571773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69993822836332102491432245 6561920890906134608571773)
        ·
          refine ⟨2460720334089800478214415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6561920890906134608571773 2460720334089800478214415)
          ·
            refine ⟨3691080501134700717321623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460720334089800478214415 3691080501134700717321623)
            ·
              refine ⟨5536620751702051075982435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691080501134700717321623 5536620751702051075982435)
              ·
                refine ⟨8304931127553076613973653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536620751702051075982435 8304931127553076613973653)
                ·
                  refine ⟨389293646604050466280015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8304931127553076613973653 389293646604050466280015)
                  ·
                    rfl

theorem cell22_3411660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_3411660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411660 prefixEnd_3411660 := by exact prefixLift 3411660
  have htrace : WordTrace (prefixWord ++ tailWord_3411660) baseStart_3411660 baseEnd_3411660 := by
    simpa [prefixWord, tailWord_3411660, baseEnd_3411660] using wordTrace_append hprefix tailTrace_3411660
  have hstable : (prefixWord ++ tailWord_3411660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411660).length < 2 ^ (prefixWord ++ tailWord_3411660).sum := by decide
  have hdescent : baseEnd_3411660 < baseStart_3411660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411699 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 9]
def baseStart_3411699 : Nat := 118140960795 + 3411699 * 2 ^ 59
def prefixEnd_3411699 : Nat := 4983230072969 + 3 ^ 40 * 3411699 * 2
def baseEnd_3411699 : Nat := 389298096769722765704975

theorem tailTrace_3411699 : CollatzResearch.WordTrace tailWord_3411699 prefixEnd_3411699 389298096769722765704975 := by
  unfold tailWord_3411699
  simp only [CollatzResearch.WordTrace]
  refine ⟨124434885267004669645438151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82956590178003113096958767 124434885267004669645438151)
  ·
    refine ⟨186652327900507004468157227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124434885267004669645438151 186652327900507004468157227)
    ·
      refine ⟨279978491850760506702235841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186652327900507004468157227 279978491850760506702235841)
      ·
        refine ⟨209983868888070380026676881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 279978491850760506702235841 209983868888070380026676881)
        ·
          refine ⟨157487901666052785020007661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209983868888070380026676881 157487901666052785020007661)
          ·
            refine ⟨59057963124769794382502873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157487901666052785020007661 59057963124769794382502873)
            ·
              refine ⟨44293472343577345786877155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59057963124769794382502873 44293472343577345786877155)
              ·
                refine ⟨66440208515366018680315733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44293472343577345786877155 66440208515366018680315733)
                ·
                  refine ⟨389298096769722765704975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66440208515366018680315733 389298096769722765704975)
                  ·
                    rfl

theorem cell22_3411699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_3411699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411699 prefixEnd_3411699 := by exact prefixLift 3411699
  have htrace : WordTrace (prefixWord ++ tailWord_3411699) baseStart_3411699 baseEnd_3411699 := by
    simpa [prefixWord, tailWord_3411699, baseEnd_3411699] using wordTrace_append hprefix tailTrace_3411699
  have hstable : (prefixWord ++ tailWord_3411699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411699).length < 2 ^ (prefixWord ++ tailWord_3411699).sum := by decide
  have hdescent : baseEnd_3411699 < baseStart_3411699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411720 : List Nat := [2, 1, 3, 2, 2, 1, 3, 4, 1, 3]
def baseStart_3411720 : Nat := 118140960795 + 3411720 * 2 ^ 59
def prefixEnd_3411720 : Nat := 4983230072969 + 3 ^ 40 * 3411720 * 2
def baseEnd_3411720 : Nat := 1167901479038331242339861

theorem tailTrace_3411720 : CollatzResearch.WordTrace tailWord_3411720 prefixEnd_3411720 1167901479038331242339861 := by
  unfold tailWord_3411720
  simp only [CollatzResearch.WordTrace]
  refine ⟨62217825599964295115976307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82957100799952393487968409 62217825599964295115976307)
  ·
    refine ⟨93326738399946442673964461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62217825599964295115976307 93326738399946442673964461)
    ·
      refine ⟨34997526899979916002736673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93326738399946442673964461 34997526899979916002736673)
      ·
        refine ⟨26248145174984937002052505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34997526899979916002736673 26248145174984937002052505)
        ·
          refine ⟨19686108881238702751539379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26248145174984937002052505 19686108881238702751539379)
          ·
            refine ⟨29529163321858054127309069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19686108881238702751539379 29529163321858054127309069)
            ·
              refine ⟨11073436245696770297740901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29529163321858054127309069 11073436245696770297740901)
              ·
                refine ⟨2076269296068144430826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11073436245696770297740901 2076269296068144430826419)
                ·
                  refine ⟨3114403944102216646239629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076269296068144430826419 3114403944102216646239629)
                  ·
                    refine ⟨1167901479038331242339861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114403944102216646239629 1167901479038331242339861)
                    ·
                      rfl

theorem cell22_3411720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_3411720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411720 prefixEnd_3411720 := by exact prefixLift 3411720
  have htrace : WordTrace (prefixWord ++ tailWord_3411720) baseStart_3411720 baseEnd_3411720 := by
    simpa [prefixWord, tailWord_3411720, baseEnd_3411720] using wordTrace_append hprefix tailTrace_3411720
  have hstable : (prefixWord ++ tailWord_3411720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411720).length < 2 ^ (prefixWord ++ tailWord_3411720).sum := by decide
  have hdescent : baseEnd_3411720 < baseStart_3411720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411793 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 1, 5]
def baseStart_3411793 : Nat := 118140960795 + 3411793 * 2 ^ 59
def prefixEnd_3411793 : Nat := 4983230072969 + 3 ^ 40 * 3411793 * 2
def baseEnd_3411793 : Nat := 1167926468430183385264637

theorem tailTrace_3411793 : CollatzResearch.WordTrace tailWord_3411793 prefixEnd_3411793 1167926468430183385264637 := by
  unfold tailWord_3411793
  simp only [CollatzResearch.WordTrace]
  refine ⟨124438313728664123699360033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82958875819109415799573355 124438313728664123699360033)
  ·
    refine ⟨93328735296498092774520025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124438313728664123699360033 93328735296498092774520025)
    ·
      refine ⟨69996551472373569580890019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93328735296498092774520025 69996551472373569580890019)
      ·
        refine ⟨104994827208560354371335029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69996551472373569580890019 104994827208560354371335029)
        ·
          refine ⟨9843265050802533222312659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104994827208560354371335029 9843265050802533222312659)
          ·
            refine ⟨14764897576203799833468989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843265050802533222312659 14764897576203799833468989)
            ·
              refine ⟨5536836591076424937550871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14764897576203799833468989 5536836591076424937550871)
              ·
                refine ⟨8305254886614637406326307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5536836591076424937550871 8305254886614637406326307)
                ·
                  refine ⟨12457882329921956109489461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305254886614637406326307 12457882329921956109489461)
                  ·
                    refine ⟨1167926468430183385264637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12457882329921956109489461 1167926468430183385264637)
                    ·
                      rfl

theorem cell22_3411793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_3411793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411793 prefixEnd_3411793 := by exact prefixLift 3411793
  have htrace : WordTrace (prefixWord ++ tailWord_3411793) baseStart_3411793 baseEnd_3411793 := by
    simpa [prefixWord, tailWord_3411793, baseEnd_3411793] using wordTrace_append hprefix tailTrace_3411793
  have hstable : (prefixWord ++ tailWord_3411793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411793).length < 2 ^ (prefixWord ++ tailWord_3411793).sum := by decide
  have hdescent : baseEnd_3411793 < baseStart_3411793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411810 : List Nat := [3, 3, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_3411810 : Nat := 118140960795 + 3411810 * 2 ^ 59
def prefixEnd_3411810 : Nat := 4983230072969 + 3 ^ 40 * 3411810 * 2
def baseEnd_3411810 : Nat := 1167932287877601007589585

theorem tailTrace_3411810 : CollatzResearch.WordTrace tailWord_3411810 prefixEnd_3411810 1167932287877601007589585 := by
  unfold tailWord_3411810
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109733442400633900682221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82959289179735023735152589 31109733442400633900682221)
  ·
    refine ⟨11666150040900237712755833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31109733442400633900682221 11666150040900237712755833)
    ·
      refine ⟨8749612530675178284566875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11666150040900237712755833 8749612530675178284566875)
      ·
        refine ⟨13124418796012767426850313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8749612530675178284566875 13124418796012767426850313)
        ·
          refine ⟨9843314097009575570137735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124418796012767426850313 9843314097009575570137735)
          ·
            refine ⟨14764971145514363355206603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843314097009575570137735 14764971145514363355206603)
            ·
              refine ⟨22147456718271545032809905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14764971145514363355206603 22147456718271545032809905)
              ·
                refine ⟨16610592538703658774607429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22147456718271545032809905 16610592538703658774607429)
                ·
                  refine ⟨3114486101006936020238893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16610592538703658774607429 3114486101006936020238893)
                  ·
                    refine ⟨1167932287877601007589585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114486101006936020238893 1167932287877601007589585)
                    ·
                      rfl

theorem cell22_3411810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_3411810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411810 prefixEnd_3411810 := by exact prefixLift 3411810
  have htrace : WordTrace (prefixWord ++ tailWord_3411810) baseStart_3411810 baseEnd_3411810 := by
    simpa [prefixWord, tailWord_3411810, baseEnd_3411810] using wordTrace_append hprefix tailTrace_3411810
  have hstable : (prefixWord ++ tailWord_3411810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411810).length < 2 ^ (prefixWord ++ tailWord_3411810).sum := by decide
  have hdescent : baseEnd_3411810 < baseStart_3411810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411812 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 4]
def baseStart_3411812 : Nat := 118140960795 + 3411812 * 2 ^ 59
def prefixEnd_3411812 : Nat := 4983230072969 + 3 ^ 40 * 3411812 * 2
def baseEnd_3411812 : Nat := 389310990839491223013193

theorem tailTrace_3411812 : CollatzResearch.WordTrace tailWord_3411812 prefixEnd_3411812 389310990839491223013193 := by
  unfold tailWord_3411812
  simp only [CollatzResearch.WordTrace]
  refine ⟨62219503357797644972150845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82959337810396859962867793 62219503357797644972150845)
  ·
    refine ⟨23332313759174116864556567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62219503357797644972150845 23332313759174116864556567)
    ·
      refine ⟨34998470638761175296834851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332313759174116864556567 34998470638761175296834851)
      ·
        refine ⟨52497705958141762945252277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34998470638761175296834851 52497705958141762945252277)
        ·
          refine ⟨4921659933575790276117401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52497705958141762945252277 4921659933575790276117401)
          ·
            refine ⟨3691244950181842707088051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4921659933575790276117401 3691244950181842707088051)
            ·
              refine ⟨5536867425272764060632077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3691244950181842707088051 5536867425272764060632077)
              ·
                refine ⟨2076325284477286522737029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536867425272764060632077 2076325284477286522737029)
                ·
                  refine ⟨389310990839491223013193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076325284477286522737029 389310990839491223013193)
                  ·
                    rfl

theorem cell22_3411812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_3411812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411812 prefixEnd_3411812 := by exact prefixLift 3411812
  have htrace : WordTrace (prefixWord ++ tailWord_3411812) baseStart_3411812 baseEnd_3411812 := by
    simpa [prefixWord, tailWord_3411812, baseEnd_3411812] using wordTrace_append hprefix tailTrace_3411812
  have hstable : (prefixWord ++ tailWord_3411812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411812).length < 2 ^ (prefixWord ++ tailWord_3411812).sum := by decide
  have hdescent : baseEnd_3411812 < baseStart_3411812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411889 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 1, 3]
def baseStart_3411889 : Nat := 118140960795 + 3411889 * 2 ^ 59
def prefixEnd_3411889 : Nat := 4983230072969 + 3 ^ 40 * 3411889 * 2
def baseEnd_3411889 : Nat := 1167959331192071134864343

theorem tailTrace_3411889 : CollatzResearch.WordTrace tailWord_3411889 prefixEnd_3411889 1167959331192071134864343 := by
  unfold tailWord_3411889
  simp only [CollatzResearch.WordTrace]
  refine ⟨124441815136316332094854721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82961210090877554729903147 124441815136316332094854721)
  ·
    refine ⟨93331361352237249071141041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124441815136316332094854721 93331361352237249071141041)
    ·
      refine ⟨69998521014177936803355781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93331361352237249071141041 69998521014177936803355781)
      ·
        refine ⟨13124722690158363150629209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69998521014177936803355781 13124722690158363150629209)
        ·
          refine ⟨9843542017618772362971907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124722690158363150629209 9843542017618772362971907)
          ·
            refine ⟨14765313026428158544457861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9843542017618772362971907 14765313026428158544457861)
            ·
              refine ⟨2768496192455279727085849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14765313026428158544457861 2768496192455279727085849)
              ·
                refine ⟨2076372144341459795314387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2768496192455279727085849 2076372144341459795314387)
                ·
                  refine ⟨3114558216512189692971581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076372144341459795314387 3114558216512189692971581)
                  ·
                    refine ⟨1167959331192071134864343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114558216512189692971581 1167959331192071134864343)
                    ·
                      rfl

theorem cell22_3411889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 3].length) (baseStart_3411889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411889 prefixEnd_3411889 := by exact prefixLift 3411889
  have htrace : WordTrace (prefixWord ++ tailWord_3411889) baseStart_3411889 baseEnd_3411889 := by
    simpa [prefixWord, tailWord_3411889, baseEnd_3411889] using wordTrace_append hprefix tailTrace_3411889
  have hstable : (prefixWord ++ tailWord_3411889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411889).length < 2 ^ (prefixWord ++ tailWord_3411889).sum := by decide
  have hdescent : baseEnd_3411889 < baseStart_3411889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411928 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 5]
def baseStart_3411928 : Nat := 118140960795 + 3411928 * 2 ^ 59
def prefixEnd_3411928 : Nat := 4983230072969 + 3 ^ 40 * 3411928 * 2
def baseEnd_3411928 : Nat := 1167972681689088033139223

theorem tailTrace_3411928 : CollatzResearch.WordTrace tailWord_3411928 prefixEnd_3411928 1167972681689088033139223 := by
  unfold tailWord_3411928
  simp only [CollatzResearch.WordTrace]
  refine ⟨62221618791587520877762219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82962158388783361170349625 62221618791587520877762219)
  ·
    refine ⟨93332428187381281316643329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62221618791587520877762219 93332428187381281316643329)
    ·
      refine ⟨69999321140535960987482497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93332428187381281316643329 69999321140535960987482497)
      ·
        refine ⟨52499490855401970740611873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69999321140535960987482497 52499490855401970740611873)
        ·
          refine ⟨39374618141551478055458905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52499490855401970740611873 39374618141551478055458905)
          ·
            refine ⟨29530963606163608541594179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39374618141551478055458905 29530963606163608541594179)
            ·
              refine ⟨44296445409245412812391269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29530963606163608541594179 44296445409245412812391269)
              ·
                refine ⟨8305583514233514902323363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44296445409245412812391269 8305583514233514902323363)
                ·
                  refine ⟨12458375271350272353485045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305583514233514902323363 12458375271350272353485045)
                  ·
                    refine ⟨1167972681689088033139223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12458375271350272353485045 1167972681689088033139223)
                    ·
                      rfl

theorem cell22_3411928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_3411928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411928 prefixEnd_3411928 := by exact prefixLift 3411928
  have htrace : WordTrace (prefixWord ++ tailWord_3411928) baseStart_3411928 baseEnd_3411928 := by
    simpa [prefixWord, tailWord_3411928, baseEnd_3411928] using wordTrace_append hprefix tailTrace_3411928
  have hstable : (prefixWord ++ tailWord_3411928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411928).length < 2 ^ (prefixWord ++ tailWord_3411928).sum := by decide
  have hdescent : baseEnd_3411928 < baseStart_3411928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3411975 : List Nat := [1, 1, 4, 3, 1, 2, 4, 6]
def baseStart_3411975 : Nat := 118140960795 + 3411975 * 2 ^ 59
def prefixEnd_3411975 : Nat := 4983230072969 + 3 ^ 40 * 3411975 * 2
def baseEnd_3411975 : Nat := 129776530083288397468231

theorem tailTrace_3411975 : CollatzResearch.WordTrace tailWord_3411975 prefixEnd_3411975 129776530083288397468231 := by
  unfold tailWord_3411975
  simp only [CollatzResearch.WordTrace]
  refine ⟨124444951814004768782485379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82963301209336512521656919 124444951814004768782485379)
  ·
    refine ⟨186667427721007153173728069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124444951814004768782485379 186667427721007153173728069)
    ·
      refine ⟨35000142697688841220074013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186667427721007153173728069 35000142697688841220074013)
      ·
        refine ⟨13125053511633315457527755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35000142697688841220074013 13125053511633315457527755)
        ·
          refine ⟨19687580267449973186291633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13125053511633315457527755 19687580267449973186291633)
          ·
            refine ⟨14765685200587479889718725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19687580267449973186291633 14765685200587479889718725)
            ·
              refine ⟨2768565975110152479322261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14765685200587479889718725 2768565975110152479322261)
              ·
                refine ⟨129776530083288397468231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2768565975110152479322261 129776530083288397468231)
                ·
                  rfl

theorem cell22_3411975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 6].length) (baseStart_3411975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3411975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3411975 prefixEnd_3411975 := by exact prefixLift 3411975
  have htrace : WordTrace (prefixWord ++ tailWord_3411975) baseStart_3411975 baseEnd_3411975 := by
    simpa [prefixWord, tailWord_3411975, baseEnd_3411975] using wordTrace_append hprefix tailTrace_3411975
  have hstable : (prefixWord ++ tailWord_3411975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3411975).length < 2 ^ (prefixWord ++ tailWord_3411975).sum := by decide
  have hdescent : baseEnd_3411975 < baseStart_3411975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3411975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412003 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 7]
def baseStart_3412003 : Nat := 118140960795 + 3412003 * 2 ^ 59
def prefixEnd_3412003 : Nat := 4983230072969 + 3 ^ 40 * 3412003 * 2
def baseEnd_3412003 : Nat := 389332785240604279171331

theorem tailTrace_3412003 : CollatzResearch.WordTrace tailWord_3412003 prefixEnd_3412003 389332785240604279171331 := by
  unfold tailWord_3412003
  simp only [CollatzResearch.WordTrace]
  refine ⟨124445973057903329564504663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82963982038602219709669775 124445973057903329564504663)
  ·
    refine ⟨186668959586854994346756995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124445973057903329564504663 186668959586854994346756995)
    ·
      refine ⟨280003439380282491520135493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186668959586854994346756995 280003439380282491520135493)
      ·
        refine ⟨52500644883802967160025405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280003439380282491520135493 52500644883802967160025405)
        ·
          refine ⟨19687741831426112685009527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52500644883802967160025405 19687741831426112685009527)
          ·
            refine ⟨29531612747139169027514291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19687741831426112685009527 29531612747139169027514291)
            ·
              refine ⟨44297419120708753541271437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531612747139169027514291 44297419120708753541271437)
              ·
                refine ⟨16611532170265782577976789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44297419120708753541271437 16611532170265782577976789)
                ·
                  refine ⟨389332785240604279171331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16611532170265782577976789 389332785240604279171331)
                  ·
                    rfl

theorem cell22_3412003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_3412003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412003 prefixEnd_3412003 := by exact prefixLift 3412003
  have htrace : WordTrace (prefixWord ++ tailWord_3412003) baseStart_3412003 baseEnd_3412003 := by
    simpa [prefixWord, tailWord_3412003, baseEnd_3412003] using wordTrace_append hprefix tailTrace_3412003
  have hstable : (prefixWord ++ tailWord_3412003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412003).length < 2 ^ (prefixWord ++ tailWord_3412003).sum := by decide
  have hdescent : baseEnd_3412003 < baseStart_3412003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412054 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3412054 : Nat := 118140960795 + 3412054 * 2 ^ 59
def prefixEnd_3412054 : Nat := 4983230072969 + 3 ^ 40 * 3412054 * 2
def baseEnd_3412054 : Nat := 389338604688021901496279

theorem tailTrace_3412054 : CollatzResearch.WordTrace tailWord_3412054 prefixEnd_3412054 389338604688021901496279 := by
  unfold tailWord_3412054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777989573794910329663201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82965222120479043516407477 7777989573794910329663201)
  ·
    refine ⟨5833492180346182747247401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7777989573794910329663201 5833492180346182747247401)
    ·
      refine ⟨4375119135259637060435551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5833492180346182747247401 4375119135259637060435551)
      ·
        refine ⟨6562678702889455590653327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375119135259637060435551 6562678702889455590653327)
        ·
          refine ⟨9844018054334183385979991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562678702889455590653327 9844018054334183385979991)
          ·
            refine ⟨14766027081501275078969987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844018054334183385979991 14766027081501275078969987)
            ·
              refine ⟨22149040622251912618454981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766027081501275078969987 22149040622251912618454981)
              ·
                refine ⟨4152945116672233615960309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22149040622251912618454981 4152945116672233615960309)
                ·
                  refine ⟨389338604688021901496279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4152945116672233615960309 389338604688021901496279)
                  ·
                    rfl

theorem cell22_3412054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3412054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412054 prefixEnd_3412054 := by exact prefixLift 3412054
  have htrace : WordTrace (prefixWord ++ tailWord_3412054) baseStart_3412054 baseEnd_3412054 := by
    simpa [prefixWord, tailWord_3412054, baseEnd_3412054] using wordTrace_append hprefix tailTrace_3412054
  have hstable : (prefixWord ++ tailWord_3412054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412054).length < 2 ^ (prefixWord ++ tailWord_3412054).sum := by decide
  have hdescent : baseEnd_3412054 < baseStart_3412054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412080 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 1, 5]
def baseStart_3412080 : Nat := 118140960795 + 3412080 * 2 ^ 59
def prefixEnd_3412080 : Nat := 4983230072969 + 3 ^ 40 * 3412080 * 2
def baseEnd_3412080 : Nat := 1168024714395410303338757

theorem tailTrace_3412080 : CollatzResearch.WordTrace tailWord_3412080 prefixEnd_3412080 1168024714395410303338757 := by
  unfold tailWord_3412080
  simp only [CollatzResearch.WordTrace]
  refine ⟨62224390739312185857528847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82965854319082914476705129 62224390739312185857528847)
  ·
    refine ⟨93336586108968278786293271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62224390739312185857528847 93336586108968278786293271)
    ·
      refine ⟨140004879163452418179439907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93336586108968278786293271 140004879163452418179439907)
      ·
        refine ⟨210007318745178627269159861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140004879163452418179439907 210007318745178627269159861)
        ·
          refine ⟨19688186132360496306483737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210007318745178627269159861 19688186132360496306483737)
          ·
            refine ⟨14766139599270372229862803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19688186132360496306483737 14766139599270372229862803)
            ·
              refine ⟨22149209398905558344794205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766139599270372229862803 22149209398905558344794205)
              ·
                refine ⟨8305953524589584379297827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22149209398905558344794205 8305953524589584379297827)
                ·
                  refine ⟨12458930286884376568946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8305953524589584379297827 12458930286884376568946741)
                  ·
                    refine ⟨1168024714395410303338757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12458930286884376568946741 1168024714395410303338757)
                    ·
                      rfl

theorem cell22_3412080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_3412080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412080 prefixEnd_3412080 := by exact prefixLift 3412080
  have htrace : WordTrace (prefixWord ++ tailWord_3412080) baseStart_3412080 baseEnd_3412080 := by
    simpa [prefixWord, tailWord_3412080, baseEnd_3412080] using wordTrace_append hprefix tailTrace_3412080
  have hstable : (prefixWord ++ tailWord_3412080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412080).length < 2 ^ (prefixWord ++ tailWord_3412080).sum := by decide
  have hdescent : baseEnd_3412080 < baseStart_3412080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412189 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 5]
def baseStart_3412189 : Nat := 118140960795 + 3412189 * 2 ^ 59
def prefixEnd_3412189 : Nat := 4983230072969 + 3 ^ 40 * 3412189 * 2
def baseEnd_3412189 : Nat := 389354009107656784121141

theorem tailTrace_3412189 : CollatzResearch.WordTrace tailWord_3412189 prefixEnd_3412189 389354009107656784121141 := by
  unfold tailWord_3412189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124452757035229483330775621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82968504690152988887183747 124452757035229483330775621)
  ·
    refine ⟨23334891944105528124520429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124452757035229483330775621 23334891944105528124520429)
    ·
      refine ⟨8750584479039573046695161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23334891944105528124520429 8750584479039573046695161)
      ·
        refine ⟨6562938359279679785021371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8750584479039573046695161 6562938359279679785021371)
        ·
          refine ⟨9844407538919519677532057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6562938359279679785021371 9844407538919519677532057)
          ·
            refine ⟨7383305654189639758149043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9844407538919519677532057 7383305654189639758149043)
            ·
              refine ⟨11074958481284459637223565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383305654189639758149043 11074958481284459637223565)
              ·
                refine ⟨4153109430481672363958837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11074958481284459637223565 4153109430481672363958837)
                ·
                  refine ⟨389354009107656784121141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153109430481672363958837 389354009107656784121141)
                  ·
                    rfl

theorem cell22_3412189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_3412189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412189 prefixEnd_3412189 := by exact prefixLift 3412189
  have htrace : WordTrace (prefixWord ++ tailWord_3412189) baseStart_3412189 baseEnd_3412189 := by
    simpa [prefixWord, tailWord_3412189, baseEnd_3412189] using wordTrace_append hprefix tailTrace_3412189
  have hstable : (prefixWord ++ tailWord_3412189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412189).length < 2 ^ (prefixWord ++ tailWord_3412189).sum := by decide
  have hdescent : baseEnd_3412189 < baseStart_3412189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412202 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_3412202 : Nat := 118140960795 + 3412202 * 2 ^ 59
def prefixEnd_3412202 : Nat := 4983230072969 + 3 ^ 40 * 3412202 * 2
def baseEnd_3412202 : Nat := 1168066477488642651788383

theorem tailTrace_3412202 : CollatzResearch.WordTrace tailWord_3412202 prefixEnd_3412202 1168066477488642651788383 := by
  unfold tailWord_3412202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113307796045596637749715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82968820789454924367332573 31113307796045596637749715)
  ·
    refine ⟨46669961694068394956624573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31113307796045596637749715 46669961694068394956624573)
    ·
      refine ⟨17501235635275648108734215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46669961694068394956624573 17501235635275648108734215)
      ·
        refine ⟨26251853452913472163101323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17501235635275648108734215 26251853452913472163101323)
        ·
          refine ⟨39377780179370208244651985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26251853452913472163101323 39377780179370208244651985)
          ·
            refine ⟨29533335134527656183488989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39377780179370208244651985 29533335134527656183488989)
            ·
              refine ⟨11075000675447871068808371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29533335134527656183488989 11075000675447871068808371)
              ·
                refine ⟨16612501013171806603212557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075000675447871068808371 16612501013171806603212557)
                ·
                  refine ⟨6229687879939427476204709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16612501013171806603212557 6229687879939427476204709)
                  ·
                    refine ⟨1168066477488642651788383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229687879939427476204709 1168066477488642651788383)
                    ·
                      rfl

theorem cell22_3412202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_3412202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412202 prefixEnd_3412202 := by exact prefixLift 3412202
  have htrace : WordTrace (prefixWord ++ tailWord_3412202) baseStart_3412202 baseEnd_3412202 := by
    simpa [prefixWord, tailWord_3412202, baseEnd_3412202] using wordTrace_append hprefix tailTrace_3412202
  have hstable : (prefixWord ++ tailWord_3412202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412202).length < 2 ^ (prefixWord ++ tailWord_3412202).sum := by decide
  have hdescent : baseEnd_3412202 < baseStart_3412202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412264 : List Nat := [2, 1, 5, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3412264 : Nat := 118140960795 + 3412264 * 2 ^ 59
def prefixEnd_3412264 : Nat := 4983230072969 + 3 ^ 40 * 3412264 * 2
def baseEnd_3412264 : Nat := 1168087701355695156738193

theorem tailTrace_3412264 : CollatzResearch.WordTrace tailWord_3412264 prefixEnd_3412264 1168087701355695156738193 := by
  unfold tailWord_3412264
  simp only [CollatzResearch.WordTrace]
  refine ⟨62227746254978885569877923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82970328339971847426503897 62227746254978885569877923)
  ·
    refine ⟨93341619382468328354816885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62227746254978885569877923 93341619382468328354816885)
    ·
      refine ⟨8750776817106405783264083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93341619382468328354816885 8750776817106405783264083)
      ·
        refine ⟨13126165225659608674896125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8750776817106405783264083 13126165225659608674896125)
        ·
          refine ⟨4922311959622353253086047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13126165225659608674896125 4922311959622353253086047)
          ·
            refine ⟨7383467939433529879629071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4922311959622353253086047 7383467939433529879629071)
            ·
              refine ⟨11075201909150294819443607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383467939433529879629071 11075201909150294819443607)
              ·
                refine ⟨16612802863725442229165411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075201909150294819443607 16612802863725442229165411)
                ·
                  refine ⟨24919204295588163343748117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16612802863725442229165411 24919204295588163343748117)
                  ·
                    refine ⟨1168087701355695156738193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24919204295588163343748117 1168087701355695156738193)
                    ·
                      rfl

theorem cell22_3412264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3412264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412264 prefixEnd_3412264 := by exact prefixLift 3412264
  have htrace : WordTrace (prefixWord ++ tailWord_3412264) baseStart_3412264 baseEnd_3412264 := by
    simpa [prefixWord, tailWord_3412264, baseEnd_3412264] using wordTrace_append hprefix tailTrace_3412264
  have hstable : (prefixWord ++ tailWord_3412264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412264).length < 2 ^ (prefixWord ++ tailWord_3412264).sum := by decide
  have hdescent : baseEnd_3412264 < baseStart_3412264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412270 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 1, 4]
def baseStart_3412270 : Nat := 118140960795 + 3412270 * 2 ^ 59
def prefixEnd_3412270 : Nat := 4983230072969 + 3 ^ 40 * 3412270 * 2
def baseEnd_3412270 : Nat := 1168089755278313141088175

theorem tailTrace_3412270 : CollatzResearch.WordTrace tailWord_3412270 prefixEnd_3412270 1168089755278313141088175 := by
  unfold tailWord_3412270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15556963918492004270559283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82970474231957356109649509 15556963918492004270559283)
  ·
    refine ⟨23335445877738006405838925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15556963918492004270559283 23335445877738006405838925)
    ·
      refine ⟨8750792204151752402189597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23335445877738006405838925 8750792204151752402189597)
      ·
        refine ⟨3281547076556907150821099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8750792204151752402189597 3281547076556907150821099)
        ·
          refine ⟨4922320614835360726231649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3281547076556907150821099 4922320614835360726231649)
          ·
            refine ⟨3691740461126520544673737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922320614835360726231649 3691740461126520544673737)
            ·
              refine ⟨2768805345844890408505303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3691740461126520544673737 2768805345844890408505303)
              ·
                refine ⟨4153208018767335612757955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2768805345844890408505303 4153208018767335612757955)
                ·
                  refine ⟨6229812028151003419136933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153208018767335612757955 6229812028151003419136933)
                  ·
                    refine ⟨1168089755278313141088175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229812028151003419136933 1168089755278313141088175)
                    ·
                      rfl

theorem cell22_3412270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_3412270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412270 prefixEnd_3412270 := by exact prefixLift 3412270
  have htrace : WordTrace (prefixWord ++ tailWord_3412270) baseStart_3412270 baseEnd_3412270 := by
    simpa [prefixWord, tailWord_3412270, baseEnd_3412270] using wordTrace_append hprefix tailTrace_3412270
  have hstable : (prefixWord ++ tailWord_3412270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412270).length < 2 ^ (prefixWord ++ tailWord_3412270).sum := by decide
  have hdescent : baseEnd_3412270 < baseStart_3412270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412328 : List Nat := [2, 1, 4, 2, 2, 1, 3, 3, 1, 3]
def baseStart_3412328 : Nat := 118140960795 + 3412328 * 2 ^ 59
def prefixEnd_3412328 : Nat := 4983230072969 + 3 ^ 40 * 3412328 * 2
def baseEnd_3412328 : Nat := 1168109609863620323137997

theorem tailTrace_3412328 : CollatzResearch.WordTrace tailWord_3412328 prefixEnd_3412328 1168109609863620323137997 := by
  unfold tailWord_3412328
  simp only [CollatzResearch.WordTrace]
  refine ⟨62228913390862955035042819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82971884521150606713390425 62228913390862955035042819)
  ·
    refine ⟨93343370086294432552564229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62228913390862955035042819 93343370086294432552564229)
    ·
      refine ⟨17501881891180206103605793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93343370086294432552564229 17501881891180206103605793)
      ·
        refine ⟨13126411418385154577704345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17501881891180206103605793 13126411418385154577704345)
        ·
          refine ⟨9844808563788865933278259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13126411418385154577704345 9844808563788865933278259)
          ·
            refine ⟨14767212845683298899917389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9844808563788865933278259 14767212845683298899917389)
            ·
              refine ⟨5537704817131237087469021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14767212845683298899917389 5537704817131237087469021)
              ·
                refine ⟨2076639306424213907800883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5537704817131237087469021 2076639306424213907800883)
                ·
                  refine ⟨3114958959636320861701325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076639306424213907800883 3114958959636320861701325)
                  ·
                    refine ⟨1168109609863620323137997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3114958959636320861701325 1168109609863620323137997)
                    ·
                      rfl

theorem cell22_3412328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_3412328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412328 prefixEnd_3412328 := by exact prefixLift 3412328
  have htrace : WordTrace (prefixWord ++ tailWord_3412328) baseStart_3412328 baseEnd_3412328 := by
    simpa [prefixWord, tailWord_3412328, baseEnd_3412328] using wordTrace_append hprefix tailTrace_3412328
  have hstable : (prefixWord ++ tailWord_3412328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412328).length < 2 ^ (prefixWord ++ tailWord_3412328).sum := by decide
  have hdescent : baseEnd_3412328 < baseStart_3412328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412337 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 5, 4]
def baseStart_3412337 : Nat := 118140960795 + 3412337 * 2 ^ 59
def prefixEnd_3412337 : Nat := 4983230072969 + 3 ^ 40 * 3412337 * 2
def baseEnd_3412337 : Nat := 1168112690747547299662969

theorem tailTrace_3412337 : CollatzResearch.WordTrace tailWord_3412337 prefixEnd_3412337 1168112690747547299662969 := by
  unfold tailWord_3412337
  simp only [CollatzResearch.WordTrace]
  refine ⟨124458155038693304607163265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82972103359128869738108843 124458155038693304607163265)
  ·
    refine ⟨93343616279019978455372449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124458155038693304607163265 93343616279019978455372449)
    ·
      refine ⟨70007712209264983841529337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93343616279019978455372449 70007712209264983841529337)
      ·
        refine ⟨52505784156948737881147003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70007712209264983841529337 52505784156948737881147003)
        ·
          refine ⟨78758676235423106821720505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52505784156948737881147003 78758676235423106821720505)
          ·
            refine ⟨59069007176567330116290379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78758676235423106821720505 59069007176567330116290379)
            ·
              refine ⟨88603510764850995174435569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59069007176567330116290379 88603510764850995174435569)
              ·
                refine ⟨66452633073638246380826677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88603510764850995174435569 66452633073638246380826677)
                ·
                  refine ⟨6229934350653585598202501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66452633073638246380826677 6229934350653585598202501)
                  ·
                    refine ⟨1168112690747547299662969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6229934350653585598202501 1168112690747547299662969)
                    ·
                      rfl

theorem cell22_3412337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_3412337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412337 prefixEnd_3412337 := by exact prefixLift 3412337
  have htrace : WordTrace (prefixWord ++ tailWord_3412337) baseStart_3412337 baseEnd_3412337 := by
    simpa [prefixWord, tailWord_3412337, baseEnd_3412337] using wordTrace_append hprefix tailTrace_3412337
  have hstable : (prefixWord ++ tailWord_3412337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412337).length < 2 ^ (prefixWord ++ tailWord_3412337).sum := by decide
  have hdescent : baseEnd_3412337 < baseStart_3412337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412384 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 1, 5]
def baseStart_3412384 : Nat := 118140960795 + 3412384 * 2 ^ 59
def prefixEnd_3412384 : Nat := 4983230072969 + 3 ^ 40 * 3412384 * 2
def baseEnd_3412384 : Nat := 1168128779808054843737825

theorem tailTrace_3412384 : CollatzResearch.WordTrace tailWord_3412384 prefixEnd_3412384 1168128779808054843737825 := by
  unfold tailWord_3412384
  simp only [CollatzResearch.WordTrace]
  refine ⟨62229934634761515817062103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82973246179682021089416137 62229934634761515817062103)
  ·
    refine ⟨93344901952142273725593155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62229934634761515817062103 93344901952142273725593155)
    ·
      refine ⟨140017352928213410588389733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93344901952142273725593155 140017352928213410588389733)
      ·
        refine ⟨26253253674040014485323075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140017352928213410588389733 26253253674040014485323075)
        ·
          refine ⟨39379880511060021727984613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26253253674040014485323075 39379880511060021727984613)
          ·
            refine ⟨7383727595823754073997115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39379880511060021727984613 7383727595823754073997115)
            ·
              refine ⟨11075591393735631110995673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383727595823754073997115 11075591393735631110995673)
              ·
                refine ⟨8306693545301723333246755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11075591393735631110995673 8306693545301723333246755)
                ·
                  refine ⟨12460040317952584999870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8306693545301723333246755 12460040317952584999870133)
                  ·
                    refine ⟨1168128779808054843737825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12460040317952584999870133 1168128779808054843737825)
                    ·
                      rfl

theorem cell22_3412384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_3412384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412384 prefixEnd_3412384 := by exact prefixLift 3412384
  have htrace : WordTrace (prefixWord ++ tailWord_3412384) baseStart_3412384 baseEnd_3412384 := by
    simpa [prefixWord, tailWord_3412384, baseEnd_3412384] using wordTrace_append hprefix tailTrace_3412384
  have hstable : (prefixWord ++ tailWord_3412384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412384).length < 2 ^ (prefixWord ++ tailWord_3412384).sum := by decide
  have hdescent : baseEnd_3412384 < baseStart_3412384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412386 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3412386 : Nat := 118140960795 + 3412386 * 2 ^ 59
def prefixEnd_3412386 : Nat := 4983230072969 + 3 ^ 40 * 3412386 * 2
def baseEnd_3412386 : Nat := 389376488149642501729273

theorem tailTrace_3412386 : CollatzResearch.WordTrace tailWord_3412386 prefixEnd_3412386 389376488149642501729273 := by
  unfold tailWord_3412386
  simp only [CollatzResearch.WordTrace]
  refine ⟨31114985553878946493924253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82973294810343857317131341 31114985553878946493924253)
  ·
    refine ⟨11668119582704604935221595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31114985553878946493924253 11668119582704604935221595)
    ·
      refine ⟨17502179374056907402832393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668119582704604935221595 17502179374056907402832393)
      ·
        refine ⟨13126634530542680552124295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17502179374056907402832393 13126634530542680552124295)
        ·
          refine ⟨19689951795814020828186443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126634530542680552124295 19689951795814020828186443)
          ·
            refine ⟨29534927693721031242279665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19689951795814020828186443 29534927693721031242279665)
            ·
              refine ⟨22151195770290773431709749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29534927693721031242279665 22151195770290773431709749)
              ·
                refine ⟨2076674603464760009222789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22151195770290773431709749 2076674603464760009222789)
                ·
                  refine ⟨389376488149642501729273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076674603464760009222789 389376488149642501729273)
                  ·
                    rfl

theorem cell22_3412386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3412386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412386 prefixEnd_3412386 := by exact prefixLift 3412386
  have htrace : WordTrace (prefixWord ++ tailWord_3412386) baseStart_3412386 baseEnd_3412386 := by
    simpa [prefixWord, tailWord_3412386, baseEnd_3412386] using wordTrace_append hprefix tailTrace_3412386
  have hstable : (prefixWord ++ tailWord_3412386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412386).length < 2 ^ (prefixWord ++ tailWord_3412386).sum := by decide
  have hdescent : baseEnd_3412386 < baseStart_3412386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412401 : List Nat := [1, 2, 2, 4, 1, 2, 1, 4, 2, 3]
def baseStart_3412401 : Nat := 118140960795 + 3412401 * 2 ^ 59
def prefixEnd_3412401 : Nat := 4983230072969 + 3 ^ 40 * 3412401 * 2
def baseEnd_3412401 : Nat := 1168134599255472466062773

theorem tailTrace_3412401 : CollatzResearch.WordTrace tailWord_3412401 prefixEnd_3412401 1168134599255472466062773 := by
  unfold tailWord_3412401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124460489310461443537493057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82973659540307629024995371 124460489310461443537493057)
  ·
    refine ⟨93345366982846082653119793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124460489310461443537493057 93345366982846082653119793)
    ·
      refine ⟨70009025237134561989839845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93345366982846082653119793 70009025237134561989839845)
      ·
        refine ⟨13126692231962730373094971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70009025237134561989839845 13126692231962730373094971)
        ·
          refine ⟨19690038347944095559642457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126692231962730373094971 19690038347944095559642457)
          ·
            refine ⟨14767528760958071669731843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19690038347944095559642457 14767528760958071669731843)
            ·
              refine ⟨22151293141437107504597765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767528760958071669731843 22151293141437107504597765)
              ·
                refine ⟨4153367464019457657112081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22151293141437107504597765 4153367464019457657112081)
                ·
                  refine ⟨3115025598014593242834061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153367464019457657112081 3115025598014593242834061)
                  ·
                    refine ⟨1168134599255472466062773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115025598014593242834061 1168134599255472466062773)
                    ·
                      rfl

theorem cell22_3412401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_3412401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412401 prefixEnd_3412401 := by exact prefixLift 3412401
  have htrace : WordTrace (prefixWord ++ tailWord_3412401) baseStart_3412401 baseEnd_3412401 := by
    simpa [prefixWord, tailWord_3412401, baseEnd_3412401] using wordTrace_append hprefix tailTrace_3412401
  have hstable : (prefixWord ++ tailWord_3412401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412401).length < 2 ^ (prefixWord ++ tailWord_3412401).sum := by decide
  have hdescent : baseEnd_3412401 < baseStart_3412401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412414 : List Nat := [4, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3412414 : Nat := 118140960795 + 3412414 * 2 ^ 59
def prefixEnd_3412414 : Nat := 4983230072969 + 3 ^ 40 * 3412414 * 2
def baseEnd_3412414 : Nat := 129793227713460529498637

theorem tailTrace_3412414 : CollatzResearch.WordTrace tailWord_3412414 prefixEnd_3412414 129793227713460529498637 := by
  unfold tailWord_3412414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557620432426793344714537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82973975639609564505144197 15557620432426793344714537)
  ·
    refine ⟨11668215324320095008535903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557620432426793344714537 11668215324320095008535903)
    ·
      refine ⟨17502322986480142512803855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668215324320095008535903 17502322986480142512803855)
      ·
        refine ⟨26253484479720213769205783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17502322986480142512803855 26253484479720213769205783)
        ·
          refine ⟨39380226719580320653808675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26253484479720213769205783 39380226719580320653808675)
          ·
            refine ⟨59070340079370480980713013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39380226719580320653808675 59070340079370480980713013)
            ·
              refine ⟨5537844382440982591941845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59070340079370480980713013 5537844382440982591941845)
              ·
                refine ⟨129793227713460529498637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5537844382440982591941845 129793227713460529498637)
                ·
                  rfl

theorem cell22_3412414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3412414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412414 prefixEnd_3412414 := by exact prefixLift 3412414
  have htrace : WordTrace (prefixWord ++ tailWord_3412414) baseStart_3412414 baseEnd_3412414 := by
    simpa [prefixWord, tailWord_3412414, baseEnd_3412414] using wordTrace_append hprefix tailTrace_3412414
  have hstable : (prefixWord ++ tailWord_3412414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412414).length < 2 ^ (prefixWord ++ tailWord_3412414).sum := by decide
  have hdescent : baseEnd_3412414 < baseStart_3412414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412427 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 4, 6]
def baseStart_3412427 : Nat := 118140960795 + 3412427 * 2 ^ 59
def prefixEnd_3412427 : Nat := 4983230072969 + 3 ^ 40 * 3412427 * 2
def baseEnd_3412427 : Nat := 1168143499586817064912693

theorem tailTrace_3412427 : CollatzResearch.WordTrace tailWord_3412427 prefixEnd_3412427 1168143499586817064912693 := by
  unfold tailWord_3412427
  simp only [CollatzResearch.WordTrace]
  refine ⟨124461437608367249977939535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82974291738911499985293023 124461437608367249977939535)
  ·
    refine ⟨186692156412550874966909303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124461437608367249977939535 186692156412550874966909303)
    ·
      refine ⟨280038234618826312450363955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186692156412550874966909303 280038234618826312450363955)
      ·
        refine ⟨420057351928239468675545933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280038234618826312450363955 420057351928239468675545933)
        ·
          refine ⟨157521506973089800753329725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420057351928239468675545933 157521506973089800753329725)
          ·
            refine ⟨59070565114908675282498647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157521506973089800753329725 59070565114908675282498647)
            ·
              refine ⟨88605847672363012923747971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59070565114908675282498647 88605847672363012923747971)
              ·
                refine ⟨132908771508544519385621957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88605847672363012923747971 132908771508544519385621957)
                ·
                  refine ⟨24920394657852097384804117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 132908771508544519385621957 24920394657852097384804117)
                  ·
                    refine ⟨1168143499586817064912693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24920394657852097384804117 1168143499586817064912693)
                    ·
                      rfl

theorem cell22_3412427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 6].length) (baseStart_3412427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412427 prefixEnd_3412427 := by exact prefixLift 3412427
  have htrace : WordTrace (prefixWord ++ tailWord_3412427) baseStart_3412427 baseEnd_3412427 := by
    simpa [prefixWord, tailWord_3412427, baseEnd_3412427] using wordTrace_append hprefix tailTrace_3412427
  have hstable : (prefixWord ++ tailWord_3412427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412427).length < 2 ^ (prefixWord ++ tailWord_3412427).sum := by decide
  have hdescent : baseEnd_3412427 < baseStart_3412427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412493 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3412493 : Nat := 118140960795 + 3412493 * 2 ^ 59
def prefixEnd_3412493 : Nat := 4983230072969 + 3 ^ 40 * 3412493 * 2
def baseEnd_3412493 : Nat := 389388697578538297587497

theorem tailTrace_3412493 : CollatzResearch.WordTrace tailWord_3412493 prefixEnd_3412493 389388697578538297587497 := by
  unfold tailWord_3412493
  simp only [CollatzResearch.WordTrace]
  refine ⟨124463844826128143249842133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82975896550752095499894755 124463844826128143249842133)
  ·
    refine ⟨2917121363112378357418175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 124463844826128143249842133 2917121363112378357418175)
    ·
      refine ⟨4375682044668567536127263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917121363112378357418175 4375682044668567536127263)
      ·
        refine ⟨6563523067002851304190895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375682044668567536127263 6563523067002851304190895)
        ·
          refine ⟨9845284600504276956286343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563523067002851304190895 9845284600504276956286343)
          ·
            refine ⟨14767926900756415434429515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845284600504276956286343 14767926900756415434429515)
            ·
              refine ⟨22151890351134623151644273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14767926900756415434429515 22151890351134623151644273)
              ·
                refine ⟨16613917763350967363733205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22151890351134623151644273 16613917763350967363733205)
                ·
                  refine ⟨389388697578538297587497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16613917763350967363733205 389388697578538297587497)
                  ·
                    rfl

theorem cell22_3412493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3412493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412493 prefixEnd_3412493 := by exact prefixLift 3412493
  have htrace : WordTrace (prefixWord ++ tailWord_3412493) baseStart_3412493 baseEnd_3412493 := by
    simpa [prefixWord, tailWord_3412493, baseEnd_3412493] using wordTrace_append hprefix tailTrace_3412493
  have hstable : (prefixWord ++ tailWord_3412493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412493).length < 2 ^ (prefixWord ++ tailWord_3412493).sum := by decide
  have hdescent : baseEnd_3412493 < baseStart_3412493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412506 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_3412506 : Nat := 118140960795 + 3412506 * 2 ^ 59
def prefixEnd_3412506 : Nat := 4983230072969 + 3 ^ 40 * 3412506 * 2
def baseEnd_3412506 : Nat := 1168170542901287192187451

theorem tailTrace_3412506 : CollatzResearch.WordTrace tailWord_3412506 prefixEnd_3412506 1168170542901287192187451 := by
  unfold tailWord_3412506
  simp only [CollatzResearch.WordTrace]
  refine ⟨31116079743770261617516343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82976212650054030980043581 31116079743770261617516343)
  ·
    refine ⟨46674119615655392426274515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31116079743770261617516343 46674119615655392426274515)
    ·
      refine ⟨70011179423483088639411773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46674119615655392426274515 70011179423483088639411773)
      ·
        refine ⟨26254192283806158239779415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70011179423483088639411773 26254192283806158239779415)
        ·
          refine ⟨39381288425709237359669123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254192283806158239779415 39381288425709237359669123)
          ·
            refine ⟨59071932638563856039503685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39381288425709237359669123 59071932638563856039503685)
            ·
              refine ⟨11075987369730723007406941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59071932638563856039503685 11075987369730723007406941)
              ·
                refine ⟨4153495263649021127777603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11075987369730723007406941 4153495263649021127777603)
                ·
                  refine ⟨6230242895473531691666405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4153495263649021127777603 6230242895473531691666405)
                  ·
                    refine ⟨1168170542901287192187451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6230242895473531691666405 1168170542901287192187451)
                    ·
                      rfl

theorem cell22_3412506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_3412506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412506 prefixEnd_3412506 := by exact prefixLift 3412506
  have htrace : WordTrace (prefixWord ++ tailWord_3412506) baseStart_3412506 baseEnd_3412506 := by
    simpa [prefixWord, tailWord_3412506, baseEnd_3412506] using wordTrace_append hprefix tailTrace_3412506
  have hstable : (prefixWord ++ tailWord_3412506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412506).length < 2 ^ (prefixWord ++ tailWord_3412506).sum := by decide
  have hdescent : baseEnd_3412506 < baseStart_3412506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412549 : List Nat := [1, 3, 1, 1, 1, 5, 2, 8]
def baseStart_3412549 : Nat := 118140960795 + 3412549 * 2 ^ 59
def prefixEnd_3412549 : Nat := 4983230072969 + 3 ^ 40 * 3412549 * 2
def baseEnd_3412549 : Nat := 129798362520005490373591

theorem tailTrace_3412549 : CollatzResearch.WordTrace tailWord_3412549 prefixEnd_3412549 129798362520005490373591 := by
  unfold tailWord_3412549
  simp only [CollatzResearch.WordTrace]
  refine ⟨124465887313925264813880701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82977258209283509875920467 124465887313925264813880701)
  ·
    refine ⟨46674707742721974305205263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124465887313925264813880701 46674707742721974305205263)
    ·
      refine ⟨70012061614082961457807895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46674707742721974305205263 70012061614082961457807895)
      ·
        refine ⟨105018092421124442186711843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70012061614082961457807895 105018092421124442186711843)
        ·
          refine ⟨157527138631686663280067765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105018092421124442186711843 157527138631686663280067765)
          ·
            refine ⟨14768169246720624682506353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157527138631686663280067765 14768169246720624682506353)
            ·
              refine ⟨11076126935040468511879765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14768169246720624682506353 11076126935040468511879765)
              ·
                refine ⟨129798362520005490373591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11076126935040468511879765 129798362520005490373591)
                ·
                  rfl

theorem cell22_3412549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 8].length) (baseStart_3412549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412549 prefixEnd_3412549 := by exact prefixLift 3412549
  have htrace : WordTrace (prefixWord ++ tailWord_3412549) baseStart_3412549 baseEnd_3412549 := by
    simpa [prefixWord, tailWord_3412549, baseEnd_3412549] using wordTrace_append hprefix tailTrace_3412549
  have hstable : (prefixWord ++ tailWord_3412549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412549).length < 2 ^ (prefixWord ++ tailWord_3412549).sum := by decide
  have hdescent : baseEnd_3412549 < baseStart_3412549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412551 : List Nat := [1, 1, 4, 1, 4, 1, 1, 3, 2, 4]
def baseStart_3412551 : Nat := 118140960795 + 3412551 * 2 ^ 59
def prefixEnd_3412551 : Nat := 4983230072969 + 3 ^ 40 * 3412551 * 2
def baseEnd_3412551 : Nat := 1168185947320922074812313

theorem tailTrace_3412551 : CollatzResearch.WordTrace tailWord_3412551 prefixEnd_3412551 1168185947320922074812313 := by
  unfold tailWord_3412551
  simp only [CollatzResearch.WordTrace]
  refine ⟨124465960259918019155453507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82977306839945346103635671 124465960259918019155453507)
  ·
    refine ⟨186698940389877028733180261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124465960259918019155453507 186698940389877028733180261)
    ·
      refine ⟨35006051323101942887471299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186698940389877028733180261 35006051323101942887471299)
      ·
        refine ⟨52509076984652914331206949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35006051323101942887471299 52509076984652914331206949)
        ·
          refine ⟨9845451934622421437101303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52509076984652914331206949 9845451934622421437101303)
          ·
            refine ⟨14768177901933632155651955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9845451934622421437101303 14768177901933632155651955)
            ·
              refine ⟨22152266852900448233477933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14768177901933632155651955 22152266852900448233477933)
              ·
                refine ⟨8307100069837668087554225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22152266852900448233477933 8307100069837668087554225)
                ·
                  refine ⟨6230325052378251065665669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8307100069837668087554225 6230325052378251065665669)
                  ·
                    refine ⟨1168185947320922074812313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6230325052378251065665669 1168185947320922074812313)
                    ·
                      rfl

theorem cell22_3412551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_3412551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412551 prefixEnd_3412551 := by exact prefixLift 3412551
  have htrace : WordTrace (prefixWord ++ tailWord_3412551) baseStart_3412551 baseEnd_3412551 := by
    simpa [prefixWord, tailWord_3412551, baseEnd_3412551] using wordTrace_append hprefix tailTrace_3412551
  have hstable : (prefixWord ++ tailWord_3412551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412551).length < 2 ^ (prefixWord ++ tailWord_3412551).sum := by decide
  have hdescent : baseEnd_3412551 < baseStart_3412551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412566 : List Nat := [5, 2, 2, 13]
def baseStart_3412566 : Nat := 118140960795 + 3412566 * 2 ^ 59
def prefixEnd_3412566 : Nat := 4983230072969 + 3 ^ 40 * 3412566 * 2
def baseEnd_3412566 : Nat := 1602456902781161914523

theorem tailTrace_3412566 : CollatzResearch.WordTrace tailWord_3412566 prefixEnd_3412566 1602456902781161914523 := by
  unfold tailWord_3412566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7779156709678979794828097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82977671569909117811499701 7779156709678979794828097)
  ·
    refine ⟨5834367532259234846121073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7779156709678979794828097 5834367532259234846121073)
    ·
      refine ⟨4375775649194426134590805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834367532259234846121073 4375775649194426134590805)
      ·
        refine ⟨1602456902781161914523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4375775649194426134590805 1602456902781161914523)
        ·
          rfl

theorem cell22_3412566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 13].length) (baseStart_3412566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412566 prefixEnd_3412566 := by exact prefixLift 3412566
  have htrace : WordTrace (prefixWord ++ tailWord_3412566) baseStart_3412566 baseEnd_3412566 := by
    simpa [prefixWord, tailWord_3412566, baseEnd_3412566] using wordTrace_append hprefix tailTrace_3412566
  have hstable : (prefixWord ++ tailWord_3412566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412566).length < 2 ^ (prefixWord ++ tailWord_3412566).sum := by decide
  have hdescent : baseEnd_3412566 < baseStart_3412566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412572 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 4]
def baseStart_3412572 : Nat := 118140960795 + 3412572 * 2 ^ 59
def prefixEnd_3412572 : Nat := 4983230072969 + 3 ^ 40 * 3412572 * 2
def baseEnd_3412572 : Nat := 389397712016695006679083

theorem tailTrace_3412572 : CollatzResearch.WordTrace tailWord_3412572 prefixEnd_3412572 389397712016695006679083 := by
  unfold tailWord_3412572
  simp only [CollatzResearch.WordTrace]
  refine ⟨62233363096420969870983985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82977817461894626494645313 62233363096420969870983985)
  ·
    refine ⟨46675022322315727403237989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62233363096420969870983985 46675022322315727403237989)
    ·
      refine ⟨8751566685434198888107123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46675022322315727403237989 8751566685434198888107123)
      ·
        refine ⟨13127350028151298332160685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751566685434198888107123 13127350028151298332160685)
        ·
          refine ⟨4922756260556736874560257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13127350028151298332160685 4922756260556736874560257)
          ·
            refine ⟨3692067195417552655920193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922756260556736874560257 3692067195417552655920193)
            ·
              refine ⟨2769050396563164491940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692067195417552655920193 2769050396563164491940145)
              ·
                refine ⟨2076787797422373368955109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769050396563164491940145 2076787797422373368955109)
                ·
                  refine ⟨389397712016695006679083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076787797422373368955109 389397712016695006679083)
                  ·
                    rfl

theorem cell22_3412572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_3412572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412572 prefixEnd_3412572 := by exact prefixLift 3412572
  have htrace : WordTrace (prefixWord ++ tailWord_3412572) baseStart_3412572 baseEnd_3412572 := by
    simpa [prefixWord, tailWord_3412572, baseEnd_3412572] using wordTrace_append hprefix tailTrace_3412572
  have hstable : (prefixWord ++ tailWord_3412572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412572).length < 2 ^ (prefixWord ++ tailWord_3412572).sum := by decide
  have hdescent : baseEnd_3412572 < baseStart_3412572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412579 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 8]
def baseStart_3412579 : Nat := 118140960795 + 3412579 * 2 ^ 59
def prefixEnd_3412579 : Nat := 4983230072969 + 3 ^ 40 * 3412579 * 2
def baseEnd_3412579 : Nat := 1168195532293139335112227

theorem tailTrace_3412579 : CollatzResearch.WordTrace tailWord_3412579 prefixEnd_3412579 1168195532293139335112227 := by
  unfold tailWord_3412579
  simp only [CollatzResearch.WordTrace]
  refine ⟨124466981503816579937472791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82977987669211053291648527 124466981503816579937472791)
  ·
    refine ⟨186700472255724869906209187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124466981503816579937472791 186700472255724869906209187)
    ·
      refine ⟨280050708383587304859313781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186700472255724869906209187 280050708383587304859313781)
      ·
        refine ⟨26254753910961309830560667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280050708383587304859313781 26254753910961309830560667)
        ·
          refine ⟨39382130866441964745841001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26254753910961309830560667 39382130866441964745841001)
          ·
            refine ⟨29536598149831473559380751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39382130866441964745841001 29536598149831473559380751)
            ·
              refine ⟨44304897224747210339071127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29536598149831473559380751 44304897224747210339071127)
              ·
                refine ⟨66457345837120815508606691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44304897224747210339071127 66457345837120815508606691)
                ·
                  refine ⟨99686018755681223262910037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66457345837120815508606691 99686018755681223262910037)
                  ·
                    refine ⟨1168195532293139335112227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99686018755681223262910037 1168195532293139335112227)
                    ·
                      rfl

theorem cell22_3412579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 8].length) (baseStart_3412579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412579 prefixEnd_3412579 := by exact prefixLift 3412579
  have htrace : WordTrace (prefixWord ++ tailWord_3412579) baseStart_3412579 baseEnd_3412579 := by
    simpa [prefixWord, tailWord_3412579, baseEnd_3412579] using wordTrace_append hprefix tailTrace_3412579
  have hstable : (prefixWord ++ tailWord_3412579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412579).length < 2 ^ (prefixWord ++ tailWord_3412579).sum := by decide
  have hdescent : baseEnd_3412579 < baseStart_3412579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412615 : List Nat := [1, 1, 4, 2, 1, 2, 4, 3, 1, 3]
def baseStart_3412615 : Nat := 118140960795 + 3412615 * 2 ^ 59
def prefixEnd_3412615 : Nat := 4983230072969 + 3 ^ 40 * 3412615 * 2
def baseEnd_3412615 : Nat := 1168207855828847241212117

theorem tailTrace_3412615 : CollatzResearch.WordTrace tailWord_3412615 prefixEnd_3412615 1168207855828847241212117 := by
  unfold tailWord_3412615
  simp only [CollatzResearch.WordTrace]
  refine ⟨124468294531686158085783299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82978863021124105390522199 124468294531686158085783299)
  ·
    refine ⟨186702441797529237128674949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124468294531686158085783299 186702441797529237128674949)
    ·
      refine ⟨35006707837036731961626553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186702441797529237128674949 35006707837036731961626553)
      ·
        refine ⟨26255030877777548971219915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35006707837036731961626553 26255030877777548971219915)
        ·
          refine ⟨39382546316666323456829873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26255030877777548971219915 39382546316666323456829873)
          ·
            refine ⟨29536909737499742592622405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39382546316666323456829873 29536909737499742592622405)
            ·
              refine ⟨5538170575781201736116701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29536909737499742592622405 5538170575781201736116701)
              ·
                refine ⟨2076813965917950651043763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5538170575781201736116701 2076813965917950651043763)
                ·
                  refine ⟨3115220948876925976565645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076813965917950651043763 3115220948876925976565645)
                  ·
                    refine ⟨1168207855828847241212117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115220948876925976565645 1168207855828847241212117)
                    ·
                      rfl

theorem cell22_3412615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_3412615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412615 prefixEnd_3412615 := by exact prefixLift 3412615
  have htrace : WordTrace (prefixWord ++ tailWord_3412615) baseStart_3412615 baseEnd_3412615 := by
    simpa [prefixWord, tailWord_3412615, baseEnd_3412615] using wordTrace_append hprefix tailTrace_3412615
  have hstable : (prefixWord ++ tailWord_3412615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412615).length < 2 ^ (prefixWord ++ tailWord_3412615).sum := by decide
  have hdescent : baseEnd_3412615 < baseStart_3412615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412628 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 7]
def baseStart_3412628 : Nat := 118140960795 + 3412628 * 2 ^ 59
def prefixEnd_3412628 : Nat := 4983230072969 + 3 ^ 40 * 3412628 * 2
def baseEnd_3412628 : Nat := 389404101998173180212359

theorem tailTrace_3412628 : CollatzResearch.WordTrace tailWord_3412628 prefixEnd_3412628 389404101998173180212359 := by
  unfold tailWord_3412628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62234384340319530653003269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82979179120426040870671025 62234384340319530653003269)
  ·
    refine ⟨11668947063809911997438113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62234384340319530653003269 11668947063809911997438113)
    ·
      refine ⟨8751710297857433998078585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11668947063809911997438113 8751710297857433998078585)
      ·
        refine ⟨6563782723393075498558939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8751710297857433998078585 6563782723393075498558939)
        ·
          refine ⟨9845674085089613247838409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563782723393075498558939 9845674085089613247838409)
          ·
            refine ⟨7384255563817209935878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845674085089613247838409 7384255563817209935878807)
            ·
              refine ⟨11076383345725814903818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384255563817209935878807 11076383345725814903818211)
              ·
                refine ⟨16614575018588722355727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11076383345725814903818211 16614575018588722355727317)
                ·
                  refine ⟨389404101998173180212359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16614575018588722355727317 389404101998173180212359)
                  ·
                    rfl

theorem cell22_3412628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_3412628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412628 prefixEnd_3412628 := by exact prefixLift 3412628
  have htrace : WordTrace (prefixWord ++ tailWord_3412628) baseStart_3412628 baseEnd_3412628 := by
    simpa [prefixWord, tailWord_3412628, baseEnd_3412628] using wordTrace_append hprefix tailTrace_3412628
  have hstable : (prefixWord ++ tailWord_3412628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412628).length < 2 ^ (prefixWord ++ tailWord_3412628).sum := by decide
  have hdescent : baseEnd_3412628 < baseStart_3412628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412690 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_3412690 : Nat := 118140960795 + 3412690 * 2 ^ 59
def prefixEnd_3412690 : Nat := 4983230072969 + 3 ^ 40 * 3412690 * 2
def baseEnd_3412690 : Nat := 389411176620524015195629

theorem tailTrace_3412690 : CollatzResearch.WordTrace tailWord_3412690 prefixEnd_3412690 389411176620524015195629 := by
  unfold tailWord_3412690
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117757501603611473690881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82980686670942963929842349 31117757501603611473690881)
  ·
    refine ⟨23338318126202708605268161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31117757501603611473690881 23338318126202708605268161)
    ·
      refine ⟨17503738594652031453951121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23338318126202708605268161 17503738594652031453951121)
      ·
        refine ⟨13127803945989023590463341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17503738594652031453951121 13127803945989023590463341)
        ·
          refine ⟨4922926479745883846423753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13127803945989023590463341 4922926479745883846423753)
          ·
            refine ⟨3692194859809412884817815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4922926479745883846423753 3692194859809412884817815)
            ·
              refine ⟨5538292289714119327226723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692194859809412884817815 5538292289714119327226723)
              ·
                refine ⟨8307438434571178990840085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538292289714119327226723 8307438434571178990840085)
                ·
                  refine ⟨389411176620524015195629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8307438434571178990840085 389411176620524015195629)
                  ·
                    rfl

theorem cell22_3412690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_3412690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412690 prefixEnd_3412690 := by exact prefixLift 3412690
  have htrace : WordTrace (prefixWord ++ tailWord_3412690) baseStart_3412690 baseEnd_3412690 := by
    simpa [prefixWord, tailWord_3412690, baseEnd_3412690] using wordTrace_append hprefix tailTrace_3412690
  have hstable : (prefixWord ++ tailWord_3412690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412690).length < 2 ^ (prefixWord ++ tailWord_3412690).sum := by decide
  have hdescent : baseEnd_3412690 < baseStart_3412690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412705 : List Nat := [1, 2, 3, 1, 4, 2, 1, 3, 2, 3]
def baseStart_3412705 : Nat := 118140960795 + 3412705 * 2 ^ 59
def prefixEnd_3412705 : Nat := 4983230072969 + 3 ^ 40 * 3412705 * 2
def baseEnd_3412705 : Nat := 1168238664668117006461841

theorem tailTrace_3412705 : CollatzResearch.WordTrace tailWord_3412705 prefixEnd_3412705 1168238664668117006461841 := by
  unfold tailWord_3412705
  simp only [CollatzResearch.WordTrace]
  refine ⟨124471577101360103456559569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82981051400906735637706379 124471577101360103456559569)
  ·
    refine ⟨93353682826020077592419677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124471577101360103456559569 93353682826020077592419677)
    ·
      refine ⟨35007631059757529097157379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93353682826020077592419677 35007631059757529097157379)
      ·
        refine ⟨52511446589636293645736069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35007631059757529097157379 52511446589636293645736069)
        ·
          refine ⟨9845896235556805058575513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52511446589636293645736069 9845896235556805058575513)
          ·
            refine ⟨7384422176667603793931635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845896235556805058575513 7384422176667603793931635)
            ·
              refine ⟨11076633265001405690897453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7384422176667603793931635 11076633265001405690897453)
              ·
                refine ⟨4153737474375527134086545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11076633265001405690897453 4153737474375527134086545)
                ·
                  refine ⟨3115303105781645350564909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153737474375527134086545 3115303105781645350564909)
                  ·
                    refine ⟨1168238664668117006461841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115303105781645350564909 1168238664668117006461841)
                    ·
                      rfl

theorem cell22_3412705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_3412705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412705 prefixEnd_3412705 := by exact prefixLift 3412705
  have htrace : WordTrace (prefixWord ++ tailWord_3412705) baseStart_3412705 baseEnd_3412705 := by
    simpa [prefixWord, tailWord_3412705, baseEnd_3412705] using wordTrace_append hprefix tailTrace_3412705
  have hstable : (prefixWord ++ tailWord_3412705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412705).length < 2 ^ (prefixWord ++ tailWord_3412705).sum := by decide
  have hdescent : baseEnd_3412705 < baseStart_3412705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412791 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 8]
def baseStart_3412791 : Nat := 118140960795 + 3412791 * 2 ^ 59
def prefixEnd_3412791 : Nat := 4983230072969 + 3 ^ 40 * 3412791 * 2
def baseEnd_3412791 : Nat := 389422701408547149603859

theorem tailTrace_3412791 : CollatzResearch.WordTrace tailWord_3412791 prefixEnd_3412791 389422701408547149603859 := by
  unfold tailWord_3412791
  simp only [CollatzResearch.WordTrace]
  refine ⟨124474713779048540144190227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82983142519365693429460151 124474713779048540144190227)
  ·
    refine ⟨186712070668572810216285341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124474713779048540144190227 186712070668572810216285341)
    ·
      refine ⟨70017026500714803831107003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186712070668572810216285341 70017026500714803831107003)
      ·
        refine ⟨105025539751072205746660505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70017026500714803831107003 105025539751072205746660505)
        ·
          refine ⟨78769154813304154309995379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105025539751072205746660505 78769154813304154309995379)
          ·
            refine ⟨118153732219956231464993069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78769154813304154309995379 118153732219956231464993069)
            ·
              refine ⟨44307649582483586799372401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118153732219956231464993069 44307649582483586799372401)
              ·
                refine ⟨33230737186862690099529301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44307649582483586799372401 33230737186862690099529301)
                ·
                  refine ⟨389422701408547149603859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33230737186862690099529301 389422701408547149603859)
                  ·
                    rfl

theorem cell22_3412791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 8].length) (baseStart_3412791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412791 prefixEnd_3412791 := by exact prefixLift 3412791
  have htrace : WordTrace (prefixWord ++ tailWord_3412791) baseStart_3412791 baseEnd_3412791 := by
    simpa [prefixWord, tailWord_3412791, baseEnd_3412791] using wordTrace_append hprefix tailTrace_3412791
  have hstable : (prefixWord ++ tailWord_3412791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412791).length < 2 ^ (prefixWord ++ tailWord_3412791).sum := by decide
  have hdescent : baseEnd_3412791 < baseStart_3412791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412797 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3412797 : Nat := 118140960795 + 3412797 * 2 ^ 59
def prefixEnd_3412797 : Nat := 4983230072969 + 3 ^ 40 * 3412797 * 2
def baseEnd_3412797 : Nat := 389423386049419811053853

theorem tailTrace_3412797 : CollatzResearch.WordTrace tailWord_3412797 prefixEnd_3412797 389423386049419811053853 := by
  unfold tailWord_3412797
  simp only [CollatzResearch.WordTrace]
  refine ⟨124474932617026803168908645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82983288411351202112605763 124474932617026803168908645)
  ·
    refine ⟨23339049865692525594170371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124474932617026803168908645 23339049865692525594170371)
    ·
      refine ⟨35008574798538788391255557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23339049865692525594170371 35008574798538788391255557)
      ·
        refine ⟨6564107774726022823360417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35008574798538788391255557 6564107774726022823360417)
        ·
          refine ⟨4923080831044517117520313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6564107774726022823360417 4923080831044517117520313)
          ·
            refine ⟨3692310623283387838140235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4923080831044517117520313 3692310623283387838140235)
            ·
              refine ⟨5538465934925081757210353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3692310623283387838140235 5538465934925081757210353)
              ·
                refine ⟨4153849451193811317907765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5538465934925081757210353 4153849451193811317907765)
                ·
                  refine ⟨389423386049419811053853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4153849451193811317907765 389423386049419811053853)
                  ·
                    rfl

theorem cell22_3412797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3412797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412797 prefixEnd_3412797 := by exact prefixLift 3412797
  have htrace : WordTrace (prefixWord ++ tailWord_3412797) baseStart_3412797 baseEnd_3412797 := by
    simpa [prefixWord, tailWord_3412797, baseEnd_3412797] using wordTrace_append hprefix tailTrace_3412797
  have hstable : (prefixWord ++ tailWord_3412797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412797).length < 2 ^ (prefixWord ++ tailWord_3412797).sum := by decide
  have hdescent : baseEnd_3412797 < baseStart_3412797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412808 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 6]
def baseStart_3412808 : Nat := 118140960795 + 3412808 * 2 ^ 59
def prefixEnd_3412808 : Nat := 4983230072969 + 3 ^ 40 * 3412808 * 2
def baseEnd_3412808 : Nat := 389424641224353023712175

theorem tailTrace_3412808 : CollatzResearch.WordTrace tailWord_3412808 prefixEnd_3412808 389424641224353023712175 := by
  unfold tailWord_3412808
  simp only [CollatzResearch.WordTrace]
  refine ⟨62237666909993476023779539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82983555879991301365039385 62237666909993476023779539)
  ·
    refine ⟨93356500364990214035669309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62237666909993476023779539 93356500364990214035669309)
    ·
      refine ⟨35008687636871330263375991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93356500364990214035669309 35008687636871330263375991)
      ·
        refine ⟨52513031455306995395063987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35008687636871330263375991 52513031455306995395063987)
        ·
          refine ⟨78769547182960493092595981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52513031455306995395063987 78769547182960493092595981)
          ·
            refine ⟨29538580193610184909723493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78769547182960493092595981 29538580193610184909723493)
            ·
              refine ⟨5538483786301909670573155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29538580193610184909723493 5538483786301909670573155)
              ·
                refine ⟨8307725679452864505859733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5538483786301909670573155 8307725679452864505859733)
                ·
                  refine ⟨389424641224353023712175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8307725679452864505859733 389424641224353023712175)
                  ·
                    rfl

theorem cell22_3412808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 6].length) (baseStart_3412808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412808 prefixEnd_3412808 := by exact prefixLift 3412808
  have htrace : WordTrace (prefixWord ++ tailWord_3412808) baseStart_3412808 baseEnd_3412808 := by
    simpa [prefixWord, tailWord_3412808, baseEnd_3412808] using wordTrace_append hprefix tailTrace_3412808
  have hstable : (prefixWord ++ tailWord_3412808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412808).length < 2 ^ (prefixWord ++ tailWord_3412808).sum := by decide
  have hdescent : baseEnd_3412808 < baseStart_3412808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412840 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3412840 : Nat := 118140960795 + 3412840 * 2 ^ 59
def prefixEnd_3412840 : Nat := 4983230072969 + 3 ^ 40 * 3412840 * 2
def baseEnd_3412840 : Nat := 1168284877927021654336427

theorem tailTrace_3412840 : CollatzResearch.WordTrace tailWord_3412840 prefixEnd_3412840 1168284877927021654336427 := by
  unfold tailWord_3412840
  simp only [CollatzResearch.WordTrace]
  refine ⟨62238250477935510756361987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82984333970580681008482649 62238250477935510756361987)
  ·
    refine ⟨93357375716903266134542981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62238250477935510756361987 93357375716903266134542981)
    ·
      refine ⟨17504507946919362400226809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93357375716903266134542981 17504507946919362400226809)
      ·
        refine ⟨13128380960189521800170107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17504507946919362400226809 13128380960189521800170107)
        ·
          refine ⟨19692571440284282700255161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13128380960189521800170107 19692571440284282700255161)
          ·
            refine ⟨14769428580213212025191371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19692571440284282700255161 14769428580213212025191371)
            ·
              refine ⟨22154142870319818037787057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769428580213212025191371 22154142870319818037787057)
              ·
                refine ⟨16615607152739863528340293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22154142870319818037787057 16615607152739863528340293)
                ·
                  refine ⟨3115426341138724411563805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16615607152739863528340293 3115426341138724411563805)
                  ·
                    refine ⟨1168284877927021654336427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115426341138724411563805 1168284877927021654336427)
                    ·
                      rfl

theorem cell22_3412840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3412840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412840 prefixEnd_3412840 := by exact prefixLift 3412840
  have htrace : WordTrace (prefixWord ++ tailWord_3412840) baseStart_3412840 baseEnd_3412840 := by
    simpa [prefixWord, tailWord_3412840, baseEnd_3412840] using wordTrace_append hprefix tailTrace_3412840
  have hstable : (prefixWord ++ tailWord_3412840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412840).length < 2 ^ (prefixWord ++ tailWord_3412840).sum := by decide
  have hdescent : baseEnd_3412840 < baseStart_3412840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412853 : List Nat := [1, 3, 4, 1, 1, 2, 10]
def baseStart_3412853 : Nat := 118140960795 + 3412853 * 2 ^ 59
def prefixEnd_3412853 : Nat := 4983230072969 + 3 ^ 40 * 3412853 * 2
def baseEnd_3412853 : Nat := 43269975114544220509681

theorem tailTrace_3412853 : CollatzResearch.WordTrace tailWord_3412853 prefixEnd_3412853 43269975114544220509681 := by
  unfold tailWord_3412853
  simp only [CollatzResearch.WordTrace]
  refine ⟨124476975104823924732947213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82984650069882616488631475 124476975104823924732947213)
  ·
    refine ⟨46678865664308971774855205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124476975104823924732947213 46678865664308971774855205)
    ·
      refine ⟨8752287312057932207785351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46678865664308971774855205 8752287312057932207785351)
      ·
        refine ⟨13128430968086898311678027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8752287312057932207785351 13128430968086898311678027)
        ·
          refine ⟨19692646452130347467517041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13128430968086898311678027 19692646452130347467517041)
          ·
            refine ⟨14769484839097760600637781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19692646452130347467517041 14769484839097760600637781)
            ·
              refine ⟨43269975114544220509681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14769484839097760600637781 43269975114544220509681)
              ·
                rfl

theorem cell22_3412853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 10].length) (baseStart_3412853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412853 prefixEnd_3412853 := by exact prefixLift 3412853
  have htrace : WordTrace (prefixWord ++ tailWord_3412853) baseStart_3412853 baseEnd_3412853 := by
    simpa [prefixWord, tailWord_3412853, baseEnd_3412853] using wordTrace_append hprefix tailTrace_3412853
  have hstable : (prefixWord ++ tailWord_3412853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412853).length < 2 ^ (prefixWord ++ tailWord_3412853).sum := by decide
  have hdescent : baseEnd_3412853 < baseStart_3412853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412874 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3412874 : Nat := 118140960795 + 3412874 * 2 ^ 59
def prefixEnd_3412874 : Nat := 4983230072969 + 3 ^ 40 * 3412874 * 2
def baseEnd_3412874 : Nat := 1168296516821856898986323

theorem tailTrace_3412874 : CollatzResearch.WordTrace tailWord_3412874 prefixEnd_3412874 1168296516821856898986323 := by
  unfold tailWord_3412874
  simp only [CollatzResearch.WordTrace]
  refine ⟨31119435259436961329865419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82985160691831896879641117 31119435259436961329865419)
  ·
    refine ⟨46679152889155441994798129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31119435259436961329865419 46679152889155441994798129)
    ·
      refine ⟨35009364666866581496098597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46679152889155441994798129 35009364666866581496098597)
      ·
        refine ⟨6564255875037484030518487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35009364666866581496098597 6564255875037484030518487)
        ·
          refine ⟨9846383812556226045777731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564255875037484030518487 9846383812556226045777731)
          ·
            refine ⟨14769575718834339068666597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846383812556226045777731 14769575718834339068666597)
            ·
              refine ⟨2769295447281438575374987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14769575718834339068666597 2769295447281438575374987)
              ·
                refine ⟨4153943170922157863062481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2769295447281438575374987 4153943170922157863062481)
                ·
                  refine ⟨3115457378191618397296861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4153943170922157863062481 3115457378191618397296861)
                  ·
                    refine ⟨1168296516821856898986323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115457378191618397296861 1168296516821856898986323)
                    ·
                      rfl

theorem cell22_3412874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3412874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412874 prefixEnd_3412874 := by exact prefixLift 3412874
  have htrace : WordTrace (prefixWord ++ tailWord_3412874) baseStart_3412874 baseEnd_3412874 := by
    simpa [prefixWord, tailWord_3412874, baseEnd_3412874] using wordTrace_append hprefix tailTrace_3412874
  have hstable : (prefixWord ++ tailWord_3412874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412874).length < 2 ^ (prefixWord ++ tailWord_3412874).sum := by decide
  have hdescent : baseEnd_3412874 < baseStart_3412874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412919 : List Nat := [1, 1, 3, 1, 3, 1, 6, 2, 1, 3]
def baseStart_3412919 : Nat := 118140960795 + 3412919 * 2 ^ 59
def prefixEnd_3412919 : Nat := 4983230072969 + 3 ^ 40 * 3412919 * 2
def baseEnd_3412919 : Nat := 1168311921241491781611185

theorem tailTrace_3412919 : CollatzResearch.WordTrace tailWord_3412919 prefixEnd_3412919 1168311921241491781611185 := by
  unfold tailWord_3412919
  simp only [CollatzResearch.WordTrace]
  refine ⟨124479382322584818004849811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82986254881723212003233207 124479382322584818004849811)
  ·
    refine ⟨186719073483877227007274717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124479382322584818004849811 186719073483877227007274717)
    ·
      refine ⟨70019652556453960127728019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186719073483877227007274717 70019652556453960127728019)
      ·
        refine ⟨105029478834680940191592029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70019652556453960127728019 105029478834680940191592029)
        ·
          refine ⟨39386054563005352571847011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105029478834680940191592029 39386054563005352571847011)
          ·
            refine ⟨59079081844508028857770517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39386054563005352571847011 59079081844508028857770517)
            ·
              refine ⟨2769331961461313852707993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59079081844508028857770517 2769331961461313852707993)
              ·
                refine ⟨2076998971095985389530995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769331961461313852707993 2076998971095985389530995)
                ·
                  refine ⟨3115498456643978084296493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2076998971095985389530995 3115498456643978084296493)
                  ·
                    refine ⟨1168311921241491781611185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115498456643978084296493 1168311921241491781611185)
                    ·
                      rfl

theorem cell22_3412919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2, 1, 3].length) (baseStart_3412919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412919 prefixEnd_3412919 := by exact prefixLift 3412919
  have htrace : WordTrace (prefixWord ++ tailWord_3412919) baseStart_3412919 baseEnd_3412919 := by
    simpa [prefixWord, tailWord_3412919, baseEnd_3412919] using wordTrace_append hprefix tailTrace_3412919
  have hstable : (prefixWord ++ tailWord_3412919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412919).length < 2 ^ (prefixWord ++ tailWord_3412919).sum := by decide
  have hdescent : baseEnd_3412919 < baseStart_3412919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412943 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 8]
def baseStart_3412943 : Nat := 118140960795 + 3412943 * 2 ^ 59
def prefixEnd_3412943 : Nat := 4983230072969 + 3 ^ 40 * 3412943 * 2
def baseEnd_3412943 : Nat := 389440045643987906337037

theorem tailTrace_3412943 : CollatzResearch.WordTrace tailWord_3412943 prefixEnd_3412943 389440045643987906337037 := by
  unfold tailWord_3412943
  simp only [CollatzResearch.WordTrace]
  refine ⟨124480257674497870103723483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82986838449665246735815655 124480257674497870103723483)
  ·
    refine ⟨186720386511746805155585225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124480257674497870103723483 186720386511746805155585225)
    ·
      refine ⟨140040289883810103866688919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186720386511746805155585225 140040289883810103866688919)
      ·
        refine ⟨210060434825715155800033379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140040289883810103866688919 210060434825715155800033379)
        ·
          refine ⟨315090652238572733700050069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210060434825715155800033379 315090652238572733700050069)
          ·
            refine ⟨14769874323683096892189847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315090652238572733700050069 14769874323683096892189847)
            ·
              refine ⟨22154811485524645338284771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14769874323683096892189847 22154811485524645338284771)
              ·
                refine ⟨33232217228286968007427157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22154811485524645338284771 33232217228286968007427157)
                ·
                  refine ⟨389440045643987906337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33232217228286968007427157 389440045643987906337037)
                  ·
                    rfl

theorem cell22_3412943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 8].length) (baseStart_3412943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412943 prefixEnd_3412943 := by exact prefixLift 3412943
  have htrace : WordTrace (prefixWord ++ tailWord_3412943) baseStart_3412943 baseEnd_3412943 := by
    simpa [prefixWord, tailWord_3412943, baseEnd_3412943] using wordTrace_append hprefix tailTrace_3412943
  have hstable : (prefixWord ++ tailWord_3412943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412943).length < 2 ^ (prefixWord ++ tailWord_3412943).sum := by decide
  have hdescent : baseEnd_3412943 < baseStart_3412943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412945 : List Nat := [1, 2, 2, 1, 2, 1, 4, 4, 1, 4]
def baseStart_3412945 : Nat := 118140960795 + 3412945 * 2 ^ 59
def prefixEnd_3412945 : Nat := 4983230072969 + 3 ^ 40 * 3412945 * 2
def baseEnd_3412945 : Nat := 1168320821572836380461105

theorem tailTrace_3412945 : CollatzResearch.WordTrace tailWord_3412945 prefixEnd_3412945 1168320821572836380461105 := by
  unfold tailWord_3412945
  simp only [CollatzResearch.WordTrace]
  refine ⟨124480330620490624445296289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82986887080327082963530859 124480330620490624445296289)
  ·
    refine ⟨93360247965367968333972217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124480330620490624445296289 93360247965367968333972217)
    ·
      refine ⟨70020185974025976250479163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93360247965367968333972217 70020185974025976250479163)
      ·
        refine ⟨105030278961038964375718745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70020185974025976250479163 105030278961038964375718745)
        ·
          refine ⟨78772709220779223281789059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105030278961038964375718745 78772709220779223281789059)
          ·
            refine ⟨118159063831168834922683589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78772709220779223281789059 118159063831168834922683589)
            ·
              refine ⟨22154824468344156548003173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118159063831168834922683589 22154824468344156548003173)
              ·
                refine ⟨4154029587814529352750595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22154824468344156548003173 4154029587814529352750595)
                ·
                  refine ⟨6231044381721794029125893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154029587814529352750595 6231044381721794029125893)
                  ·
                    refine ⟨1168320821572836380461105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6231044381721794029125893 1168320821572836380461105)
                    ·
                      rfl

theorem cell22_3412945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_3412945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412945 prefixEnd_3412945 := by exact prefixLift 3412945
  have htrace : WordTrace (prefixWord ++ tailWord_3412945) baseStart_3412945 baseEnd_3412945 := by
    simpa [prefixWord, tailWord_3412945, baseEnd_3412945] using wordTrace_append hprefix tailTrace_3412945
  have hstable : (prefixWord ++ tailWord_3412945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412945).length < 2 ^ (prefixWord ++ tailWord_3412945).sum := by decide
  have hdescent : baseEnd_3412945 < baseStart_3412945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3412977 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 4]
def baseStart_3412977 : Nat := 118140960795 + 3412977 * 2 ^ 59
def prefixEnd_3412977 : Nat := 4983230072969 + 3 ^ 40 * 3412977 * 2
def baseEnd_3412977 : Nat := 389443925275599654553669

theorem tailTrace_3412977 : CollatzResearch.WordTrace tailWord_3412977 prefixEnd_3412977 389443925275599654553669 := by
  unfold tailWord_3412977
  simp only [CollatzResearch.WordTrace]
  refine ⟨124481497756374693910461185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82987665170916462606974123 124481497756374693910461185)
  ·
    refine ⟨93361123317281020432845889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124481497756374693910461185 93361123317281020432845889)
    ·
      refine ⟨70020842487960765324634417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93361123317281020432845889 70020842487960765324634417)
      ·
        refine ⟨52515631865970573993475813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70020842487960765324634417 52515631865970573993475813)
        ·
          refine ⟨9846680974869482623776715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52515631865970573993475813 9846680974869482623776715)
          ·
            refine ⟨14770021462304223935665073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846680974869482623776715 14770021462304223935665073)
            ·
              refine ⟨11077516096728167951748805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14770021462304223935665073 11077516096728167951748805)
              ·
                refine ⟨2077034268136531490952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11077516096728167951748805 2077034268136531490952901)
                ·
                  refine ⟨389443925275599654553669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077034268136531490952901 389443925275599654553669)
                  ·
                    rfl

theorem cell22_3412977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_3412977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3412977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3412977 prefixEnd_3412977 := by exact prefixLift 3412977
  have htrace : WordTrace (prefixWord ++ tailWord_3412977) baseStart_3412977 baseEnd_3412977 := by
    simpa [prefixWord, tailWord_3412977, baseEnd_3412977] using wordTrace_append hprefix tailTrace_3412977
  have hstable : (prefixWord ++ tailWord_3412977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3412977).length < 2 ^ (prefixWord ++ tailWord_3412977).sum := by decide
  have hdescent : baseEnd_3412977 < baseStart_3412977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3412977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413024 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 2, 4]
def baseStart_3413024 : Nat := 118140960795 + 3413024 * 2 ^ 59
def prefixEnd_3413024 : Nat := 4983230072969 + 3 ^ 40 * 3413024 * 2
def baseEnd_3413024 : Nat := 1168347864887306507735863

theorem tailTrace_3413024 : CollatzResearch.WordTrace tailWord_3413024 prefixEnd_3413024 1168347864887306507735863 := by
  unfold tailWord_3413024
  simp only [CollatzResearch.WordTrace]
  refine ⟨62241605993602210468711063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82988807991469613958281417 62241605993602210468711063)
  ·
    refine ⟨93362408990403315703066595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62241605993602210468711063 93362408990403315703066595)
    ·
      refine ⟨140043613485604973554599893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93362408990403315703066595 140043613485604973554599893)
      ·
        refine ⟨3282272191068866567685935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 140043613485604973554599893 3282272191068866567685935)
        ·
          refine ⟨4923408286603299851528903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282272191068866567685935 4923408286603299851528903)
          ·
            refine ⟨7385112429904949777293355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923408286603299851528903 7385112429904949777293355)
            ·
              refine ⟨11077668644857424665940033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385112429904949777293355 11077668644857424665940033)
              ·
                refine ⟨8308251483643068499455025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11077668644857424665940033 8308251483643068499455025)
                ·
                  refine ⟨6231188612732301374591269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8308251483643068499455025 6231188612732301374591269)
                  ·
                    refine ⟨1168347864887306507735863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6231188612732301374591269 1168347864887306507735863)
                    ·
                      rfl

theorem cell22_3413024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 4].length) (baseStart_3413024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413024 prefixEnd_3413024 := by exact prefixLift 3413024
  have htrace : WordTrace (prefixWord ++ tailWord_3413024) baseStart_3413024 baseEnd_3413024 := by
    simpa [prefixWord, tailWord_3413024, baseEnd_3413024] using wordTrace_append hprefix tailTrace_3413024
  have hstable : (prefixWord ++ tailWord_3413024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413024).length < 2 ^ (prefixWord ++ tailWord_3413024).sum := by decide
  have hdescent : baseEnd_3413024 < baseStart_3413024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413127 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 4, 3]
def baseStart_3413127 : Nat := 118140960795 + 3413127 * 2 ^ 59
def prefixEnd_3413127 : Nat := 4983230072969 + 3 ^ 40 * 3413127 * 2
def baseEnd_3413127 : Nat := 1168383123892248572410547

theorem tailTrace_3413127 : CollatzResearch.WordTrace tailWord_3413127 prefixEnd_3413127 1168383123892248572410547 := by
  unfold tailWord_3413127
  simp only [CollatzResearch.WordTrace]
  refine ⟨124486968705831269528421635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82991312470554179685614423 124486968705831269528421635)
  ·
    refine ⟨186730453058746904292632453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124486968705831269528421635 186730453058746904292632453)
    ·
      refine ⟨35011959948515044554868585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186730453058746904292632453 35011959948515044554868585)
      ·
        refine ⟨26258969961386283416151439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35011959948515044554868585 26258969961386283416151439)
        ·
          refine ⟨39388454942079425124227159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26258969961386283416151439 39388454942079425124227159)
          ·
            refine ⟨59082682413119137686340739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39388454942079425124227159 59082682413119137686340739)
            ·
              refine ⟨88624023619678706529511109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59082682413119137686340739 88624023619678706529511109)
              ·
                refine ⟨16617004428689757474283333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88624023619678706529511109 16617004428689757474283333)
                ·
                  refine ⟨3115688330379329526428125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16617004428689757474283333 3115688330379329526428125)
                  ·
                    refine ⟨1168383123892248572410547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115688330379329526428125 1168383123892248572410547)
                    ·
                      rfl

theorem cell22_3413127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_3413127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413127 prefixEnd_3413127 := by exact prefixLift 3413127
  have htrace : WordTrace (prefixWord ++ tailWord_3413127) baseStart_3413127 baseEnd_3413127 := by
    simpa [prefixWord, tailWord_3413127, baseEnd_3413127] using wordTrace_append hprefix tailTrace_3413127
  have hstable : (prefixWord ++ tailWord_3413127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413127).length < 2 ^ (prefixWord ++ tailWord_3413127).sum := by decide
  have hdescent : baseEnd_3413127 < baseStart_3413127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413129 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 4]
def baseStart_3413129 : Nat := 118140960795 + 3413129 * 2 ^ 59
def prefixEnd_3413129 : Nat := 4983230072969 + 3 ^ 40 * 3413129 * 2
def baseEnd_3413129 : Nat := 389461269511040411286847

theorem tailTrace_3413129 : CollatzResearch.WordTrace tailWord_3413129 prefixEnd_3413129 389461269511040411286847 := by
  unfold tailWord_3413129
  simp only [CollatzResearch.WordTrace]
  refine ⟨124487041651824023869994441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82991361101216015913329627 124487041651824023869994441)
  ·
    refine ⟨93365281238868017902495831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124487041651824023869994441 93365281238868017902495831)
    ·
      refine ⟨140047921858302026853743747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93365281238868017902495831 140047921858302026853743747)
      ·
        refine ⟨210071882787453040280615621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140047921858302026853743747 210071882787453040280615621)
        ·
          refine ⟨39388478022647445052615429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210071882787453040280615621 39388478022647445052615429)
          ·
            refine ⟨7385339629246395947365393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39388478022647445052615429 7385339629246395947365393)
            ·
              refine ⟨5539004721934796960524045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7385339629246395947365393 5539004721934796960524045)
              ·
                refine ⟨2077126770725548860196517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5539004721934796960524045 2077126770725548860196517)
                ·
                  refine ⟨389461269511040411286847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077126770725548860196517 389461269511040411286847)
                  ·
                    rfl

theorem cell22_3413129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 4].length) (baseStart_3413129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413129 prefixEnd_3413129 := by exact prefixLift 3413129
  have htrace : WordTrace (prefixWord ++ tailWord_3413129) baseStart_3413129 baseEnd_3413129 := by
    simpa [prefixWord, tailWord_3413129, baseEnd_3413129] using wordTrace_append hprefix tailTrace_3413129
  have hstable : (prefixWord ++ tailWord_3413129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413129).length < 2 ^ (prefixWord ++ tailWord_3413129).sum := by decide
  have hdescent : baseEnd_3413129 < baseStart_3413129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413144 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 4, 3]
def baseStart_3413144 : Nat := 118140960795 + 3413144 * 2 ^ 59
def prefixEnd_3413144 : Nat := 4983230072969 + 3 ^ 40 * 3413144 * 2
def baseEnd_3413144 : Nat := 1168388943339666194735495

theorem tailTrace_3413144 : CollatzResearch.WordTrace tailWord_3413144 prefixEnd_3413144 1168388943339666194735495 := by
  unfold tailWord_3413144
  simp only [CollatzResearch.WordTrace]
  refine ⟨62243794373384840715895243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82991725831179787621193657 62243794373384840715895243)
  ·
    refine ⟨93365691560077261073842865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62243794373384840715895243 93365691560077261073842865)
    ·
      refine ⟨70024268670057945805382149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93365691560077261073842865 70024268670057945805382149)
      ·
        refine ⟨13129550375635864838509153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70024268670057945805382149 13129550375635864838509153)
        ·
          refine ⟨9847162781726898628881865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13129550375635864838509153 9847162781726898628881865)
          ·
            refine ⟨7385372086295173971661399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9847162781726898628881865 7385372086295173971661399)
            ·
              refine ⟨11078058129442760957492099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385372086295173971661399 11078058129442760957492099)
              ·
                refine ⟨16617087194164141436238149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11078058129442760957492099 16617087194164141436238149)
                ·
                  refine ⟨3115703848905776519294653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16617087194164141436238149 3115703848905776519294653)
                  ·
                    refine ⟨1168388943339666194735495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115703848905776519294653 1168388943339666194735495)
                    ·
                      rfl

theorem cell22_3413144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_3413144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413144 prefixEnd_3413144 := by exact prefixLift 3413144
  have htrace : WordTrace (prefixWord ++ tailWord_3413144) baseStart_3413144 baseEnd_3413144 := by
    simpa [prefixWord, tailWord_3413144, baseEnd_3413144] using wordTrace_append hprefix tailTrace_3413144
  have hstable : (prefixWord ++ tailWord_3413144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413144).length < 2 ^ (prefixWord ++ tailWord_3413144).sum := by decide
  have hdescent : baseEnd_3413144 < baseStart_3413144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413202 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 7]
def baseStart_3413202 : Nat := 118140960795 + 3413202 * 2 ^ 59
def prefixEnd_3413202 : Nat := 4983230072969 + 3 ^ 40 * 3413202 * 2
def baseEnd_3413202 : Nat := 389469599308324458928439

theorem tailTrace_3413202 : CollatzResearch.WordTrace tailWord_3413202 prefixEnd_3413202 389469599308324458928439 := by
  unfold tailWord_3413202
  simp only [CollatzResearch.WordTrace]
  refine ⟨31122426045139889334350465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82993136120373038224934573 31122426045139889334350465)
  ·
    refine ⟨23341819533854917000762849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31122426045139889334350465 23341819533854917000762849)
    ·
      refine ⟨17506364650391187750572137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23341819533854917000762849 17506364650391187750572137)
      ·
        refine ⟨13129773487793390812929103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17506364650391187750572137 13129773487793390812929103)
        ·
          refine ⟨19694660231690086219393655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13129773487793390812929103 19694660231690086219393655)
          ·
            refine ⟨29541990347535129329090483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19694660231690086219393655 29541990347535129329090483)
            ·
              refine ⟨44312985521302693993635725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29541990347535129329090483 44312985521302693993635725)
              ·
                refine ⟨16617369570488510247613397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44312985521302693993635725 16617369570488510247613397)
                ·
                  refine ⟨389469599308324458928439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16617369570488510247613397 389469599308324458928439)
                  ·
                    rfl

theorem cell22_3413202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_3413202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413202 prefixEnd_3413202 := by exact prefixLift 3413202
  have htrace : WordTrace (prefixWord ++ tailWord_3413202) baseStart_3413202 baseEnd_3413202 := by
    simpa [prefixWord, tailWord_3413202, baseEnd_3413202] using wordTrace_append hprefix tailTrace_3413202
  have hstable : (prefixWord ++ tailWord_3413202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413202).length < 2 ^ (prefixWord ++ tailWord_3413202).sum := by decide
  have hdescent : baseEnd_3413202 < baseStart_3413202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413313 : List Nat := [1, 2, 5, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3413313 : Nat := 118140960795 + 3413313 * 2 ^ 59
def prefixEnd_3413313 : Nat := 4983230072969 + 3 ^ 40 * 3413313 * 2
def baseEnd_3413313 : Nat := 1168446795493406087259977

theorem tailTrace_3413313 : CollatzResearch.WordTrace tailWord_3413313 prefixEnd_3413313 1168446795493406087259977 := by
  unfold tailWord_3413313
  simp only [CollatzResearch.WordTrace]
  refine ⟨124493752683157423294692593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82995835122104948863128395 124493752683157423294692593)
  ·
    refine ⟨93370314512368067471019445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124493752683157423294692593 93370314512368067471019445)
    ·
      refine ⟨8753466985534506325408073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93370314512368067471019445 8753466985534506325408073)
      ·
        refine ⟨6565100239150879744056055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8753466985534506325408073 6565100239150879744056055)
        ·
          refine ⟨9847650358726319616084083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6565100239150879744056055 9847650358726319616084083)
          ·
            refine ⟨14771475538089479424126125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9847650358726319616084083 14771475538089479424126125)
            ·
              refine ⟨5539303326783554784047297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14771475538089479424126125 5539303326783554784047297)
              ·
                refine ⟨4154477495087666088035473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539303326783554784047297 4154477495087666088035473)
                ·
                  refine ⟨3115858121315749566026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4154477495087666088035473 3115858121315749566026605)
                  ·
                    refine ⟨1168446795493406087259977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3115858121315749566026605 1168446795493406087259977)
                    ·
                      rfl

theorem cell22_3413313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3413313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413313 prefixEnd_3413313 := by exact prefixLift 3413313
  have htrace : WordTrace (prefixWord ++ tailWord_3413313) baseStart_3413313 baseEnd_3413313 := by
    simpa [prefixWord, tailWord_3413313, baseEnd_3413313] using wordTrace_append hprefix tailTrace_3413313
  have hstable : (prefixWord ++ tailWord_3413313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413313).length < 2 ^ (prefixWord ++ tailWord_3413313).sum := by decide
  have hdescent : baseEnd_3413313 < baseStart_3413313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413322 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_3413322 : Nat := 118140960795 + 3413322 * 2 ^ 59
def prefixEnd_3413322 : Nat := 4983230072969 + 3 ^ 40 * 3413322 * 2
def baseEnd_3413322 : Nat := 1168449876377333063784949

theorem tailTrace_3413322 : CollatzResearch.WordTrace tailWord_3413322 prefixEnd_3413322 1168449876377333063784949 := by
  unfold tailWord_3413322
  simp only [CollatzResearch.WordTrace]
  refine ⟨31123520235031204457942555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82996053960083211887846813 31123520235031204457942555)
  ·
    refine ⟨46685280352546806686913833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31123520235031204457942555 46685280352546806686913833)
    ·
      refine ⟨35013960264410105015185375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46685280352546806686913833 35013960264410105015185375)
      ·
        refine ⟨52520940396615157522778063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35013960264410105015185375 52520940396615157522778063)
        ·
          refine ⟨78781410594922736284167095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52520940396615157522778063 78781410594922736284167095)
          ·
            refine ⟨118172115892384104426250643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78781410594922736284167095 118172115892384104426250643)
            ·
              refine ⟨177258173838576156639375965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118172115892384104426250643 177258173838576156639375965)
              ·
                refine ⟨66471815189466058739765987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177258173838576156639375965 66471815189466058739765987)
                ·
                  refine ⟨99707722784199088109648981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66471815189466058739765987 99707722784199088109648981)
                  ·
                    refine ⟨1168449876377333063784949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99707722784199088109648981 1168449876377333063784949)
                    ·
                      rfl

theorem cell22_3413322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_3413322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413322 prefixEnd_3413322 := by exact prefixLift 3413322
  have htrace : WordTrace (prefixWord ++ tailWord_3413322) baseStart_3413322 baseEnd_3413322 := by
    simpa [prefixWord, tailWord_3413322, baseEnd_3413322] using wordTrace_append hprefix tailTrace_3413322
  have hstable : (prefixWord ++ tailWord_3413322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413322).length < 2 ^ (prefixWord ++ tailWord_3413322).sum := by decide
  have hdescent : baseEnd_3413322 < baseStart_3413322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413401 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 1, 4]
def baseStart_3413401 : Nat := 118140960795 + 3413401 * 2 ^ 59
def prefixEnd_3413401 : Nat := 4983230072969 + 3 ^ 40 * 3413401 * 2
def baseEnd_3413401 : Nat := 1168476919691803191059707

theorem tailTrace_3413401 : CollatzResearch.WordTrace tailWord_3413401 prefixEnd_3413401 1168476919691803191059707 := by
  unfold tailWord_3413401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124496962306838614323896057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82997974871225742882597371 124496962306838614323896057)
  ·
    refine ⟨93372721730128960742922043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124496962306838614323896057 93372721730128960742922043)
    ·
      refine ⟨140059082595193441114383065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93372721730128960742922043 140059082595193441114383065)
      ·
        refine ⟨105044311946395080835787299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140059082595193441114383065 105044311946395080835787299)
        ·
          refine ⟨157566467919592621253680949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105044311946395080835787299 157566467919592621253680949)
          ·
            refine ⟨14771856367461808242532589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157566467919592621253680949 14771856367461808242532589)
            ·
              refine ⟨5539446137798178090949721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14771856367461808242532589 5539446137798178090949721)
              ·
                refine ⟨4154584603348633568212291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539446137798178090949721 4154584603348633568212291)
                ·
                  refine ⟨6231876905022950352318437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4154584603348633568212291 6231876905022950352318437)
                  ·
                    refine ⟨1168476919691803191059707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6231876905022950352318437 1168476919691803191059707)
                    ·
                      rfl

theorem cell22_3413401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 4].length) (baseStart_3413401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413401 prefixEnd_3413401 := by exact prefixLift 3413401
  have htrace : WordTrace (prefixWord ++ tailWord_3413401) baseStart_3413401 baseEnd_3413401 := by
    simpa [prefixWord, tailWord_3413401, baseEnd_3413401] using wordTrace_append hprefix tailTrace_3413401
  have hstable : (prefixWord ++ tailWord_3413401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413401).length < 2 ^ (prefixWord ++ tailWord_3413401).sum := by decide
  have hdescent : baseEnd_3413401 < baseStart_3413401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413433 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 4]
def baseStart_3413433 : Nat := 118140960795 + 3413433 * 2 ^ 59
def prefixEnd_3413433 : Nat := 4983230072969 + 3 ^ 40 * 3413433 * 2
def baseEnd_3413433 : Nat := 389495957981921924753203

theorem tailTrace_3413433 : CollatzResearch.WordTrace tailWord_3413433 prefixEnd_3413433 389495957981921924753203 := by
  unfold tailWord_3413433
  simp only [CollatzResearch.WordTrace]
  refine ⟨124498129442722683789060953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82998752961815122526040635 124498129442722683789060953)
  ·
    refine ⟨93373597082042012841795715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124498129442722683789060953 93373597082042012841795715)
    ·
      refine ⟨140060395623063019262693573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93373597082042012841795715 140060395623063019262693573)
      ·
        refine ⟨26261324179324316111755045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140060395623063019262693573 26261324179324316111755045)
        ·
          refine ⟨4923998283623309270954071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26261324179324316111755045 4923998283623309270954071)
          ·
            refine ⟨7385997425434963906431107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923998283623309270954071 7385997425434963906431107)
            ·
              refine ⟨11078996138152445859646661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7385997425434963906431107 11078996138152445859646661)
              ·
                refine ⟨2077311775903583598683749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11078996138152445859646661 2077311775903583598683749)
                ·
                  refine ⟨389495957981921924753203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077311775903583598683749 389495957981921924753203)
                  ·
                    rfl

theorem cell22_3413433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_3413433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413433 prefixEnd_3413433 := by exact prefixLift 3413433
  have htrace : WordTrace (prefixWord ++ tailWord_3413433) baseStart_3413433 baseEnd_3413433 := by
    simpa [prefixWord, tailWord_3413433, baseEnd_3413433] using wordTrace_append hprefix tailTrace_3413433
  have hstable : (prefixWord ++ tailWord_3413433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413433).length < 2 ^ (prefixWord ++ tailWord_3413433).sum := by decide
  have hdescent : baseEnd_3413433 < baseStart_3413433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413461 : List Nat := [1, 3, 2, 3, 1, 1, 5, 6]
def baseStart_3413461 : Nat := 118140960795 + 3413461 * 2 ^ 59
def prefixEnd_3413461 : Nat := 4983230072969 + 3 ^ 40 * 3413461 * 2
def baseEnd_3413461 : Nat := 129833050990887003839947

theorem tailTrace_3413461 : CollatzResearch.WordTrace tailWord_3413461 prefixEnd_3413461 129833050990887003839947 := by
  unfold tailWord_3413461
  simp only [CollatzResearch.WordTrace]
  refine ⟨124499150686621244571080237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82999433791080829714053491 124499150686621244571080237)
  ·
    refine ⟨46687181507482966714155089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124499150686621244571080237 46687181507482966714155089)
    ·
      refine ⟨35015386130612225035616317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46687181507482966714155089 35015386130612225035616317)
      ·
        refine ⟨13130769798979584388356119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35015386130612225035616317 13130769798979584388356119)
        ·
          refine ⟨19696154698469376582534179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13130769798979584388356119 19696154698469376582534179)
          ·
            refine ⟨29544232047704064873801269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19696154698469376582534179 29544232047704064873801269)
            ·
              refine ⟨2769771754472256081918869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29544232047704064873801269 2769771754472256081918869)
              ·
                refine ⟨129833050990887003839947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2769771754472256081918869 129833050990887003839947)
                ·
                  rfl

theorem cell22_3413461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 6].length) (baseStart_3413461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413461 prefixEnd_3413461 := by exact prefixLift 3413461
  have htrace : WordTrace (prefixWord ++ tailWord_3413461) baseStart_3413461 baseEnd_3413461 := by
    simpa [prefixWord, tailWord_3413461, baseEnd_3413461] using wordTrace_append hprefix tailTrace_3413461
  have hstable : (prefixWord ++ tailWord_3413461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413461).length < 2 ^ (prefixWord ++ tailWord_3413461).sum := by decide
  have hdescent : baseEnd_3413461 < baseStart_3413461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413482 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_3413482 : Nat := 118140960795 + 3413482 * 2 ^ 59
def prefixEnd_3413482 : Nat := 4983230072969 + 3 ^ 40 * 3413482 * 2
def baseEnd_3413482 : Nat := 1168504647647145979784459

theorem tailTrace_3413482 : CollatzResearch.WordTrace tailWord_3413482 prefixEnd_3413482 1168504647647145979784459 := by
  unfold tailWord_3413482
  simp only [CollatzResearch.WordTrace]
  refine ⟨31124979154886291289398675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82999944413030110105063133 31124979154886291289398675)
  ·
    refine ⟨46687468732329436934098013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31124979154886291289398675 46687468732329436934098013)
    ·
      refine ⟨17507800774623538850286755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46687468732329436934098013 17507800774623538850286755)
      ·
        refine ⟨26261701161935308275430133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17507800774623538850286755 26261701161935308275430133)
        ·
          refine ⟨2462034483931435150821575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26261701161935308275430133 2462034483931435150821575)
          ·
            refine ⟨3693051725897152726232363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462034483931435150821575 3693051725897152726232363)
            ·
              refine ⟨5539577588845729089348545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693051725897152726232363 5539577588845729089348545)
              ·
                refine ⟨4154683191634296817011409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5539577588845729089348545 4154683191634296817011409)
                ·
                  refine ⟨3116012393725722612758557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4154683191634296817011409 3116012393725722612758557)
                  ·
                    refine ⟨1168504647647145979784459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116012393725722612758557 1168504647647145979784459)
                    ·
                      rfl

theorem cell22_3413482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_3413482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413482 prefixEnd_3413482 := by exact prefixLift 3413482
  have htrace : WordTrace (prefixWord ++ tailWord_3413482) baseStart_3413482 baseEnd_3413482 := by
    simpa [prefixWord, tailWord_3413482, baseEnd_3413482] using wordTrace_append hprefix tailTrace_3413482
  have hstable : (prefixWord ++ tailWord_3413482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413482).length < 2 ^ (prefixWord ++ tailWord_3413482).sum := by decide
  have hdescent : baseEnd_3413482 < baseStart_3413482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413544 : List Nat := [2, 1, 5, 2, 2, 1, 3, 2, 1, 3]
def baseStart_3413544 : Nat := 118140960795 + 3413544 * 2 ^ 59
def prefixEnd_3413544 : Nat := 4983230072969 + 3 ^ 40 * 3413544 * 2
def baseEnd_3413544 : Nat := 1168525871514198484734269

theorem tailTrace_3413544 : CollatzResearch.WordTrace tailWord_3413544 prefixEnd_3413544 1168525871514198484734269 := by
  unfold tailWord_3413544
  simp only [CollatzResearch.WordTrace]
  refine ⟨62251088972660274873175843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83001451963547033164234457 62251088972660274873175843)
  ·
    refine ⟨93376633458990412309763765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62251088972660274873175843 93376633458990412309763765)
    ·
      refine ⟨8754059386780351154040353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93376633458990412309763765 8754059386780351154040353)
      ·
        refine ⟨6565544540085263365530265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8754059386780351154040353 6565544540085263365530265)
        ·
          refine ⟨4924158405063947524147699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6565544540085263365530265 4924158405063947524147699)
          ·
            refine ⟨7386237607595921286221549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4924158405063947524147699 7386237607595921286221549)
            ·
              refine ⟨2769839102848470482333081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7386237607595921286221549 2769839102848470482333081)
              ·
                refine ⟨2077379327136352861749811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2769839102848470482333081 2077379327136352861749811)
                ·
                  refine ⟨3116068990704529292624717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077379327136352861749811 3116068990704529292624717)
                  ·
                    refine ⟨1168525871514198484734269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116068990704529292624717 1168525871514198484734269)
                    ·
                      rfl

theorem cell22_3413544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_3413544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413544 prefixEnd_3413544 := by exact prefixLift 3413544
  have htrace : WordTrace (prefixWord ++ tailWord_3413544) baseStart_3413544 baseEnd_3413544 := by
    simpa [prefixWord, tailWord_3413544, baseEnd_3413544] using wordTrace_append hprefix tailTrace_3413544
  have hstable : (prefixWord ++ tailWord_3413544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413544).length < 2 ^ (prefixWord ++ tailWord_3413544).sum := by decide
  have hdescent : baseEnd_3413544 < baseStart_3413544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413596 : List Nat := [2, 2, 4, 1, 2, 11]
def baseStart_3413596 : Nat := 118140960795 + 3413596 * 2 ^ 59
def prefixEnd_3413596 : Nat := 4983230072969 + 3 ^ 40 * 3413596 * 2
def baseEnd_3413596 : Nat := 14426465088603551634989

theorem tailTrace_3413596 : CollatzResearch.WordTrace tailWord_3413596 prefixEnd_3413596 14426465088603551634989 := by
  unfold tailWord_3413596
  simp only [CollatzResearch.WordTrace]
  refine ⟨62252037270566081313622321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83002716360754775084829761 62252037270566081313622321)
  ·
    refine ⟨46689027952924560985216741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62252037270566081313622321 46689027952924560985216741)
    ·
      refine ⟨8754192741173355184728139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46689027952924560985216741 8754192741173355184728139)
      ·
        refine ⟨13131289111760032777092209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754192741173355184728139 13131289111760032777092209)
        ·
          refine ⟨9848466833820024582819157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13131289111760032777092209 9848466833820024582819157)
          ·
            refine ⟨14426465088603551634989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9848466833820024582819157 14426465088603551634989)
            ·
              rfl

theorem cell22_3413596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 11].length) (baseStart_3413596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413596 prefixEnd_3413596 := by exact prefixLift 3413596
  have htrace : WordTrace (prefixWord ++ tailWord_3413596) baseStart_3413596 baseEnd_3413596 := by
    simpa [prefixWord, tailWord_3413596, baseEnd_3413596] using wordTrace_append hprefix tailTrace_3413596
  have hstable : (prefixWord ++ tailWord_3413596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413596).length < 2 ^ (prefixWord ++ tailWord_3413596).sum := by decide
  have hdescent : baseEnd_3413596 < baseStart_3413596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413662 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_3413662 : Nat := 118140960795 + 3413662 * 2 ^ 59
def prefixEnd_3413662 : Nat := 4983230072969 + 3 ^ 40 * 3413662 * 2
def baseEnd_3413662 : Nat := 1168566265325685510283907

theorem tailTrace_3413662 : CollatzResearch.WordTrace tailWord_3413662 prefixEnd_3413662 1168566265325685510283907 := by
  unfold tailWord_3413662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15563310219861631987393405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83004321172595370599431493 15563310219861631987393405)
  ·
    refine ⟨5836241332448111995272527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15563310219861631987393405 5836241332448111995272527)
    ·
      refine ⟨8754361998672167992908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5836241332448111995272527 8754361998672167992908791)
      ·
        refine ⟨13131542998008251989363187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8754361998672167992908791 13131542998008251989363187)
        ·
          refine ⟨19697314497012377984044781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13131542998008251989363187 19697314497012377984044781)
          ·
            refine ⟨7386492936379641744016793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19697314497012377984044781 7386492936379641744016793)
            ·
              refine ⟨5539869702284731308012595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7386492936379641744016793 5539869702284731308012595)
              ·
                refine ⟨8309804553427096962018893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5539869702284731308012595 8309804553427096962018893)
                ·
                  refine ⟨3116176707535161360757085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8309804553427096962018893 3116176707535161360757085)
                  ·
                    refine ⟨1168566265325685510283907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116176707535161360757085 1168566265325685510283907)
                    ·
                      rfl

theorem cell22_3413662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_3413662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413662 prefixEnd_3413662 := by exact prefixLift 3413662
  have htrace : WordTrace (prefixWord ++ tailWord_3413662) baseStart_3413662 baseEnd_3413662 := by
    simpa [prefixWord, tailWord_3413662, baseEnd_3413662] using wordTrace_append hprefix tailTrace_3413662
  have hstable : (prefixWord ++ tailWord_3413662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413662).length < 2 ^ (prefixWord ++ tailWord_3413662).sum := by decide
  have hdescent : baseEnd_3413662 < baseStart_3413662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413733 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 4, 4]
def baseStart_3413733 : Nat := 118140960795 + 3413733 * 2 ^ 59
def prefixEnd_3413733 : Nat := 4983230072969 + 3 ^ 40 * 3413733 * 2
def baseEnd_3413733 : Nat := 1168590570076664991758689

theorem tailTrace_3413733 : CollatzResearch.WordTrace tailWord_3413733 prefixEnd_3413733 1168590570076664991758689 := by
  unfold tailWord_3413733
  simp only [CollatzResearch.WordTrace]
  refine ⟨124509071341635835024981853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83006047561090556683321235 124509071341635835024981853)
  ·
    refine ⟨46690901753113438134368195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124509071341635835024981853 46690901753113438134368195)
    ·
      refine ⟨70036352629670157201552293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46690901753113438134368195 70036352629670157201552293)
      ·
        refine ⟨13131816118063154475291055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70036352629670157201552293 13131816118063154475291055)
        ·
          refine ⟨19697724177094731712936583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13131816118063154475291055 19697724177094731712936583)
          ·
            refine ⟨29546586265642097569404875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19697724177094731712936583 29546586265642097569404875)
            ·
              refine ⟨44319879398463146354107313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29546586265642097569404875 44319879398463146354107313)
              ·
                refine ⟨33239909548847359765580485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44319879398463146354107313 33239909548847359765580485)
                ·
                  refine ⟨6232483040408879956046341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33239909548847359765580485 6232483040408879956046341)
                  ·
                    refine ⟨1168590570076664991758689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232483040408879956046341 1168590570076664991758689)
                    ·
                      rfl

theorem cell22_3413733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_3413733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413733 prefixEnd_3413733 := by exact prefixLift 3413733
  have htrace : WordTrace (prefixWord ++ tailWord_3413733) baseStart_3413733 baseEnd_3413733 := by
    simpa [prefixWord, tailWord_3413733, baseEnd_3413733] using wordTrace_append hprefix tailTrace_3413733
  have hstable : (prefixWord ++ tailWord_3413733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413733).length < 2 ^ (prefixWord ++ tailWord_3413733).sum := by decide
  have hdescent : baseEnd_3413733 < baseStart_3413733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413750 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3413750 : Nat := 118140960795 + 3413750 * 2 ^ 59
def prefixEnd_3413750 : Nat := 4983230072969 + 3 ^ 40 * 3413750 * 2
def baseEnd_3413750 : Nat := 1168596389524082614083637

theorem tailTrace_3413750 : CollatzResearch.WordTrace tailWord_3413750 prefixEnd_3413750 1168596389524082614083637 := by
  unfold tailWord_3413750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781855711410890433021919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83006460921716164618900469 7781855711410890433021919)
  ·
    refine ⟨11672783567116335649532879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7781855711410890433021919 11672783567116335649532879)
    ·
      refine ⟨17509175350674503474299319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11672783567116335649532879 17509175350674503474299319)
      ·
        refine ⟨26263763026011755211448979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17509175350674503474299319 26263763026011755211448979)
        ·
          refine ⟨39395644539017632817173469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26263763026011755211448979 39395644539017632817173469)
          ·
            refine ⟨14773366702131612306440051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39395644539017632817173469 14773366702131612306440051)
            ·
              refine ⟨22160050053197418459660077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14773366702131612306440051 22160050053197418459660077)
              ·
                refine ⟨8310018769949031922372529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22160050053197418459660077 8310018769949031922372529)
                ·
                  refine ⟨6232514077461773941779397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8310018769949031922372529 6232514077461773941779397)
                  ·
                    refine ⟨1168596389524082614083637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232514077461773941779397 1168596389524082614083637)
                    ·
                      rfl

theorem cell22_3413750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3413750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413750 prefixEnd_3413750 := by exact prefixLift 3413750
  have htrace : WordTrace (prefixWord ++ tailWord_3413750) baseStart_3413750 baseEnd_3413750 := by
    simpa [prefixWord, tailWord_3413750, baseEnd_3413750] using wordTrace_append hprefix tailTrace_3413750
  have hstable : (prefixWord ++ tailWord_3413750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413750).length < 2 ^ (prefixWord ++ tailWord_3413750).sum := by decide
  have hdescent : baseEnd_3413750 < baseStart_3413750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413889 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 6]
def baseStart_3413889 : Nat := 118140960795 + 3413889 * 2 ^ 59
def prefixEnd_3413889 : Nat := 4983230072969 + 3 ^ 40 * 3413889 * 2
def baseEnd_3413889 : Nat := 389547990688244194952737

theorem tailTrace_3413889 : CollatzResearch.WordTrace tailWord_3413889 prefixEnd_3413889 389547990688244194952737 := by
  unfold tailWord_3413889
  simp only [CollatzResearch.WordTrace]
  refine ⟨124514761129070673667660721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83009840752713782445107147 124514761129070673667660721)
  ·
    refine ⟨93386070846803005250745541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124514761129070673667660721 93386070846803005250745541)
    ·
      refine ⟨17509888283775563484514789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93386070846803005250745541 17509888283775563484514789)
      ·
        refine ⟨3283104053207918153346523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17509888283775563484514789 3283104053207918153346523)
        ·
          refine ⟨4924656079811877230019785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283104053207918153346523 4924656079811877230019785)
          ·
            refine ⟨3693492059858907922514839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924656079811877230019785 3693492059858907922514839)
            ·
              refine ⟨5540238089788361883772259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693492059858907922514839 5540238089788361883772259)
              ·
                refine ⟨8310357134682542825658389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5540238089788361883772259 8310357134682542825658389)
                ·
                  refine ⟨389547990688244194952737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8310357134682542825658389 389547990688244194952737)
                  ·
                    rfl

theorem cell22_3413889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_3413889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413889 prefixEnd_3413889 := by exact prefixLift 3413889
  have htrace : WordTrace (prefixWord ++ tailWord_3413889) baseStart_3413889 baseEnd_3413889 := by
    simpa [prefixWord, tailWord_3413889, baseEnd_3413889] using wordTrace_append hprefix tailTrace_3413889
  have hstable : (prefixWord ++ tailWord_3413889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413889).length < 2 ^ (prefixWord ++ tailWord_3413889).sum := by decide
  have hdescent : baseEnd_3413889 < baseStart_3413889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413934 : List Nat := [4, 1, 5, 1, 1, 10]
def baseStart_3413934 : Nat := 118140960795 + 3413934 * 2 ^ 59
def prefixEnd_3413934 : Nat := 4983230072969 + 3 ^ 40 * 3413934 * 2
def baseEnd_3413934 : Nat := 14427893536844042808433

theorem tailTrace_3413934 : CollatzResearch.WordTrace tailWord_3413934 prefixEnd_3413934 14427893536844042808433 := by
  unfold tailWord_3413934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564550301738455794131107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83010934942605097568699237 15564550301738455794131107)
  ·
    refine ⟨23346825452607683691196661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15564550301738455794131107 23346825452607683691196661)
    ·
      refine ⟨2188764886181970346049687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23346825452607683691196661 2188764886181970346049687)
      ·
        refine ⟨3283147329272955519074531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188764886181970346049687 3283147329272955519074531)
        ·
          refine ⟨4924720993909433278611797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283147329272955519074531 4924720993909433278611797)
          ·
            refine ⟨14427893536844042808433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4924720993909433278611797 14427893536844042808433)
            ·
              rfl

theorem cell22_3413934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 10].length) (baseStart_3413934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413934 prefixEnd_3413934 := by exact prefixLift 3413934
  have htrace : WordTrace (prefixWord ++ tailWord_3413934) baseStart_3413934 baseEnd_3413934 := by
    simpa [prefixWord, tailWord_3413934, baseEnd_3413934] using wordTrace_append hprefix tailTrace_3413934
  have hstable : (prefixWord ++ tailWord_3413934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413934).length < 2 ^ (prefixWord ++ tailWord_3413934).sum := by decide
  have hdescent : baseEnd_3413934 < baseStart_3413934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413940 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3413940 : Nat := 118140960795 + 3413940 * 2 ^ 59
def prefixEnd_3413940 : Nat := 4983230072969 + 3 ^ 40 * 3413940 * 2
def baseEnd_3413940 : Nat := 389553810135661817277685

theorem tailTrace_3413940 : CollatzResearch.WordTrace tailWord_3413940 prefixEnd_3413940 389553810135661817277685 := by
  unfold tailWord_3413940
  simp only [CollatzResearch.WordTrace]
  refine ⟨62258310625942954688883637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83011080834590606251844849 62258310625942954688883637)
  ·
    refine ⟨5836716621182152002082841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62258310625942954688883637 5836716621182152002082841)
    ·
      refine ⟨4377537465886614001562131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5836716621182152002082841 4377537465886614001562131)
      ·
        refine ⟨6566306198829921002343197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377537465886614001562131 6566306198829921002343197)
        ·
          refine ⟨2462364824561220375878699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6566306198829921002343197 2462364824561220375878699)
          ·
            refine ⟨3693547236841830563818049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462364824561220375878699 3693547236841830563818049)
            ·
              refine ⟨2770160427631372922863537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693547236841830563818049 2770160427631372922863537)
              ·
                refine ⟨2077620320723529692147653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2770160427631372922863537 2077620320723529692147653)
                ·
                  refine ⟨389553810135661817277685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077620320723529692147653 389553810135661817277685)
                  ·
                    rfl

theorem cell22_3413940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3413940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413940 prefixEnd_3413940 := by exact prefixLift 3413940
  have htrace : WordTrace (prefixWord ++ tailWord_3413940) baseStart_3413940 baseEnd_3413940 := by
    simpa [prefixWord, tailWord_3413940, baseEnd_3413940] using wordTrace_append hprefix tailTrace_3413940
  have hstable : (prefixWord ++ tailWord_3413940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413940).length < 2 ^ (prefixWord ++ tailWord_3413940).sum := by decide
  have hdescent : baseEnd_3413940 < baseStart_3413940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413960 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 1, 7]
def baseStart_3413960 : Nat := 118140960795 + 3413960 * 2 ^ 59
def prefixEnd_3413960 : Nat := 4983230072969 + 3 ^ 40 * 3413960 * 2
def baseEnd_3413960 : Nat := 1168668276815712066332993

theorem tailTrace_3413960 : CollatzResearch.WordTrace tailWord_3413960 prefixEnd_3413960 1168668276815712066332993 := by
  unfold tailWord_3413960
  simp only [CollatzResearch.WordTrace]
  refine ⟨62258675355906726396747667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83011567141208968528996889 62258675355906726396747667)
  ·
    refine ⟨93388013033860089595121501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62258675355906726396747667 93388013033860089595121501)
    ·
      refine ⟨35020504887697533598170563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93388013033860089595121501 35020504887697533598170563)
      ·
        refine ⟨52530757331546300397255845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35020504887697533598170563 52530757331546300397255845)
        ·
          refine ⟨9849516999664931324485471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52530757331546300397255845 9849516999664931324485471)
          ·
            refine ⟨14774275499497396986728207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9849516999664931324485471 14774275499497396986728207)
            ·
              refine ⟨22161413249246095480092311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14774275499497396986728207 22161413249246095480092311)
              ·
                refine ⟨33242119873869143220138467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22161413249246095480092311 33242119873869143220138467)
                ·
                  refine ⟨49863179810803714830207701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33242119873869143220138467 49863179810803714830207701)
                  ·
                    refine ⟨1168668276815712066332993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49863179810803714830207701 1168668276815712066332993)
                    ·
                      rfl

theorem cell22_3413960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_3413960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413960 prefixEnd_3413960 := by exact prefixLift 3413960
  have htrace : WordTrace (prefixWord ++ tailWord_3413960) baseStart_3413960 baseEnd_3413960 := by
    simpa [prefixWord, tailWord_3413960, baseEnd_3413960] using wordTrace_append hprefix tailTrace_3413960
  have hstable : (prefixWord ++ tailWord_3413960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413960).length < 2 ^ (prefixWord ++ tailWord_3413960).sum := by decide
  have hdescent : baseEnd_3413960 < baseStart_3413960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3413975 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3413975 : Nat := 118140960795 + 3413975 * 2 ^ 59
def prefixEnd_3413975 : Nat := 4983230072969 + 3 ^ 40 * 3413975 * 2
def baseEnd_3413975 : Nat := 1168673411622257027207947

theorem tailTrace_3413975 : CollatzResearch.WordTrace tailWord_3413975 prefixEnd_3413975 1168673411622257027207947 := by
  unfold tailWord_3413975
  simp only [CollatzResearch.WordTrace]
  refine ⟨124517897806759110355291379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83011931871172740236860919 124517897806759110355291379)
  ·
    refine ⟨186776846710138665532937069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124517897806759110355291379 186776846710138665532937069)
    ·
      refine ⟨70041317516301999574851401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186776846710138665532937069 70041317516301999574851401)
      ·
        refine ⟨52530988137226499681138551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70041317516301999574851401 52530988137226499681138551)
        ·
          refine ⟨78796482205839749521707827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52530988137226499681138551 78796482205839749521707827)
          ·
            refine ⟨118194723308759624282561741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78796482205839749521707827 118194723308759624282561741)
            ·
              refine ⟨44323021240784859105960653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118194723308759624282561741 44323021240784859105960653)
              ·
                refine ⟨16621132965294322164735245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44323021240784859105960653 16621132965294322164735245)
                ·
                  refine ⟨6232924861985370811775717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16621132965294322164735245 6232924861985370811775717)
                  ·
                    refine ⟨1168673411622257027207947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6232924861985370811775717 1168673411622257027207947)
                    ·
                      rfl

theorem cell22_3413975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3413975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3413975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3413975 prefixEnd_3413975 := by exact prefixLift 3413975
  have htrace : WordTrace (prefixWord ++ tailWord_3413975) baseStart_3413975 baseEnd_3413975 := by
    simpa [prefixWord, tailWord_3413975, baseEnd_3413975] using wordTrace_append hprefix tailTrace_3413975
  have hstable : (prefixWord ++ tailWord_3413975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3413975).length < 2 ^ (prefixWord ++ tailWord_3413975).sum := by decide
  have hdescent : baseEnd_3413975 < baseStart_3413975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3413975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414073 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 2, 3]
def baseStart_3414073 : Nat := 118140960795 + 3414073 * 2 ^ 59
def prefixEnd_3414073 : Nat := 4983230072969 + 3 ^ 40 * 3414073 * 2
def baseEnd_3414073 : Nat := 1168706959025017438257647

theorem tailTrace_3414073 : CollatzResearch.WordTrace tailWord_3414073 prefixEnd_3414073 1168706959025017438257647 := by
  unfold tailWord_3414073
  simp only [CollatzResearch.WordTrace]
  refine ⟨124521472160404073092358873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83014314773602715394905915 124521472160404073092358873)
  ·
    refine ⟨93391104120303054819269155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124521472160404073092358873 93391104120303054819269155)
    ·
      refine ⟨140086656180454582228903733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93391104120303054819269155 140086656180454582228903733)
      ·
        refine ⟨13133124016917617083959725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140086656180454582228903733 13133124016917617083959725)
        ·
          refine ⟨4924921506344106406484897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13133124016917617083959725 4924921506344106406484897)
          ·
            refine ⟨3693691129758079804863673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924921506344106406484897 3693691129758079804863673)
            ·
              refine ⟨2770268347318559853647755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3693691129758079804863673 2770268347318559853647755)
              ·
                refine ⟨4155402520977839780471633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770268347318559853647755 4155402520977839780471633)
                ·
                  refine ⟨3116551890733379835353725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4155402520977839780471633 3116551890733379835353725)
                  ·
                    refine ⟨1168706959025017438257647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116551890733379835353725 1168706959025017438257647)
                    ·
                      rfl

theorem cell22_3414073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 3].length) (baseStart_3414073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414073 prefixEnd_3414073 := by exact prefixLift 3414073
  have htrace : WordTrace (prefixWord ++ tailWord_3414073) baseStart_3414073 baseEnd_3414073 := by
    simpa [prefixWord, tailWord_3414073, baseEnd_3414073] using wordTrace_append hprefix tailTrace_3414073
  have hstable : (prefixWord ++ tailWord_3414073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414073).length < 2 ^ (prefixWord ++ tailWord_3414073).sum := by decide
  have hdescent : baseEnd_3414073 < baseStart_3414073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414095 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_3414095 : Nat := 118140960795 + 3414095 * 2 ^ 59
def prefixEnd_3414095 : Nat := 4983230072969 + 3 ^ 40 * 3414095 * 2
def baseEnd_3414095 : Nat := 1168714490074616714207579

theorem tailTrace_3414095 : CollatzResearch.WordTrace tailWord_3414095 prefixEnd_3414095 1168714490074616714207579 := by
  unfold tailWord_3414095
  simp only [CollatzResearch.WordTrace]
  refine ⟨124522274566324370849659739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83014849710882913899773159 124522274566324370849659739)
  ·
    refine ⟨186783411849486556274489609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124522274566324370849659739 186783411849486556274489609)
    ·
      refine ⟨140087558887114917205867207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186783411849486556274489609 140087558887114917205867207)
      ·
        refine ⟨210131338330672375808800811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140087558887114917205867207 210131338330672375808800811)
        ·
          refine ⟨315197007496008563713201217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210131338330672375808800811 315197007496008563713201217)
          ·
            refine ⟨236397755622006422784900913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315197007496008563713201217 236397755622006422784900913)
            ·
              refine ⟨177298316716504817088675685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236397755622006422784900913 177298316716504817088675685)
              ·
                refine ⟨33243434384344653204126691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177298316716504817088675685 33243434384344653204126691)
                ·
                  refine ⟨49865151576516979806190037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33243434384344653204126691 49865151576516979806190037)
                  ·
                    refine ⟨1168714490074616714207579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49865151576516979806190037 1168714490074616714207579)
                    ·
                      rfl

theorem cell22_3414095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_3414095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414095 prefixEnd_3414095 := by exact prefixLift 3414095
  have htrace : WordTrace (prefixWord ++ tailWord_3414095) baseStart_3414095 baseEnd_3414095 := by
    simpa [prefixWord, tailWord_3414095, baseEnd_3414095] using wordTrace_append hprefix tailTrace_3414095
  have hstable : (prefixWord ++ tailWord_3414095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414095).length < 2 ^ (prefixWord ++ tailWord_3414095).sum := by decide
  have hdescent : baseEnd_3414095 < baseStart_3414095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414127 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_3414127 : Nat := 118140960795 + 3414127 * 2 ^ 59
def prefixEnd_3414127 : Nat := 4983230072969 + 3 ^ 40 * 3414127 * 2
def baseEnd_3414127 : Nat := 1168725444328579297407481

theorem tailTrace_3414127 : CollatzResearch.WordTrace tailWord_3414127 prefixEnd_3414127 1168725444328579297407481 := by
  unfold tailWord_3414127
  simp only [CollatzResearch.WordTrace]
  refine ⟨124523441702208440314824635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83015627801472293543216423 124523441702208440314824635)
  ·
    refine ⟨186785162553312660472236953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124523441702208440314824635 186785162553312660472236953)
    ·
      refine ⟨140088871914984495354177715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186785162553312660472236953 140088871914984495354177715)
      ·
        refine ⟨210133307872476743031266573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140088871914984495354177715 210133307872476743031266573)
        ·
          refine ⟨78799990452178778636724965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210133307872476743031266573 78799990452178778636724965)
          ·
            refine ⟨14774998209783520994385931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78799990452178778636724965 14774998209783520994385931)
            ·
              refine ⟨22162497314675281491578897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14774998209783520994385931 22162497314675281491578897)
              ·
                refine ⟨16621872986006461118684173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22162497314675281491578897 16621872986006461118684173)
                ·
                  refine ⟨6233202369752422919506565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16621872986006461118684173 6233202369752422919506565)
                  ·
                    refine ⟨1168725444328579297407481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233202369752422919506565 1168725444328579297407481)
                    ·
                      rfl

theorem cell22_3414127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_3414127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414127 prefixEnd_3414127 := by exact prefixLift 3414127
  have htrace : WordTrace (prefixWord ++ tailWord_3414127) baseStart_3414127 baseEnd_3414127 := by
    simpa [prefixWord, tailWord_3414127, baseEnd_3414127] using wordTrace_append hprefix tailTrace_3414127
  have hstable : (prefixWord ++ tailWord_3414127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414127).length < 2 ^ (prefixWord ++ tailWord_3414127).sum := by decide
  have hdescent : baseEnd_3414127 < baseStart_3414127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414189 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3414189 : Nat := 118140960795 + 3414189 * 2 ^ 59
def prefixEnd_3414189 : Nat := 4983230072969 + 3 ^ 40 * 3414189 * 2
def baseEnd_3414189 : Nat := 1168746668195631802357291

theorem tailTrace_3414189 : CollatzResearch.WordTrace tailWord_3414189 prefixEnd_3414189 1168746668195631802357291 := by
  unfold tailWord_3414189
  simp only [CollatzResearch.WordTrace]
  refine ⟨124525703027983824903581621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83017135351989216602387747 124525703027983824903581621)
  ·
    refine ⟨11674284658873483584710777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124525703027983824903581621 11674284658873483584710777)
    ·
      refine ⟨8755713494155112688533083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11674284658873483584710777 8755713494155112688533083)
      ·
        refine ⟨13133570241232669032799625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8755713494155112688533083 13133570241232669032799625)
        ·
          refine ⟨9850177680924501774599719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13133570241232669032799625 9850177680924501774599719)
          ·
            refine ⟨14775266521386752661899579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850177680924501774599719 14775266521386752661899579)
            ·
              refine ⟨22162899782080128992849369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14775266521386752661899579 22162899782080128992849369)
              ·
                refine ⟨16622174836560096744637027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22162899782080128992849369 16622174836560096744637027)
                ·
                  refine ⟨24933262254840145116955541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16622174836560096744637027 24933262254840145116955541)
                  ·
                    refine ⟨1168746668195631802357291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24933262254840145116955541 1168746668195631802357291)
                    ·
                      rfl

theorem cell22_3414189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3414189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414189 prefixEnd_3414189 := by exact prefixLift 3414189
  have htrace : WordTrace (prefixWord ++ tailWord_3414189) baseStart_3414189 baseEnd_3414189 := by
    simpa [prefixWord, tailWord_3414189, baseEnd_3414189] using wordTrace_append hprefix tailTrace_3414189
  have hstable : (prefixWord ++ tailWord_3414189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414189).length < 2 ^ (prefixWord ++ tailWord_3414189).sum := by decide
  have hdescent : baseEnd_3414189 < baseStart_3414189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414204 : List Nat := [2, 2, 2, 3, 3, 1, 1, 8]
def baseStart_3414204 : Nat := 118140960795 + 3414204 * 2 ^ 59
def prefixEnd_3414204 : Nat := 4983230072969 + 3 ^ 40 * 3414204 * 2
def baseEnd_3414204 : Nat := 129861311444686307025805

theorem tailTrace_3414204 : CollatzResearch.WordTrace tailWord_3414204 prefixEnd_3414204 129861311444686307025805 := by
  unfold tailWord_3414204
  simp only [CollatzResearch.WordTrace]
  refine ⟨62263125061464741232688833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83017500081952988310251777 62263125061464741232688833)
  ·
    refine ⟨46697343796098555924516625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62263125061464741232688833 46697343796098555924516625)
    ·
      refine ⟨35023007847073916943387469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46697343796098555924516625 35023007847073916943387469)
      ·
        refine ⟨13133627942652718853770301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35023007847073916943387469 13133627942652718853770301)
        ·
          refine ⟨4925110478494769570163863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13133627942652718853770301 4925110478494769570163863)
          ·
            refine ⟨7387665717742154355245795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925110478494769570163863 7387665717742154355245795)
            ·
              refine ⟨11081498576613231532868693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387665717742154355245795 11081498576613231532868693)
              ·
                refine ⟨129861311444686307025805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11081498576613231532868693 129861311444686307025805)
                ·
                  rfl

theorem cell22_3414204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 8].length) (baseStart_3414204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414204 prefixEnd_3414204 := by exact prefixLift 3414204
  have htrace : WordTrace (prefixWord ++ tailWord_3414204) baseStart_3414204 baseEnd_3414204 := by
    simpa [prefixWord, tailWord_3414204, baseEnd_3414204] using wordTrace_append hprefix tailTrace_3414204
  have hstable : (prefixWord ++ tailWord_3414204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414204).length < 2 ^ (prefixWord ++ tailWord_3414204).sum := by decide
  have hdescent : baseEnd_3414204 < baseStart_3414204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414210 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3414210 : Nat := 118140960795 + 3414210 * 2 ^ 59
def prefixEnd_3414210 : Nat := 4983230072969 + 3 ^ 40 * 3414210 * 2
def baseEnd_3414210 : Nat := 389584618974931582527409

theorem tailTrace_3414210 : CollatzResearch.WordTrace tailWord_3414210 prefixEnd_3414210 389584618974931582527409 := by
  unfold tailWord_3414210
  simp only [CollatzResearch.WordTrace]
  refine ⟨31131617240226936372524021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83017645973938496993397389 31131617240226936372524021)
  ·
    refine ⟨2918589116271275284924127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31131617240226936372524021 2918589116271275284924127)
    ·
      refine ⟨4377883674406912927386191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918589116271275284924127 4377883674406912927386191)
      ·
        refine ⟨6566825511610369391079287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4377883674406912927386191 6566825511610369391079287)
        ·
          refine ⟨9850238267415554086618931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6566825511610369391079287 9850238267415554086618931)
          ·
            refine ⟨14775357401123331129928397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850238267415554086618931 14775357401123331129928397)
            ·
              refine ⟨5540759025421249173723149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14775357401123331129928397 5540759025421249173723149)
              ·
                refine ⟨2077784634532968440146181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5540759025421249173723149 2077784634532968440146181)
                ·
                  refine ⟨389584618974931582527409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077784634532968440146181 389584618974931582527409)
                  ·
                    rfl

theorem cell22_3414210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3414210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414210 prefixEnd_3414210 := by exact prefixLift 3414210
  have htrace : WordTrace (prefixWord ++ tailWord_3414210) baseStart_3414210 baseEnd_3414210 := by
    simpa [prefixWord, tailWord_3414210, baseEnd_3414210] using wordTrace_append hprefix tailTrace_3414210
  have hstable : (prefixWord ++ tailWord_3414210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414210).length < 2 ^ (prefixWord ++ tailWord_3414210).sum := by decide
  have hdescent : baseEnd_3414210 < baseStart_3414210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414242 : List Nat := [3, 3, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3414242 : Nat := 118140960795 + 3414242 * 2 ^ 59
def prefixEnd_3414242 : Nat := 4983230072969 + 3 ^ 40 * 3414242 * 2
def baseEnd_3414242 : Nat := 1168764811178757330782129

theorem tailTrace_3414242 : CollatzResearch.WordTrace tailWord_3414242 prefixEnd_3414242 1168764811178757330782129 := by
  unfold tailWord_3414242
  simp only [CollatzResearch.WordTrace]
  refine ⟨31131909024197953738815245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83018424064527876636840653 31131909024197953738815245)
  ·
    refine ⟨11674465884074232652055717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31131909024197953738815245 11674465884074232652055717)
    ·
      refine ⟨2188962353263918622260447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11674465884074232652055717 2188962353263918622260447)
      ·
        refine ⟨3283443529895877933390671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2188962353263918622260447 3283443529895877933390671)
        ·
          refine ⟨4925165294843816900086007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283443529895877933390671 4925165294843816900086007)
          ·
            refine ⟨7387747942265725350129011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925165294843816900086007 7387747942265725350129011)
            ·
              refine ⟨11081621913398588025193517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7387747942265725350129011 11081621913398588025193517)
              ·
                refine ⟨4155608217524470509447569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11081621913398588025193517 4155608217524470509447569)
                ·
                  refine ⟨3116706163143352882085677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4155608217524470509447569 3116706163143352882085677)
                  ·
                    refine ⟨1168764811178757330782129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116706163143352882085677 1168764811178757330782129)
                    ·
                      rfl

theorem cell22_3414242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3414242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414242 prefixEnd_3414242 := by exact prefixLift 3414242
  have htrace : WordTrace (prefixWord ++ tailWord_3414242) baseStart_3414242 baseEnd_3414242 := by
    simpa [prefixWord, tailWord_3414242, baseEnd_3414242] using wordTrace_append hprefix tailTrace_3414242
  have hstable : (prefixWord ++ tailWord_3414242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414242).length < 2 ^ (prefixWord ++ tailWord_3414242).sum := by decide
  have hdescent : baseEnd_3414242 < baseStart_3414242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414277 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 10]
def baseStart_3414277 : Nat := 118140960795 + 3414277 * 2 ^ 59
def prefixEnd_3414277 : Nat := 4983230072969 + 3 ^ 40 * 3414277 * 2
def baseEnd_3414277 : Nat := 389592264131342968719007

theorem tailTrace_3414277 : CollatzResearch.WordTrace tailWord_3414277 prefixEnd_3414277 389592264131342968719007 := by
  unfold tailWord_3414277
  simp only [CollatzResearch.WordTrace]
  refine ⟨124528912651665015932785085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83019275101110010621856723 124528912651665015932785085)
  ·
    refine ⟨46698342244374380974794407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124528912651665015932785085 46698342244374380974794407)
    ·
      refine ⟨70047513366561571462191611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46698342244374380974794407 70047513366561571462191611)
      ·
        refine ⟨105071270049842357193287417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70047513366561571462191611 105071270049842357193287417)
        ·
          refine ⟨78803452537381767894965563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105071270049842357193287417 78803452537381767894965563)
          ·
            refine ⟨118205178806072651842448345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78803452537381767894965563 118205178806072651842448345)
            ·
              refine ⟨88653884104554488881836259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118205178806072651842448345 88653884104554488881836259)
              ·
                refine ⟨132980826156831733322754389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88653884104554488881836259 132980826156831733322754389)
                ·
                  refine ⟨389592264131342968719007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 132980826156831733322754389 389592264131342968719007)
                  ·
                    rfl

theorem cell22_3414277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_3414277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414277 prefixEnd_3414277 := by exact prefixLift 3414277
  have htrace : WordTrace (prefixWord ++ tailWord_3414277) baseStart_3414277 baseEnd_3414277 := by
    simpa [prefixWord, tailWord_3414277, baseEnd_3414277] using wordTrace_append hprefix tailTrace_3414277
  have hstable : (prefixWord ++ tailWord_3414277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414277).length < 2 ^ (prefixWord ++ tailWord_3414277).sum := by decide
  have hdescent : baseEnd_3414277 < baseStart_3414277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414371 : List Nat := [1, 1, 1, 5, 2, 1, 1, 4, 3, 3]
def baseStart_3414371 : Nat := 118140960795 + 3414371 * 2 ^ 59
def prefixEnd_3414371 : Nat := 4983230072969 + 3 ^ 40 * 3414371 * 2
def baseEnd_3414371 : Nat := 1168808970515043994306733

theorem tailTrace_3414371 : CollatzResearch.WordTrace tailWord_3414371 prefixEnd_3414371 1168808970515043994306733 := by
  unfold tailWord_3414371
  simp only [CollatzResearch.WordTrace]
  refine ⟨124532341113324469986706967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83021560742216313324471311 124532341113324469986706967)
  ·
    refine ⟨186798511669986704980060451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124532341113324469986706967 186798511669986704980060451)
    ·
      refine ⟨280197767504980057470090677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186798511669986704980060451 280197767504980057470090677)
      ·
        refine ⟨26268540703591880387821001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280197767504980057470090677 26268540703591880387821001)
        ·
          refine ⟨19701405527693910290865751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26268540703591880387821001 19701405527693910290865751)
          ·
            refine ⟨29552108291540865436298627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701405527693910290865751 29552108291540865436298627)
            ·
              refine ⟨44328162437311298154447941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29552108291540865436298627 44328162437311298154447941)
              ·
                refine ⟨8311530456995868403958989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44328162437311298154447941 8311530456995868403958989)
                ·
                  refine ⟨3116823921373450651484621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8311530456995868403958989 3116823921373450651484621)
                  ·
                    refine ⟨1168808970515043994306733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116823921373450651484621 1168808970515043994306733)
                    ·
                      rfl

theorem cell22_3414371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 3].length) (baseStart_3414371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414371 prefixEnd_3414371 := by exact prefixLift 3414371
  have htrace : WordTrace (prefixWord ++ tailWord_3414371) baseStart_3414371 baseEnd_3414371 := by
    simpa [prefixWord, tailWord_3414371, baseEnd_3414371] using wordTrace_append hprefix tailTrace_3414371
  have hstable : (prefixWord ++ tailWord_3414371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414371).length < 2 ^ (prefixWord ++ tailWord_3414371).sum := by decide
  have hdescent : baseEnd_3414371 < baseStart_3414371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414384 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 7]
def baseStart_3414384 : Nat := 118140960795 + 3414384 * 2 ^ 59
def prefixEnd_3414384 : Nat := 4983230072969 + 3 ^ 40 * 3414384 * 2
def baseEnd_3414384 : Nat := 389604473560238764577231

theorem tailTrace_3414384 : CollatzResearch.WordTrace tailWord_3414384 prefixEnd_3414384 389604473560238764577231 := by
  unfold tailWord_3414384
  simp only [CollatzResearch.WordTrace]
  refine ⟨62266407631138686603465103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83021876841518248804620137 62266407631138686603465103)
  ·
    refine ⟨93399611446708029905197655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62266407631138686603465103 93399611446708029905197655)
    ·
      refine ⟨140099417170062044857796483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93399611446708029905197655 140099417170062044857796483)
      ·
        refine ⟨210149125755093067286694725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140099417170062044857796483 210149125755093067286694725)
        ·
          refine ⟨39402961079079950116255261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210149125755093067286694725 39402961079079950116255261)
          ·
            refine ⟨14776110404654981293595723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39402961079079950116255261 14776110404654981293595723)
            ·
              refine ⟨22164165606982471940393585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14776110404654981293595723 22164165606982471940393585)
              ·
                refine ⟨16623124205236853955295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22164165606982471940393585 16623124205236853955295189)
                ·
                  refine ⟨389604473560238764577231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16623124205236853955295189 389604473560238764577231)
                  ·
                    rfl

theorem cell22_3414384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 7].length) (baseStart_3414384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414384 prefixEnd_3414384 := by exact prefixLift 3414384
  have htrace : WordTrace (prefixWord ++ tailWord_3414384) baseStart_3414384 baseEnd_3414384 := by
    simpa [prefixWord, tailWord_3414384, baseEnd_3414384] using wordTrace_append hprefix tailTrace_3414384
  have hstable : (prefixWord ++ tailWord_3414384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414384).length < 2 ^ (prefixWord ++ tailWord_3414384).sum := by decide
  have hdescent : baseEnd_3414384 < baseStart_3414384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414390 : List Nat := [5, 1, 1, 4, 2, 1, 8]
def baseStart_3414390 : Nat := 118140960795 + 3414390 * 2 ^ 59
def prefixEnd_3414390 : Nat := 4983230072969 + 3 ^ 40 * 3414390 * 2
def baseEnd_3414390 : Nat := 43289462022345714003025

theorem tailTrace_3414390 : CollatzResearch.WordTrace tailWord_3414390 prefixEnd_3414390 43289462022345714003025 := by
  unfold tailWord_3414390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7783314631265977264478039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 83022022733503757487765749 7783314631265977264478039)
  ·
    refine ⟨11674971946898965896717059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7783314631265977264478039 11674971946898965896717059)
    ·
      refine ⟨17512457920348448845075589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11674971946898965896717059 17512457920348448845075589)
      ·
        refine ⟨3283585860065334158451673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17512457920348448845075589 3283585860065334158451673)
        ·
          refine ⟨2462689395049000618838755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283585860065334158451673 2462689395049000618838755)
          ·
            refine ⟨3694034092573500928258133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462689395049000618838755 3694034092573500928258133)
            ·
              refine ⟨43289462022345714003025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3694034092573500928258133 43289462022345714003025)
              ·
                rfl

theorem cell22_3414390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 8].length) (baseStart_3414390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414390 prefixEnd_3414390 := by exact prefixLift 3414390
  have htrace : WordTrace (prefixWord ++ tailWord_3414390) baseStart_3414390 baseEnd_3414390 := by
    simpa [prefixWord, tailWord_3414390, baseEnd_3414390] using wordTrace_append hprefix tailTrace_3414390
  have hstable : (prefixWord ++ tailWord_3414390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414390).length < 2 ^ (prefixWord ++ tailWord_3414390).sum := by decide
  have hdescent : baseEnd_3414390 < baseStart_3414390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414401 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 7]
def baseStart_3414401 : Nat := 118140960795 + 3414401 * 2 ^ 59
def prefixEnd_3414401 : Nat := 4983230072969 + 3 ^ 40 * 3414401 * 2
def baseEnd_3414401 : Nat := 389606413376044638685547

theorem tailTrace_3414401 : CollatzResearch.WordTrace tailWord_3414401 prefixEnd_3414401 389606413376044638685547 := by
  unfold tailWord_3414401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124533435303215785110299057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83022290202143856740199371 124533435303215785110299057)
  ·
    refine ⟨93400076477411838832724293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124533435303215785110299057 93400076477411838832724293)
    ·
      refine ⟨17512514339514719781135805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93400076477411838832724293 17512514339514719781135805)
      ·
        refine ⟨6567192877318019917925927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17512514339514719781135805 6567192877318019917925927)
        ·
          refine ⟨9850789315977029876888891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567192877318019917925927 9850789315977029876888891)
          ·
            refine ⟨14776183973965544815333337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9850789315977029876888891 14776183973965544815333337)
            ·
              refine ⟨11082137980474158611500003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14776183973965544815333337 11082137980474158611500003)
              ·
                refine ⟨16623206970711237917250005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082137980474158611500003 16623206970711237917250005)
                ·
                  refine ⟨389606413376044638685547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16623206970711237917250005 389606413376044638685547)
                  ·
                    rfl

theorem cell22_3414401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_3414401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414401 prefixEnd_3414401 := by exact prefixLift 3414401
  have htrace : WordTrace (prefixWord ++ tailWord_3414401) baseStart_3414401 baseEnd_3414401 := by
    simpa [prefixWord, tailWord_3414401, baseEnd_3414401] using wordTrace_append hprefix tailTrace_3414401
  have hstable : (prefixWord ++ tailWord_3414401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414401).length < 2 ^ (prefixWord ++ tailWord_3414401).sum := by decide
  have hdescent : baseEnd_3414401 < baseStart_3414401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414431 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_3414431 : Nat := 118140960795 + 3414431 * 2 ^ 59
def prefixEnd_3414431 : Nat := 4983230072969 + 3 ^ 40 * 3414431 * 2
def baseEnd_3414431 : Nat := 1168829509741223837806549

theorem tailTrace_3414431 : CollatzResearch.WordTrace tailWord_3414431 prefixEnd_3414431 1168829509741223837806549 := by
  unfold tailWord_3414431
  simp only [CollatzResearch.WordTrace]
  refine ⟨124534529493107100233891147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83023019662071400155927431 124534529493107100233891147)
  ·
    refine ⟨186801794239660650350836721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124534529493107100233891147 186801794239660650350836721)
    ·
      refine ⟨140101345679745487763127541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186801794239660650350836721 140101345679745487763127541)
      ·
        refine ⟨13134501157476139477793207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140101345679745487763127541 13134501157476139477793207)
        ·
          refine ⟨19701751736214209216689811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13134501157476139477793207 19701751736214209216689811)
          ·
            refine ⟨29552627604321313825034717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701751736214209216689811 29552627604321313825034717)
            ·
              refine ⟨11082235351620492684388019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29552627604321313825034717 11082235351620492684388019)
              ·
                refine ⟨16623353027430739026582029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11082235351620492684388019 16623353027430739026582029)
                ·
                  refine ⟨6233757385286527134968261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16623353027430739026582029 6233757385286527134968261)
                  ·
                    refine ⟨1168829509741223837806549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6233757385286527134968261 1168829509741223837806549)
                    ·
                      rfl

theorem cell22_3414431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_3414431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414431 prefixEnd_3414431 := by exact prefixLift 3414431
  have htrace : WordTrace (prefixWord ++ tailWord_3414431) baseStart_3414431 baseEnd_3414431 := by
    simpa [prefixWord, tailWord_3414431, baseEnd_3414431] using wordTrace_append hprefix tailTrace_3414431
  have hstable : (prefixWord ++ tailWord_3414431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414431).length < 2 ^ (prefixWord ++ tailWord_3414431).sum := by decide
  have hdescent : baseEnd_3414431 < baseStart_3414431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414452 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3414452 : Nat := 118140960795 + 3414452 * 2 ^ 59
def prefixEnd_3414452 : Nat := 4983230072969 + 3 ^ 40 * 3414452 * 2
def baseEnd_3414452 : Nat := 389612232823462261010495

theorem tailTrace_3414452 : CollatzResearch.WordTrace tailWord_3414452 prefixEnd_3414452 389612232823462261010495 := by
  unfold tailWord_3414452
  simp only [CollatzResearch.WordTrace]
  refine ⟨62267647713015510410202805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83023530284020680546937073 62267647713015510410202805)
  ·
    refine ⟨5837591973095204100956513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62267647713015510410202805 5837591973095204100956513)
    ·
      refine ⟨4378193979821403075717385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5837591973095204100956513 4378193979821403075717385)
      ·
        refine ⟨3283645484866052306788039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378193979821403075717385 3283645484866052306788039)
        ·
          refine ⟨4925468227299078460182059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3283645484866052306788039 4925468227299078460182059)
          ·
            refine ⟨7388202340948617690273089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925468227299078460182059 7388202340948617690273089)
            ·
              refine ⟨5541151755711463267704817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7388202340948617690273089 5541151755711463267704817)
              ·
                refine ⟨4155863816783597450778613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541151755711463267704817 4155863816783597450778613)
                ·
                  refine ⟨389612232823462261010495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155863816783597450778613 389612232823462261010495)
                  ·
                    rfl

theorem cell22_3414452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3414452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414452 prefixEnd_3414452 := by exact prefixLift 3414452
  have htrace : WordTrace (prefixWord ++ tailWord_3414452) baseStart_3414452 baseEnd_3414452 := by
    simpa [prefixWord, tailWord_3414452, baseEnd_3414452] using wordTrace_append hprefix tailTrace_3414452
  have hstable : (prefixWord ++ tailWord_3414452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414452).length < 2 ^ (prefixWord ++ tailWord_3414452).sum := by decide
  have hdescent : baseEnd_3414452 < baseStart_3414452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414557 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3414557 : Nat := 118140960795 + 3414557 * 2 ^ 59
def prefixEnd_3414557 : Nat := 4983230072969 + 3 ^ 40 * 3414557 * 2
def baseEnd_3414557 : Nat := 1168872642116201509156163

theorem tailTrace_3414557 : CollatzResearch.WordTrace tailWord_3414557 prefixEnd_3414557 1168872642116201509156163 := by
  unfold tailWord_3414557
  simp only [CollatzResearch.WordTrace]
  refine ⟨124539125090650623752977925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83026083393767082501985283 124539125090650623752977925)
  ·
    refine ⟨23351085954496991953683361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124539125090650623752977925 23351085954496991953683361)
    ·
      refine ⟨17513314465872743965262521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23351085954496991953683361 17513314465872743965262521)
      ·
        refine ⟨13134985849404557973946891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17513314465872743965262521 13134985849404557973946891)
        ·
          refine ⟨19702478774106836960920337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13134985849404557973946891 19702478774106836960920337)
          ·
            refine ⟨14776859080580127720690253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19702478774106836960920337 14776859080580127720690253)
            ·
              refine ⟨5541322155217547895258845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14776859080580127720690253 5541322155217547895258845)
              ·
                refine ⟨2077995808206580460722067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5541322155217547895258845 2077995808206580460722067)
                ·
                  refine ⟨3116993712309870691083101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2077995808206580460722067 3116993712309870691083101)
                  ·
                    refine ⟨1168872642116201509156163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3116993712309870691083101 1168872642116201509156163)
                    ·
                      rfl

theorem cell22_3414557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3414557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414557 prefixEnd_3414557 := by exact prefixLift 3414557
  have htrace : WordTrace (prefixWord ++ tailWord_3414557) baseStart_3414557 baseEnd_3414557 := by
    simpa [prefixWord, tailWord_3414557, baseEnd_3414557] using wordTrace_append hprefix tailTrace_3414557
  have hstable : (prefixWord ++ tailWord_3414557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414557).length < 2 ^ (prefixWord ++ tailWord_3414557).sum := by decide
  have hdescent : baseEnd_3414557 < baseStart_3414557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414574 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 3, 3]
def baseStart_3414574 : Nat := 118140960795 + 3414574 * 2 ^ 59
def prefixEnd_3414574 : Nat := 4983230072969 + 3 ^ 40 * 3414574 * 2
def baseEnd_3414574 : Nat := 1168878461563619131481111

theorem tailTrace_3414574 : CollatzResearch.WordTrace tailWord_3414574 prefixEnd_3414574 1168878461563619131481111 := by
  unfold tailWord_3414574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15567468141448629457043347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83026496754392690437564517 15567468141448629457043347)
  ·
    refine ⟨23351202212172944185565021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15567468141448629457043347 23351202212172944185565021)
    ·
      refine ⟨8756700829564854069586883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23351202212172944185565021 8756700829564854069586883)
      ·
        refine ⟨13135051244347281104380325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8756700829564854069586883 13135051244347281104380325)
        ·
          refine ⟨2462822108315115207071311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13135051244347281104380325 2462822108315115207071311)
          ·
            refine ⟨3694233162472672810606967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462822108315115207071311 3694233162472672810606967)
            ·
              refine ⟨5541349743709009215910451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694233162472672810606967 5541349743709009215910451)
              ·
                refine ⟨8312024615563513823865677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541349743709009215910451 8312024615563513823865677)
                ·
                  refine ⟨3117009230836317683949629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8312024615563513823865677 3117009230836317683949629)
                  ·
                    refine ⟨1168878461563619131481111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117009230836317683949629 1168878461563619131481111)
                    ·
                      rfl

theorem cell22_3414574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_3414574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414574 prefixEnd_3414574 := by exact prefixLift 3414574
  have htrace : WordTrace (prefixWord ++ tailWord_3414574) baseStart_3414574 baseEnd_3414574 := by
    simpa [prefixWord, tailWord_3414574, baseEnd_3414574] using wordTrace_append hprefix tailTrace_3414574
  have hstable : (prefixWord ++ tailWord_3414574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414574).length < 2 ^ (prefixWord ++ tailWord_3414574).sum := by decide
  have hdescent : baseEnd_3414574 < baseStart_3414574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414613 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3414613 : Nat := 118140960795 + 3414613 * 2 ^ 59
def prefixEnd_3414613 : Nat := 4983230072969 + 3 ^ 40 * 3414613 * 2
def baseEnd_3414613 : Nat := 1168891812060636029755991

theorem tailTrace_3414613 : CollatzResearch.WordTrace tailWord_3414613 prefixEnd_3414613 1168891812060636029755991 := by
  unfold tailWord_3414613
  simp only [CollatzResearch.WordTrace]
  refine ⟨124541167578447745317016493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83027445052298496878010995 124541167578447745317016493)
  ·
    refine ⟨46702937841917904493881185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124541167578447745317016493 46702937841917904493881185)
    ·
      refine ⟨35027203381438428370410889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46702937841917904493881185 35027203381438428370410889)
      ·
        refine ⟨26270402536078821277808167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35027203381438428370410889 26270402536078821277808167)
        ·
          refine ⟨39405603804118231916712251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26270402536078821277808167 39405603804118231916712251)
          ·
            refine ⟨59108405706177347875068377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39405603804118231916712251 59108405706177347875068377)
            ·
              refine ⟨44331304279633010906301283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59108405706177347875068377 44331304279633010906301283)
              ·
                refine ⟨66496956419449516359451925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44331304279633010906301283 66496956419449516359451925)
                ·
                  refine ⟨3117044832161696079349309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66496956419449516359451925 3117044832161696079349309)
                  ·
                    refine ⟨1168891812060636029755991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117044832161696079349309 1168891812060636029755991)
                    ·
                      rfl

theorem cell22_3414613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3414613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414613 prefixEnd_3414613 := by exact prefixLift 3414613
  have htrace : WordTrace (prefixWord ++ tailWord_3414613) baseStart_3414613 baseEnd_3414613 := by
    simpa [prefixWord, tailWord_3414613, baseEnd_3414613] using wordTrace_append hprefix tailTrace_3414613
  have hstable : (prefixWord ++ tailWord_3414613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414613).length < 2 ^ (prefixWord ++ tailWord_3414613).sum := by decide
  have hdescent : baseEnd_3414613 < baseStart_3414613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414628 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_3414628 : Nat := 118140960795 + 3414628 * 2 ^ 59
def prefixEnd_3414628 : Nat := 4983230072969 + 3 ^ 40 * 3414628 * 2
def baseEnd_3414628 : Nat := 1168896946867180990630945

theorem tailTrace_3414628 : CollatzResearch.WordTrace tailWord_3414628 prefixEnd_3414628 1168896946867180990630945 := by
  unfold tailWord_3414628
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270857336696701439406269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83027809782262268585875025 62270857336696701439406269)
  ·
    refine ⟨23351571501261263039777351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62270857336696701439406269 23351571501261263039777351)
    ·
      refine ⟨35027357251891894559666027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23351571501261263039777351 35027357251891894559666027)
      ·
        refine ⟨52541035877837841839499041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35027357251891894559666027 52541035877837841839499041)
        ·
          refine ⟨39405776908378381379624281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52541035877837841839499041 39405776908378381379624281)
          ·
            refine ⟨29554332681283786034718211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39405776908378381379624281 29554332681283786034718211)
            ·
              refine ⟨44331499021925679052077317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29554332681283786034718211 44331499021925679052077317)
              ·
                refine ⟨8312156066611064822264497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44331499021925679052077317 8312156066611064822264497)
                ·
                  refine ⟨6234117049958298616698373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8312156066611064822264497 6234117049958298616698373)
                  ·
                    refine ⟨1168896946867180990630945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234117049958298616698373 1168896946867180990630945)
                    ·
                      rfl

theorem cell22_3414628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_3414628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414628 prefixEnd_3414628 := by exact prefixLift 3414628
  have htrace : WordTrace (prefixWord ++ tailWord_3414628) baseStart_3414628 baseEnd_3414628 := by
    simpa [prefixWord, tailWord_3414628, baseEnd_3414628] using wordTrace_append hprefix tailTrace_3414628
  have hstable : (prefixWord ++ tailWord_3414628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414628).length < 2 ^ (prefixWord ++ tailWord_3414628).sum := by decide
  have hdescent : baseEnd_3414628 < baseStart_3414628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414632 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 4]
def baseStart_3414632 : Nat := 118140960795 + 3414632 * 2 ^ 59
def prefixEnd_3414632 : Nat := 4983230072969 + 3 ^ 40 * 3414632 * 2
def baseEnd_3414632 : Nat := 389632772049642104510311

theorem tailTrace_3414632 : CollatzResearch.WordTrace tailWord_3414632 prefixEnd_3414632 389632772049642104510311 := by
  unfold tailWord_3414632
  simp only [CollatzResearch.WordTrace]
  refine ⟨62270930282689455780979075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83027907043585941041305433 62270930282689455780979075)
  ·
    refine ⟨93406395424034183671468613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62270930282689455780979075 93406395424034183671468613)
    ·
      refine ⟨17513699142006409438400365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93406395424034183671468613 17513699142006409438400365)
      ·
        refine ⟨6567637178252403539400137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17513699142006409438400365 6567637178252403539400137)
        ·
          refine ⟨4925727883689302654550103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6567637178252403539400137 4925727883689302654550103)
          ·
            refine ⟨7388591825533953981825155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4925727883689302654550103 7388591825533953981825155)
            ·
              refine ⟨11082887738300930972737733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388591825533953981825155 11082887738300930972737733)
              ·
                refine ⟨2078041450931424557388325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11082887738300930972737733 2078041450931424557388325)
                ·
                  refine ⟨389632772049642104510311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078041450931424557388325 389632772049642104510311)
                  ·
                    rfl

theorem cell22_3414632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 4].length) (baseStart_3414632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414632 prefixEnd_3414632 := by exact prefixLift 3414632
  have htrace : WordTrace (prefixWord ++ tailWord_3414632) baseStart_3414632 baseEnd_3414632 := by
    simpa [prefixWord, tailWord_3414632, baseEnd_3414632] using wordTrace_append hprefix tailTrace_3414632
  have hstable : (prefixWord ++ tailWord_3414632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414632).length < 2 ^ (prefixWord ++ tailWord_3414632).sum := by decide
  have hdescent : baseEnd_3414632 < baseStart_3414632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414641 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_3414641 : Nat := 118140960795 + 3414641 * 2 ^ 59
def prefixEnd_3414641 : Nat := 4983230072969 + 3 ^ 40 * 3414641 * 2
def baseEnd_3414641 : Nat := 1168901397032853290055905

theorem tailTrace_3414641 : CollatzResearch.WordTrace tailWord_3414641 prefixEnd_3414641 1168901397032853290055905 := by
  unfold tailWord_3414641
  simp only [CollatzResearch.WordTrace]
  refine ⟨124542188822346306099035777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83028125881564204066023851 124542188822346306099035777)
  ·
    refine ⟨93406641616759729574276833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124542188822346306099035777 93406641616759729574276833)
    ·
      refine ⟨70054981212569797180707625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93406641616759729574276833 70054981212569797180707625)
      ·
        refine ⟨52541235909427347885530719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70054981212569797180707625 52541235909427347885530719)
        ·
          refine ⟨78811853864141021828296079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52541235909427347885530719 78811853864141021828296079)
          ·
            refine ⟨118217780796211532742444119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78811853864141021828296079 118217780796211532742444119)
            ·
              refine ⟨177326671194317299113666179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118217780796211532742444119 177326671194317299113666179)
              ·
                refine ⟨265990006791475948670499269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177326671194317299113666179 265990006791475948670499269)
                ·
                  refine ⟨49873126273401740375718613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 265990006791475948670499269 49873126273401740375718613)
                  ·
                    refine ⟨1168901397032853290055905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49873126273401740375718613 1168901397032853290055905)
                    ·
                      rfl

theorem cell22_3414641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_3414641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414641 prefixEnd_3414641 := by exact prefixLift 3414641
  have htrace : WordTrace (prefixWord ++ tailWord_3414641) baseStart_3414641 baseEnd_3414641 := by
    simpa [prefixWord, tailWord_3414641, baseEnd_3414641] using wordTrace_append hprefix tailTrace_3414641
  have hstable : (prefixWord ++ tailWord_3414641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414641).length < 2 ^ (prefixWord ++ tailWord_3414641).sum := by decide
  have hdescent : baseEnd_3414641 < baseStart_3414641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414660 : List Nat := [2, 3, 2, 1, 3, 2, 3, 6]
def baseStart_3414660 : Nat := 118140960795 + 3414660 * 2 ^ 59
def prefixEnd_3414660 : Nat := 4983230072969 + 3 ^ 40 * 3414660 * 2
def baseEnd_3414660 : Nat := 129878655680127063758983

theorem tailTrace_3414660 : CollatzResearch.WordTrace tailWord_3414660 prefixEnd_3414660 129878655680127063758983 := by
  unfold tailWord_3414660
  simp only [CollatzResearch.WordTrace]
  refine ⟨62271440904638736171988717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83028587872851648229318289 62271440904638736171988717)
  ·
    refine ⟨23351790339239526064495769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62271440904638736171988717 23351790339239526064495769)
    ·
      refine ⟨17513842754429644548371827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23351790339239526064495769 17513842754429644548371827)
      ·
        refine ⟨26270764131644466822557741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17513842754429644548371827 26270764131644466822557741)
        ·
          refine ⟨9851536549366675058459153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26270764131644466822557741 9851536549366675058459153)
          ·
            refine ⟨7388652412025006293844365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9851536549366675058459153 7388652412025006293844365)
            ·
              refine ⟨2770744654509377360191637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7388652412025006293844365 2770744654509377360191637)
              ·
                refine ⟨129878655680127063758983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2770744654509377360191637 129878655680127063758983)
                ·
                  rfl

theorem cell22_3414660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 6].length) (baseStart_3414660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414660 prefixEnd_3414660 := by exact prefixLift 3414660
  have htrace : WordTrace (prefixWord ++ tailWord_3414660) baseStart_3414660 baseEnd_3414660 := by
    simpa [prefixWord, tailWord_3414660, baseEnd_3414660] using wordTrace_append hprefix tailTrace_3414660
  have hstable : (prefixWord ++ tailWord_3414660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414660).length < 2 ^ (prefixWord ++ tailWord_3414660).sum := by decide
  have hdescent : baseEnd_3414660 < baseStart_3414660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414671 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 9]
def baseStart_3414671 : Nat := 118140960795 + 3414671 * 2 ^ 59
def prefixEnd_3414671 : Nat := 4983230072969 + 3 ^ 40 * 3414671 * 2
def baseEnd_3414671 : Nat := 389637222215314403935271

theorem tailTrace_3414671 : CollatzResearch.WordTrace tailWord_3414671 prefixEnd_3414671 389637222215314403935271 := by
  unfold tailWord_3414671
  simp only [CollatzResearch.WordTrace]
  refine ⟨124543283012237621222627867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83028855341491747481751911 124543283012237621222627867)
  ·
    refine ⟨186814924518356431833941801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124543283012237621222627867 186814924518356431833941801)
    ·
      refine ⟨140111193388767323875456351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186814924518356431833941801 140111193388767323875456351)
      ·
        refine ⟨210166790083150985813184527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140111193388767323875456351 210166790083150985813184527)
        ·
          refine ⟨315250185124726478719776791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210166790083150985813184527 315250185124726478719776791)
          ·
            refine ⟨472875277687089718079665187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315250185124726478719776791 472875277687089718079665187)
            ·
              refine ⟨709312916530634577119497781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472875277687089718079665187 709312916530634577119497781)
              ·
                refine ⟨66498085924746991604952917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709312916530634577119497781 66498085924746991604952917)
                ·
                  refine ⟨389637222215314403935271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66498085924746991604952917 389637222215314403935271)
                  ·
                    rfl

theorem cell22_3414671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_3414671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414671 prefixEnd_3414671 := by exact prefixLift 3414671
  have htrace : WordTrace (prefixWord ++ tailWord_3414671) baseStart_3414671 baseEnd_3414671 := by
    simpa [prefixWord, tailWord_3414671, baseEnd_3414671] using wordTrace_append hprefix tailTrace_3414671
  have hstable : (prefixWord ++ tailWord_3414671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414671).length < 2 ^ (prefixWord ++ tailWord_3414671).sum := by decide
  have hdescent : baseEnd_3414671 < baseStart_3414671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414692 : List Nat := [2, 3, 1, 2, 2, 1, 1, 6, 1, 3]
def baseStart_3414692 : Nat := 118140960795 + 3414692 * 2 ^ 59
def prefixEnd_3414692 : Nat := 4983230072969 + 3 ^ 40 * 3414692 * 2
def baseEnd_3414692 : Nat := 1168918855375106157030749

theorem tailTrace_3414692 : CollatzResearch.WordTrace tailWord_3414692 prefixEnd_3414692 1168918855375106157030749 := by
  unfold tailWord_3414692
  simp only [CollatzResearch.WordTrace]
  refine ⟨62272024472580770904571165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83029365963441027872761553 62272024472580770904571165)
  ·
    refine ⟨23352009177217789089214187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62272024472580770904571165 23352009177217789089214187)
    ·
      refine ⟨35028013765826683633821281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23352009177217789089214187 35028013765826683633821281)
      ·
        refine ⟨26271010324370012725365961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35028013765826683633821281 26271010324370012725365961)
        ·
          refine ⟨19703257743277509544024471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26271010324370012725365961 19703257743277509544024471)
          ·
            refine ⟨29554886614916264316036707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19703257743277509544024471 29554886614916264316036707)
            ·
              refine ⟨44332329922374396474055061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29554886614916264316036707 44332329922374396474055061)
              ·
                refine ⟨2078077965111299834721331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44332329922374396474055061 2078077965111299834721331)
                ·
                  refine ⟨3117116947666949752081997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078077965111299834721331 3117116947666949752081997)
                  ·
                    refine ⟨1168918855375106157030749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117116947666949752081997 1168918855375106157030749)
                    ·
                      rfl

theorem cell22_3414692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_3414692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414692 prefixEnd_3414692 := by exact prefixLift 3414692
  have htrace : WordTrace (prefixWord ++ tailWord_3414692) baseStart_3414692 baseEnd_3414692 := by
    simpa [prefixWord, tailWord_3414692, baseEnd_3414692] using wordTrace_append hprefix tailTrace_3414692
  have hstable : (prefixWord ++ tailWord_3414692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414692).length < 2 ^ (prefixWord ++ tailWord_3414692).sum := by decide
  have hdescent : baseEnd_3414692 < baseStart_3414692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414703 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_3414703 : Nat := 118140960795 + 3414703 * 2 ^ 59
def prefixEnd_3414703 : Nat := 4983230072969 + 3 ^ 40 * 3414703 * 2
def baseEnd_3414703 : Nat := 1168922620899905795005715

theorem tailTrace_3414703 : CollatzResearch.WordTrace tailWord_3414703 prefixEnd_3414703 1168922620899905795005715 := by
  unfold tailWord_3414703
  simp only [CollatzResearch.WordTrace]
  refine ⟨124544450148121690687792763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83029633432081127125195175 124544450148121690687792763)
  ·
    refine ⟨186816675222182536031689145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124544450148121690687792763 186816675222182536031689145)
    ·
      refine ⟨140112506416636902023766859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186816675222182536031689145 140112506416636902023766859)
      ·
        refine ⟨210168759624955353035650289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140112506416636902023766859 210168759624955353035650289)
        ·
          refine ⟨157626569718716514776737717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210168759624955353035650289 157626569718716514776737717)
          ·
            refine ⟨14777490911129673260319161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157626569718716514776737717 14777490911129673260319161)
            ·
              refine ⟨11083118183347254945239371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14777490911129673260319161 11083118183347254945239371)
              ·
                refine ⟨16624677275020882417859057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083118183347254945239371 16624677275020882417859057)
                ·
                  refine ⟨12468507956265661813394293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16624677275020882417859057 12468507956265661813394293)
                  ·
                    refine ⟨1168922620899905795005715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12468507956265661813394293 1168922620899905795005715)
                    ·
                      rfl

theorem cell22_3414703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_3414703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414703 prefixEnd_3414703 := by exact prefixLift 3414703
  have htrace : WordTrace (prefixWord ++ tailWord_3414703) baseStart_3414703 baseEnd_3414703 := by
    simpa [prefixWord, tailWord_3414703, baseEnd_3414703] using wordTrace_append hprefix tailTrace_3414703
  have hstable : (prefixWord ++ tailWord_3414703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414703).length < 2 ^ (prefixWord ++ tailWord_3414703).sum := by decide
  have hdescent : baseEnd_3414703 < baseStart_3414703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414763 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_3414763 : Nat := 118140960795 + 3414763 * 2 ^ 59
def prefixEnd_3414763 : Nat := 4983230072969 + 3 ^ 40 * 3414763 * 2
def baseEnd_3414763 : Nat := 1168943160126085638505531

theorem tailTrace_3414763 : CollatzResearch.WordTrace tailWord_3414763 prefixEnd_3414763 1168943160126085638505531 := by
  unfold tailWord_3414763
  simp only [CollatzResearch.WordTrace]
  refine ⟨124546638527904320934976943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83031092351936213956651295 124546638527904320934976943)
  ·
    refine ⟨186819957791856481402465415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124546638527904320934976943 186819957791856481402465415)
    ·
      refine ⟨280229936687784722103698123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186819957791856481402465415 280229936687784722103698123)
      ·
        refine ⟨420344905031677083155547185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280229936687784722103698123 420344905031677083155547185)
        ·
          refine ⟨315258678773757812366660389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420344905031677083155547185 315258678773757812366660389)
          ·
            refine ⟨59111002270079589818748823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315258678773757812366660389 59111002270079589818748823)
            ·
              refine ⟨88666503405119384728123235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59111002270079589818748823 88666503405119384728123235)
              ·
                refine ⟨132999755107679077092184853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88666503405119384728123235 132999755107679077092184853)
                ·
                  refine ⟨6234363520672456738696165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132999755107679077092184853 6234363520672456738696165)
                  ·
                    refine ⟨1168943160126085638505531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234363520672456738696165 1168943160126085638505531)
                    ·
                      rfl

theorem cell22_3414763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_3414763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414763 prefixEnd_3414763 := by exact prefixLift 3414763
  have htrace : WordTrace (prefixWord ++ tailWord_3414763) baseStart_3414763 baseEnd_3414763 := by
    simpa [prefixWord, tailWord_3414763, baseEnd_3414763] using wordTrace_append hprefix tailTrace_3414763
  have hstable : (prefixWord ++ tailWord_3414763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414763).length < 2 ^ (prefixWord ++ tailWord_3414763).sum := by decide
  have hdescent : baseEnd_3414763 < baseStart_3414763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414765 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3414765 : Nat := 118140960795 + 3414765 * 2 ^ 59
def prefixEnd_3414765 : Nat := 4983230072969 + 3 ^ 40 * 3414765 * 2
def baseEnd_3414765 : Nat := 1168943844766958299955525

theorem tailTrace_3414765 : CollatzResearch.WordTrace tailWord_3414765 prefixEnd_3414765 1168943844766958299955525 := by
  unfold tailWord_3414765
  simp only [CollatzResearch.WordTrace]
  refine ⟨124546711473897075276549749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83031140982598050184366499 124546711473897075276549749)
  ·
    refine ⟨11676254200677850807176539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124546711473897075276549749 11676254200677850807176539)
    ·
      refine ⟨17514381301016776210764809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11676254200677850807176539 17514381301016776210764809)
      ·
        refine ⟨13135785975762582158073607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17514381301016776210764809 13135785975762582158073607)
        ·
          refine ⟨19703678963643873237110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13135785975762582158073607 19703678963643873237110411)
          ·
            refine ⟨29555518445465809855665617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19703678963643873237110411 29555518445465809855665617)
            ·
              refine ⟨22166638834099357391749213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29555518445465809855665617 22166638834099357391749213)
              ·
                refine ⟨8312489562787259021905955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22166638834099357391749213 8312489562787259021905955)
                ·
                  refine ⟨12468734344180888532858933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312489562787259021905955 12468734344180888532858933)
                  ·
                    refine ⟨1168943844766958299955525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12468734344180888532858933 1168943844766958299955525)
                    ·
                      rfl

theorem cell22_3414765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3414765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414765 prefixEnd_3414765 := by exact prefixLift 3414765
  have htrace : WordTrace (prefixWord ++ tailWord_3414765) baseStart_3414765 baseEnd_3414765 := by
    simpa [prefixWord, tailWord_3414765, baseEnd_3414765] using wordTrace_append hprefix tailTrace_3414765
  have hstable : (prefixWord ++ tailWord_3414765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414765).length < 2 ^ (prefixWord ++ tailWord_3414765).sum := by decide
  have hdescent : baseEnd_3414765 < baseStart_3414765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414778 : List Nat := [3, 1, 1, 1, 1, 3, 4, 8]
def baseStart_3414778 : Nat := 118140960795 + 3414778 * 2 ^ 59
def prefixEnd_3414778 : Nat := 4983230072969 + 3 ^ 40 * 3414778 * 2
def baseEnd_3414778 : Nat := 129883143881403399931165

theorem tailTrace_3414778 : CollatzResearch.WordTrace tailWord_3414778 prefixEnd_3414778 129883143881403399931165 := by
  unfold tailWord_3414778
  simp only [CollatzResearch.WordTrace]
  refine ⟨31136796405712494624193247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83031457081899985664515325 31136796405712494624193247)
  ·
    refine ⟨46705194608568741936289871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31136796405712494624193247 46705194608568741936289871)
    ·
      refine ⟨70057791912853112904434807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46705194608568741936289871 70057791912853112904434807)
      ·
        refine ⟨105086687869279669356652211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70057791912853112904434807 105086687869279669356652211)
        ·
          refine ⟨157630031803919504034978317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105086687869279669356652211 157630031803919504034978317)
          ·
            refine ⟨59111261926469814013116869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157630031803919504034978317 59111261926469814013116869)
            ·
              refine ⟨11083361611213090127459413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59111261926469814013116869 11083361611213090127459413)
              ·
                refine ⟨129883143881403399931165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11083361611213090127459413 129883143881403399931165)
                ·
                  rfl

theorem cell22_3414778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_3414778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414778 prefixEnd_3414778 := by exact prefixLift 3414778
  have htrace : WordTrace (prefixWord ++ tailWord_3414778) baseStart_3414778 baseEnd_3414778 := by
    simpa [prefixWord, tailWord_3414778, baseEnd_3414778] using wordTrace_append hprefix tailTrace_3414778
  have hstable : (prefixWord ++ tailWord_3414778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414778).length < 2 ^ (prefixWord ++ tailWord_3414778).sum := by decide
  have hdescent : baseEnd_3414778 < baseStart_3414778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414780 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_3414780 : Nat := 118140960795 + 3414780 * 2 ^ 59
def prefixEnd_3414780 : Nat := 4983230072969 + 3 ^ 40 * 3414780 * 2
def baseEnd_3414780 : Nat := 1168948979573503260830479

theorem tailTrace_3414780 : CollatzResearch.WordTrace tailWord_3414780 prefixEnd_3414780 1168948979573503260830479 := by
  unfold tailWord_3414780
  simp only [CollatzResearch.WordTrace]
  refine ⟨62273629284421366419172897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83031505712561821892230529 62273629284421366419172897)
  ·
    refine ⟨46705221963316024814379673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62273629284421366419172897 46705221963316024814379673)
    ·
      refine ⟨35028916472487018610784755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46705221963316024814379673 35028916472487018610784755)
      ·
        refine ⟨52543374708730527916177133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35028916472487018610784755 52543374708730527916177133)
        ·
          refine ⟨19703765515773947968566425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52543374708730527916177133 19703765515773947968566425)
          ·
            refine ⟨14777824136830460976424819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19703765515773947968566425 14777824136830460976424819)
            ·
              refine ⟨22166736205245691464637229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14777824136830460976424819 22166736205245691464637229)
              ·
                refine ⟨8312526076967134299238961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22166736205245691464637229 8312526076967134299238961)
                ·
                  refine ⟨6234394557725350724429221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8312526076967134299238961 6234394557725350724429221)
                  ·
                    refine ⟨1168948979573503260830479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234394557725350724429221 1168948979573503260830479)
                    ·
                      rfl

theorem cell22_3414780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_3414780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414780 prefixEnd_3414780 := by exact prefixLift 3414780
  have htrace : WordTrace (prefixWord ++ tailWord_3414780) baseStart_3414780 baseEnd_3414780 := by
    simpa [prefixWord, tailWord_3414780, baseEnd_3414780] using wordTrace_append hprefix tailTrace_3414780
  have hstable : (prefixWord ++ tailWord_3414780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414780).length < 2 ^ (prefixWord ++ tailWord_3414780).sum := by decide
  have hdescent : baseEnd_3414780 < baseStart_3414780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414782 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_3414782 : Nat := 118140960795 + 3414782 * 2 ^ 59
def prefixEnd_3414782 : Nat := 4983230072969 + 3 ^ 40 * 3414782 * 2
def baseEnd_3414782 : Nat := 1168949664214375922280473

theorem tailTrace_3414782 : CollatzResearch.WordTrace tailWord_3414782 prefixEnd_3414782 1168949664214375922280473 := by
  unfold tailWord_3414782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15568416439354435897489825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83031554343223658119945733 15568416439354435897489825)
  ·
    refine ⟨11676312329515826923117369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15568416439354435897489825 11676312329515826923117369)
    ·
      refine ⟨8757234247136870192338027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11676312329515826923117369 8757234247136870192338027)
      ·
        refine ⟨13135851370705305288507041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757234247136870192338027 13135851370705305288507041)
        ·
          refine ⟨9851888528028978966380281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13135851370705305288507041 9851888528028978966380281)
          ·
            refine ⟨7388916396021734224785211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9851888528028978966380281 7388916396021734224785211)
            ·
              refine ⟨11083374594032601337177817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7388916396021734224785211 11083374594032601337177817)
              ·
                refine ⟨8312530945524451002883363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11083374594032601337177817 8312530945524451002883363)
                ·
                  refine ⟨12468796418286676504325045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312530945524451002883363 12468796418286676504325045)
                  ·
                    refine ⟨1168949664214375922280473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12468796418286676504325045 1168949664214375922280473)
                    ·
                      rfl

theorem cell22_3414782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_3414782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414782 prefixEnd_3414782 := by exact prefixLift 3414782
  have htrace : WordTrace (prefixWord ++ tailWord_3414782) baseStart_3414782 baseEnd_3414782 := by
    simpa [prefixWord, tailWord_3414782, baseEnd_3414782] using wordTrace_append hprefix tailTrace_3414782
  have hstable : (prefixWord ++ tailWord_3414782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414782).length < 2 ^ (prefixWord ++ tailWord_3414782).sum := by decide
  have hdescent : baseEnd_3414782 < baseStart_3414782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414857 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 5]
def baseStart_3414857 : Nat := 118140960795 + 3414857 * 2 ^ 59
def prefixEnd_3414857 : Nat := 4983230072969 + 3 ^ 40 * 3414857 * 2
def baseEnd_3414857 : Nat := 389658446082366908885081

theorem tailTrace_3414857 : CollatzResearch.WordTrace tailWord_3414857 prefixEnd_3414857 389658446082366908885081 := by
  unfold tailWord_3414857
  simp only [CollatzResearch.WordTrace]
  refine ⟨124550066989563774988898825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83033377993042516659265883 124550066989563774988898825)
  ·
    refine ⟨93412550242172831241674119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124550066989563774988898825 93412550242172831241674119)
    ·
      refine ⟨140118825363259246862511179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93412550242172831241674119 140118825363259246862511179)
      ·
        refine ⟨210178238044888870293766769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140118825363259246862511179 210178238044888870293766769)
        ·
          refine ⟨157633678533666652720325077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210178238044888870293766769 157633678533666652720325077)
          ·
            refine ⟨3694539340632812173132619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 157633678533666652720325077 3694539340632812173132619)
            ·
              refine ⟨5541809010949218259698929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694539340632812173132619 5541809010949218259698929)
              ·
                refine ⟨4156356758211913694774197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5541809010949218259698929 4156356758211913694774197)
                ·
                  refine ⟨389658446082366908885081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4156356758211913694774197 389658446082366908885081)
                  ·
                    rfl

theorem cell22_3414857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 5].length) (baseStart_3414857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414857 prefixEnd_3414857 := by exact prefixLift 3414857
  have htrace : WordTrace (prefixWord ++ tailWord_3414857) baseStart_3414857 baseEnd_3414857 := by
    simpa [prefixWord, tailWord_3414857, baseEnd_3414857] using wordTrace_append hprefix tailTrace_3414857
  have hstable : (prefixWord ++ tailWord_3414857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414857).length < 2 ^ (prefixWord ++ tailWord_3414857).sum := by decide
  have hdescent : baseEnd_3414857 < baseStart_3414857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414861 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3414861 : Nat := 118140960795 + 3414861 * 2 ^ 59
def prefixEnd_3414861 : Nat := 4983230072969 + 3 ^ 40 * 3414861 * 2
def baseEnd_3414861 : Nat := 1168976707528846049555231

theorem tailTrace_3414861 : CollatzResearch.WordTrace tailWord_3414861 prefixEnd_3414861 1168976707528846049555231 := by
  unfold tailWord_3414861
  simp only [CollatzResearch.WordTrace]
  refine ⟨124550212881549283672044437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83033475254366189114696291 124550212881549283672044437)
  ·
    refine ⟨5838291228822622672127083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 124550212881549283672044437 5838291228822622672127083)
    ·
      refine ⟨8757436843233934008190625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838291228822622672127083 8757436843233934008190625)
      ·
        refine ⟨6568077632425450506142969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8757436843233934008190625 6568077632425450506142969)
        ·
          refine ⟨4926058224319087879607227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6568077632425450506142969 4926058224319087879607227)
          ·
            refine ⟨7389087336478631819410841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926058224319087879607227 7389087336478631819410841)
            ·
              refine ⟨5541815502358973864558131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389087336478631819410841 5541815502358973864558131)
              ·
                refine ⟨8312723253538460796837197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541815502358973864558131 8312723253538460796837197)
                ·
                  refine ⟨3117271220076922798813949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8312723253538460796837197 3117271220076922798813949)
                  ·
                    refine ⟨1168976707528846049555231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117271220076922798813949 1168976707528846049555231)
                    ·
                      rfl

theorem cell22_3414861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3414861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414861 prefixEnd_3414861 := by exact prefixLift 3414861
  have htrace : WordTrace (prefixWord ++ tailWord_3414861) baseStart_3414861 baseEnd_3414861 := by
    simpa [prefixWord, tailWord_3414861, baseEnd_3414861] using wordTrace_append hprefix tailTrace_3414861
  have hstable : (prefixWord ++ tailWord_3414861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414861).length < 2 ^ (prefixWord ++ tailWord_3414861).sum := by decide
  have hdescent : baseEnd_3414861 < baseStart_3414861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414885 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3414885 : Nat := 118140960795 + 3414885 * 2 ^ 59
def prefixEnd_3414885 : Nat := 4983230072969 + 3 ^ 40 * 3414885 * 2
def baseEnd_3414885 : Nat := 389661641073105995651719

theorem tailTrace_3414885 : CollatzResearch.WordTrace tailWord_3414885 prefixEnd_3414885 389661641073105995651719 := by
  unfold tailWord_3414885
  simp only [CollatzResearch.WordTrace]
  refine ⟨124551088233462335770918109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83034058822308223847278739 124551088233462335770918109)
  ·
    refine ⟨46706658087548375914094291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124551088233462335770918109 46706658087548375914094291)
    ·
      refine ⟨70059987131322563871141437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46706658087548375914094291 70059987131322563871141437)
      ·
        refine ⟨26272495174245961451678039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70059987131322563871141437 26272495174245961451678039)
        ·
          refine ⟨39408742761368942177517059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26272495174245961451678039 39408742761368942177517059)
          ·
            refine ⟨59113114142053413266275589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39408742761368942177517059 59113114142053413266275589)
            ·
              refine ⟨11083708901635014987426673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59113114142053413266275589 11083708901635014987426673)
              ·
                refine ⟨8312781676226261240570005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11083708901635014987426673 8312781676226261240570005)
                ·
                  refine ⟨389661641073105995651719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8312781676226261240570005 389661641073105995651719)
                  ·
                    rfl

theorem cell22_3414885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3414885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414885 prefixEnd_3414885 := by exact prefixLift 3414885
  have htrace : WordTrace (prefixWord ++ tailWord_3414885) baseStart_3414885 baseEnd_3414885 := by
    simpa [prefixWord, tailWord_3414885, baseEnd_3414885] using wordTrace_append hprefix tailTrace_3414885
  have hstable : (prefixWord ++ tailWord_3414885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414885).length < 2 ^ (prefixWord ++ tailWord_3414885).sum := by decide
  have hdescent : baseEnd_3414885 < baseStart_3414885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414887 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 1, 4]
def baseStart_3414887 : Nat := 118140960795 + 3414887 * 2 ^ 59
def prefixEnd_3414887 : Nat := 4983230072969 + 3 ^ 40 * 3414887 * 2
def baseEnd_3414887 : Nat := 1168985607860190648405151

theorem tailTrace_3414887 : CollatzResearch.WordTrace tailWord_3414887 prefixEnd_3414887 1168985607860190648405151 := by
  unfold tailWord_3414887
  simp only [CollatzResearch.WordTrace]
  refine ⟨124551161179455090112490915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83034107452970060074993943 124551161179455090112490915)
  ·
    refine ⟨186826741769182635168736373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124551161179455090112490915 186826741769182635168736373)
    ·
      refine ⟨17515007040860872047069035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186826741769182635168736373 17515007040860872047069035)
      ·
        refine ⟨26272510561291308070603553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515007040860872047069035 26272510561291308070603553)
        ·
          refine ⟨19704382920968481052952665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26272510561291308070603553 19704382920968481052952665)
          ·
            refine ⟨14778287190726360789714499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19704382920968481052952665 14778287190726360789714499)
            ·
              refine ⟨22167430786089541184571749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14778287190726360789714499 22167430786089541184571749)
              ·
                refine ⟨4156393272391788972107203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22167430786089541184571749 4156393272391788972107203)
                ·
                  refine ⟨6234589908587683458160805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156393272391788972107203 6234589908587683458160805)
                  ·
                    refine ⟨1168985607860190648405151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234589908587683458160805 1168985607860190648405151)
                    ·
                      rfl

theorem cell22_3414887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_3414887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414887 prefixEnd_3414887 := by exact prefixLift 3414887
  have htrace : WordTrace (prefixWord ++ tailWord_3414887) baseStart_3414887 baseEnd_3414887 := by
    simpa [prefixWord, tailWord_3414887, baseEnd_3414887] using wordTrace_append hprefix tailTrace_3414887
  have hstable : (prefixWord ++ tailWord_3414887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414887).length < 2 ^ (prefixWord ++ tailWord_3414887).sum := by decide
  have hdescent : baseEnd_3414887 < baseStart_3414887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414917 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 4, 3]
def baseStart_3414917 : Nat := 118140960795 + 3414917 * 2 ^ 59
def prefixEnd_3414917 : Nat := 4983230072969 + 3 ^ 40 * 3414917 * 2
def baseEnd_3414917 : Nat := 1168995877473280570155059

theorem tailTrace_3414917 : CollatzResearch.WordTrace tailWord_3414917 prefixEnd_3414917 1168995877473280570155059 := by
  unfold tailWord_3414917
  simp only [CollatzResearch.WordTrace]
  refine ⟨124552255369346405236083005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83034836912897603490722003 124552255369346405236083005)
  ·
    refine ⟨46707095763504901963531127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124552255369346405236083005 46707095763504901963531127)
    ·
      refine ⟨70060643645257352945296691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46707095763504901963531127 70060643645257352945296691)
      ·
        refine ⟨105090965467886029417945037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70060643645257352945296691 105090965467886029417945037)
        ·
          refine ⟨39409112050457261031729389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105090965467886029417945037 39409112050457261031729389)
          ·
            refine ⟨14778417018921472886898521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39409112050457261031729389 14778417018921472886898521)
            ·
              refine ⟨11083812764191104665173891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14778417018921472886898521 11083812764191104665173891)
              ·
                refine ⟨16625719146286656997760837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083812764191104665173891 16625719146286656997760837)
                ·
                  refine ⟨3117322339928748187080157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16625719146286656997760837 3117322339928748187080157)
                  ·
                    refine ⟨1168995877473280570155059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117322339928748187080157 1168995877473280570155059)
                    ·
                      rfl

theorem cell22_3414917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 3].length) (baseStart_3414917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414917 prefixEnd_3414917 := by exact prefixLift 3414917
  have htrace : WordTrace (prefixWord ++ tailWord_3414917) baseStart_3414917 baseEnd_3414917 := by
    simpa [prefixWord, tailWord_3414917, baseEnd_3414917] using wordTrace_append hprefix tailTrace_3414917
  have hstable : (prefixWord ++ tailWord_3414917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414917).length < 2 ^ (prefixWord ++ tailWord_3414917).sum := by decide
  have hdescent : baseEnd_3414917 < baseStart_3414917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414932 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3414932 : Nat := 118140960795 + 3414932 * 2 ^ 59
def prefixEnd_3414932 : Nat := 4983230072969 + 3 ^ 40 * 3414932 * 2
def baseEnd_3414932 : Nat := 1169001012279825531030013

theorem tailTrace_3414932 : CollatzResearch.WordTrace tailWord_3414932 prefixEnd_3414932 1169001012279825531030013 := by
  unfold tailWord_3414932
  simp only [CollatzResearch.WordTrace]
  refine ⟨62276401232146031398939525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83035201642861375198586033 62276401232146031398939525)
  ·
    refine ⟨11676825231027380887301161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62276401232146031398939525 11676825231027380887301161)
    ·
      refine ⟨8757618923270535665475871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11676825231027380887301161 8757618923270535665475871)
      ·
        refine ⟨13136428384905803498213807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757618923270535665475871 13136428384905803498213807)
        ·
          refine ⟨19704642577358705247320711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13136428384905803498213807 19704642577358705247320711)
          ·
            refine ⟨29556963866038057870981067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19704642577358705247320711 29556963866038057870981067)
            ·
              refine ⟨44335445799057086806471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29556963866038057870981067 44335445799057086806471601)
              ·
                refine ⟨33251584349292815104853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44335445799057086806471601 33251584349292815104853701)
                ·
                  refine ⟨6234672065492402832160069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33251584349292815104853701 6234672065492402832160069)
                  ·
                    refine ⟨1169001012279825531030013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234672065492402832160069 1169001012279825531030013)
                    ·
                      rfl

theorem cell22_3414932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3414932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414932 prefixEnd_3414932 := by exact prefixLift 3414932
  have htrace : WordTrace (prefixWord ++ tailWord_3414932) baseStart_3414932 baseEnd_3414932 := by
    simpa [prefixWord, tailWord_3414932, baseEnd_3414932] using wordTrace_append hprefix tailTrace_3414932
  have hstable : (prefixWord ++ tailWord_3414932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414932).length < 2 ^ (prefixWord ++ tailWord_3414932).sum := by decide
  have hdescent : baseEnd_3414932 < baseStart_3414932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3414979 : List Nat := [1, 1, 1, 3, 1, 1, 2, 8, 1, 3]
def baseStart_3414979 : Nat := 118140960795 + 3414979 * 2 ^ 59
def prefixEnd_3414979 : Nat := 4983230072969 + 3 ^ 40 * 3414979 * 2
def baseEnd_3414979 : Nat := 1169017101340333075104869

theorem tailTrace_3414979 : CollatzResearch.WordTrace tailWord_3414979 prefixEnd_3414979 1169017101340333075104869 := by
  unfold tailWord_3414979
  simp only [CollatzResearch.WordTrace]
  refine ⟨124554516695121789824839991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83036344463414526549893327 124554516695121789824839991)
  ·
    refine ⟨186831775042682684737259987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124554516695121789824839991 186831775042682684737259987)
    ·
      refine ⟨280247662564024027105889981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186831775042682684737259987 280247662564024027105889981)
      ·
        refine ⟨105092873461509010164708743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280247662564024027105889981 105092873461509010164708743)
        ·
          refine ⟨157639310192263515247063115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105092873461509010164708743 157639310192263515247063115)
          ·
            refine ⟨236458965288395272870594673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157639310192263515247063115 236458965288395272870594673)
            ·
              refine ⟨177344223966296454652946005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236458965288395272870594673 177344223966296454652946005)
              ·
                refine ⟨2078252624605036577964211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 177344223966296454652946005 2078252624605036577964211)
                ·
                  refine ⟨3117378936907554866946317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2078252624605036577964211 3117378936907554866946317)
                  ·
                    refine ⟨1169017101340333075104869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117378936907554866946317 1169017101340333075104869)
                    ·
                      rfl

theorem cell22_3414979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 8, 1, 3].length) (baseStart_3414979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3414979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3414979 prefixEnd_3414979 := by exact prefixLift 3414979
  have htrace : WordTrace (prefixWord ++ tailWord_3414979) baseStart_3414979 baseEnd_3414979 := by
    simpa [prefixWord, tailWord_3414979, baseEnd_3414979] using wordTrace_append hprefix tailTrace_3414979
  have hstable : (prefixWord ++ tailWord_3414979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3414979).length < 2 ^ (prefixWord ++ tailWord_3414979).sum := by decide
  have hdescent : baseEnd_3414979 < baseStart_3414979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3414979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415071 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 4]
def baseStart_3415071 : Nat := 118140960795 + 3415071 * 2 ^ 59
def prefixEnd_3415071 : Nat := 4983230072969 + 3 ^ 40 * 3415071 * 2
def baseEnd_3415071 : Nat := 389682864940158500601529

theorem tailTrace_3415071 : CollatzResearch.WordTrace tailWord_3415071 prefixEnd_3415071 389682864940158500601529 := by
  unfold tailWord_3415071
  simp only [CollatzResearch.WordTrace]
  refine ⟨124557872210788489537189067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83038581473858993024792711 124557872210788489537189067)
  ·
    refine ⟨186836808316182734305783601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124557872210788489537189067 186836808316182734305783601)
    ·
      refine ⟨140127606237137050729337701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186836808316182734305783601 140127606237137050729337701)
      ·
        refine ⟨26273926169463197011750819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140127606237137050729337701 26273926169463197011750819)
        ·
          refine ⟨39410889254194795517626229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26273926169463197011750819 39410889254194795517626229)
          ·
            refine ⟨3694770867580762079777459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39410889254194795517626229 3694770867580762079777459)
            ·
              refine ⟨5542156301371143119666189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3694770867580762079777459 5542156301371143119666189)
              ·
                refine ⟨2078308613014178669874821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5542156301371143119666189 2078308613014178669874821)
                ·
                  refine ⟨389682864940158500601529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078308613014178669874821 389682864940158500601529)
                  ·
                    rfl

theorem cell22_3415071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 4].length) (baseStart_3415071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415071 prefixEnd_3415071 := by exact prefixLift 3415071
  have htrace : WordTrace (prefixWord ++ tailWord_3415071) baseStart_3415071 baseEnd_3415071 := by
    simpa [prefixWord, tailWord_3415071, baseEnd_3415071] using wordTrace_append hprefix tailTrace_3415071
  have hstable : (prefixWord ++ tailWord_3415071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415071).length < 2 ^ (prefixWord ++ tailWord_3415071).sum := by decide
  have hdescent : baseEnd_3415071 < baseStart_3415071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415086 : List Nat := [4, 1, 3, 1, 1, 1, 2, 4, 2, 3]
def baseStart_3415086 : Nat := 118140960795 + 3415086 * 2 ^ 59
def prefixEnd_3415086 : Nat := 4983230072969 + 3 ^ 40 * 3415086 * 2
def baseEnd_3415086 : Nat := 1169053729627020462679541

theorem tailTrace_3415086 : CollatzResearch.WordTrace tailWord_3415086 prefixEnd_3415086 1169053729627020462679541 := by
  unfold tailWord_3415086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15569802413216768387373139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83038946203822764732656741 15569802413216768387373139)
  ·
    refine ⟨23354703619825152581059709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15569802413216768387373139 23354703619825152581059709)
    ·
      refine ⟨8758013857434432217897391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23354703619825152581059709 8758013857434432217897391)
      ·
        refine ⟨13137020786151648326846087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8758013857434432217897391 13137020786151648326846087)
        ·
          refine ⟨19705531179227472490269131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13137020786151648326846087 19705531179227472490269131)
          ·
            refine ⟨29558296768841208735403697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705531179227472490269131 29558296768841208735403697)
            ·
              refine ⟨22168722576630906551552773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29558296768841208735403697 22168722576630906551552773)
              ·
                refine ⟨4156635483118294978416145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22168722576630906551552773 4156635483118294978416145)
                ·
                  refine ⟨3117476612338721233812109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4156635483118294978416145 3117476612338721233812109)
                  ·
                    refine ⟨1169053729627020462679541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117476612338721233812109 1169053729627020462679541)
                    ·
                      rfl

theorem cell22_3415086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_3415086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415086 prefixEnd_3415086 := by exact prefixLift 3415086
  have htrace : WordTrace (prefixWord ++ tailWord_3415086) baseStart_3415086 baseEnd_3415086 := by
    simpa [prefixWord, tailWord_3415086, baseEnd_3415086] using wordTrace_append hprefix tailTrace_3415086
  have hstable : (prefixWord ++ tailWord_3415086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415086).length < 2 ^ (prefixWord ++ tailWord_3415086).sum := by decide
  have hdescent : baseEnd_3415086 < baseStart_3415086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415114 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_3415114 : Nat := 118140960795 + 3415114 * 2 ^ 59
def prefixEnd_3415114 : Nat := 4983230072969 + 3 ^ 40 * 3415114 * 2
def baseEnd_3415114 : Nat := 1169063314599237722979455

theorem tailTrace_3415114 : CollatzResearch.WordTrace tailWord_3415114 prefixEnd_3415114 1169063314599237722979455 := by
  unfold tailWord_3415114
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139860137408176970251099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 83039627033088471920669597 31139860137408176970251099)
  ·
    refine ⟨46709790206112265455376649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31139860137408176970251099 46709790206112265455376649)
    ·
      refine ⟨35032342654584199091532487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46709790206112265455376649 35032342654584199091532487)
      ·
        refine ⟨52548513981876298637298731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35032342654584199091532487 52548513981876298637298731)
        ·
          refine ⟨78822770972814447955948097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52548513981876298637298731 78822770972814447955948097)
          ·
            refine ⟨59117078229610835966961073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78822770972814447955948097 59117078229610835966961073)
            ·
              refine ⟨44337808672208126975220805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59117078229610835966961073 44337808672208126975220805)
              ·
                refine ⟨8313339126039023807853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44337808672208126975220805 8313339126039023807853901)
                ·
                  refine ⟨3117502172264633927945213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8313339126039023807853901 3117502172264633927945213)
                  ·
                    refine ⟨1169063314599237722979455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117502172264633927945213 1169063314599237722979455)
                    ·
                      rfl

theorem cell22_3415114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_3415114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415114 prefixEnd_3415114 := by exact prefixLift 3415114
  have htrace : WordTrace (prefixWord ++ tailWord_3415114) baseStart_3415114 baseEnd_3415114 := by
    simpa [prefixWord, tailWord_3415114, baseEnd_3415114] using wordTrace_append hprefix tailTrace_3415114
  have hstable : (prefixWord ++ tailWord_3415114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415114).length < 2 ^ (prefixWord ++ tailWord_3415114).sum := by decide
  have hdescent : baseEnd_3415114 < baseStart_3415114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415191 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 1, 4]
def baseStart_3415191 : Nat := 118140960795 + 3415191 * 2 ^ 59
def prefixEnd_3415191 : Nat := 4983230072969 + 3 ^ 40 * 3415191 * 2
def baseEnd_3415191 : Nat := 1169089673272835188804219

theorem tailTrace_3415191 : CollatzResearch.WordTrace tailWord_3415191 prefixEnd_3415191 1169089673272835188804219 := by
  unfold tailWord_3415191
  simp only [CollatzResearch.WordTrace]
  refine ⟨124562248970353750031557427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83041499313569166687704951 124562248970353750031557427)
  ·
    refine ⟨186843373455530625047336141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124562248970353750031557427 186843373455530625047336141)
    ·
      refine ⟨70066265045823984392751053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186843373455530625047336141 70066265045823984392751053)
      ·
        refine ⟨26274849392183994147281645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70066265045823984392751053 26274849392183994147281645)
        ·
          refine ⟨9853068522068997805230617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26274849392183994147281645 9853068522068997805230617)
          ·
            refine ⟨7389801391551748353922963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9853068522068997805230617 7389801391551748353922963)
            ·
              refine ⟨11084702087327622530884445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389801391551748353922963 11084702087327622530884445)
              ·
                refine ⟨4156763282747858449081667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11084702087327622530884445 4156763282747858449081667)
                ·
                  refine ⟨6235144924121787673622501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156763282747858449081667 6235144924121787673622501)
                  ·
                    refine ⟨1169089673272835188804219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6235144924121787673622501 1169089673272835188804219)
                    ·
                      rfl

theorem cell22_3415191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_3415191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415191 prefixEnd_3415191 := by exact prefixLift 3415191
  have htrace : WordTrace (prefixWord ++ tailWord_3415191) baseStart_3415191 baseEnd_3415191 := by
    simpa [prefixWord, tailWord_3415191, baseEnd_3415191] using wordTrace_append hprefix tailTrace_3415191
  have hstable : (prefixWord ++ tailWord_3415191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415191).length < 2 ^ (prefixWord ++ tailWord_3415191).sum := by decide
  have hdescent : baseEnd_3415191 < baseStart_3415191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415356 : List Nat := [2, 2, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_3415356 : Nat := 118140960795 + 3415356 * 2 ^ 59
def prefixEnd_3415356 : Nat := 4983230072969 + 3 ^ 40 * 3415356 * 2
def baseEnd_3415356 : Nat := 1169146156144829758428713

theorem tailTrace_3415356 : CollatzResearch.WordTrace tailWord_3415356 prefixEnd_3415356 1169146156144829758428713 := by
  unfold tailWord_3415356
  simp only [CollatzResearch.WordTrace]
  refine ⟨62284133507377991605656961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 83045511343170655474209281 62284133507377991605656961)
  ·
    refine ⟨46713100130533493704242721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62284133507377991605656961 46713100130533493704242721)
    ·
      refine ⟨35034825097900120278182041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46713100130533493704242721 35034825097900120278182041)
      ·
        refine ⟨26276118823425090208636531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35034825097900120278182041 26276118823425090208636531)
        ·
          refine ⟨39414178235137635312954797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26276118823425090208636531 39414178235137635312954797)
          ·
            refine ⟨14780316838176613242358049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39414178235137635312954797 14780316838176613242358049)
            ·
              refine ⟨11085237628632459931768537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14780316838176613242358049 11085237628632459931768537)
              ·
                refine ⟨8313928221474344948826403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11085237628632459931768537 8313928221474344948826403)
                ·
                  refine ⟨12470892332211517423239605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313928221474344948826403 12470892332211517423239605)
                  ·
                    refine ⟨1169146156144829758428713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12470892332211517423239605 1169146156144829758428713)
                    ·
                      rfl

theorem cell22_3415356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_3415356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415356 prefixEnd_3415356 := by exact prefixLift 3415356
  have htrace : WordTrace (prefixWord ++ tailWord_3415356) baseStart_3415356 baseEnd_3415356 := by
    simpa [prefixWord, tailWord_3415356, baseEnd_3415356] using wordTrace_append hprefix tailTrace_3415356
  have hstable : (prefixWord ++ tailWord_3415356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415356).length < 2 ^ (prefixWord ++ tailWord_3415356).sum := by decide
  have hdescent : baseEnd_3415356 < baseStart_3415356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415401 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 5, 3]
def baseStart_3415401 : Nat := 118140960795 + 3415401 * 2 ^ 59
def prefixEnd_3415401 : Nat := 4983230072969 + 3 ^ 40 * 3415401 * 2
def baseEnd_3415401 : Nat := 1169161560564464641053575

theorem tailTrace_3415401 : CollatzResearch.WordTrace tailWord_3415401 prefixEnd_3415401 1169161560564464641053575 := by
  unfold tailWord_3415401
  simp only [CollatzResearch.WordTrace]
  refine ⟨124569908299592955896702057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 83046605533061970597801371 124569908299592955896702057)
  ·
    refine ⟨93427431224694716922526543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124569908299592955896702057 93427431224694716922526543)
    ·
      refine ⟨140141146837042075383789815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93427431224694716922526543 140141146837042075383789815)
      ·
        refine ⟨210211720255563113075684723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140141146837042075383789815 210211720255563113075684723)
        ·
          refine ⟨315317580383344669613527085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210211720255563113075684723 315317580383344669613527085)
          ·
            refine ⟨118244092643754251105072657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315317580383344669613527085 118244092643754251105072657)
            ·
              refine ⟨88683069482815688328804493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118244092643754251105072657 88683069482815688328804493)
              ·
                refine ⟨33256151056055883123301685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88683069482815688328804493 33256151056055883123301685)
                ·
                  refine ⟨3117764161505239042809533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33256151056055883123301685 3117764161505239042809533)
                  ·
                    refine ⟨1169161560564464641053575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3117764161505239042809533 1169161560564464641053575)
                    ·
                      rfl

theorem cell22_3415401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 3].length) (baseStart_3415401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415401 prefixEnd_3415401 := by exact prefixLift 3415401
  have htrace : WordTrace (prefixWord ++ tailWord_3415401) baseStart_3415401 baseEnd_3415401 := by
    simpa [prefixWord, tailWord_3415401, baseEnd_3415401] using wordTrace_append hprefix tailTrace_3415401
  have hstable : (prefixWord ++ tailWord_3415401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415401).length < 2 ^ (prefixWord ++ tailWord_3415401).sum := by decide
  have hdescent : baseEnd_3415401 < baseStart_3415401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3415422 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 2, 4]
def baseStart_3415422 : Nat := 118140960795 + 3415422 * 2 ^ 59
def prefixEnd_3415422 : Nat := 4983230072969 + 3 ^ 40 * 3415422 * 2
def baseEnd_3415422 : Nat := 1169168749293627586278511

theorem tailTrace_3415422 : CollatzResearch.WordTrace tailWord_3415422 prefixEnd_3415422 1169168749293627586278511 := by
  unfold tailWord_3415422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15571334279064609560402065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 83047116155011250988811013 15571334279064609560402065)
  ·
    refine ⟨11678500709298457170301549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15571334279064609560402065 11678500709298457170301549)
    ·
      refine ⟨4379437765986921438863081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11678500709298457170301549 4379437765986921438863081)
      ·
        refine ⟨3284578324490191079147311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4379437765986921438863081 3284578324490191079147311)
        ·
          refine ⟨4926867486735286618720967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284578324490191079147311 4926867486735286618720967)
          ·
            refine ⟨7390301230102929928081451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926867486735286618720967 7390301230102929928081451)
            ·
              refine ⟨11085451845154394892122177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390301230102929928081451 11085451845154394892122177)
              ·
                refine ⟨8314088883865796169091633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11085451845154394892122177 8314088883865796169091633)
                ·
                  refine ⟨6235566662899347126818725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8314088883865796169091633 6235566662899347126818725)
                  ·
                    refine ⟨1169168749293627586278511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6235566662899347126818725 1169168749293627586278511)
                    ·
                      rfl

theorem cell22_3415422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_3415422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3415422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3415422 prefixEnd_3415422 := by exact prefixLift 3415422
  have htrace : WordTrace (prefixWord ++ tailWord_3415422) baseStart_3415422 baseEnd_3415422 := by
    simpa [prefixWord, tailWord_3415422, baseEnd_3415422] using wordTrace_append hprefix tailTrace_3415422
  have hstable : (prefixWord ++ tailWord_3415422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3415422).length < 2 ^ (prefixWord ++ tailWord_3415422).sum := by decide
  have hdescent : baseEnd_3415422 < baseStart_3415422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3415422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
